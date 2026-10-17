#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ULTRA-MEGA IPTV COLLECTOR 6.1
=============================
Единый мощный коллектор/чекер IPTV, объединяющий:

  • ULTRA IPTV CHECKER 5.x  — append-only архив, self-healing, орбиты,
    diversity, rate-limit, SQLite + ML-наблюдения, telemetry
  • RU IPTV MEGA PARSER     — каноническая база каналов (CSV/JSON/PY),
    агрегация по db_id/алиасам, EPG, russian-priority, Stable-состояние

Ключевые свойства (ничего не теряется):
  - НЕ удаляет старые записи и мёртвые потоки
  - НЕ схлопывает одинаковые названия / URL в архиве
  - Каждый проход только ДОБАВЛЯЕТ
  - Альтернативы ищутся по каноническому identity + fuzzy + орбиты/качество
  - Цель: ≥ MIN_ALTERNATIVES реально рабочих разнообразных потоков на канал
  - Внешняя база каналов загружается безопасно (AST/literal_eval, без exec)
  - Append-only: records.jsonl, diagnostics.jsonl, alternatives.jsonl
  - Постоянный каталог output_iptv/ со Stable / Mega / Ultra + SQLite + ML
  - Никакой дедупликации источников/записей: повторные URL сохраняются как повторы
  - Параметры авторизации в URL сохраняются, но редактируются в логах

Зависимости:
    pip install aiohttp
Опционально:
    ffprobe / ffmpeg

Пример:
    python ultra_mega_iptv.py --passes 2 --workers 64 --alt-workers 48
    python ultra_mega_iptv.py -s my.m3u --source-list sources.txt --ffprobe
"""

from __future__ import annotations

import argparse
import ast
import asyncio
import csv
import gzip
import hashlib
import io
import json
import logging
import math
import os
import platform
import random
import re
import socket
import sqlite3
import statistics
import subprocess
import sys
import time
import unicodedata
import xml.etree.ElementTree as ET
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone
from difflib import SequenceMatcher
from pathlib import Path
from typing import Any, Iterable, Optional
from urllib.parse import quote, urljoin, urlparse, urlsplit, urlunsplit

import aiohttp

# ---------------------------------------------------------------------------
# VERSION / POLICY
# ---------------------------------------------------------------------------
VERSION = "6.1-ULTRA-MEGA-APPEND-ONLY"

DEFAULT_SOURCE_WORKERS = 64
DEFAULT_CHECK_WORKERS = 64
DEFAULT_ALT_WORKERS = 48
DEFAULT_OPS_PER_SECOND = 85.0
DEFAULT_MIN_ALTERNATIVES = 12
DEFAULT_TARGET_ALTERNATIVES = 20
DEFAULT_ALTERNATIVE_CANDIDATES = 200
DEFAULT_SIMILARITY = 0.60
STREAM_CHECK_RETRIES = 2
SOURCE_FETCH_RETRIES = 2
CONNECT_TIMEOUT = 6
READ_TIMEOUT = 14
MAX_SOURCE_BYTES = 80 * 1024 * 1024
CACHE_TTL = 6 * 3600
STABLE_LATENCY_THRESHOLD_MS = 1500
ALT_INDEX_MIN_TOKEN_LEN = 3
ALT_DIVERSITY_BONUS = 0.08

ORBIT_SEARCH_ORDER = (
    "-1", "+0", "+1", "+2", "+3", "+4", "+5", "+6", "+7", "+8", "+9",
    "+10", "+11",
)
ORBIT_QUALITY_TARGETS = ("SD", "HD", "FHD")
ORBIT_SEARCH_QUALITY_BONUS = 0.12
ORBIT_MISSING_BONUS = 0.20

CINERAMA_HOST_REPLACEMENTS = {
    "https://stream8.cinerama.uz": "https://stream1.cinerama.uz",
    "http://stream8.cinerama.uz": "http://stream1.cinerama.uz",
}

DEFAULT_UA = (
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 "
    "(KHTML, like Gecko) Chrome/140 Safari/537.36 "
    "Ultra-Mega-IPTV/6.0"
)
USER_AGENT_POOL = [
    DEFAULT_UA,
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/140 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/605.1.15 Version/17.6 Safari/605.1.15",
    "Mozilla/5.0 (X11; Linux x86_64; rv:131.0) Gecko/20100101 Firefox/131.0",
    "VLC/3.0.20 LibVLC/3.0.20",
    "Lavf/60.16.100",
]

GENERATED_NAMES = {
    "best.m3u", "online.m3u", "all.m3u", "all_with_alts.m3u",
    "results.json", "records.jsonl", "diagnostics.jsonl",
    "alternatives.jsonl", "run_state.json", "channels_report.json",
    "Stable.m3u", "Mega.m3u", "Ultra.m3u", "Stable_Ru_IPTV.m3u",
}

BAD_NAME_TOKENS = {
    "xxx", "porn", "porno", "pornhub", "adult", "sex", "erotic", "18+",
    "казино", "casino", "bet", "ставки", "букмекер",
}

RU_WORDS = {
    "россия", "российский", "русский", "русская", "москва", "мск",
    "санкт-петербург", "петербург", "питер", "регион", "область", "край",
    "республика", "чувашия", "татарстан", "башкортостан", "сибирь", "урал",
    "кубань", "дон", "сахалин", "калининград", "новосибирск", "екатеринбург",
    "казань", "самара", "омск", "томск", "владивосток", "хабаровск",
    "архангельск", "мурманск", "рус", "ru", "cis", "снг", "беларусь",
    "казахстан", "кыргызстан", "узбекистан", "армения", "азербайджан", "молдова",
}

REGION_MARKERS = {
    "RU": (".ru", "russia", "россия", "moscow", "москва", "spb", "питер",
           "wink", "rostelecom", "rt", "nginx", "rutube"),
    "KZ": (".kz", "kaz", "kazakh", "kazakhstan", "qazaq", "almaty", "astana"),
    "BY": (".by", "belarus", "belarusian", "минск", "minsk"),
    "UZ": (".uz", "uzbek", "uzbekistan", "tashkent", "samarkand"),
    "TJ": (".tj", "tajik", "tajikistan", "dushanbe", "khujand"),
    "TM": (".tm", "turkmen", "ashgabat"),
    "KG": (".kg", "kyrgyz", "bishkek"),
}

NON_STREAM_HOSTS = (
    "youtube.com", "youtu.be", "vk.com", "vk.ru", "rutube.ru",
    "telegram.me", "t.me", "instagram.com", "facebook.com",
)

SPECIAL_CHANNEL_TERMS = (
    "ключ", "хит", "hit", "hit hd", "fан", "fan", "fan hd", "sumiko",
    "сапфир", "сапфир hd", "amedia hit", "amedia hit hd", "amedia",
    "кинеко", "нтв хит", "нтв-хит", "старт", "старт hd",
    "романтичное", "романтичное hd", "кинопоказ", "кинопоказ hd",
    "наше", "наше hd", "премиальное", "премиальное hd",
    "остросюжетное", "остросюжетное hd", "советская киноклассика",
    "моя стихия", "моя стихия hd", "мосфильм", "мосфильм hd",
)

# External channel database (safe load)
CHANNEL_DB_CSV_URL = "https://raw.githubusercontent.com/findmydevice364-hub/Iptv-ru-full2/main/channel_database/channels.csv"
CHANNEL_DB_JSON_URL = "https://raw.githubusercontent.com/findmydevice364-hub/Iptv-ru-full2/main/channel_database/channels.json"
CHANNEL_DB_PY_URL = "https://raw.githubusercontent.com/findmydevice364-hub/Iptv-ru-full2/main/channel_database/channels_data.py"
CHANNEL_DB_MAX_BYTES = 64 * 1024 * 1024
CHANNEL_DB_MATCH_THRESHOLD = 0.72
CHANNEL_DB_ALIAS_MATCH = 0.98

# Local DB filenames (priority order: cwd, script dir, output dir)
LOCAL_CHANNEL_DB_FILES = (
    "channels.csv",
    "channels.json",
    "channels_data.py",
    "channel_database/channels.csv",
    "channel_database/channels.json",
    "channel_database/channels_data.py",
    "channel_db.csv",
    "channel_db.json",
)

EPG_SOURCES = [
    ("epg.one", "https://epg.one/epg2.xml.gz"),
    ("teleguide", "https://www.teleguide.info/download/new3/xmltv.xml.gz"),
]



# Вспомогательная встроенная БД: канонические имена + алиасы для сопоставления
# орбит (+0/+1/+2…) и версий качества (SD/HD/FHD). Основная БД — local/remote.
BUILTIN_CHANNEL_DB: list[dict] = [
    {"id": "1tv.ru", "name": "Первый канал", "aliases": ["1TV", "Первый", "Channel One", "1 канал", "ОРТ", "Первый канал HD", "Первый канал +0", "Первый канал +1", "Первый канал +2", "Первый канал +3", "Первый канал +4", "Первый канал +7"], "country": "RU", "language": "ru", "categories": ["Общие"]},
    {"id": "russia1.ru", "name": "Россия 1", "aliases": ["Россия-1", "RTR", "Russia 1", "Россия", "Россия 1 HD", "Россия 1 +0", "Россия 1 +1", "Россия 1 +2", "Россия 1 +3", "Россия 1 +4", "Россия 1 +7"], "country": "RU", "language": "ru", "categories": ["Общие"]},
    {"id": "matchtv.ru", "name": "Матч ТВ", "aliases": ["Match TV", "Матч", "МатчТВ", "Матч ТВ HD", "Матч ТВ +0", "Матч ТВ +1", "Матч ТВ +2", "Матч ТВ +3", "Матч ТВ +4"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "ntv.ru", "name": "НТВ", "aliases": ["NTV", "НТВ HD", "НТВ +0", "НТВ +1", "НТВ +2", "НТВ +3", "НТВ +4", "НТВ +7"], "country": "RU", "language": "ru", "categories": ["Общие"]},
    {"id": "5tv.ru", "name": "Пятый канал", "aliases": ["5 канал", "Channel 5", "Пятый", "Пятый канал HD", "Пятый канал +0", "Пятый канал +1", "Пятый канал +2"], "country": "RU", "language": "ru", "categories": ["Общие"]},
    {"id": "russia-k.ru", "name": "Россия К", "aliases": ["Культура", "Россия Культура", "Russia K", "Россия К HD", "Культура +0", "Культура +1", "Культура +2"], "country": "RU", "language": "ru", "categories": ["Культура"]},
    {"id": "russia24.ru", "name": "Россия 24", "aliases": ["Россия-24", "Russia 24", "Вести 24", "Россия 24 HD", "Россия 24 +0", "Россия 24 +1"], "country": "RU", "language": "ru", "categories": ["Новости"]},
    {"id": "karusel.ru", "name": "Карусель", "aliases": ["Karusel", "Карусель HD", "Карусель +0", "Карусель +1", "Карусель +2", "Карусель +3", "Карусель +4"], "country": "RU", "language": "ru", "categories": ["Детские"]},
    {"id": "otr.ru", "name": "ОТР", "aliases": ["Общественное телевидение России", "OTR", "ОТР HD", "ОТР +0", "ОТР +1"], "country": "RU", "language": "ru", "categories": ["Общие"]},
    {"id": "tvc.ru", "name": "ТВ Центр", "aliases": ["ТВЦ", "TV Center", "ТВЦ HD", "ТВ Центр HD", "ТВЦ +0", "ТВЦ +1", "ТВЦ +2"], "country": "RU", "language": "ru", "categories": ["Общие"]},
    {"id": "ren.tv", "name": "РЕН ТВ", "aliases": ["REN TV", "РЕН", "РЕНТВ", "РЕН ТВ HD", "РЕН ТВ +0", "РЕН ТВ +1", "РЕН ТВ +2", "РЕН ТВ +3", "РЕН ТВ +4"], "country": "RU", "language": "ru", "categories": ["Общие"]},
    {"id": "sts.ru", "name": "СТС", "aliases": ["STS", "CTC", "СТС HD", "СТС +0", "СТС +1", "СТС +2", "СТС +3", "СТС +4", "СТС +7"], "country": "RU", "language": "ru", "categories": ["Развлекательные"]},
    {"id": "domashniy.ru", "name": "Домашний", "aliases": ["Domashniy", "Домашний HD", "Домашний +0", "Домашний +1", "Домашний +2", "Домашний +3", "Домашний +4"], "country": "RU", "language": "ru", "categories": ["Развлекательные"]},
    {"id": "tv3.ru", "name": "ТВ-3", "aliases": ["TV-3", "ТВ3", "TV3", "ТВ-3 HD", "ТВ-3 +0", "ТВ-3 +1", "ТВ-3 +2", "ТВ-3 +3", "ТВ-3 +4"], "country": "RU", "language": "ru", "categories": ["Развлекательные"]},
    {"id": "friday.ru", "name": "Пятница!", "aliases": ["Пятница", "Friday", "Friday!", "Пятница HD", "Пятница +0", "Пятница +1", "Пятница +2", "Пятница +3", "Пятница +4"], "country": "RU", "language": "ru", "categories": ["Развлекательные"]},
    {"id": "zvezda.ru", "name": "Звезда", "aliases": ["Zvezda", "ТВ Звезда", "Звезда HD", "Звезда +0", "Звезда +1", "Звезда +2"], "country": "RU", "language": "ru", "categories": ["Общие"]},
    {"id": "mir.ru", "name": "Мир", "aliases": ["Mir", "ТВ Мир", "Мир HD", "Мир +0", "Мир +1", "Мир +2", "Мир +3"], "country": "RU", "language": "ru", "categories": ["Общие"]},
    {"id": "tnt.ru", "name": "ТНТ", "aliases": ["TNT", "ТНТ HD", "ТНТ +0", "ТНТ +1", "ТНТ +2", "ТНТ +3", "ТНТ +4", "ТНТ +7"], "country": "RU", "language": "ru", "categories": ["Развлекательные"]},
    {"id": "muztv.ru", "name": "МУЗ-ТВ", "aliases": ["МУЗ ТВ", "Muz-TV", "MuzTV", "МУЗ-ТВ HD", "МУЗ-ТВ +0", "МУЗ-ТВ +1"], "country": "RU", "language": "ru", "categories": ["Музыка"]},
    {"id": "che.ru", "name": "Че!", "aliases": ["Че", "Che", "Че! HD", "Че +0", "Че +1", "Че +2"], "country": "RU", "language": "ru", "categories": ["Развлекательные"]},
    {"id": "u.ru", "name": "Ю", "aliases": ["Ю ТВ", "U TV", "Ю HD", "Ю +0", "Ю +1", "Ю +2"], "country": "RU", "language": "ru", "categories": ["Развлекательные"]},
    {"id": "2x2.ru", "name": "2x2", "aliases": ["2х2", "2X2", "2x2 HD", "2x2 +0", "2x2 +1", "2x2 +2"], "country": "RU", "language": "ru", "categories": ["Развлекательные"]},
    {"id": "tnt4.ru", "name": "ТНТ4", "aliases": ["TNT4", "ТНТ 4", "ТНТ4 HD", "ТНТ4 +0", "ТНТ4 +1", "ТНТ4 +2"], "country": "RU", "language": "ru", "categories": ["Развлекательные"]},
    {"id": "matchpremier.ru", "name": "Матч! Премьер", "aliases": ["Матч Премьер", "Match Premier", "Матч! Премьер HD", "Матч! Премьер +0", "Матч! Премьер +1", "Матч! Премьер +2"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "matchfootball1.ru", "name": "Матч! Футбол 1", "aliases": ["Матч Футбол 1", "Match Football 1", "Матч! Футбол 1 HD", "Матч! Футбол 1 +0", "Матч! Футбол 1 +1"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "matchfootball2.ru", "name": "Матч! Футбол 2", "aliases": ["Матч Футбол 2", "Match Football 2", "Матч! Футбол 2 HD", "Матч! Футбол 2 +0", "Матч! Футбол 2 +1"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "matchfootball3.ru", "name": "Матч! Футбол 3", "aliases": ["Матч Футбол 3", "Match Football 3", "Матч! Футбол 3 HD"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "matcharena.ru", "name": "Матч! Арена", "aliases": ["Матч Арена", "Match Arena", "Матч! Арена HD"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "matchgame.ru", "name": "Матч! Игра", "aliases": ["Матч Игра", "Match Igra", "Матч! Игра HD"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "matchboets.ru", "name": "Матч! Боец", "aliases": ["Матч Боец", "Match Boets", "Матч! Боец HD"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "khl.ru", "name": "КХЛ ТВ", "aliases": ["KHL", "КХЛ", "KHL TV", "КХЛ HD", "КХЛ ТВ HD"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "eurosport1.ru", "name": "Eurosport 1", "aliases": ["EuroSport 1", "Евроспорт 1", "Eurosport 1 HD"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "eurosport2.ru", "name": "Eurosport 2", "aliases": ["EuroSport 2", "Евроспорт 2", "Eurosport 2 HD"], "country": "RU", "language": "ru", "categories": ["Спорт"]},
    {"id": "kinopokaz.ru", "name": "Кинопоказ", "aliases": ["Кинопоказ HD", "Кинопоказ +0", "Кинопоказ +1", "Кинопоказ SD", "Кинопоказ FHD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "nashe.ru", "name": "Наше", "aliases": ["Наше HD", "Nashe", "Наше +0", "Наше +1", "Наше SD", "Наше FHD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "premiere.ru", "name": "Премиальное", "aliases": ["Премиальное HD", "Премиальное +0", "Премиальное +1", "Премиальное SD", "Премиальное FHD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "ostrosyuzhetnoe.ru", "name": "Остросюжетное", "aliases": ["Остросюжетное HD", "Остросюжетное +0", "Остросюжетное +1", "Остросюжетное SD", "Остросюжетное FHD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "romantic.ru", "name": "Романтичное", "aliases": ["Романтичное HD", "Романтичное +0", "Романтичное +1", "Романтичное SD", "Романтичное FHD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "start.ru", "name": "Старт", "aliases": ["Старт HD", "Start", "Старт +0", "Старт +1", "Старт SD", "Старт FHD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "hit.ru", "name": "Хит", "aliases": ["Хит HD", "Hit", "Hit HD", "Хит +0", "Хит +1", "Хит SD", "Хит FHD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "fan.ru", "name": "Fan", "aliases": ["Fan HD", "Фан", "Фан HD", "Fan +0", "Fan +1", "Fan SD", "Fan FHD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "kluch.ru", "name": "Ключ", "aliases": ["Ключ HD", "Ключ +0", "Ключ +1", "Ключ SD", "Ключ FHD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "sapfir.ru", "name": "Сапфир", "aliases": ["Сапфир HD", "Sapphire", "Сапфир +0", "Сапфир +1", "Сапфир SD", "Сапфир FHD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "amediahit.ru", "name": "Amedia Hit", "aliases": ["Амедиа Хит", "Amedia Hit HD", "Amedia Hit +0", "Amedia Hit +1", "Amedia Hit SD", "Amedia Hit FHD"], "country": "RU", "language": "ru", "categories": ["Сериалы"]},
    {"id": "amedia.ru", "name": "Amedia", "aliases": ["Амедиа", "Amedia Premium", "Amedia HD", "Amedia +0", "Amedia +1"], "country": "RU", "language": "ru", "categories": ["Сериалы"]},
    {"id": "ntvhit.ru", "name": "НТВ Хит", "aliases": ["НТВ-Хит", "NTV Hit", "НТВ Хит HD", "НТВ Хит +0", "НТВ Хит +1"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "mosfilm.ru", "name": "Мосфильм", "aliases": ["Мосфильм HD", "Mosfilm", "Мосфильм +0", "Мосфильм +1"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "sovkino.ru", "name": "Советская киноклассика", "aliases": ["Совкино", "Советская киноклассика HD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "moystihiya.ru", "name": "Моя стихия", "aliases": ["Моя стихия HD", "Моя стихия +0", "Моя стихия +1"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "kineko.ru", "name": "Кинеко", "aliases": ["Kineko", "Кинеко HD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "sumiko.ru", "name": "Sumiko", "aliases": ["Сумико", "Sumiko HD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "domkino.ru", "name": "Дом Кино", "aliases": ["ДомКино", "Dom Kino", "Дом Кино HD", "Дом Кино +0", "Дом Кино +1"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "kinohit.ru", "name": "Кинохит", "aliases": ["КиноХит", "Кинохит HD", "Кинохит +0", "Кинохит +1"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "kinopremiera.ru", "name": "Кинопремьера", "aliases": ["КиноПремьера", "Кинопремьера HD"], "country": "RU", "language": "ru", "categories": ["Фильмы"]},
    {"id": "discovery.ru", "name": "Discovery Channel", "aliases": ["Discovery", "Дисковери", "Discovery HD", "Discovery +0", "Discovery +1"], "country": "RU", "language": "ru", "categories": ["Познавательные"]},
    {"id": "natgeo.ru", "name": "National Geographic", "aliases": ["Nat Geo", "Национал Географик", "Nat Geo HD", "National Geographic HD"], "country": "RU", "language": "ru", "categories": ["Познавательные"]},
    {"id": "animalplanet.ru", "name": "Animal Planet", "aliases": ["Animal Planet HD"], "country": "RU", "language": "ru", "categories": ["Познавательные"]},
    {"id": "history.ru", "name": "History", "aliases": ["History Channel", "Хистори", "History HD"], "country": "RU", "language": "ru", "categories": ["Познавательные"]},
    {"id": "viasathistory.ru", "name": "Viasat History", "aliases": ["Виасат Хистори", "Viasat History HD"], "country": "RU", "language": "ru", "categories": ["Познавательные"]},
    {"id": "viasatexplore.ru", "name": "Viasat Explore", "aliases": ["Виасат Эксплор", "Viasat Explore HD"], "country": "RU", "language": "ru", "categories": ["Познавательные"]},
    {"id": "viasatnature.ru", "name": "Viasat Nature", "aliases": ["Виасат Нэйчер", "Viasat Nature HD"], "country": "RU", "language": "ru", "categories": ["Познавательные"]},
    {"id": "myplanet.ru", "name": "Моя Планета", "aliases": ["My Planet", "Моя Планета HD"], "country": "RU", "language": "ru", "categories": ["Познавательные"]},
    {"id": "science.ru", "name": "Наука", "aliases": ["Наука 2.0", "Science", "Наука HD"], "country": "RU", "language": "ru", "categories": ["Познавательные"]},
    {"id": "bridge.ru", "name": "Bridge TV", "aliases": ["Bridge", "Бридж ТВ", "Bridge TV HD"], "country": "RU", "language": "ru", "categories": ["Музыка"]},
    {"id": "ru.tv", "name": "RU.TV", "aliases": ["РУ ТВ", "RU TV", "RU.TV HD"], "country": "RU", "language": "ru", "categories": ["Музыка"]},
    {"id": "mtvmusic.ru", "name": "MTV", "aliases": ["MTV Russia", "MTV HD"], "country": "RU", "language": "ru", "categories": ["Музыка"]},
    {"id": "shanson.ru", "name": "Шансон ТВ", "aliases": ["ШансонТВ", "Shanson TV", "Шансон ТВ HD"], "country": "RU", "language": "ru", "categories": ["Музыка"]},
    {"id": "nickelodeon.ru", "name": "Nickelodeon", "aliases": ["Nick", "Никелодеон", "Nickelodeon HD"], "country": "RU", "language": "ru", "categories": ["Детские"]},
    {"id": "cartoon.ru", "name": "Cartoon Network", "aliases": ["CN", "Картун Нетворк", "Cartoon Network HD"], "country": "RU", "language": "ru", "categories": ["Детские"]},
    {"id": "mult.ru", "name": "Мульт", "aliases": ["Мульт HD", "Mult", "Мульт +0", "Мульт +1"], "country": "RU", "language": "ru", "categories": ["Детские"]},
    {"id": "disney.ru", "name": "Канал Disney", "aliases": ["Disney", "Disney Channel", "Disney HD"], "country": "RU", "language": "ru", "categories": ["Детские"]},
    {"id": "moscow24.ru", "name": "Москва 24", "aliases": ["Москва24", "Moscow 24", "Москва 24 HD"], "country": "RU", "language": "ru", "categories": ["Новости"]},
    {"id": "rbk.ru", "name": "РБК", "aliases": ["RBC", "РБК ТВ", "РБК HD"], "country": "RU", "language": "ru", "categories": ["Новости"]},
    {"id": "iz.ru", "name": "Известия", "aliases": ["Izvestia", "ИЗ", "Известия HD"], "country": "RU", "language": "ru", "categories": ["Новости"]},
    {"id": "rt.ru", "name": "RT", "aliases": ["Russia Today", "РТ", "RT HD"], "country": "RU", "language": "ru", "categories": ["Новости"]},
    {"id": "bel.ru", "name": "Беларусь 1", "aliases": ["Беларусь-1", "BT", "Belarus 1", "Беларусь 1 HD"], "country": "BY", "language": "ru", "categories": ["Общие"]},
    {"id": "ont.by", "name": "ОНТ", "aliases": ["ONT", "Общенациональное телевидение", "ОНТ HD"], "country": "BY", "language": "ru", "categories": ["Общие"]},
    {"id": "qazaqstan.kz", "name": "Qazaqstan", "aliases": ["Казахстан", "Kazakhstan", "Qazaqstan HD"], "country": "KZ", "language": "kk", "categories": ["Общие"]},
    {"id": "khabar.kz", "name": "Хабар", "aliases": ["Khabar", "Хабар ТВ", "Хабар HD"], "country": "KZ", "language": "kk", "categories": ["Общие"]},
    {"id": "firstchannel.eurasia.kz", "name": "Первый канал Евразия", "aliases": ["Евразия", "1 канал Евразия", "Первый канал Евразия HD"], "country": "KZ", "language": "ru", "categories": ["Общие"]},
]

# Built-in verified sources (cleaned + expanded)
VERIFIED_REAL_SOURCES = [
    "https://iptv-org.github.io/iptv/index.m3u",
    "https://iptv-org.github.io/iptv/index.country.m3u",
    "https://iptv-org.github.io/iptv/index.language.m3u",
    "https://iptv-org.github.io/iptv/languages/rus.m3u",
    "https://iptv-org.github.io/iptv/regions/cis.m3u",
    "https://iptv-org.github.io/iptv/regions/cas.m3u",
    "https://iptv-org.github.io/iptv/countries/ru.m3u",
    "https://iptv-org.github.io/iptv/countries/by.m3u",
    "https://iptv-org.github.io/iptv/countries/kz.m3u",
    "https://iptv-org.github.io/iptv/countries/kg.m3u",
    "https://iptv-org.github.io/iptv/countries/tj.m3u",
    "https://iptv-org.github.io/iptv/countries/tm.m3u",
    "https://iptv-org.github.io/iptv/countries/uz.m3u",
    "https://iptv-org.github.io/iptv/countries/mn.m3u",
    "https://iptv-org.github.io/iptv/countries/am.m3u",
    "https://iptv-org.github.io/iptv/countries/az.m3u",
    "https://iptv-org.github.io/iptv/countries/ge.m3u",
    "https://iptv-org.github.io/iptv/countries/md.m3u",
    "https://iptv-org.github.io/iptv/countries/ua.m3u",
    "https://dearbulut.github.io/iptv/playlists/best.m3u",
    "https://dearbulut.github.io/iptv/playlists/online.m3u",
    "https://dearbulut.github.io/iptv/playlists/index.m3u",
    "https://dearbulut.github.io/iptv/playlists/country/ru.m3u",
    "https://dearbulut.github.io/iptv/playlists/country/by.m3u",
    "https://dearbulut.github.io/iptv/playlists/country/kz.m3u",
    "https://dearbulut.github.io/iptv/playlists/country/tj.m3u",
    "https://dearbulut.github.io/iptv/playlists/country/uz.m3u",
    "https://dearbulut.github.io/iptv/playlists/country/mn.m3u",
    "https://dearbulut.github.io/iptv/playlists/language/rus.m3u",
    "https://dearbulut.github.io/iptv/playlists/category/news.m3u",
    "https://dearbulut.github.io/iptv/playlists/category/sports.m3u",
    "https://dearbulut.github.io/iptv/playlists/category/movies.m3u",
    "https://dearbulut.github.io/iptv/playlists/category/music.m3u",
    "https://dearbulut.github.io/iptv/playlists/category/kids.m3u",
    "https://raw.githubusercontent.com/substanc1/iptv-russia/main/streams/ru.m3u",
    "https://substanc1.github.io/iptv-russia/streams/ru.m3u",
    "https://ngrch.github.io/iptv/ru.m3u",
    "https://ngrch.github.io/iptv/music.m3u",
    "https://smolnp.github.io/IPTVru/IPTVru.m3u",
    "https://smolnp.github.io/IPTVru/IPTVstable.m3u8",
    "https://smolnp.github.io/IPTVru/IPTVmir.m3u8",
    "https://raw.githubusercontent.com/smolnp/IPTVru/refs/heads/gh-pages/IPTVru.m3u",
    "https://raw.githubusercontent.com/smolnp/IPTVru/refs/heads/gh-pages/IPTVstable.m3u8",
    "https://raw.githubusercontent.com/smolnp/IPTVru/refs/heads/gh-pages/IPTVmir.m3u8",
    "https://raw.githubusercontent.com/Free-TV/IPTV/master/playlist.m3u8",
    "https://raw.githubusercontent.com/Free-TV/IPTV/master/playlists/playlist_russia.m3u8",
    "https://raw.githubusercontent.com/denxvofficial/IPTV/refs/heads/main/iptv.m3u",
    "https://raw.githubusercontent.com/denxvofficial/IPTV/refs/heads/main/iptv-top.m3u",
    "https://raw.githubusercontent.com/devsground/IPTV/master/all/grouped_by_country.m3u",
    "https://raw.githubusercontent.com/devsground/IPTV/master/all/grouped_by_country_and_content.m3u",
    "https://raw.githubusercontent.com/devsground/IPTV/master/all/grouped_by_content.m3u",
    "https://raw.githubusercontent.com/Guovin/iptv-api/gd/output/result.m3u",
    "https://raw.githubusercontent.com/Guovin/iptv-api/gd/output/ipv4/result.m3u",
    "https://raw.githubusercontent.com/Guovin/iptv-api/gd/output/ipv6/result.m3u",
    "https://github.com/MaximKiselev/iptv/raw/refs/heads/main/playlist.m3u",
]

# User-provided general IPTV sources remembered from the earlier source list.
# These are kept separately from the public index list and intentionally NOT deduplicated.
# Sources have not all been live-verified; inaccessible sources are reported and skipped.
USER_PROVIDED_SOURCES = [
    # Imported from the user's supplied source list. Exact query strings, auth
    # parameters and repeated lines are intentionally preserved.
    "https://m3url.ru/2.0.m3u",
    "https://dl.dropboxusercontent.com/scl/fi/5153istx5rd2v8vau5osw/2024.m3u?rlkey=oz3idqm6v6dg9lfm3u96xygq7&dl=0",
    "https://dl.dropboxusercontent.com/scl/fi/vuj6oesoevfcsq1piokiq/.NET_1.m3u?rlkey=g5barth3y9yrua1q25rrz9nec&dl=0",
    "http://50na50.net/IPTV-list.m3u",
    "https://iptv-org.github.io/iptv/regions/asia.m3u",
    "https://dl.dropbox.com/scl/fi/74m171q8t8opwhve485pf/Moi_ip.m3u?rlkey=8cj23dvra85s2u7eh1kfzq4bp",
    "https://iptv-org.github.io/iptv/index.language.m3u",
    "https://m3url.ru/Another.TV.m3u",
    "https://m3url.ru/antifriz.tv.m3u",
    "https://avdmono.do.am/AVD/Armenia-avd.m3u",
    "https://avdmono.do.am/AVD/armenija.m3u",
    "https://tva.org.ua/ip/sam/avto-iptv-tva.m3u",
    "https://m3url.ru/Az.m3u",
    "http://bgdc.live:25461/get.php?username=6066278099&password=buddyburnette&type=m3u_plus",
    "https://tviptv.site/upl/1_brazil_2023.m3u",
    "https://m3url.ru/Bruce_Willies_31.05.23.m3u",
    "https://avdmono.do.am/AVD/CTV-AVD.m3u",
    "https://tviptv.site/upl/1_canada_2023.m3u",
    "https://tviptv.site/upl/1_china_2023.m3u",
    "https://raw.githubusercontent.com/Cartoonworldcs2/tsiptvmay/main/Cs2_Iptv.m3u8",
    "https://raw.githubusercontent.com/Dimonovich/TV/Dimonovich/FREE/CAMERA",
    "https://raw.githubusercontent.com/Dimonovich/TV/Dimonovich/FREE/FILMS",
    "https://raw.githubusercontent.com/Dimonovich/TV/Dimonovich/FREE/RADIO.m3u",
    "https://raw.githubusercontent.com/Dimonovich/TV/Dimonovich/FREE/RADIO_GENRES.m3u",
    "https://raw.githubusercontent.com/Dimonovich/TV/Dimonovich/FREE/TV",
    "https://raw.githubusercontent.com/Dimonovich/TV/Dimonovich/FREE/ZARUB",
    "https://dl.dropbox.com/s/zs5nkfqjz7c8jwj/iptv",
    "https://iptv-org.github.io/iptv/languages/eng.m3u",
    "http://vekart.ucoz.net/v/Eralash.m3u",
    "https://mater.com.ua/ip/iptv-s-2021.m3u",
    "http://samigiptv.ucoz.net/ottfilms.m3u8",
    "http://samigiptv.ucoz.net/film1800.m3u",
    "http://bluecrabstv.do.am/Free.m3u",
    "http://iptv-2020.do.am/Free.m3u",
    "https://raw.githubusercontent.com/Free-TV/IPTV/master/playlists/playlist_russia.m3u8",
    "https://gavrilovka.net/G.NET.m3u",
    "https://edemtv.my1.ru/Gedem.m3u",
    "https://edemtv.my1.ru/CatcastTV.m3u",
    "https://edemtv.my1.ru/TorrentTV.m3u",
    "https://edemtv.my1.ru/WinkZabava.m3u",
    "https://edemtv.my1.ru/mediateka.m3u",
    "https://m3url.ru/IPTV_GOLD_Angelina_Jolie_13.06.23.m3u",
    "https://edemtv.my1.ru/iptv/Gedem.m3u",
    "https://tviptv.site/upl/1_germany_2023.m3u",
    "http://413994677292339256.of2100.xyz/get.php?username=fe316596&password=fS4bBbVf5rW&type=m3u_plus",
    "http://hideip.me/IPTV-list.m3u",
    "https://avdmono.do.am/AVD/IPTV-AVD.m3u",
    "https://tviptv.site/upl/1_india_2023.m3u",
    "http://samigiptv.ucoz.net/iptvfull2121.txt",
    "https://mater.com.ua/ip/iptv-s-2021.m3u",
    "https://iptv-org.github.io/iptv/countries/ua.m3u",
    "https://iptv-org.github.io/iptv/countries/ru.m3u",
    "https://iptv-org.github.io/iptv/index.m3u",
    "https://iptv-org.github.io/iptv/categories/music.m3u",
    "https://iptv-org.github.io/iptv/categories/sports.m3u",
    "https://iptvforall.ucoz.net/zf.m3u",
    "https://tviptv.site/upl/1_italy_2023.m3u",
    "https://tviptv.site/upl/1_japan_2023.m3u",
    "https://jekalich.github.io/smtk/tv.smtk.m3u",
    "https://avdmono.do.am/AVD/kino-avd.m3u",
    "http://bit.ly/lazyiptvplaylist",
    "http://fork.iptvsmotri.ru/lime.m3u",
    "http://bluecrabstv.do.am/mediateka.m3u",
    "http://bluecrabstv.do.am/megogo.m3u",
    "https://m3url.ru/Multi.Streams.m3u",
    "https://avdmono.do.am/AVD/Muzz-avd.m3u",
    "https://avdmono.do.am/AVD/OTA-AVD.m3u",
    "https://m3url.ru/okko.m3u",
    "https://jeka345.github.io/playlive.m3u",
    "https://iptv-org.github.io/iptv/languages/rus.m3u",
    "http://topplay.do.am/RadioTopPlay.m3u",
    "https://avdmono.do.am/AVD/Rustv.m3u",
    "https://m3url.ru/Rus.m3u",
    "https://m3url.ru/s-net.m3u",
    "https://tva.org.ua/ip/u/iptv_ukr.m3u",
    "https://tva.org.ua/ip/sam/sam-03-2021.m3u",
    "https://www.dropbox.com/scl/fi/4cguthaanirgxa9hbqoac/Shamil_Bro.m3u8?rlkey=xdcwtuqqfvgxgvrwgs6e7388o&dl=1",
    "http://siptv.eu/lists/example.m3u",
    "https://strannikmodz.me/uploads/smartoteka.m3u",
    "https://smolnp.github.io/IPTVru//IPTVru.m3u",
    "https://m3url.ru/source.m3u",
    "https://m3url.ru/Sport.m3u",
    "https://avdmono.do.am/AVD/sports-avd.m3u",
    "http://stb.ge/tv.m3u",
    "http://samigiptv.ucoz.net/Stream2121.txt",
    "https://raw.githubusercontent.com/jura00/mytest.m3u/master/TBmir.m3u",
    "https://avdmono.do.am/AVD/TTV-AVD.m3u",
    "https://avdmono.do.am/AVD/TTV-AVD.m3u",
    "http://topplay.do.am/FreeBestTV.m3u",
    "http://topplay.do.am/FreeWorldTV.m3u",
    "http://troya.today/pl/11/62a77fd7a1547/playlist.m3u8",
    "https://tva.in.ua/iptv/iptv_ukr.m3u",
    "https://www.tvbox.one/iptv/playlist.m3u",
    "http://tvpremiumhd.club/hd/tv.m3u",
    "https://iptv-org.github.io/iptv/languages/ukr.m3u",
    "https://url.ott.blue/war",
    "http://iptv.ualinux.com/m3u/iptv_ualinux_mega.m3u",
    "https://mater.com.ua/ip/ua+reg-14.08.21-ip.m3u",
    "http://samigiptv.ucoz.net/ukraine.txt",
    "https://dl.dropbox.com/s/u9a0m18jmdr44tb/playlist_free.m3u8",
    "https://myplaylists.github.io/iptv/ua.m3u",
    "https://avdmono.do.am/AVD/Ukr-avd.m3u",
    "https://m3url.ru/Ukraine.m3u",
    "https://m3url.ru/ukr.m3u",
    "https://tviptv.site/upl/1_usa_2023.m3u",
    "https://avdmono.do.am/AVD/Uzbekistan.m3u",
    "https://m3url.ru/Uzbekistan.m3u",
    "http://viva-russia.ru/iptv.m3u",
    "https://dl.dropbox.com/s/zs5nkfqjz7c8jwj/iptv_full_playlist.m3u",
    "http://uiptv.do.am/pl/youriptv.m3u",
    "https://avdmono.do.am/AVD/ZEN-AVD.m3u",
    "http://fork.iptvsmotri.ru/zabava.m3u8",
    "https://m3url.ru/zabava.m3u",
    "https://m3url.ru/alltv_111.m3u",
    "https://tva.org.ua/ip/sam/avto-iptv-tva.m3u",
    "https://raw.githubusercontent.com/empty180/IPTVrus/main/ekb.m3u",
    "https://raw.githubusercontent.com/empty180/IPTVrus/main/ekb.m3u",
    "https://raw.githubusercontent.com/empty180/IPTVrus/main/pishma.m3u",
    "http://fix-rom.ucoz.com/iptv_full_playlist.m3u",
    "https://edemtv.my1.ru/ilook.m3u",
    "http://c60e879f2dcb.faststreem.org/playlists/uplist/814ec891b59d5b67015397bf65d7bd3f/playlist.m3u8",
    "https://ilook.epg.one/GNR4H3U46DQNX8",
    "https://raw.githubusercontent.com/iptv-org/iptv/master/streams/ru.m3u",
    "https://iptv.ucoz.org/iptv_ru.m3u",
    "https://dl.dropbox.com/scl/fi/11dofsqizkkv7u9cn1sao/Live_5.m3u?rlkey=px9rag3hhctpxjkqg0r0u49kj",
    "https://edemtv.my1.ru/ottclub.m3u",
    "https://www.apsattv.com/rakuten.m3u",
    "http://158.101.194.132:8080/playlist.m3u8?q=eyJ1c2VySWQiOiJBa3VkamkifQ.stFYGe-D7fLuWsranXPN4VmSqsoRLLASEQd9v-ppQSQS1a7A4S2sYc5B9X0ODyIo30SBnV6IGFvyVdiUprOc1Q",
    "https://avdmono.do.am/AVD/roman-avd.m3u",
    "https://m3url.ru/rp.m3u",
    "https://m3url.ru/santix_tv_.m3u",
    "https://www.dropbox.com/scl/fi/ggpduxik0438c3246lag5/santix-tv.m3u?rlkey=7j5a2kg4i7b8z914f6rdk6qz8&dl=1",
    "https://m3url.ru/tv-wd-2.m3u",
    "https://m3url.ru/tv-wd-2.m3u",
    "https://mater.com.ua/ip/ua.m3u",
    "https://m3u.in/uBuZtv.m3u",
    "https://edemtv.my1.ru/ucomhaykakan.m3u",
    "http://sascha.ucoz.net/plst/radio/radio_po_ispolniteljam.m3u",
    "https://edemtv.my1.ru/beetv.m3u",
    "https://dl.dropbox.com/scl/fi/a5k0wkr42vwem0coxldl8/1.m3u?rlkey=58gg6tn8ss8d54iv1dgvm3myq&dl=0",
    "http://sascha.ucoz.net/plst/radio/radio_ukrainy.m3u",
    "https://github.com/Shamilbro/Shamil_bro/releases/download/ShamS.TV/Shamil_Bro.m3u8",
    "https://dl.dropbox.com/scl/fi/vfhlfx6ciw4bovbtann6z/telegram-gruppa-free-tv-sport.m3u8?rlkey=8j2c3jl5b9hbjbc8sbgh83t4h&dl=0",
    "https://dl.dropbox.com/scl/fi/yrc1lpomt612b4qvlowj9/TOPPEHT_TB.m3u?rlkey=1pi40ollx19ae0q7pag6r22gn",
    # Earlier source URLs from the conversation, retained as well.
    "https://iptv.axenov.dev/so",
    "https://pastebin.com/raw/d3mDM8Tv",
    "https://iptv.axenov.dev/mult",
    "https://telekarta-tv.ru/wp-content/uploads/kids-all.m3u",
    "https://smart-iptv.ru/radio.m3u",
    "https://loganet.vercel.app/LoganetXAll.m3u",
    "https://tfrthuikijuyg.online/IPTV.m3u",
    "https://satexpresstv.ru/apk/setv.m3u",
    "https://shamilbro.ucoz.net/TV.m3u8",
    "https://shamilbro.ucoz.net/Wink.m3u8",
    "https://goo.su/KIp3",
    "https://polzafre.short.gy/IPTV",
]

# Regexes
ORBIT_RE = re.compile(r"(?i)(?:\s*[\[(]?([+-]?\d{1,2})\s*(?:h|ч)?[\])]?)\s*$")
QUALITY_RE = re.compile(
    r"(?i)\b(?:uhd|4k|fhd|full\s*hd|hd|sd|8k|2160p|1440p|1080p|720p|576p|480p)\b"
)
PUNCT_RE = re.compile(r"[^\w\s+#а-яА-ЯёЁ]+", re.UNICODE)
_ATTR_RE = re.compile(r'([\w-]+)\s*=\s*(?:"([^"]*)"|\'([^\']*)\'|([^\s,]+))')

OUTPUT_DIR_NAME = "output_iptv"
DB_NAME = "M3U_Base.db"
ML_JSON_NAME = "M3U.JSON"
ML_DATA_NAME = "Vladik_llm.ml"
TELEMETRY_NAME = "telemetry.jsonl"
TELEMETRY_SUMMARY = "telemetry_summary.json"
STABLE_STATE_NAME = "stable_state.json"


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------
def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_text(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8", errors="ignore")).hexdigest()


def clean_text(s: str) -> str:
    s = unicodedata.normalize("NFKC", s or "")
    s = s.replace("ё", "е").replace("Ё", "Е")
    return re.sub(r"\s+", " ", s).strip()


def clean_url(url: str) -> str:
    # Preserve query strings and credentials exactly; only trim surrounding syntax.
    return str(url or "").strip().strip("<>\"'")


def safe_url_for_log(url: str) -> str:
    """Redact credentials/query values before writing URLs to logs."""
    try:
        p = urlsplit(str(url or ""))
        host = p.hostname or ""
        if p.port:
            host = f"{host}:{p.port}"
        return urlunsplit((p.scheme, host, p.path, "<redacted-query>" if p.query else "", ""))
    except Exception:
        return "<redacted-url>"


def is_adult_source(url: str = "", name: str = "") -> bool:
    """Reject explicitly adult-only source URLs and channel labels.

    This is a conservative guard, not a general content classifier.
    """
    text = f"{url} {name}".casefold()
    markers = (
        "adultiptv", "/adult/", "adult.", "xxx", "porn", "porno",
        "pornhub", "erotic", "sexcam", "18plus", "18+", "iptvххх",
    )
    return any(marker in text for marker in markers)


def safe_error_text(value: object) -> str:
    """Remove URL credentials/query values from exception text before logging."""
    text = str(value or "")
    # Redact complete URLs so userinfo, signed paths and query tokens do not leak.
    pattern = re.compile(r"https?://[^\s\"'<>]+", re.IGNORECASE)
    def replace(match: re.Match) -> str:
        raw = match.group(0).rstrip(")],;.")
        suffix = match.group(0)[len(raw):]
        return safe_url_for_log(raw) + suffix
    return pattern.sub(replace, text)[:500]


def is_http_url(url: str) -> bool:
    try:
        p = urlparse(url)
        return p.scheme in ("http", "https") and bool(p.netloc)
    except Exception:
        return False


def normalize_url(url: str) -> str:
    url = (url or "").strip()
    if not url:
        return ""
    try:
        p = urlsplit(url)
        path = re.sub(r"/{2,}", "/", p.path)
        return urlunsplit((p.scheme.lower(), p.netloc.lower(), path, p.query, ""))
    except Exception:
        return url.lower()


def host_from_url(url: str) -> str:
    try:
        return urlparse(url).hostname or ""
    except Exception:
        return ""


def apply_host_rewrites(url: str) -> str:
    url = (url or "").strip()
    for old, new in CINERAMA_HOST_REPLACEMENTS.items():
        if url.startswith(old):
            return new + url[len(old):]
    return url


def host_rewrite_candidates(url: str) -> list[str]:
    out = []
    for u in (apply_host_rewrites(url), url):
        if u and u not in out:
            out.append(u)
    return out


def is_placeholder_source(source: str) -> bool:
    s = (source or "").strip().lower()
    if not s:
        return True
    return (
        s.startswith("#")
        or s in {"здесь будет ссылка", "сюда будет ссылка", "placeholder", "todo"}
        or "здесь будет ссылка" in s
    )


def normalize_name(name: str) -> str:
    s = clean_text(name).lower()
    s = ORBIT_RE.sub("", s)
    s = QUALITY_RE.sub("", s)
    s = re.sub(r"\b(?:рус|ru|rus|eng|en|russia)\b", " ", s)
    s = PUNCT_RE.sub(" ", s)
    s = re.sub(r"\s+", " ", s).strip()
    return s


def orbit_variant(name: str) -> str:
    m = ORBIT_RE.search(str(name or "").strip())
    if not m:
        return "+0"
    n = int(m.group(1))
    return "+0" if n == 0 else f"+{n}" if n > 0 else str(n)


def quality_variant(name: str) -> str:
    m = QUALITY_RE.search(str(name or ""))
    if not m:
        return "UNKNOWN"
    q = m.group(0).upper().replace(" ", "")
    return {
        "FULLHD": "FHD", "1080P": "FHD", "720P": "HD",
        "576P": "SD", "480P": "SD", "2160P": "UHD",
        "4K": "UHD", "1440P": "QHD", "8K": "8K",
    }.get(q, q)


def quality_rank(q: str) -> int:
    return {
        "8K": 60, "UHD": 50, "4K": 50, "QHD": 40,
        "FHD": 35, "HD": 25, "SD": 10, "UNKNOWN": 0,
    }.get((q or "UNKNOWN").upper(), 0)


def base_channel_name(name: str) -> str:
    return re.sub(
        r"\s+", " ",
        QUALITY_RE.sub("", ORBIT_RE.sub("", clean_text(name))),
    ).strip()


def channel_similarity(a: str, b: str) -> float:
    na, nb = normalize_name(a), normalize_name(b)
    if not na or not nb:
        return 0.0
    if na == nb:
        return 1.0
    aa, bb = set(na.split()), set(nb.split())
    j = len(aa & bb) / len(aa | bb) if aa and bb else 0.0
    if na in nb or nb in na:
        j = max(j, 0.86)
    seq = SequenceMatcher(None, na, nb).ratio()
    sa = {x for x in aa if len(x) >= ALT_INDEX_MIN_TOKEN_LEN}
    sb = {x for x in bb if len(x) >= ALT_INDEX_MIN_TOKEN_LEN}
    sig = len(sa & sb) / len(sa | sb) if sa and sb else 0.0
    short, longer = (sa, sb) if len(sa) <= len(sb) else (sb, sa)
    if short and short <= longer:
        sig = max(sig, 0.90)
    return max(j, seq, sig)


def is_special_channel(name: str) -> bool:
    n = normalize_name(name)
    return any(term in n for term in SPECIAL_CHANNEL_TERMS)


def is_bad_name(name: str) -> bool:
    low = clean_text(name).lower()
    if is_adult_source(name=name):
        return True
    # Keep adult/betting labels out without accidentally matching unrelated words
    # such as "Essex" for the token "sex".
    for token in BAD_NAME_TOKENS:
        if token in {"sex", "bet", "xxx", "porn", "porno", "adult", "erotic", "18+", "casino", "казино", "ставки", "букмекер"}:
            if re.search(rf"(?<![\w]){re.escape(token)}(?![\w])", low):
                return True
        elif token in low:
            return True
    return False


def infer_region(url: str, name: str = "", source: str = "") -> str:
    text = f"{url} {name} {source}".lower()
    for region, markers in REGION_MARKERS.items():
        if any(m in text for m in markers):
            return region
    return "UNK"


def classify_endpoint(url: str, name: str = "", source: str = "") -> dict[str, str]:
    host = host_from_url(url)
    h = host.lower()
    if "wink" in h:
        operator = "Wink"
    elif "nginx" in h:
        operator = "Nginx"
    elif "rt" in h or "rostelecom" in h:
        operator = "Rostelecom/RT"
    else:
        operator = ""
    return {
        "host": host,
        "operator": operator,
        "region": infer_region(url, name, source),
    }


def russian_score(name: str, group: str, country: str, language: str, source: str) -> int:
    text = " ".join((name, group, country, language, source)).lower()
    score = 5 if re.search(r"[а-яё]", text) else 0
    if country.lower() in {"ru", "russia", "rus"}:
        score += 10
    if language.lower().startswith("ru") or language.lower() in {"rus", "russian"}:
        score += 10
    score += sum(1 for w in RU_WORDS if w in text)
    return score


def parse_attrs(line: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for m in _ATTR_RE.finditer(line):
        out[m.group(1).lower()] = m.group(2) or m.group(3) or m.group(4) or ""
    return out


def significant_tokens(name: str) -> set[str]:
    return {x for x in normalize_name(name).split() if len(x) >= ALT_INDEX_MIN_TOKEN_LEN}


# ---------------------------------------------------------------------------
# Rate limiter
# ---------------------------------------------------------------------------
class AsyncRateLimiter:
    def __init__(self, rate: float):
        self.rate = max(1.0, float(rate))
        self.interval = 1.0 / self.rate
        self._lock = asyncio.Lock()
        self._next = 0.0

    async def wait(self) -> None:
        async with self._lock:
            now = time.monotonic()
            if now < self._next:
                await asyncio.sleep(self._next - now)
                now = time.monotonic()
            self._next = max(now, self._next) + self.interval


# ---------------------------------------------------------------------------
# Data classes
# ---------------------------------------------------------------------------
@dataclass
class StreamRecord:
    record_id: int
    name: str
    url: str
    group: str = ""
    tvg_id: str = ""
    tvg_name: str = ""
    logo: str = ""
    source: str = ""
    source_type: str = "playlist"
    discovered_pass: int = 1
    discovered_at: str = field(default_factory=now_iso)

    working: bool = False
    status_code: int = 0
    latency_ms: float = 999999.0
    final_url: str = ""
    content_type: str = ""
    protocol: str = ""
    resolution: str = ""
    width: int = 0
    height: int = 0
    bitrate_kbps: float = 0.0
    codec: str = ""
    has_audio: bool = False
    has_video: bool = False
    is_live: bool = False
    is_vod: bool = False
    archive_supported: bool = False
    error: str = ""

    region: str = "UNK"
    host: str = ""
    operator: str = ""
    cdn_node: str = ""
    asn: str = ""

    normalized_channel: str = ""
    orbit: str = "+0"
    quality: str = "UNKNOWN"
    special: bool = False
    russian_priority: bool = False

    # External DB enrichment
    db_id: str = ""
    db_name: str = ""
    db_aliases: list[str] = field(default_factory=list)
    db_country: str = ""
    db_language: str = ""
    db_network: str = ""
    db_match_score: float = 0.0
    db_match_type: str = ""

    alternative_of: str = ""
    alternative_rank: int = 0
    similarity: float = 0.0
    is_alternative: bool = False

    successes: int = 0
    failures: int = 0


@dataclass
class CheckEvent:
    record_id: int
    pass_no: int
    timestamp: str
    working: bool
    status_code: int
    latency_ms: float
    final_url: str
    content_type: str
    protocol: str
    resolution: str
    width: int
    height: int
    bitrate_kbps: float
    codec: str
    has_audio: bool
    has_video: bool
    is_live: bool
    is_vod: bool
    archive_supported: bool
    error: str


@dataclass
class AlternativeEvent:
    pass_no: int
    timestamp: str
    failed_record_id: int
    failed_name: str
    candidate_record_id: int
    candidate_name: str
    candidate_url: str
    similarity: float
    working: bool
    rank: int
    region: str
    host: str
    operator: str
    orbit: str
    quality: str


# ---------------------------------------------------------------------------
# External Channel Database (safe AST load)
# ---------------------------------------------------------------------------
CHANNEL_DB: list[dict] = []
CHANNEL_DB_BY_ID: dict[str, dict] = {}
CHANNEL_DB_BY_NAME: dict[str, list[dict]] = defaultdict(list)
CHANNEL_DB_BY_ALIAS: dict[str, list[dict]] = defaultdict(list)
CHANNEL_DB_TOKEN_INDEX: dict[str, list[dict]] = defaultdict(list)


def _db_list(v) -> list[str]:
    if v is None:
        return []
    if isinstance(v, (list, tuple, set)):
        return [clean_text(str(x)) for x in v if clean_text(str(x))]
    if isinstance(v, str):
        t = v.strip()
        if not t:
            return []
        if t[:1] in "[{(":
            try:
                x = ast.literal_eval(t)
                if isinstance(x, (list, tuple, set)):
                    return [clean_text(str(y)) for y in x if clean_text(str(y))]
            except Exception:
                pass
        return [clean_text(x) for x in re.split(r"[|,;]", t) if clean_text(x)]
    return [clean_text(str(v))]


def _db_field(r: dict, *names, default=""):
    for n in names:
        if n in r and r[n] not in (None, ""):
            return r[n]
    return default


def normalize_db_record(r) -> Optional[dict]:
    if not isinstance(r, dict):
        return None
    rid = clean_text(str(_db_field(r, "id", "channel_id", "tvg_id", "slug", "key", default="")))
    name = clean_text(str(_db_field(r, "name", "channel_name", "title", "display_name", "tvg_name", default="")))
    aliases = _db_list(_db_field(r, "alt_names", "aliases", "alias", "alternative_names", "names", default=[]))
    if name:
        aliases = [x for x in aliases if normalize_name(x) != normalize_name(name)]
    if not rid and not name:
        return None
    return {
        "id": rid,
        "name": name or rid,
        "aliases": aliases,
        "network": clean_text(str(_db_field(r, "network", "operator", default=""))),
        "owners": _db_list(_db_field(r, "owners", "owner", default=[])),
        "country": clean_text(str(_db_field(r, "country", "countries", default=""))),
        "language": clean_text(str(_db_field(r, "language", "languages", default=""))),
        "categories": _db_list(_db_field(r, "categories", "category", "genres", default=[])),
        "website": clean_text(str(_db_field(r, "website", "site", "url", default=""))),
    }


def load_channel_db_csv(data: bytes) -> list[dict]:
    return [r for row in csv.DictReader(io.StringIO(data.decode("utf-8-sig", "replace"))) if (r := normalize_db_record(row))]


def load_channel_db_json(data: bytes) -> list[dict]:
    try:
        obj = json.loads(data.decode("utf-8-sig", "replace"))
    except Exception as e:
        logging.getLogger("ultra").warning("CHANNEL DB JSON parse failed: %s", e)
        return []
    if isinstance(obj, list):
        raw = obj
    elif isinstance(obj, dict) and any(k in obj for k in ("id", "name", "title", "channel_name", "tvg_name")):
        raw = [obj]
    elif isinstance(obj, dict):
        raw = list(obj.values())
    else:
        raw = []
    return [r for x in raw if (r := normalize_db_record(x))]


def load_channel_db_py(data: bytes) -> list[dict]:
    try:
        tree = ast.parse(data.decode("utf-8", "replace"))
    except Exception as e:
        logging.getLogger("ultra").warning("CHANNEL DB PY parse failed: %s", e)
        return []
    out = []
    for node in tree.body:
        value = None
        if isinstance(node, (ast.Assign, ast.AnnAssign)):
            value = node.value
        if value is None:
            continue
        try:
            obj = ast.literal_eval(value)
        except Exception:
            continue
        if isinstance(obj, dict):
            if any(k in obj for k in ("id", "name", "title", "channel_name", "tvg_name")):
                out.append(obj)
            else:
                out.extend(v for v in obj.values() if isinstance(v, dict))
        elif isinstance(obj, (list, tuple, set)):
            out.extend(v for v in obj if isinstance(v, dict))
    return [r for x in out if (r := normalize_db_record(x))]


def merge_db(records: list[dict]) -> list[dict]:
    merged: dict[str, dict] = {}
    for r in records:
        k = r["id"] or "name:" + normalize_name(r["name"])
        if k not in merged:
            merged[k] = dict(r)
            continue
        d = merged[k]
        d["aliases"] = list(dict.fromkeys(d.get("aliases", []) + r.get("aliases", [])))
        for x in ("network", "country", "language", "website"):
            if not d.get(x):
                d[x] = r.get(x, "")
        for x in ("owners", "categories"):
            d[x] = list(dict.fromkeys(d.get(x, []) + r.get(x, [])))
    return list(merged.values())


def build_db_indexes(records: list[dict]) -> None:
    global CHANNEL_DB, CHANNEL_DB_BY_ID, CHANNEL_DB_BY_NAME, CHANNEL_DB_BY_ALIAS, CHANNEL_DB_TOKEN_INDEX
    CHANNEL_DB = records
    CHANNEL_DB_BY_ID = {}
    CHANNEL_DB_BY_NAME = defaultdict(list)
    CHANNEL_DB_BY_ALIAS = defaultdict(list)
    CHANNEL_DB_TOKEN_INDEX = defaultdict(list)
    for r in records:
        if r["id"]:
            CHANNEL_DB_BY_ID[r["id"].lower()] = r
        for value, target in [(r["name"], CHANNEL_DB_BY_NAME)] + [(a, CHANNEL_DB_BY_ALIAS) for a in r["aliases"]]:
            k = normalize_name(value)
            if not k:
                continue
            target[k].append(r)
            for t in significant_tokens(k):
                CHANNEL_DB_TOKEN_INDEX[t].append(r)


async def fetch_bytes(session: aiohttp.ClientSession, url: str, max_bytes: int = CHANNEL_DB_MAX_BYTES) -> bytes:
    async with session.get(url, timeout=aiohttp.ClientTimeout(total=45), allow_redirects=True) as resp:
        if resp.status >= 400:
            raise RuntimeError(f"HTTP {resp.status}: {safe_url_for_log(url)}")
        data = await resp.content.read(max_bytes + 1)
        if len(data) > max_bytes:
            raise ValueError(f"response exceeds {max_bytes} bytes")
        if url.lower().split("?", 1)[0].endswith(".gz") or data[:2] == b"\x1f\x8b":
            data = gzip.decompress(data)
        return data


def _candidate_local_db_paths(extra_dirs: Optional[list[Path]] = None) -> list[Path]:
    """Collect possible local channel-db paths (cwd, script dir, extra dirs)."""
    bases: list[Path] = [
        Path.cwd(),
        Path(__file__).resolve().parent if "__file__" in globals() else Path.cwd(),
    ]
    if extra_dirs:
        bases.extend(extra_dirs)
    seen: set[str] = set()
    out: list[Path] = []
    for base in bases:
        for name in LOCAL_CHANNEL_DB_FILES:
            p = (base / name).resolve()
            key = str(p)
            if key not in seen and p.is_file():
                seen.add(key)
                out.append(p)
    return out


def _parse_db_by_suffix(path: Path, data: bytes) -> list[dict]:
    name = path.name.lower()
    if name.endswith(".csv"):
        return load_channel_db_csv(data)
    if name.endswith(".json"):
        return load_channel_db_json(data)
    if name.endswith(".py"):
        return load_channel_db_py(data)
    return []


def load_local_channel_files(paths: list[Path]) -> list[dict]:
    """
    Последовательная загрузка локальных вариантов: CSV → JSON → PY.
    Если один файл не прочитался / пуст — пробуем следующий.
    Успешные источники объединяются (merge позже).
    """
    log = logging.getLogger("ultra")
    # Сортируем: сначала .csv, потом .json, потом .py
    order = {".csv": 0, ".json": 1, ".py": 2}
    ordered = sorted(
        paths,
        key=lambda p: (order.get(Path(p.name).suffix.lower(), 9), str(p)),
    )
    allr: list[dict] = []
    loaded_labels: list[str] = []
    for p in ordered:
        label = p.suffix.lower().lstrip(".") or p.name
        try:
            data = p.read_bytes()
            rows = _parse_db_by_suffix(p, data)
            if not rows:
                log.warning(
                    "CHANNEL DB LOCAL %s: 0 records — пробуем следующий вариант",
                    p,
                )
                continue
            allr.extend(rows)
            loaded_labels.append(f"{p.name}:{len(rows)}")
            log.info(
                "CHANNEL DB LOCAL %s OK: records=%d bytes=%d",
                p, len(rows), len(data),
            )
        except Exception as e:
            log.warning(
                "CHANNEL DB LOCAL %s failed (%s) — пробуем следующий вариант",
                p, e,
            )
    if loaded_labels:
        log.info("CHANNEL DB LOCAL loaded: %s", ", ".join(loaded_labels))
    else:
        log.info("CHANNEL DB LOCAL: ни один csv/json/py не загрузился")
    return allr


async def _load_remote_db_cascade(
    session: aiohttp.ClientSession,
) -> list[dict]:
    """
    Remote cascade: CSV → JSON → PY.
    Если вариант упал или дал 0 записей — грузим следующий.
    Все успешные источники объединяются.
    """
    log = logging.getLogger("ultra")
    sources = (
        ("CSV", CHANNEL_DB_CSV_URL, load_channel_db_csv),
        ("JSON", CHANNEL_DB_JSON_URL, load_channel_db_json),
        ("PY", CHANNEL_DB_PY_URL, load_channel_db_py),
    )
    allr: list[dict] = []
    loaded: list[str] = []
    for label, url, parser in sources:
        try:
            data = await fetch_bytes(session, url)
            rows = parser(data)
            if not rows:
                log.warning(
                    "CHANNEL DB REMOTE %s: 0 records — пробуем следующий вариант",
                    label,
                )
                continue
            allr.extend(rows)
            loaded.append(f"{label}:{len(rows)}")
            log.info(
                "CHANNEL DB REMOTE %s OK: records=%d bytes=%d",
                label, len(rows), len(data),
            )
        except Exception as e:
            log.warning(
                "CHANNEL DB REMOTE %s failed (%s) — пробуем следующий вариант",
                label, e,
            )
    if loaded:
        log.info("CHANNEL DB REMOTE loaded: %s", ", ".join(loaded))
    else:
        log.warning("CHANNEL DB REMOTE: ни один csv/json/py не загрузился")
    return allr


async def load_external_channel_database(
    session: aiohttp.ClientSession,
    extra_dirs: Optional[list[Path]] = None,
    skip_remote: bool = False,
) -> int:
    """
    Загрузка основной БД с каскадом форматов CSV → JSON → PY:

      1. Local files (channels.csv → channels.json → channels_data.py)
      2. Remote GitHub (csv → json → py), unless skip_remote
      3. Built-in seed — орбиты/качества (SD/HD/FHD, +0..+7), всегда

    Если один вариант не подгрузился (ошибка / 0 записей) — берём следующий.
    Успешные источники мержатся (алиасы дополняются).
    """
    log = logging.getLogger("ultra")
    allr: list[dict] = []

    # 1) Local cascade CSV → JSON → PY
    local_paths = _candidate_local_db_paths(extra_dirs)
    if local_paths:
        allr.extend(load_local_channel_files(local_paths))
    else:
        log.info("CHANNEL DB LOCAL: файлы channels.csv/json/py не найдены")

    # 2) Remote cascade CSV → JSON → PY
    if not skip_remote:
        allr.extend(await _load_remote_db_cascade(session))
    else:
        log.info("CHANNEL DB REMOTE: пропуск (--no-remote-db)")

    # 3) Built-in supplementary: orbit / quality variant aliases
    builtin = [r for x in BUILTIN_CHANNEL_DB if (r := normalize_db_record(x))]
    allr.extend(builtin)
    log.info("CHANNEL DB BUILTIN (orbits/qualities support): records=%d", len(builtin))

    rows = merge_db(allr)
    build_db_indexes(rows)
    log.info("CHANNEL DB READY: %d canonical records (merged)", len(rows))
    return len(rows)


def database_match_channel(
    name: str,
    tvg_id: str = "",
    original_names: Optional[list[str]] = None,
) -> tuple[Optional[dict], float, str]:
    if tvg_id:
        tid = clean_text(tvg_id).lower()
        if tid in CHANNEL_DB_BY_ID:
            return CHANNEL_DB_BY_ID[tid], 1.0, "id"
        base = tid.split("@", 1)[0]
        if base in CHANNEL_DB_BY_ID:
            return CHANNEL_DB_BY_ID[base], 0.99, "id-base"
    best = None
    best_score = 0.0
    best_type = ""
    for raw in [name] + list(original_names or []):
        k = normalize_name(raw)
        if not k:
            continue
        if CHANNEL_DB_BY_NAME.get(k):
            return CHANNEL_DB_BY_NAME[k][0], 1.0, "name"
        if CHANNEL_DB_BY_ALIAS.get(k):
            return CHANNEL_DB_BY_ALIAS[k][0], CHANNEL_DB_ALIAS_MATCH, "alias"
        candidates = []
        seen = set()
        for token in significant_tokens(k):
            for r in CHANNEL_DB_TOKEN_INDEX.get(token, []):
                ident = r.get("id") or r.get("name")
                if ident not in seen:
                    seen.add(ident)
                    candidates.append(r)
        for r in candidates[:300]:
            score = max(
                (channel_similarity(k, normalize_name(x)) for x in [r["name"]] + r["aliases"] if x),
                default=0.0,
            )
            if score > best_score:
                best, best_score, best_type = r, score, "fuzzy"
    if best is not None and best_score >= CHANNEL_DB_MATCH_THRESHOLD:
        return best, best_score, best_type
    return None, 0.0, ""


def enrich_record_from_db(r: StreamRecord) -> None:
    db, score, typ = database_match_channel(r.name, r.tvg_id)
    if not db:
        return
    r.db_id = db["id"]
    r.db_name = db["name"]
    r.db_aliases = list(db["aliases"])
    r.db_country = db["country"]
    r.db_language = db["language"]
    r.db_network = db["network"]
    r.db_match_score = score
    r.db_match_type = typ
    if not r.tvg_id and r.db_id:
        r.tvg_id = r.db_id
    if not r.group and db.get("categories"):
        r.group = db["categories"][0]
    if str(r.db_country).lower() in {"ru", "rus", "russia"} or str(r.db_language).lower().startswith(("ru", "rus", "russian")):
        r.russian_priority = True


# ---------------------------------------------------------------------------
# Archive (append-only)
# ---------------------------------------------------------------------------
class Archive:
    def __init__(self, root: Path):
        self.root = root
        self.root.mkdir(parents=True, exist_ok=True)
        self.records_path = root / "records.jsonl"
        self.diag_path = root / "diagnostics.jsonl"
        self.alt_path = root / "alternatives.jsonl"
        self.state_path = root / "run_state.json"
        self.records: list[StreamRecord] = []
        self._load()

    def _load(self) -> None:
        if not self.records_path.exists():
            return
        with self.records_path.open("r", encoding="utf-8") as f:
            for line in f:
                try:
                    d = json.loads(line)
                    # Compatibility: ensure list fields
                    if "db_aliases" not in d:
                        d["db_aliases"] = []
                    self.records.append(StreamRecord(**{k: v for k, v in d.items() if k in StreamRecord.__dataclass_fields__}))
                except Exception:
                    continue

    def next_id(self) -> int:
        return max((r.record_id for r in self.records), default=0) + 1

    def append_records(self, records: Iterable[StreamRecord]) -> None:
        rows = list(records)
        if not rows:
            return
        with self.records_path.open("a", encoding="utf-8") as f:
            for r in rows:
                f.write(json.dumps(asdict(r), ensure_ascii=False) + "\n")
        self.records.extend(rows)

    def append_diagnostics(self, events: Iterable[CheckEvent]) -> None:
        with self.diag_path.open("a", encoding="utf-8") as f:
            for e in events:
                f.write(json.dumps(asdict(e), ensure_ascii=False) + "\n")

    def append_alternatives(self, events: Iterable[AlternativeEvent]) -> None:
        with self.alt_path.open("a", encoding="utf-8") as f:
            for e in events:
                f.write(json.dumps(asdict(e), ensure_ascii=False) + "\n")

    def load_pass(self) -> int:
        if not self.state_path.exists():
            return 0
        try:
            return int(json.loads(self.state_path.read_text("utf-8")).get("last_pass", 0))
        except Exception:
            return 0

    def save_pass(self, pass_no: int) -> None:
        self.state_path.write_text(
            json.dumps({"last_pass": pass_no, "updated_at": now_iso()}, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )


# ---------------------------------------------------------------------------
# Source loader
# ---------------------------------------------------------------------------
class SourceLoader:
    def __init__(self, output: Path, timeout: int, workers: int, user_agent: str, ops_per_second: float):
        self.output = output.resolve()
        self.timeout = timeout
        self.workers = workers
        self.user_agent = user_agent
        self.session_headers = {"User-Agent": user_agent}
        self.rate_limiter = AsyncRateLimiter(ops_per_second)

    def is_generated(self, path: Path) -> bool:
        try:
            p = path.resolve()
            if self.output == p or self.output in p.parents:
                return True
        except Exception:
            return False
        return p.name.lower() in GENERATED_NAMES

    def validate_local(self, path: Path) -> bool:
        return path.exists() and path.is_file() and not self.is_generated(path)

    async def fetch_text(self, session: aiohttp.ClientSession, url: str) -> str:
        last_error: Optional[Exception] = None
        for attempt in range(1, SOURCE_FETCH_RETRIES + 1):
            try:
                await self.rate_limiter.wait()
                async with session.get(
                    apply_host_rewrites(url),
                    timeout=aiohttp.ClientTimeout(total=self.timeout),
                    allow_redirects=True,
                ) as resp:
                    if resp.status >= 400:
                        raise RuntimeError(f"HTTP {resp.status}: {safe_url_for_log(url)}")
                    raw = await resp.content.read(MAX_SOURCE_BYTES + 1)
                    if len(raw) > MAX_SOURCE_BYTES:
                        raise ValueError(f"source exceeds {MAX_SOURCE_BYTES} byte limit")
                    return raw.decode("utf-8-sig", errors="replace")
            except Exception as exc:
                last_error = RuntimeError(safe_error_text(exc))
                if attempt < SOURCE_FETCH_RETRIES:
                    await asyncio.sleep(0.25 * attempt)
        raise last_error or RuntimeError(f"source fetch failed: {safe_url_for_log(url)}")

    def parse_m3u(self, text: str, source: str, pass_no: int, start_id: int) -> list[StreamRecord]:
        records: list[StreamRecord] = []
        lines = text.replace("\r\n", "\n").replace("\r", "\n").split("\n")
        pending: Optional[tuple[str, dict[str, str]]] = None
        rid = start_id

        for raw in lines:
            line = raw.strip()
            if not line:
                continue
            if line.upper().startswith("#EXTINF"):
                left, _, display = line.partition(",")
                attrs = parse_attrs(left)
                name = display.strip() or attrs.get("tvg-name", "") or attrs.get("tvg-id", "") or "Unknown"
                pending = (name, attrs)
                continue
            if line.startswith("#"):
                continue
            if not is_http_url(line):
                continue
            if pending:
                name, attrs = pending
                pending = None
            else:
                name, attrs = "Unknown", {}

            if is_bad_name(name) or is_adult_source(url=line, name=name):
                continue

            url = apply_host_rewrites(clean_url(line))
            if is_adult_source(url=url, name=name):
                continue
            host = host_from_url(url)
            if any(h in host.lower() for h in NON_STREAM_HOSTS):
                continue

            meta = classify_endpoint(url, name, source)
            orbit = orbit_variant(name)
            quality = quality_variant(name)
            r = StreamRecord(
                record_id=rid,
                name=name,
                url=url,
                group=attrs.get("group-title", ""),
                tvg_id=attrs.get("tvg-id", ""),
                tvg_name=attrs.get("tvg-name", "") or name,
                logo=attrs.get("tvg-logo", ""),
                source=source,
                source_type="playlist",
                discovered_pass=pass_no,
                region=meta["region"],
                host=meta["host"],
                operator=meta["operator"],
                normalized_channel=normalize_name(name),
                orbit=orbit,
                quality=quality,
                special=is_special_channel(name),
                russian_priority=russian_score(
                    name, attrs.get("group-title", ""), attrs.get("tvg-country", ""),
                    attrs.get("tvg-language", ""), source,
                ) >= 6,
            )
            enrich_record_from_db(r)
            records.append(r)
            rid += 1

        # Plain URL fallback
        if not records:
            for line in lines:
                line = line.strip()
                if is_http_url(line) and not is_adult_source(url=line):
                    line = apply_host_rewrites(line)
                    if is_adult_source(url=line):
                        continue
                    meta = classify_endpoint(line)
                    records.append(StreamRecord(
                        record_id=rid,
                        name="Unknown",
                        url=line,
                        source=source,
                        source_type="text",
                        discovered_pass=pass_no,
                        region=meta["region"],
                        host=meta["host"],
                        operator=meta["operator"],
                        normalized_channel="unknown",
                    ))
                    rid += 1
        return records

    async def load_one(
        self,
        session: aiohttp.ClientSession,
        source: str,
        pass_no: int,
        start_id: int,
    ) -> list[StreamRecord]:
        if is_placeholder_source(source) or is_adult_source(url=source):
            return []
        source = apply_host_rewrites(clean_url(source))
        if not source or is_adult_source(url=source):
            return []
        if is_http_url(source):
            try:
                text = await self.fetch_text(session, source)
                return self.parse_m3u(text, source, pass_no, start_id)
            except Exception as e:
                logging.getLogger("ultra").warning("SOURCE FAIL %s :: %s", safe_url_for_log(source), safe_error_text(e))
                return []
        p = Path(source).expanduser()
        if not self.validate_local(p):
            return []
        text = p.read_text("utf-8-sig", errors="replace")
        return self.parse_m3u(text, str(p.resolve()), pass_no, start_id)

    async def load_many(self, sources: list[str], pass_no: int, start_id: int) -> list[StreamRecord]:
        timeout = aiohttp.ClientTimeout(total=self.timeout)
        connector = aiohttp.TCPConnector(limit=max(10, self.workers), ssl=False)
        async with aiohttp.ClientSession(
            timeout=timeout,
            connector=connector,
            headers=self.session_headers,
        ) as session:
            results = await asyncio.gather(
                *(self.load_one(session, src, pass_no, start_id) for src in sources),
                return_exceptions=True,
            )
        out: list[StreamRecord] = []
        rid = start_id
        for result in results:
            if isinstance(result, Exception):
                continue
            for r in result:
                r.record_id = rid
                rid += 1
                out.append(r)
        return out


# ---------------------------------------------------------------------------
# Stream checking
# ---------------------------------------------------------------------------
async def check_stream(
    session: aiohttp.ClientSession,
    record: StreamRecord,
    timeout: int,
    rate_limiter: Optional[AsyncRateLimiter] = None,
) -> CheckEvent:
    started = time.perf_counter()
    event = CheckEvent(
        record_id=record.record_id,
        pass_no=record.discovered_pass,
        timestamp=now_iso(),
        working=False,
        status_code=0,
        latency_ms=999999.0,
        final_url="",
        content_type="",
        protocol="",
        resolution="",
        width=0,
        height=0,
        bitrate_kbps=0.0,
        codec="",
        has_audio=False,
        has_video=False,
        is_live=False,
        is_vod=False,
        archive_supported=False,
        error="",
    )
    record.url = apply_host_rewrites(record.url)
    if is_placeholder_source(record.url):
        event.error = "PLACEHOLDER_SKIPPED"
        return event

    last_error = ""
    for attempt in range(1, STREAM_CHECK_RETRIES + 1):
        try:
            if rate_limiter:
                await rate_limiter.wait()
            async with session.get(
                record.url,
                timeout=aiohttp.ClientTimeout(total=timeout),
                allow_redirects=True,
                headers={"User-Agent": random.choice(USER_AGENT_POOL)},
            ) as resp:
                event.latency_ms = round((time.perf_counter() - started) * 1000.0, 2)
                event.status_code = resp.status
                # Keep the operational URL in record.url; redact credentials in check history.
                event.final_url = safe_url_for_log(str(resp.url))
                event.content_type = resp.headers.get("Content-Type", "")
                if resp.status >= 400:
                    last_error = f"HTTP {resp.status}"
                    if attempt < STREAM_CHECK_RETRIES:
                        await asyncio.sleep(0.15 * attempt)
                        continue
                    event.error = last_error
                    return event

                sample = await resp.content.read(512 * 1024)
                text = sample.decode("utf-8", errors="ignore")
                ctype = event.content_type.lower()
                if "mpegurl" in ctype or "#EXTM3U" in text.upper():
                    event.protocol = "HLS"
                    upper = text.upper()
                    event.is_live = "#EXT-X-ENDLIST" not in upper
                    event.is_vod = not event.is_live
                    event.has_video = "#EXT-X-STREAM-INF" in upper or "CODECS=" in upper or "#EXTINF:" in upper
                    event.has_audio = "#EXT-X-MEDIA" in upper and "TYPE=AUDIO" in upper
                    event.archive_supported = any(
                        x in text.lower() for x in ("timeshift", "dvr", "catchup", "start=", "utc=")
                    )
                    codecs = set()
                    for m in re.finditer(r'CODECS\s*=\s*"([^"]+)"', text, re.I):
                        codecs.update(x.strip() for x in m.group(1).split(",") if x.strip())
                    event.codec = ",".join(sorted(codecs))
                elif "<MPD" in text[:2000] or "<mpd" in text[:2000]:
                    event.protocol = "DASH"
                    low = text.lower()
                    event.is_live = 'type="dynamic"' in low or "type='dynamic'" in low
                    event.is_vod = not event.is_live
                    event.has_video = 'contenttype="video"' in low or 'mimetype="video' in low
                    event.has_audio = 'contenttype="audio"' in low or 'mimetype="audio' in low
                    event.archive_supported = "timeshift" in low or "timeshiftbufferdepth" in low
                    event.codec = ",".join(sorted(set(re.findall(r'codecs\s*=\s*["\']([^"\']+)', text, re.I))))
                else:
                    event.protocol = "HTTP_STREAM"
                    event.has_video = True
                    event.is_live = True
                event.working = True
                return event
        except asyncio.TimeoutError:
            last_error = "TIMEOUT"
        except aiohttp.ClientError as exc:
            last_error = f"{type(exc).__name__}: {safe_error_text(exc)}"
        except Exception as exc:
            last_error = f"{type(exc).__name__}: {safe_error_text(exc)}"
        if attempt < STREAM_CHECK_RETRIES:
            await asyncio.sleep(0.15 * attempt)
    event.error = last_error or "CHECK_FAILED"
    event.latency_ms = round((time.perf_counter() - started) * 1000.0, 2)
    return event


def ffprobe_metadata(url: str, timeout: int = 12) -> dict[str, Any]:
    cmd = [
        "ffprobe", "-v", "error",
        "-show_entries", "stream=codec_name,width,height,bit_rate",
        "-of", "json", "-i", url,
    ]
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        if p.returncode != 0:
            return {}
        data = json.loads(p.stdout or "{}")
        streams = data.get("streams", [])
        video = next((s for s in streams if s.get("width")), None)
        if not video:
            return {}
        width = int(video.get("width") or 0)
        height = int(video.get("height") or 0)
        br = float(video.get("bit_rate") or 0) / 1000.0
        return {
            "width": width,
            "height": height,
            "resolution": f"{width}x{height}" if width and height else "",
            "bitrate_kbps": br,
            "codec": str(video.get("codec_name") or ""),
        }
    except Exception:
        return {}


def apply_event(record: StreamRecord, event: CheckEvent) -> None:
    record.working = event.working
    record.status_code = event.status_code
    record.latency_ms = event.latency_ms
    record.final_url = event.final_url
    record.content_type = event.content_type
    record.protocol = event.protocol
    record.resolution = event.resolution
    record.width = event.width
    record.height = event.height
    record.bitrate_kbps = event.bitrate_kbps
    record.codec = event.codec
    record.has_audio = event.has_audio
    record.has_video = event.has_video
    record.is_live = event.is_live
    record.is_vod = event.is_vod
    record.archive_supported = event.archive_supported
    record.error = event.error
    if event.working:
        record.successes += 1
    else:
        record.failures += 1

    if record.final_url:
        meta = classify_endpoint(record.final_url, record.name, record.source)
        record.host = meta["host"] or record.host
        if meta["region"] != "UNK":
            record.region = meta["region"]
        if meta["operator"]:
            record.operator = meta["operator"]
    record.cdn_node = record.host


def score(record: StreamRecord) -> float:
    if not record.working:
        return -1e9
    latency_score = max(0.0, 40.0 - min(record.latency_ms, 4000.0) / 100.0)
    resolution_score = {
        "UHD": 35.0, "4K": 35.0, "FHD": 30.0, "HD": 22.0, "SD": 10.0
    }.get(record.quality, 0.0)
    if record.height >= 2160:
        resolution_score = 35.0
    elif record.height >= 1080:
        resolution_score = 30.0
    elif record.height >= 720:
        resolution_score = max(resolution_score, 22.0)
    elif record.height >= 480:
        resolution_score = max(resolution_score, 10.0)
    bitrate_score = min(15.0, math.log2(max(record.bitrate_kbps, 1.0) + 1.0) * 1.5)
    protocol_score = 5.0 if record.protocol in ("HLS", "DASH") else 2.0
    special_bonus = 3.0 if record.special else 0.0
    ru_bonus = 2.0 if record.russian_priority else 0.0
    return latency_score + resolution_score + bitrate_score + protocol_score + special_bonus + ru_bonus


def diversity_key(r: StreamRecord) -> tuple[str, str, str]:
    return (r.region, r.host.lower(), r.operator.lower())


def choose_diverse(records: list[StreamRecord], target: int = 20) -> list[StreamRecord]:
    working = [r for r in records if r.working]
    working.sort(key=score, reverse=True)
    selected: list[StreamRecord] = []
    used_nodes: set[tuple[str, str, str]] = set()
    for r in working:
        k = diversity_key(r)
        if k in used_nodes:
            continue
        used_nodes.add(k)
        selected.append(r)
        if len(selected) >= target:
            return selected
    selected_ids = {r.record_id for r in selected}
    for r in working:
        if r.record_id not in selected_ids:
            selected.append(r)
            if len(selected) >= target:
                break
    return selected


# ---------------------------------------------------------------------------
# Alternatives (channel-centric + orbit/quality aware)
# ---------------------------------------------------------------------------
async def find_and_test_alternatives(
    records: list[StreamRecord],
    pass_no: int,
    target: int,
    candidate_limit: int,
    workers: int,
    timeout: int,
    ffprobe: bool,
    min_similarity: float,
    archive: Archive,
) -> tuple[list[StreamRecord], list[AlternativeEvent]]:
    groups: dict[str, list[StreamRecord]] = defaultdict(list)
    for r in records:
        # Prefer db_id for grouping when available
        key = r.db_id or r.normalized_channel or normalize_name(r.name) or "unknown"
        groups[key].append(r)

    jobs: list[tuple[str, list[StreamRecord], list[StreamRecord]]] = []
    for key, rs in groups.items():
        working = [r for r in rs if r.working and not is_placeholder_source(r.url)]
        if len(choose_diverse(working, target)) >= target:
            continue
        seed = max(rs, key=lambda x: (x.working, len(x.name or "")))
        existing_urls = {normalize_url(r.url) for r in working if r.url}
        present_orbits = {
            (str(r.quality or "UNKNOWN").upper(), str(r.orbit or "+0"))
            for r in working
        }
        missing_pairs = {
            (q, o)
            for q in ORBIT_QUALITY_TARGETS
            for o in ORBIT_SEARCH_ORDER
            if (q, o) not in present_orbits
        }

        scored: list[tuple[float, StreamRecord]] = []
        for c in records:
            if not c.url or is_placeholder_source(c.url):
                continue
            if normalize_url(c.url) in existing_urls:
                continue
            # Strong match if same db_id
            if seed.db_id and c.db_id and seed.db_id == c.db_id:
                sim = 1.0
            else:
                sim = channel_similarity(seed.name, c.name)
                if seed.db_name and c.db_name:
                    sim = max(sim, channel_similarity(seed.db_name, c.db_name))
            if sim < min_similarity:
                continue

            quality = str(c.quality or "UNKNOWN").upper()
            orbit = str(c.orbit or "+0")
            score_value = sim
            if c.host and c.host not in {x.host for x in working}:
                score_value += ALT_DIVERSITY_BONUS
            if (quality, orbit) in missing_pairs:
                score_value += ORBIT_MISSING_BONUS
            if quality in ORBIT_QUALITY_TARGETS:
                score_value += ORBIT_SEARCH_QUALITY_BONUS
            if orbit in ORBIT_SEARCH_ORDER:
                score_value += 0.03 * (len(ORBIT_SEARCH_ORDER) - ORBIT_SEARCH_ORDER.index(orbit)) / len(ORBIT_SEARCH_ORDER)
            scored.append((score_value, c))

        scored.sort(key=lambda x: (x[0], score(x[1])), reverse=True)
        jobs.append((key, rs, [c for _, c in scored[:candidate_limit]]))

    if not jobs:
        return [], []

    all_events: list[AlternativeEvent] = []
    new_records: list[StreamRecord] = []
    next_id = archive.next_id()
    rate_limiter = AsyncRateLimiter(DEFAULT_OPS_PER_SECOND)
    connector = aiohttp.TCPConnector(limit=max(8, workers), ssl=False)
    sem = asyncio.Semaphore(max(1, workers))

    async with aiohttp.ClientSession(
        connector=connector,
        timeout=aiohttp.ClientTimeout(total=timeout),
        headers={"User-Agent": DEFAULT_UA},
    ) as session:
        async def test(candidate: StreamRecord):
            async with sem:
                e = await check_stream(session, candidate, timeout, rate_limiter)
                return candidate, e

        for key, rs, candidates in jobs:
            working = [r for r in rs if r.working]
            selected = choose_diverse(working, target)
            existing_urls = {normalize_url(r.url) for r in working if r.url}
            rank = 0
            for coro in asyncio.as_completed([test(c) for c in candidates]):
                candidate, event = await coro
                rank += 1
                sim = channel_similarity(rs[0].name, candidate.name)
                all_events.append(AlternativeEvent(
                    pass_no=pass_no,
                    timestamp=now_iso(),
                    failed_record_id=rs[0].record_id,
                    failed_name=rs[0].name,
                    candidate_record_id=candidate.record_id,
                    candidate_name=candidate.name,
                    candidate_url=apply_host_rewrites(candidate.url),
                    similarity=sim,
                    working=event.working,
                    rank=rank,
                    region=candidate.region,
                    host=candidate.host,
                    operator=candidate.operator,
                    orbit=candidate.orbit,
                    quality=candidate.quality,
                ))
                if event.working and normalize_url(candidate.url) not in existing_urls:
                    nr = StreamRecord(
                        record_id=next_id,
                        name=rs[0].name or candidate.name,
                        url=apply_host_rewrites(candidate.url),
                        group=candidate.group or rs[0].group,
                        tvg_id=rs[0].tvg_id or candidate.tvg_id,
                        tvg_name=rs[0].tvg_name or candidate.tvg_name,
                        logo=rs[0].logo or candidate.logo,
                        source=candidate.source,
                        source_type="working_alternative",
                        discovered_pass=pass_no,
                        region=candidate.region,
                        host=candidate.host,
                        operator=candidate.operator,
                        normalized_channel=key if not key.startswith("id:") else normalize_name(rs[0].name),
                        orbit=candidate.orbit,
                        quality=candidate.quality,
                        special=any(x.special for x in rs) or candidate.special,
                        russian_priority=any(x.russian_priority for x in rs) or candidate.russian_priority,
                        db_id=rs[0].db_id or candidate.db_id,
                        db_name=rs[0].db_name or candidate.db_name,
                        db_aliases=list(dict.fromkeys(rs[0].db_aliases + candidate.db_aliases)),
                        db_country=rs[0].db_country or candidate.db_country,
                        db_language=rs[0].db_language or candidate.db_language,
                        db_network=rs[0].db_network or candidate.db_network,
                        db_match_score=max(rs[0].db_match_score, candidate.db_match_score),
                        db_match_type=rs[0].db_match_type or candidate.db_match_type,
                        alternative_of=rs[0].name,
                        alternative_rank=rank,
                        similarity=sim,
                        is_alternative=True,
                    )
                    apply_event(nr, event)
                    new_records.append(nr)
                    existing_urls.add(normalize_url(nr.url))
                    selected.append(nr)
                    next_id += 1

                    diverse_count = len(choose_diverse(selected, target))
                    covered_primary = {
                        (str(x.quality or "UNKNOWN").upper(), str(x.orbit or "+0"))
                        for x in selected
                    }
                    primary_missing = any(
                        (q, o) not in covered_primary
                        for q in ORBIT_QUALITY_TARGETS
                        for o in ORBIT_SEARCH_ORDER[:11]
                    )
                    if diverse_count >= target and not primary_missing:
                        break
    return new_records, all_events


# ---------------------------------------------------------------------------
# Check batch
# ---------------------------------------------------------------------------
async def check_records(
    records: list[StreamRecord],
    pass_no: int,
    workers: int,
    timeout: int,
    ffprobe: bool,
    recheck_failed: bool,
    ops_per_second: float,
) -> list[CheckEvent]:
    targets = [r for r in records if recheck_failed or not r.working]
    if not targets:
        return []

    connector = aiohttp.TCPConnector(limit=max(8, workers), ssl=False)
    sem = asyncio.Semaphore(max(1, workers))
    rate_limiter = AsyncRateLimiter(ops_per_second)
    events: list[CheckEvent] = []

    async with aiohttp.ClientSession(
        connector=connector,
        timeout=aiohttp.ClientTimeout(total=timeout),
        headers={"User-Agent": DEFAULT_UA},
    ) as session:
        async def one(r: StreamRecord) -> CheckEvent:
            async with sem:
                e = await check_stream(session, r, timeout, rate_limiter)
                if ffprobe and e.working:
                    meta = await asyncio.to_thread(ffprobe_metadata, r.url)
                    e.width = int(meta.get("width", 0))
                    e.height = int(meta.get("height", 0))
                    e.resolution = str(meta.get("resolution", ""))
                    e.bitrate_kbps = float(meta.get("bitrate_kbps", 0.0))
                    if meta.get("codec"):
                        e.codec = str(meta["codec"])
                e.pass_no = pass_no
                return e

        for coro in asyncio.as_completed([one(r) for r in targets]):
            e = await coro
            events.append(e)

    by_id = {r.record_id: r for r in records}
    for e in events:
        r = by_id.get(e.record_id)
        if r:
            apply_event(r, e)
    return events


# ---------------------------------------------------------------------------
# Outputs
# ---------------------------------------------------------------------------
def write_m3u(path: Path, records: Iterable[StreamRecord], title: str) -> None:
    with path.open("w", encoding="utf-8", newline="\n") as f:
        f.write(f'#EXTM3U x-no-dedup="1" x-title="{title}"\n')
        for r in records:
            if not r.url:
                continue
            attrs = [
                f'tvg-id="{r.tvg_id}"' if r.tvg_id else "",
                f'tvg-name="{r.tvg_name or r.name}"',
                f'tvg-logo="{r.logo}"' if r.logo else "",
                f'group-title="{r.group}"' if r.group else "",
            ]
            attrs = [x for x in attrs if x]
            label = r.name
            if r.orbit != "+0" and r.orbit not in label:
                label += f" {r.orbit}"
            if r.quality != "UNKNOWN" and r.quality.lower() not in label.lower():
                label += f" [{r.quality}]"
            if r.is_alternative:
                label += f" [ALT {r.alternative_rank}]"
            f.write(f'#EXTINF:-1 {" ".join(attrs)},{label}\n')
            f.write(r.url + "\n")


def write_snapshot(root: Path, pass_no: int, records: list[StreamRecord]) -> None:
    payload = {
        "version": VERSION,
        "pass": pass_no,
        "created_at": now_iso(),
        "records": [asdict(r) | {"score": score(r)} for r in records],
    }
    p = root / f"snapshot_pass_{pass_no:05d}.json"
    p.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    (root / "results.json").write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def write_channel_report(root: Path, records: list[StreamRecord]) -> None:
    groups: dict[str, list[StreamRecord]] = defaultdict(list)
    for r in records:
        key = r.db_id or r.normalized_channel or normalize_name(r.name)
        groups[key].append(r)

    report: dict[str, Any] = {}
    for key, rs in groups.items():
        working = [r for r in rs if r.working]
        report[key] = {
            "display_names": sorted({r.name for r in rs}),
            "db_id": next((r.db_id for r in rs if r.db_id), ""),
            "db_name": next((r.db_name for r in rs if r.db_name), ""),
            "total_records": len(rs),
            "working_records": len(working),
            "special": any(r.special for r in rs),
            "russian_priority": any(r.russian_priority for r in rs),
            "qualities": dict(sorted(Counter(r.quality for r in rs).items())),
            "orbits": dict(sorted(Counter(r.orbit for r in rs).items())),
            "regions": dict(sorted(Counter(r.region for r in rs).items())),
            "unique_hosts": len({r.host for r in working if r.host}),
            "unique_operators": len({r.operator for r in working if r.operator}),
            "latency_min_ms": min((r.latency_ms for r in working), default=None),
            "latency_avg_ms": (
                round(sum(r.latency_ms for r in working) / len(working), 2)
                if working else None
            ),
            "best_score": max((score(r) for r in working), default=None),
        }
    (root / "channels_report.json").write_text(
        json.dumps(report, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def print_stats(pass_no: int, records: list[StreamRecord]) -> None:
    channels = defaultdict(list)
    for r in records:
        key = r.db_id or r.normalized_channel
        channels[key].append(r)
    working = [r for r in records if r.working]
    special = [r for r in records if r.special]
    ru = [r for r in records if r.russian_priority]
    print()
    print("=" * 78)
    print(f"PASS {pass_no} | records={len(records)} | channels={len(channels)}")
    print(f"working={len(working)} | special={len(special)} | russian={len(ru)}")
    print(f"regions={dict(Counter(r.region for r in working))}")
    if working:
        print(f"latency min={min(r.latency_ms for r in working):.1f} ms")
        print(f"latency avg={sum(r.latency_ms for r in working)/len(working):.1f} ms")
    matched = sum(1 for r in records if r.db_id)
    print(f"db_matched={matched}")
    print("=" * 78)


# ---------------------------------------------------------------------------
# Persistent output_iptv layer (SQLite + ML + telemetry)
# ---------------------------------------------------------------------------
def ensure_iptv_output(root: Path) -> Path:
    out = root / OUTPUT_DIR_NAME
    for sub in ("versions", "telemetry", "snapshots", "ml", "reports", "playlists"):
        (out / sub).mkdir(parents=True, exist_ok=True)
    return out


def db_connect(db_path: Path) -> sqlite3.Connection:
    conn = sqlite3.connect(str(db_path))
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("""
        CREATE TABLE IF NOT EXISTS streams (
            record_id INTEGER PRIMARY KEY,
            name TEXT NOT NULL,
            normalized_channel TEXT,
            url TEXT NOT NULL,
            url_hash TEXT,
            group_title TEXT,
            tvg_id TEXT,
            tvg_name TEXT,
            logo TEXT,
            source TEXT,
            source_type TEXT,
            discovered_pass INTEGER,
            discovered_at TEXT,
            working INTEGER,
            status_code INTEGER,
            latency_ms REAL,
            final_url TEXT,
            content_type TEXT,
            protocol TEXT,
            resolution TEXT,
            width INTEGER,
            height INTEGER,
            bitrate_kbps REAL,
            codec TEXT,
            has_audio INTEGER,
            has_video INTEGER,
            is_live INTEGER,
            is_vod INTEGER,
            archive_supported INTEGER,
            error TEXT,
            region TEXT,
            host TEXT,
            operator TEXT,
            cdn_node TEXT,
            asn TEXT,
            orbit TEXT,
            quality TEXT,
            special INTEGER,
            russian_priority INTEGER,
            db_id TEXT,
            db_name TEXT,
            db_match_score REAL,
            db_match_type TEXT,
            alternative_of TEXT,
            alternative_rank INTEGER,
            similarity REAL,
            score REAL
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS checks (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            record_id INTEGER,
            pass_no INTEGER,
            timestamp TEXT,
            working INTEGER,
            status_code INTEGER,
            latency_ms REAL,
            resolution TEXT,
            codec TEXT,
            bitrate_kbps REAL,
            error TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS alternatives (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            pass_no INTEGER,
            timestamp TEXT,
            failed_record_id INTEGER,
            failed_name TEXT,
            candidate_record_id INTEGER,
            candidate_name TEXT,
            candidate_url TEXT,
            similarity REAL,
            working INTEGER,
            rank_no INTEGER,
            region TEXT,
            host TEXT,
            operator TEXT,
            orbit TEXT,
            quality TEXT
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS passes (
            pass_no INTEGER PRIMARY KEY,
            timestamp TEXT,
            records INTEGER,
            working INTEGER,
            channels INTEGER,
            special_channels INTEGER,
            min_latency_ms REAL,
            avg_latency_ms REAL
        )
    """)
    conn.execute("""
        CREATE TABLE IF NOT EXISTS ml_observations (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            timestamp TEXT,
            pass_no INTEGER,
            record_id INTEGER,
            channel TEXT,
            region TEXT,
            operator TEXT,
            host TEXT,
            orbit TEXT,
            quality TEXT,
            latency_ms REAL,
            resolution TEXT,
            bitrate_kbps REAL,
            codec TEXT,
            working INTEGER,
            score REAL,
            label TEXT
        )
    """)
    conn.commit()
    return conn


def db_insert_records(conn: sqlite3.Connection, records: list[StreamRecord]) -> None:
    rows = []
    for r in records:
        rows.append((
            r.record_id, r.name, r.normalized_channel, r.url,
            sha256_text(r.url), r.group, r.tvg_id, r.tvg_name, r.logo,
            r.source, r.source_type, r.discovered_pass, r.discovered_at,
            int(r.working), r.status_code, r.latency_ms, r.final_url,
            r.content_type, r.protocol, r.resolution, r.width, r.height,
            r.bitrate_kbps, r.codec, int(r.has_audio), int(r.has_video),
            int(r.is_live), int(r.is_vod), int(r.archive_supported), r.error,
            r.region, r.host, r.operator, r.cdn_node, r.asn, r.orbit,
            r.quality, int(r.special), int(r.russian_priority),
            r.db_id, r.db_name, r.db_match_score, r.db_match_type,
            r.alternative_of, r.alternative_rank, r.similarity, score(r),
        ))
    conn.executemany("""
        INSERT OR IGNORE INTO streams (
            record_id,name,normalized_channel,url,url_hash,group_title,tvg_id,
            tvg_name,logo,source,source_type,discovered_pass,discovered_at,
            working,status_code,latency_ms,final_url,content_type,protocol,
            resolution,width,height,bitrate_kbps,codec,has_audio,has_video,
            is_live,is_vod,archive_supported,error,region,host,operator,
            cdn_node,asn,orbit,quality,special,russian_priority,
            db_id,db_name,db_match_score,db_match_type,
            alternative_of,alternative_rank,similarity,score
        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
    """, rows)
    conn.commit()


def db_insert_checks(conn: sqlite3.Connection, events: list[CheckEvent]) -> None:
    conn.executemany("""
        INSERT INTO checks (
            record_id,pass_no,timestamp,working,status_code,latency_ms,
            resolution,codec,bitrate_kbps,error
        ) VALUES (?,?,?,?,?,?,?,?,?,?)
    """, [
        (e.record_id, e.pass_no, e.timestamp, int(e.working), e.status_code,
         e.latency_ms, e.resolution, e.codec, e.bitrate_kbps, e.error)
        for e in events
    ])
    conn.commit()


def db_insert_alternatives(conn: sqlite3.Connection, events: list[AlternativeEvent]) -> None:
    conn.executemany("""
        INSERT INTO alternatives (
            pass_no,timestamp,failed_record_id,failed_name,candidate_record_id,
            candidate_name,candidate_url,similarity,working,rank_no,region,
            host,operator,orbit,quality
        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
    """, [
        (e.pass_no, e.timestamp, e.failed_record_id, e.failed_name,
         e.candidate_record_id, e.candidate_name, e.candidate_url,
         e.similarity, int(e.working), e.rank, e.region, e.host,
         e.operator, e.orbit, e.quality)
        for e in events
    ])
    conn.commit()


def ml_label(r: StreamRecord) -> str:
    if not r.working:
        return "failed"
    if r.latency_ms <= 150:
        return "excellent_latency"
    if r.latency_ms <= 300:
        return "good_latency"
    if r.latency_ms <= 800:
        return "usable_latency"
    return "slow_latency"


def write_ml_json(out: Path, records: list[StreamRecord], pass_no: int) -> None:
    rows = []
    for r in records:
        rows.append({
            "record_id": r.record_id,
            "pass": pass_no,
            "channel": r.name,
            "normalized_channel": r.normalized_channel,
            "db_id": r.db_id,
            "db_name": r.db_name,
            "url": r.url,
            "url_hash": sha256_text(r.url),
            "region": r.region,
            "operator": r.operator,
            "host": r.host,
            "cdn_node": r.cdn_node,
            "orbit": r.orbit,
            "quality": r.quality,
            "special": r.special,
            "russian_priority": r.russian_priority,
            "working": r.working,
            "latency_ms": r.latency_ms,
            "resolution": r.resolution,
            "width": r.width,
            "height": r.height,
            "bitrate_kbps": r.bitrate_kbps,
            "codec": r.codec,
            "protocol": r.protocol,
            "has_audio": r.has_audio,
            "has_video": r.has_video,
            "is_live": r.is_live,
            "score": score(r),
            "label": ml_label(r),
        })
    payload = {
        "schema_version": 1,
        "model_name": "Vladik_llm",
        "created_at": now_iso(),
        "pass": pass_no,
        "description": "Append-only feature/observation dataset for ML ranking of IPTV streams.",
        "records": rows,
    }
    (out / ML_JSON_NAME).write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
    (out / "ml" / f"M3U_pass_{pass_no:05d}.json").write_text(
        json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8",
    )


def append_ml_model_artifact(out: Path, pass_no: int, records: list[StreamRecord]) -> None:
    working = [r for r in records if r.working]
    by_region: dict[str, list[float]] = defaultdict(list)
    by_quality: dict[str, list[float]] = defaultdict(list)
    by_operator: dict[str, list[float]] = defaultdict(list)
    for r in working:
        if r.latency_ms < 999999:
            by_region[r.region].append(r.latency_ms)
            by_quality[r.quality].append(r.latency_ms)
            by_operator[r.operator or "unknown"].append(r.latency_ms)

    def stats(d):
        result = {}
        for k, vals in d.items():
            result[k] = {
                "samples": len(vals),
                "avg_latency_ms": round(statistics.mean(vals), 3),
                "median_latency_ms": round(statistics.median(vals), 3),
                "min_latency_ms": round(min(vals), 3),
            }
        return result

    model = {
        "format": "Vladik_llm_observation_model_v1",
        "model_name": "Vladik_llm",
        "kind": "incremental-ranking-statistics",
        "pass": pass_no,
        "updated_at": now_iso(),
        "samples": len(records),
        "working_samples": len(working),
        "features": [
            "channel_similarity", "latency_ms", "resolution", "bitrate_kbps",
            "codec", "protocol", "region", "operator", "host", "orbit",
            "quality", "special", "russian_priority", "working", "db_match",
        ],
        "learned_statistics": {
            "region": stats(by_region),
            "quality": stats(by_quality),
            "operator": stats(by_operator),
        },
        "note": (
            "This artifact is intentionally non-executable. It is an incremental "
            "feature/statistics model that can be consumed by a future ML trainer."
        ),
    }
    (out / ML_DATA_NAME).write_text(json.dumps(model, ensure_ascii=False, indent=2), encoding="utf-8")
    (out / "ml" / f"Vladik_llm_pass_{pass_no:05d}.ml").write_text(
        json.dumps(model, ensure_ascii=False, indent=2), encoding="utf-8",
    )


def append_telemetry(
    out: Path,
    pass_no: int,
    records: list[StreamRecord],
    events: list[CheckEvent],
    alt_events: list[AlternativeEvent],
    started_at: float,
) -> None:
    telemetry_dir = out / "telemetry"
    channels = {r.db_id or r.normalized_channel for r in records}
    working = [r for r in records if r.working]
    lat = [r.latency_ms for r in working if r.latency_ms < 999999]
    payload = {
        "timestamp": now_iso(),
        "pass": pass_no,
        "duration_sec": round(time.perf_counter() - started_at, 3),
        "records_total": len(records),
        "channels_total": len(channels),
        "working_total": len(working),
        "failed_total": len(records) - len(working),
        "special_total": sum(1 for r in records if r.special),
        "russian_total": sum(1 for r in records if r.russian_priority),
        "db_matched": sum(1 for r in records if r.db_id),
        "checks_this_pass": len(events),
        "alternatives_this_pass": len(alt_events),
        "new_alternatives_working": sum(1 for e in alt_events if e.working),
        "latency_min_ms": round(min(lat), 3) if lat else None,
        "latency_avg_ms": round(statistics.mean(lat), 3) if lat else None,
        "latency_median_ms": round(statistics.median(lat), 3) if lat else None,
        "unique_hosts": len({r.host for r in working if r.host}),
        "unique_operators": len({r.operator for r in working if r.operator}),
        "regions": dict(Counter(r.region for r in working)),
        "qualities": dict(Counter(r.quality for r in working)),
        "orbits": dict(Counter(r.orbit for r in records)),
        "python": platform.python_version(),
        "platform": platform.platform(),
    }
    with (telemetry_dir / TELEMETRY_NAME).open("a", encoding="utf-8") as f:
        f.write(json.dumps(payload, ensure_ascii=False) + "\n")
    (telemetry_dir / TELEMETRY_SUMMARY).write_text(
        json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8",
    )


def write_versioned_playlist_bundle(
    out: Path,
    pass_no: int,
    records: list[StreamRecord],
    diverse_view: list[StreamRecord],
) -> None:
    version_dir = out / "versions" / f"pass_{pass_no:05d}"
    version_dir.mkdir(parents=True, exist_ok=True)
    working = [r for r in records if r.working]
    ru_working = [r for r in working if r.russian_priority]

    write_m3u(version_dir / "Stable.m3u", diverse_view, "STABLE")
    write_m3u(version_dir / "Mega.m3u", working, "MEGA")
    write_m3u(version_dir / "Ultra.m3u", records, "ULTRA_ALL")
    write_m3u(version_dir / "Russia.m3u", ru_working, "RUSSIA")

    write_m3u(out / "Stable.m3u", diverse_view, "STABLE")
    write_m3u(out / "Mega.m3u", working, "MEGA")
    write_m3u(out / "Ultra.m3u", records, "ULTRA_ALL")
    write_m3u(out / "Russia.m3u", ru_working, "RUSSIA")


def sync_database_and_ml(
    out: Path,
    pass_no: int,
    records: list[StreamRecord],
    events: list[CheckEvent],
    alt_events: list[AlternativeEvent],
) -> None:
    conn = db_connect(out / DB_NAME)
    db_insert_records(conn, records)
    db_insert_checks(conn, events)
    db_insert_alternatives(conn, alt_events)

    working = [r for r in records if r.working]
    lat = [r.latency_ms for r in working if r.latency_ms < 999999]
    conn.execute("""
        INSERT OR REPLACE INTO passes (
            pass_no,timestamp,records,working,channels,special_channels,
            min_latency_ms,avg_latency_ms
        ) VALUES (?,?,?,?,?,?,?,?)
    """, (
        pass_no, now_iso(), len(records), len(working),
        len({r.db_id or r.normalized_channel for r in records}),
        sum(1 for r in records if r.special),
        min(lat) if lat else None,
        statistics.mean(lat) if lat else None,
    ))
    for r in records:
        conn.execute("""
            INSERT INTO ml_observations (
                timestamp,pass_no,record_id,channel,region,operator,host,
                orbit,quality,latency_ms,resolution,bitrate_kbps,codec,
                working,score,label
            ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """, (
            now_iso(), pass_no, r.record_id, r.name, r.region, r.operator,
            r.host, r.orbit, r.quality, r.latency_ms, r.resolution,
            r.bitrate_kbps, r.codec, int(r.working), score(r), ml_label(r),
        ))
    conn.commit()
    conn.close()
    write_ml_json(out, records, pass_no)
    append_ml_model_artifact(out, pass_no, records)


# ---------------------------------------------------------------------------
# Source building
# ---------------------------------------------------------------------------
def source_file_is_safe(path: Path, output: Path) -> bool:
    try:
        p = path.resolve()
        o = output.resolve()
        if p == o or o in p.parents:
            return False
    except Exception:
        return False
    return p.name.lower() not in GENERATED_NAMES


def load_source_list(path: Path, output: Path) -> list[str]:
    if not path.exists() or not source_file_is_safe(path, output):
        return []
    out = []
    for line in path.read_text("utf-8-sig", errors="replace").splitlines():
        s = line.strip()
        if not s or s.startswith("#"):
            continue
        out.append(s)
    return out


def build_sources(args: argparse.Namespace) -> list[str]:
    sources: list[str] = []
    if not args.no_builtin_sources:
        sources.extend(VERIFIED_REAL_SOURCES)
    if not args.no_user_sources:
        sources.extend(USER_PROVIDED_SOURCES)
    sources.extend(args.source or [])
    # If no --source-list was passed, automatically load a local sources.txt
    # next to the current working directory when present. Exact URLs and duplicate
    # lines are preserved; this is deliberate for append-only collection.
    source_list_paths = args.source_list or (["sources.txt"] if Path("sources.txt").is_file() else [])
    for sl in source_list_paths:
        sources.extend(load_source_list(Path(sl).expanduser(), Path(args.output)))
    out: list[str] = []
    for source in sources:
        if is_placeholder_source(source):
            continue
        source = apply_host_rewrites(clean_url(source))
        if source:
            # Intentional: repeated sources are retained. This collector is append-only
            # and does not deduplicate URLs, source entries, channels, or stream records.
            out.append(source)
    return out


# ---------------------------------------------------------------------------
# XMLTV / EPG aggregation (append all feed elements; no deduplication)
# ---------------------------------------------------------------------------
async def fetch_and_merge_epg(output: Path, timeout_seconds: int = 60) -> dict[str, Any]:
    """Download configured XMLTV feeds and merge their channel/programme elements.

    Every feed entry is retained in source order; this intentionally does not
    deduplicate channel IDs or programmes. A failed EPG feed does not stop IPTV scans.
    """
    root = ET.Element("tv", {"generator-info-name": VERSION})
    stats: dict[str, Any] = {"created_at": now_iso(), "feeds": [], "channels": 0, "programmes": 0}
    timeout = aiohttp.ClientTimeout(total=timeout_seconds)
    connector = aiohttp.TCPConnector(limit=8, ssl=False)
    async with aiohttp.ClientSession(timeout=timeout, connector=connector, headers={"User-Agent": DEFAULT_UA}) as session:
        for feed_name, feed_url in EPG_SOURCES:
            feed_stat: dict[str, Any] = {"name": feed_name, "url": safe_url_for_log(feed_url), "ok": False, "channels": 0, "programmes": 0}
            try:
                async with session.get(feed_url, allow_redirects=True) as response:
                    response.raise_for_status()
                    raw = await response.content.read(256 * 1024 * 1024 + 1)
                if len(raw) > 256 * 1024 * 1024:
                    raise ValueError("EPG feed exceeds 256 MiB limit")
                if raw[:2] == b"\x1f\x8b":
                    raw = gzip.decompress(raw)
                parsed = ET.fromstring(raw)
                for child in list(parsed):
                    tag = child.tag.rsplit("}", 1)[-1].lower()
                    if tag == "channel":
                        feed_stat["channels"] += 1
                    elif tag == "programme":
                        feed_stat["programmes"] += 1
                    root.append(child)
                feed_stat["ok"] = True
            except Exception as exc:
                feed_stat["error"] = type(exc).__name__
                logging.getLogger("ultra").warning("EPG FAIL %s (%s)", feed_name, type(exc).__name__)
            stats["channels"] += feed_stat["channels"]
            stats["programmes"] += feed_stat["programmes"]
            stats["feeds"].append(feed_stat)

    if stats["channels"] or stats["programmes"]:
        xml_bytes = ET.tostring(root, encoding="utf-8", xml_declaration=True)
        output.mkdir(parents=True, exist_ok=True)
        (output / "epg.xml").write_bytes(xml_bytes)
        with (output / "epg.xml.gz").open("wb") as f:
            with gzip.GzipFile(fileobj=f, mode="wb", mtime=0) as gz:
                gz.write(xml_bytes)
    stats["saved"] = bool(stats["channels"] or stats["programmes"])
    (output / "epg_stats.json").write_text(json.dumps(stats, ensure_ascii=False, indent=2), encoding="utf-8")
    return stats


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
async def main_async(args: argparse.Namespace) -> int:
    output = Path(args.output).expanduser().resolve()
    output.mkdir(parents=True, exist_ok=True)
    iptv_out = ensure_iptv_output(output)
    log_file = output / "scanner_ultra_mega.log"
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s | %(levelname)s | %(message)s",
        handlers=[logging.FileHandler(log_file, encoding="utf-8"), logging.StreamHandler(sys.stdout)],
        force=True,
    )
    log = logging.getLogger("ultra")
    log.info(
        "ULTRA-MEGA START | version=%s | workers=%d | alt_workers=%d | "
        "source_workers=%d | ops/s=%.1f | min_alternatives=%d",
        VERSION, args.workers, args.alt_workers, args.source_workers,
        args.ops_per_second, args.min_alternatives,
    )
    log.info(
        "ORBIT SEARCH | reference=+0 Moscow | primary=%s | rare=%s | qualities=%s",
        ",".join(ORBIT_SEARCH_ORDER[:11]),
        ",".join(ORBIT_SEARCH_ORDER[11:]),
        ",".join(ORBIT_QUALITY_TARGETS),
    )

    # Load channel database: local + remote (primary) + builtin for orbits/qualities
    extra_db_dirs = [output, Path.cwd()]
    explicit_db_files: list[Path] = []
    if args.channel_db:
        for p in args.channel_db:
            pp = Path(p).expanduser().resolve()
            if pp.is_file():
                explicit_db_files.append(pp)
            elif pp.is_dir():
                extra_db_dirs.append(pp)
    # Pre-load explicit files so they always participate
    if explicit_db_files:
        pre = load_local_channel_files(explicit_db_files)
        if pre:
            # temporarily stash into global via build after full load
            log.info("CHANNEL DB EXPLICIT: %d records from --channel-db", len(pre))
    connector = aiohttp.TCPConnector(limit=16, ssl=False)
    async with aiohttp.ClientSession(
        connector=connector,
        timeout=aiohttp.ClientTimeout(total=60),
        headers={"User-Agent": DEFAULT_UA},
    ) as session:
        db_count = await load_external_channel_database(
            session,
            extra_dirs=extra_db_dirs,
            skip_remote=args.no_remote_db,
        )
    # Merge explicit files on top if any were not picked by dir scan
    if explicit_db_files:
        extra_rows = load_local_channel_files(explicit_db_files)
        if extra_rows:
            merged = merge_db([*CHANNEL_DB, *extra_rows])
            build_db_indexes(merged)
            db_count = len(merged)
    log.info("CHANNEL DATABASE READY: %d records", db_count)

    # EPG is optional for offline/local tests and environments without network access.
    if args.no_epg:
        epg_stats = {"feeds": [], "channels": 0, "programmes": 0, "saved": False, "skipped": True}
        log.info("EPG SKIPPED (--no-epg)")
    else:
        epg_stats = await fetch_and_merge_epg(output)
        log.info(
            "EPG READY | feeds=%d | channels=%d | programmes=%d | saved=%s",
            len(epg_stats.get("feeds", [])), epg_stats.get("channels", 0),
            epg_stats.get("programmes", 0), epg_stats.get("saved", False),
        )

    archive = Archive(output)
    start_pass = archive.load_pass()
    sources = build_sources(args)
    if not sources:
        print("Нет источников. Используй -s/--source или --source-list.")
        return 2

    loader = SourceLoader(
        output=output,
        timeout=args.source_timeout,
        workers=args.source_workers,
        user_agent=args.user_agent,
        ops_per_second=args.ops_per_second,
    )

    for offset in range(args.passes):
        pass_no = start_pass + offset + 1
        print(f"\n### PASS {pass_no} ###")
        pass_started_at = time.perf_counter()

        new_records = await loader.load_many(sources, pass_no, archive.next_id())
        # Enrich any that missed DB (already done in parse, but safe)
        for r in new_records:
            if not r.db_id:
                enrich_record_from_db(r)

        archive.append_records(new_records)
        records = archive.records

        events = await check_records(
            records,
            pass_no,
            args.workers,
            args.timeout,
            args.ffprobe,
            recheck_failed=args.recheck_failed,
            ops_per_second=args.ops_per_second,
        )
        archive.append_diagnostics(events)
        by_id_for_log = {r.record_id: r for r in records}
        for e in events:
            rr = by_id_for_log.get(e.record_id)
            log.info(
                "CHECK #%d | %s | %s | HTTP=%s | %.1fms | %s",
                e.record_id, "OK" if e.working else "FAIL",
                rr.name if rr else "", e.status_code, e.latency_ms,
                e.error or e.protocol,
            )

        alt_records, alt_events = await find_and_test_alternatives(
            records,
            pass_no=pass_no,
            target=args.min_alternatives,
            candidate_limit=args.alternative_candidates,
            workers=args.alt_workers,
            timeout=args.timeout,
            ffprobe=args.ffprobe,
            min_similarity=args.similarity,
            archive=archive,
        )
        if alt_records:
            archive.append_records(alt_records)
        if alt_events:
            archive.append_alternatives(alt_events)

        records = archive.records
        working = [r for r in records if r.working]
        all_records = list(records)
        diverse_view: list[StreamRecord] = []
        seen_keys: set[str] = set()
        for r in sorted(working, key=score, reverse=True):
            key = r.db_id or r.normalized_channel
            if key in seen_keys:
                continue
            rs = [x for x in working if (x.db_id or x.normalized_channel) == key]
            diverse_view.extend(choose_diverse(rs, args.min_alternatives))
            seen_keys.add(key)

        write_m3u(output / "all.m3u", all_records, "ALL RECORDS")
        write_m3u(output / "online.m3u", working, "ALL WORKING")
        write_m3u(output / "all_with_alts.m3u", working, "ALL WORKING WITH ALTERNATIVES")
        write_m3u(output / "best.m3u", diverse_view, "DIVERSE BEST STREAMS")

        write_snapshot(output, pass_no, records)
        write_channel_report(output, records)

        write_versioned_playlist_bundle(iptv_out, pass_no, records, diverse_view)
        sync_database_and_ml(iptv_out, pass_no, records, events, alt_events)
        append_telemetry(iptv_out, pass_no, records, events, alt_events, pass_started_at)
        (iptv_out / "snapshots" / f"snapshot_pass_{pass_no:05d}.json").write_text(
            json.dumps(
                {
                    "pass": pass_no,
                    "created_at": now_iso(),
                    "records": [asdict(r) | {"score": score(r)} for r in records],
                },
                ensure_ascii=False,
                indent=2,
            ),
            encoding="utf-8",
        )

        archive.save_pass(pass_no)
        print_stats(pass_no, records)
        if alt_records:
            print(f"New working alternatives appended: {len(alt_records)}")

    print(f"\nГотово. Архив: {output}")
    print("records.jsonl      — все найденные записи, append-only")
    print("diagnostics.jsonl  — история всех проверок")
    print("alternatives.jsonl — история поиска альтернатив")
    print("all.m3u / online.m3u / best.m3u")
    print("channels_report.json — статистика по каналам/орбитам/регионам/DB")
    print(f"{iptv_out}/ — постоянный каталог результатов")
    print("  Stable.m3u / Mega.m3u / Ultra.m3u / Russia.m3u")
    print("  M3U_Base.db — SQLite база")
    print("  M3U.JSON / Vladik_llm.ml — ML feature dataset + stats model")
    print("  telemetry/telemetry.jsonl — телеметрия проходов")
    return 0


def build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Ultra-Mega IPTV Collector 6.1 — full append-only archive, channel DB, alternatives, EPG, SQLite and telemetry"
    )
    p.add_argument("-s", "--source", action="append", default=[],
                   help="M3U/TXT file or HTTP(S) playlist. Repeatable.")
    p.add_argument("--source-list", action="append", default=[],
                   help="Text file containing one source URL/path per line. Auth query strings are preserved; never publish this file.")
    p.add_argument("--no-builtin-sources", action="store_true",
                   help="Do not use the built-in public IPTV playlist indexes.")
    p.add_argument("--no-user-sources", action="store_true",
                   help="Do not use the separately stored user-provided general IPTV source list.")
    p.add_argument("-o", "--output", default="ultra_mega_iptv_data",
                   help="Persistent archive/output directory.")
    p.add_argument("--passes", type=int, default=1,
                   help="Number of passes in this run.")
    p.add_argument("--workers", type=int, default=DEFAULT_CHECK_WORKERS,
                   help="Concurrent stream check workers.")
    p.add_argument("--alt-workers", type=int, default=DEFAULT_ALT_WORKERS,
                   help="Concurrent alternative check workers.")
    p.add_argument("--source-workers", type=int, default=DEFAULT_SOURCE_WORKERS,
                   help="Concurrent source workers.")
    p.add_argument("--timeout", type=int, default=12,
                   help="Stream timeout in seconds.")
    p.add_argument("--source-timeout", type=int, default=30,
                   help="Playlist/source timeout in seconds.")
    p.add_argument("--min-alternatives", type=int, default=DEFAULT_MIN_ALTERNATIVES,
                   help="Target number of diverse working streams per channel.")
    p.add_argument("--alternative-candidates", type=int, default=DEFAULT_ALTERNATIVE_CANDIDATES,
                   help="How many candidate records to test per under-covered channel.")
    p.add_argument("--ops-per-second", type=float, default=DEFAULT_OPS_PER_SECOND,
                   help="Maximum network operation start rate.")
    p.add_argument("--similarity", type=float, default=DEFAULT_SIMILARITY,
                   help="Minimum channel-name similarity for alternatives.")
    p.add_argument("--recheck-failed", action="store_true",
                   help="Recheck all historical failed records on every pass.")
    p.add_argument("--ffprobe", action="store_true",
                   help="Run ffprobe on working streams for resolution/bitrate/codec.")
    p.add_argument("--channel-db", action="append", default=[],
                   help="Local channel DB file or directory (csv/json/py). Repeatable. "
                        "Also auto-loads channels.csv/json/py from cwd and output dir.")
    p.add_argument("--no-remote-db", action="store_true",
                   help="Do not download channel database from GitHub; use only local files.")
    p.add_argument("--no-epg", action="store_true",
                   help="Skip XMLTV downloads (useful for offline/local tests).")
    p.add_argument("--user-agent", default=DEFAULT_UA)
    p.add_argument("-v", "--verbose", action="store_true")
    return p


def main() -> int:
    args = build_parser().parse_args()
    if args.passes < 1:
        print("--passes must be >= 1")
        return 2
    try:
        return asyncio.run(main_async(args))
    except KeyboardInterrupt:
        print("\nОстановлено пользователем.")
        return 130


if __name__ == "__main__":
    raise SystemExit(main())