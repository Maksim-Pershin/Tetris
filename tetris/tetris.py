"""
Тетрис на pygame.

Запуск:   py tetris.py
(если нет pygame:  py -m pip install pygame)

Режимы: один игрок (марафон) и два игрока на одной клавиатуре.

Один игрок:
    ← →        движение
    ↓          мягкий спуск
    ↑ / X      поворот по часовой
    Z / Ctrl   поворот против часовой
    Пробел     мгновенный сброс
    C / Shift  убрать фигуру в запас

Два игрока:
    Игрок 1:   A D — движение, S — вниз, W — поворот, Q — поворот назад,
               Пробел — сброс, E — запас
    Игрок 2:   ← → — движение, ↓ — вниз, ↑ — поворот, Пр.Ctrl или / — поворот назад,
               Enter — сброс, Пр.Shift или . — запас
    Очищенные линии улетают сопернику мусором снизу.

Везде:
    P / Esc    пауза
    M          музыка вкл/выкл
    N          звуки вкл/выкл
    F11 / Alt+Enter   полный экран / окно
    Громкость музыки и звуков — стрелками ← → в меню и на паузе.

Игра по сети (без сервера): меню «Игра по сети» → «Создать игру» / «Подключиться».
    В одной Wi-Fi сети — по адресу из экрана ожидания. Через интернет — оба в одной сети
    Radmin VPN / ZeroTier / Tailscale. Порт 47474. Сетевая часть — tetris_net.py.
    Проверить на одном компьютере: вторая копия запускается с ключом --allow-second-copy.

Ярлык без консоли: pythonw.exe tetris.py (иконка — tetris.ico, создаётся командой
py tetris.py --make-icon).
"""
import json
import math
import os
import random
import sys
import threading
import time
from array import array
from collections import namedtuple

os.environ.setdefault("PYGAME_HIDE_SUPPORT_PROMPT", "1")
import pygame

import tetris_net as net

# ---------------------------------------------------------------- настройки
COLS, ROWS = 10, 20
HIDDEN = 2                      # невидимые строки сверху, где появляются фигуры
TOTAL_ROWS = ROWS + HIDDEN
MARGIN = 24

# раскладка одиночной игры
CELL = 32
SIDE_W = 180
BOARD_W = COLS * CELL
BOARD_H = ROWS * CELL
BOARD_X = MARGIN + SIDE_W + MARGIN
BOARD_Y = MARGIN
RIGHT_X = BOARD_X + BOARD_W + MARGIN
WIDTH = RIGHT_X + SIDE_W + MARGIN
HEIGHT = BOARD_H + 2 * MARGIN

# раскладка игры вдвоём
VS_CELL = 30
VS_SIDE_W = 120
VS_GAP = 32
VS_TOP = MARGIN + 36
VS_PLAYER_W = VS_SIDE_W + 20 + COLS * VS_CELL + 12 + VS_SIDE_W
VS_WIDTH = 2 * MARGIN + 2 * VS_PLAYER_W + VS_GAP
VS_HEIGHT = VS_TOP + ROWS * VS_CELL + MARGIN

# пункты главного меню
MENU_TOP = 226
MENU_STEP = 48
MENU_ITEM_SIZE = (340, 42)
NET_MENU_TOP = 230
MENU_ARROW_ZONE = 70            # клик у края пункта громкости — тише / громче


# курсор — стрелка из маленьких блоков, по которой бежит радужная волна
CURSOR_SHAPE = [
    "X.......",
    "XX......",
    "XXX.....",
    "XXXX....",
    "XXXXX...",
    "XXXXXX..",
    "XXX.....",
    "X..XX...",
    "....XX..",
]
CURSOR_FRAMES = 7
CURSOR_FPS = 10
TRAIL_LIMIT = 140


def menu_item_rect(i, width, top=MENU_TOP):
    rect = pygame.Rect((0, 0), MENU_ITEM_SIZE)
    rect.center = (width // 2, top + i * MENU_STEP)
    return rect


# игра по сети
NET_SEND_INTERVAL = 0.05        # как часто отправлять сопернику своё поле
NET_PING_INTERVAL = 1.0
NET_TIMEOUT = 8.0               # столько секунд без вестей — связь потеряна
NET_OVER_GRACE = 0.4            # проиграли почти одновременно — ничья
MENU_STATES = ("menu", "records", "net_menu", "net_host", "net_join", "net_msg")
ADDRESS_CHARS = set("0123456789.:-_abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ")

FPS = 60
DAS = 0.16                      # задержка перед автоповтором движения
ARR = 0.045                     # скорость автоповтора
SOFT_DROP_INTERVAL = 0.09       # скорость падения при зажатой стрелке вниз (сек на клетку)
LOCK_DELAY = 0.5
MAX_LOCK_RESETS = 15
CLEAR_TIME = 0.22               # вспышка очищаемых линий
COLLAPSE_TIME = 0.18            # плавное проседание блоков после очистки
RISE_TIME = 0.12                # подъём мусорных линий
NEXT_COUNT = 5
VS_NEXT_COUNT = 3
COUNTDOWN = 3.0
FINISH_INPUT_DELAY = 0.8        # после конца игры клавиши не сразу перезапускают её
RECORDS_LIMIT = 10
MAX_NAME = 12
VOLUME_STEPS = 10               # громкость от 0 до 10 (0–100 %)
DEFAULT_NAME = "Игрок"

FROZEN = getattr(sys, "frozen", False)         # запущено как собранный Тетрис.exe
BASE_DIR = os.path.dirname(sys.executable if FROZEN else os.path.abspath(__file__))
# рекорды и настройки — в папке пользователя: так они не теряются, где бы ни лежала игра
USER_DIR = os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"), "Тетрис")
WINDOW_TITLE = "Тетрис"
ICON_FILE = os.path.join(BASE_DIR, "tetris.ico")
ERROR_LOG = os.path.join(USER_DIR, "tetris_error.log")
DATA_FILE = os.path.join(USER_DIR, "tetris_data.json")
LEGACY_DATA_FILE = os.path.join(BASE_DIR, "tetris_data.json")     # где данные лежали раньше

# фото, которые появляются сбоку при очистке линий: папка photos рядом с игрой
# и (в собранном Тетрис.exe) фото, встроенные при сборке
PHOTO_DIRS = [os.path.join(BASE_DIR, "photos")]
if FROZEN:
    PHOTO_DIRS.insert(0, os.path.join(getattr(sys, "_MEIPASS", BASE_DIR), "photos"))
PHOTO_EXTENSIONS = (".jpg", ".jpeg", ".png", ".webp", ".bmp", ".gif")
PHOTO_MAX_SIDE = 640            # фото уменьшаются до такого размера при загрузке
PHOTO_BUILD_SIDE = 720          # и до такого — при встраивании в .exe
PHOTO_TIME = 2.6                # сколько секунд висит фото
PHOTO_TIME_BIG = 3.6            # за «Тетрис», T-spin и идеальную очистку — дольше и крупнее
PHOTO_MIN_MARGIN = 150          # меньше этого по бокам места нет — фото ложится на панель управления
OLD_HIGHSCORE_FILE = os.path.join(BASE_DIR, "tetris_highscore.txt")

BOARD_BG = (12, 12, 28)
PANEL = (24, 24, 50)
PANEL_BORDER = (72, 72, 140)
GRID = (30, 30, 58)
TEXT = (238, 238, 255)
TEXT_DIM = (150, 150, 195)
ACCENT = (255, 215, 90)
GOOD = (130, 255, 150)
BAD = (255, 110, 120)
PLAYER_COLORS = [(90, 220, 255), (255, 165, 80)]

# фон меняется с каждым уровнем: (цвет сверху, цвет снизу)
BG_PALETTES = [
    ((22, 18, 48), (6, 6, 16)),
    ((10, 30, 62), (4, 8, 20)),
    ((8, 46, 52), (3, 12, 16)),
    ((14, 46, 26), (4, 12, 8)),
    ((52, 42, 10), (14, 10, 4)),
    ((62, 24, 12), (16, 6, 4)),
    ((62, 12, 36), (16, 4, 10)),
    ((42, 10, 64), (10, 3, 18)),
    ((32, 34, 44), (5, 5, 8)),
    ((72, 10, 12), (18, 2, 4)),
]

COLORS = {
    "I": (0, 215, 240),
    "O": (250, 210, 40),
    "T": (170, 75, 235),
    "S": (80, 215, 95),
    "Z": (240, 60, 75),
    "J": (55, 115, 245),
    "L": (250, 145, 35),
    "G": (120, 120, 140),       # мусорные линии
}

SHAPES = {
    "I": [[0, 0, 0, 0], [1, 1, 1, 1], [0, 0, 0, 0], [0, 0, 0, 0]],
    "O": [[1, 1], [1, 1]],
    "T": [[0, 1, 0], [1, 1, 1], [0, 0, 0]],
    "S": [[0, 1, 1], [1, 1, 0], [0, 0, 0]],
    "Z": [[1, 1, 0], [0, 1, 1], [0, 0, 0]],
    "J": [[1, 0, 0], [1, 1, 1], [0, 0, 0]],
    "L": [[0, 0, 1], [1, 1, 1], [0, 0, 0]],
}


def rotate_cw(m):
    return [list(row) for row in zip(*m[::-1])]


ROTATIONS = {}
for _kind, _m in SHAPES.items():
    _states = []
    for _ in range(4):
        _states.append([(x, y) for y, row in enumerate(_m) for x, v in enumerate(row) if v])
        _m = rotate_cw(_m)
    ROTATIONS[_kind] = _states

# Таблицы "wall kick" системы SRS (ось y направлена вверх, как в стандарте)
KICKS_JLSTZ = {
    (0, 1): [(0, 0), (-1, 0), (-1, 1), (0, -2), (-1, -2)],
    (1, 0): [(0, 0), (1, 0), (1, -1), (0, 2), (1, 2)],
    (1, 2): [(0, 0), (1, 0), (1, -1), (0, 2), (1, 2)],
    (2, 1): [(0, 0), (-1, 0), (-1, 1), (0, -2), (-1, -2)],
    (2, 3): [(0, 0), (1, 0), (1, 1), (0, -2), (1, -2)],
    (3, 2): [(0, 0), (-1, 0), (-1, -1), (0, 2), (-1, 2)],
    (3, 0): [(0, 0), (-1, 0), (-1, -1), (0, 2), (-1, 2)],
    (0, 3): [(0, 0), (1, 0), (1, 1), (0, -2), (1, -2)],
}
KICKS_I = {
    (0, 1): [(0, 0), (-2, 0), (1, 0), (-2, -1), (1, 2)],
    (1, 0): [(0, 0), (2, 0), (-1, 0), (2, 1), (-1, -2)],
    (1, 2): [(0, 0), (-1, 0), (2, 0), (-1, 2), (2, -1)],
    (2, 1): [(0, 0), (1, 0), (-2, 0), (1, -2), (-2, 1)],
    (2, 3): [(0, 0), (2, 0), (-1, 0), (2, 1), (-1, -2)],
    (3, 2): [(0, 0), (-2, 0), (1, 0), (-2, -1), (1, 2)],
    (3, 0): [(0, 0), (1, 0), (-2, 0), (1, -2), (-2, 1)],
    (0, 3): [(0, 0), (-1, 0), (2, 0), (-1, 2), (2, -1)],
}

LINE_SCORES = {1: 100, 2: 300, 3: 500, 4: 800}
LINE_NAMES = {1: "ЛИНИЯ", 2: "ДВОЙНАЯ", 3: "ТРОЙНАЯ", 4: "ТЕТРИС!"}
PERFECT_SCORES = {1: 800, 2: 1200, 3: 1800, 4: 2000}

# T-spin: очки за 0, 1, 2, 3 линии (умножаются на уровень)
TSPIN_SCORES = {"full": [400, 800, 1200, 1600], "mini": [100, 200, 400, 400]}
TSPIN_NAMES = {0: "T-SPIN", 1: "T-SPIN ОДИНАРНЫЙ", 2: "T-SPIN ДВОЙНОЙ", 3: "T-SPIN ТРОЙНОЙ"}
TSPIN_COLOR = (205, 135, 255)
B2B_COLOR = (255, 170, 70)
# углы вокруг центра T-фигуры (центр в клетке (1, 1) её рамки 3×3)
T_CORNERS = [(0, 0), (2, 0), (0, 2), (2, 2)]
# «передние» углы — с той стороны, куда смотрит выступ T, для поворотов 0..3
T_FRONT = {0: [(0, 0), (2, 0)], 1: [(2, 0), (2, 2)], 2: [(0, 2), (2, 2)], 3: [(0, 0), (0, 2)]}

# сколько мусорных линий получает соперник
LINE_ATTACK = {1: 0, 2: 1, 3: 2, 4: 4}
COMBO_ATTACK = [0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 4, 5]
PERFECT_ATTACK = 10
TSPIN_ATTACK = {"full": [0, 2, 4, 6], "mini": [0, 0, 1, 1]}
B2B_ATTACK = 1


def gravity_interval(level):
    return max(0.008, (0.8 - (level - 1) * 0.007) ** (level - 1))


def format_time(seconds):
    if seconds is None:
        return "—"
    seconds = int(seconds)
    return "{}:{:02d}".format(seconds // 60, seconds % 60)


def volume_text(settings, key):
    v = settings[key + "_volume"]
    return "{}%".format(v * 100 // VOLUME_STEPS) if settings[key] and v else "выкл"


def format_score(value):
    return "{:,}".format(value).replace(",", " ")


# ---------------------------------------------------------------- сохранения
class Storage:
    """Настройки и таблицы рекордов (по таблице на режим) в одном JSON-файле."""

    def __init__(self):
        self.settings = {"music": True, "sfx": True, "music_volume": 6, "sfx_volume": 8,
                         "fullscreen": True, "name": DEFAULT_NAME, "address": ""}
        self.records = {"marathon": []}
        self.load()

    @staticmethod
    def _read(path):
        try:
            with open(path, encoding="utf-8") as f:
                return json.load(f)
        except (OSError, ValueError):
            return None

    def load(self):
        data = self._read(DATA_FILE)
        migrate = False
        if not isinstance(data, dict) and os.path.abspath(LEGACY_DATA_FILE) != os.path.abspath(DATA_FILE):
            data = self._read(LEGACY_DATA_FILE)     # рекорды из прежнего места переезжают в папку пользователя
            migrate = isinstance(data, dict)

        if not isinstance(data, dict):
            # первый запуск новой версии: переносим старый рекорд
            try:
                with open(OLD_HIGHSCORE_FILE, encoding="utf-8") as f:
                    old = int(f.read().strip() or 0)
            except (OSError, ValueError):
                old = 0
            if old > 0:
                self.records["marathon"].append({"name": DEFAULT_NAME, "score": old, "lines": None,
                                                 "level": None, "time": None, "date": ""})
                self.save()
            return

        settings = data.get("settings")
        if isinstance(settings, dict):
            for key, default in self.settings.items():
                if isinstance(settings.get(key), type(default)):
                    self.settings[key] = settings[key]
            for key in ("music_volume", "sfx_volume"):
                self.settings[key] = max(0, min(VOLUME_STEPS, int(self.settings[key])))
        records = data.get("records")
        if isinstance(records, dict):
            for mode, rows in records.items():
                if isinstance(rows, list):
                    rows = [r for r in rows if isinstance(r, dict) and isinstance(r.get("score"), int)]
                    rows.sort(key=lambda r: -r["score"])
                    self.records[mode] = rows[:RECORDS_LIMIT]
        if migrate:
            self.save()

    def save(self):
        data = {"settings": self.settings, "records": self.records}
        tmp = DATA_FILE + ".tmp"
        try:
            os.makedirs(os.path.dirname(DATA_FILE), exist_ok=True)
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
            os.replace(tmp, DATA_FILE)
        except OSError:
            pass

    def table(self, mode):
        return self.records.setdefault(mode, [])

    def best(self, mode):
        table = self.table(mode)
        return table[0] if table else None

    def rank_for(self, mode, score):
        """Место (с нуля), которое займёт счёт в таблице, или None, если не попадает."""
        if score <= 0:
            return None
        table = self.table(mode)
        for i, row in enumerate(table):
            if score > row["score"]:
                return i
        return len(table) if len(table) < RECORDS_LIMIT else None

    def add(self, mode, entry):
        rank = self.rank_for(mode, entry["score"])
        if rank is None:
            return None
        table = self.table(mode)
        table.insert(rank, entry)
        del table[RECORDS_LIMIT:]
        self.save()
        return rank


# ---------------------------------------------------------------- звук
def midi_freq(note):
    return 440.0 * 2 ** ((note - 69) / 12.0)


# "Коробейники" — народная мелодия, та самая из классического тетриса.
# Каждый такт: список (нота MIDI или None для паузы, длительность в долях).
MELODY = [
    [(76, 1), (71, .5), (72, .5), (74, 1), (72, .5), (71, .5)],
    [(69, 1), (69, .5), (72, .5), (76, 1), (74, .5), (72, .5)],
    [(71, 1.5), (72, .5), (74, 1), (76, 1)],
    [(72, 1), (69, 1), (69, 1), (None, 1)],
    [(None, .5), (74, 1), (77, .5), (81, 1), (79, .5), (77, .5)],
    [(76, 1.5), (72, .5), (76, 1), (74, .5), (72, .5)],
    [(71, 1), (71, .5), (72, .5), (74, 1), (76, 1)],
    [(72, 1), (69, 1), (69, 1), (None, 1)],
    [(76, 2), (72, 2)],
    [(74, 2), (71, 2)],
    [(72, 2), (69, 2)],
    [(68, 2), (71, 2)],
    [(76, 2), (72, 2)],
    [(74, 2), (71, 2)],
    [(72, 1), (76, 1), (81, 2)],
    [(80, 4)],
]
BASS = [40, 45, 40, 45, 38, 36, 40, 45, 45, 40, 45, 40, 45, 40, 45, 40]
MUSIC_ORDER = list(range(8)) * 2 + list(range(8, 16))
MUSIC_TEMPOS = [140, 165, 195]   # темп растёт на высоких уровнях
MUSIC_VOLUME = 0.5
MUSIC_FADE = 0.8


def music_tier(level):
    if level >= 10:
        return 2
    if level >= 5:
        return 1
    return 0


class SoundManager:
    """Все звуки синтезируются прямо в коде — внешние файлы не нужны."""

    def __init__(self, store):
        self.store = store
        self.ok = False
        self.sfx = {}
        self.music = {}
        self._ready = []
        self.pos = 0
        self.playing = False
        self.paused = False
        self.fading = 0.0
        init = pygame.mixer.get_init()
        if not init:
            return
        self.rate, fmt, self.channels = init
        if fmt != -16:
            return
        try:
            pygame.mixer.set_num_channels(16)
            pygame.mixer.set_reserved(1)
            self.channel = pygame.mixer.Channel(0)
            self._make_sfx()
        except pygame.error:
            return
        self.ok = True
        threading.Thread(target=self._build_music, daemon=True).start()

    # --- синтез
    def _to_bytes(self, buf):
        samples = array("h", [int(32767 * (v if -1.0 < v < 1.0 else (1.0 if v > 0 else -1.0))) for v in buf])
        if self.channels > 1:
            samples = array("h", [s for s in samples for _ in range(self.channels)])
        return samples.tobytes()

    @staticmethod
    def _sound(data, volume):
        sound = pygame.mixer.Sound(buffer=data)
        sound.set_volume(volume)
        return sound

    def _tone(self, f0, dur, vol, wave="square", f1=None, decay=0.0, duty=0.5):
        rate = self.rate
        n = max(1, int(dur * rate))
        a, r = max(1, int(0.003 * rate)), max(1, int(0.015 * rate))
        f1 = f0 if f1 is None else f1
        out = [0.0] * n
        phase = 0.0
        for i in range(n):
            phase += (f0 + (f1 - f0) * i / n) / rate
            phase -= int(phase)
            if wave == "square":
                v = 1.0 if phase < duty else -1.0
            elif wave == "triangle":
                v = 4.0 * abs(phase - 0.5) - 1.0
            elif wave == "sine":
                v = math.sin(2 * math.pi * phase)
            else:
                v = random.uniform(-1.0, 1.0)
            env = min(1.0, i / a, (n - i) / r)
            if decay:
                env *= math.exp(-decay * i / rate)
            out[i] = v * env * vol
        return out

    @staticmethod
    def _mix(dst, src, offset=0):
        need = offset + len(src)
        if need > len(dst):
            dst.extend([0.0] * (need - len(dst)))
        dst[offset:need] = [a + b for a, b in zip(dst[offset:need], src)]
        return dst

    def _arp(self, notes, step, vol, wave="square", duty=0.25, ring=1.8):
        buf = []
        for i, note in enumerate(notes):
            self._mix(buf, self._tone(midi_freq(note), step * ring, vol, wave, decay=9, duty=duty),
                      int(i * step * self.rate))
        return buf

    def _make_sfx(self):
        t, mix, arp = self._tone, self._mix, self._arp
        self.sfx = {
            "move": t(240, 0.025, 0.10, "square", duty=0.25),
            "rotate": t(520, 0.045, 0.12, "square", f1=780, duty=0.25),
            "lock": mix(t(150, 0.08, 0.35, "sine", f1=70, decay=30), t(0, 0.04, 0.08, "noise", decay=60)),
            "drop": mix(t(220, 0.15, 0.5, "sine", f1=50, decay=16), t(0, 0.07, 0.22, "noise", decay=45)),
            "hold": t(360, 0.09, 0.18, "triangle", f1=720),
            "clear1": arp([84, 88], 0.06, 0.16),
            "clear2": arp([84, 88, 91], 0.055, 0.16),
            "clear3": arp([84, 88, 91, 96], 0.05, 0.16),
            "tetris": mix(arp([72, 76, 79, 84, 88, 91, 96], 0.045, 0.17),
                          t(2093, 0.4, 0.07, "triangle", decay=6), int(0.3 * self.rate)),
            "perfect": arp([72, 76, 79, 84, 79, 84, 88, 91, 96, 100, 103, 108], 0.06, 0.15, "triangle", ring=2.5),
            "levelup": arp([79, 84, 88, 91, 96], 0.07, 0.18, "triangle"),
            "tspin": mix(t(250, 0.16, 0.16, "square", f1=1100, duty=0.25),
                         arp([76, 80, 83, 88, 92], 0.045, 0.15, "triangle"), int(0.1 * self.rate)),
            "b2b": arp([91, 96, 100, 103], 0.04, 0.12, "square", ring=2.2),
            "garbage": mix(t(110, 0.2, 0.28, "square", f1=60), t(0, 0.1, 0.12, "noise", decay=25)),
            "count": t(660, 0.12, 0.2, "square", duty=0.25),
            "go": t(990, 0.35, 0.2, "square", duty=0.25, decay=4),
            "gameover": arp([76, 72, 69, 65, 64, 60], 0.14, 0.18, "triangle", ring=1.6),
            "win": arp([72, 76, 79, 84, 79, 84, 88], 0.1, 0.16, ring=1.6),
            "menu": t(880, 0.03, 0.12, "square", duty=0.25),
            "select": t(660, 0.08, 0.15, "square", f1=990, duty=0.25),
        }
        self.sfx = {name: self._sound(self._to_bytes(buf), 0.7) for name, buf in self.sfx.items()}

    def _note(self, freq, n, vol, wave, duty=0.5):
        step = freq / self.rate
        a, r = max(1, int(0.004 * self.rate)), max(1, int(0.02 * self.rate))
        if wave == "square":
            hi, lo = 1.0 - (2 * duty - 1), -1.0 - (2 * duty - 1)   # без постоянной составляющей
            raw = [hi if (i * step) % 1.0 < duty else lo for i in range(n)]
        else:
            raw = [4.0 * abs((i * step) % 1.0 - 0.5) - 1.0 for i in range(n)]
        inv = 1.0 / n
        return [v * vol * min(1.0, i / a, (n - i) / r) * (1.0 - 0.4 * i * inv) for i, v in enumerate(raw)]

    def _render_measure(self, idx, bpm, hat):
        spb = 60.0 / bpm * self.rate
        buf = [0.0] * int(4 * spb)
        beat = 0.0
        for note, dur in MELODY[idx]:
            if note is not None:
                self._mix(buf, self._note(midi_freq(note), int(dur * spb * 0.92), 0.17, "square", 0.25),
                          int(beat * spb))
            beat += dur
        root = BASS[idx]
        for k in range(8):
            start = int(k * 0.5 * spb)
            self._mix(buf, self._note(midi_freq(root + 12 * (k % 2)), int(0.5 * spb * 0.85), 0.24, "triangle"),
                      start)
            if k % 2:
                self._mix(buf, hat, start)
        return buf[:int(4 * spb)]

    def _build_music(self):
        # отдельный поток, чтобы игра не ждала синтеза музыки при запуске
        try:
            hat = [random.uniform(-1, 1) * 0.05 * math.exp(-i / (0.006 * self.rate))
                   for i in range(int(0.03 * self.rate))]
            for tier, bpm in enumerate(MUSIC_TEMPOS):
                self._ready.append((tier, [self._to_bytes(self._render_measure(i, bpm, hat))
                                           for i in range(len(MELODY))]))
        except Exception:
            pass

    # --- воспроизведение
    def level(self, key):
        """Итоговая громкость 0..1 с учётом выключателя."""
        s = self.store.settings
        return s[key + "_volume"] / VOLUME_STEPS if s[key] else 0.0

    def play(self, name):
        if self.ok and name in self.sfx and self.level("sfx") > 0:
            ch = self.sfx[name].play()
            if ch is not None:
                ch.set_volume(self.level("sfx"))

    def _halt(self):
        # stop() дважды: первый запускает стоящий в очереди такт, второй останавливает его
        self.channel.stop()
        self.channel.stop()
        self.playing = self.paused = False
        self.fading = 0.0

    def restart_music(self):
        if self.ok:
            self._halt()
            self.pos = 0

    def toggle(self, key):
        self.store.settings[key] = not self.store.settings[key]
        self._changed(key)

    def change_volume(self, key, delta):
        s = self.store.settings
        s[key + "_volume"] = max(0, min(VOLUME_STEPS, s[key + "_volume"] + delta))
        if delta > 0:
            s[key] = True
        self._changed(key)
        if key == "sfx":
            self.play("menu")       # сразу слышно новую громкость

    def _changed(self, key):
        self.store.save()
        if key == "music" and self.ok and self.level("music") == 0:
            self._halt()

    def update(self, dt, want, tier, paused):
        if not self.ok:
            return
        while self._ready:
            t, measures = self._ready.pop(0)
            self.music[t] = [self._sound(m, MUSIC_VOLUME) for m in measures]

        ch = self.channel
        if self.fading > 0:
            self.fading -= dt
            if self.fading <= 0:
                self._halt()
            else:
                ch.set_volume(self.level("music") * self.fading / MUSIC_FADE)
            return
        if not (want and self.level("music") > 0):
            if self.playing:
                self.fading = MUSIC_FADE
            return
        if paused:
            if self.playing and not self.paused:
                ch.pause()
                self.paused = True
            return
        if self.paused:
            ch.unpause()
            self.paused = False
        ch.set_volume(self.level("music"))

        while tier > 0 and tier not in self.music:
            tier -= 1
        if tier not in self.music:
            return
        measures = self.music[tier]
        if not ch.get_busy():
            ch.play(measures[MUSIC_ORDER[self.pos]])
            self.pos = (self.pos + 1) % len(MUSIC_ORDER)
            self.playing = True
        elif ch.get_queue() is None:
            # следующий такт ставится в очередь — так темп меняется без обрыва мелодии
            ch.queue(measures[MUSIC_ORDER[self.pos]])
            self.pos = (self.pos + 1) % len(MUSIC_ORDER)


# ---------------------------------------------------------------- логика
class Piece:
    def __init__(self, kind):
        self.kind = kind
        self.rot = 0
        self.x = 4 if kind == "O" else 3
        self.y = 1

    def cells(self, rot=None, x=None, y=None):
        rot = self.rot if rot is None else rot
        x = self.x if x is None else x
        y = self.y if y is None else y
        return [(x + cx, y + cy) for cx, cy in ROTATIONS[self.kind][rot]]


class Game:
    def __init__(self, seed=None, versus=False, next_count=NEXT_COUNT):
        self.versus = versus
        self.next_count = next_count
        self.rng = random.Random(seed)          # одинаковый seed — одинаковые фигуры у обоих игроков
        self.garbage_rng = random.Random()
        self.reset()

    def reset(self):
        self.grid = [[None] * COLS for _ in range(TOTAL_ROWS)]
        self.bag = []
        self.queue = []
        self.fill_queue()
        self.hold = None
        self.can_hold = True
        self.score = 0
        self.lines = 0
        self.level = 1
        self.combo = -1
        self.b2b = 0                # сколько сложных очисток («Тетрис» или T-spin) подряд
        self.last_rotate = False    # последнее успешное действие — поворот (нужно для T-spin)
        self.last_kick = 0          # какой по счёту вариант отскока SRS сработал при повороте
        self.time = 0.0
        self.game_over = False
        self.frozen = False
        self.clearing = []
        self.clear_timer = 0.0
        self.collapse_drop = None
        self.collapse_timer = 0.0
        self.collapse_total = 1.0
        self.fall_timer = 0.0
        self.lock_timer = 0.0
        self.lock_resets = 0
        self.lowest_y = 0
        self.move_dir = 0
        self.held = {-1: False, 1: False}
        self.das_timer = 0.0
        self.arr_timer = 0.0
        self.soft_drop = False
        self.pending = []           # входящий мусор: список пачек линий
        self.outgoing = 0           # линии, которые надо отправить сопернику
        self.sent = 0
        self.particles = []
        self.popups = []
        self.new_popups = []        # для пересылки сопернику по сети
        self.shake = 0.0
        self.sfx = []
        self.photo_events = []      # очистки линий: True — крупная (Тетрис, T-spin, идеальная)
        self.piece = None
        self.spawn()

    # --- очередь фигур (система "мешка": все 7 фигур в случайном порядке)
    def fill_queue(self):
        while len(self.queue) < self.next_count + 1:
            if not self.bag:
                self.bag = list(SHAPES.keys())
                self.rng.shuffle(self.bag)
            self.queue.append(self.bag.pop())

    def spawn(self, kind=None):
        if kind is None:
            kind = self.queue.pop(0)
            self.fill_queue()
        self.piece = Piece(kind)
        self.last_rotate = False
        self.fall_timer = 0.0
        self.lock_timer = 0.0
        self.lock_resets = 0
        self.lowest_y = self.piece.y
        if not self.fits(self.piece.cells()):
            self.end_game()

    def fits(self, cells):
        for x, y in cells:
            if x < 0 or x >= COLS or y >= TOTAL_ROWS:
                return False
            if y >= 0 and self.grid[y][x] is not None:
                return False
        return True

    def on_ground(self):
        p = self.piece
        return not self.fits(p.cells(y=p.y + 1))

    def _moved(self):
        if self.on_ground() and self.lock_resets < MAX_LOCK_RESETS:
            self.lock_timer = 0.0
            self.lock_resets += 1

    def try_move(self, dx, dy):
        p = self.piece
        if p is None or not self.fits(p.cells(x=p.x + dx, y=p.y + dy)):
            return False
        p.x += dx
        p.y += dy
        self.last_rotate = False
        if p.y > self.lowest_y:
            self.lowest_y = p.y
            self.lock_resets = 0
            self.lock_timer = 0.0
        if dx:
            self._moved()
            self.sfx.append("move")
        return True

    def rotate(self, direction):
        p = self.piece
        if p is None or p.kind == "O":
            return
        new_rot = (p.rot + direction) % 4
        table = KICKS_I if p.kind == "I" else KICKS_JLSTZ
        for kick, (kx, ky) in enumerate(table[(p.rot, new_rot)]):
            nx, ny = p.x + kx, p.y - ky
            if self.fits(p.cells(rot=new_rot, x=nx, y=ny)):
                p.rot, p.x, p.y = new_rot, nx, ny
                self.last_rotate = True
                self.last_kick = kick
                if p.y > self.lowest_y:
                    self.lowest_y = p.y
                    self.lock_resets = 0
                self._moved()
                self.sfx.append("rotate")
                return

    def ghost_y(self):
        p = self.piece
        y = p.y
        while self.fits(p.cells(y=y + 1)):
            y += 1
        return y

    def hard_drop(self):
        p = self.piece
        if p is None:
            return
        gy = self.ghost_y()
        self.score += (gy - p.y) * 2
        for x, y in p.cells(y=gy):
            if y >= HIDDEN:
                for _ in range(3):
                    self.add_particle(x, y, COLORS[p.kind], spread=2, up=5.5)
        p.y = gy
        self.shake = 0.12
        self.sfx.append("drop")
        self.lock_piece(sound=False)

    def hold_piece(self):
        if self.piece is None or not self.can_hold:
            return
        current = self.piece.kind
        if self.hold is None:
            self.hold = current
            self.spawn()
        else:
            self.hold, swap = current, self.hold
            self.spawn(swap)
        self.can_hold = False
        self.sfx.append("hold")

    # --- ввод
    def press_dir(self, d):
        self.move_dir = d
        self.das_timer = 0.0
        self.arr_timer = 0.0
        self.try_move(d, 0)

    def release_dir(self, d):
        if self.move_dir != d:
            return
        self.move_dir = -d if self.held[-d] else 0
        self.das_timer = 0.0
        self.arr_timer = 0.0

    def key_down(self, action, active):
        """active=False во время отсчёта: запоминаем зажатые клавиши, но не двигаем фигуру."""
        if action in ("left", "right"):
            d = -1 if action == "left" else 1
            self.held[d] = True
            if active:
                self.press_dir(d)
        elif action == "down":
            self.soft_drop = True
        elif not active:
            return
        elif action == "cw":
            self.rotate(1)
        elif action == "ccw":
            self.rotate(-1)
        elif action == "drop":
            self.hard_drop()
        elif action == "hold":
            self.hold_piece()

    def key_up(self, action):
        if action in ("left", "right"):
            d = -1 if action == "left" else 1
            self.held[d] = False
            self.release_dir(d)
        elif action == "down":
            self.soft_drop = False

    def release_all(self):
        self.held = {-1: False, 1: False}
        self.move_dir = 0
        self.soft_drop = False

    def resume_input(self):
        """После отсчёта зажатая стрелка сразу начинает работать."""
        for d in (-1, 1):
            if self.held[d] and self.move_dir == 0:
                self.move_dir = d
                self.das_timer = self.arr_timer = 0.0

    # --- фиксация, очистка линий, мусор
    def occupied(self, x, y):
        return x < 0 or x >= COLS or y >= TOTAL_ROWS or (y >= 0 and self.grid[y][x] is not None)

    def detect_tspin(self, p):
        """None, "mini" или "full" — по правилу трёх углов из официальных правил тетриса."""
        if p.kind != "T" or not self.last_rotate:
            return None
        filled = [(cx, cy) for cx, cy in T_CORNERS if self.occupied(p.x + cx, p.y + cy)]
        if len(filled) < 3:
            return None
        front = sum(1 for c in T_FRONT[p.rot] if c in filled)
        # оба передних угла заняты — полноценный T-spin; иначе мини,
        # но поворот через последний, пятый отскок (T-spin Triple) всегда считается полным
        return "full" if front == 2 or self.last_kick == 4 else "mini"

    def lock_piece(self, sound=True):
        p = self.piece
        tspin = self.detect_tspin(p)
        cells = p.cells()
        for x, y in cells:
            if y >= 0:
                self.grid[y][x] = p.kind
        self.piece = None
        self.can_hold = True

        if all(y < HIDDEN for _, y in cells):
            self.end_game()
            return

        full = [y for y in range(TOTAL_ROWS) if all(c is not None for c in self.grid[y])]
        if not full:
            self.combo = -1
            if tspin:
                # T-spin без линий даёт очки и не прерывает серию back-to-back
                gained = TSPIN_SCORES[tspin][0] * self.level
                self.score += gained
                self.add_popup("{}{}  +{}".format("МИНИ " if tspin == "mini" else "", TSPIN_NAMES[0], gained),
                               TSPIN_COLOR)
                self.sfx.append("tspin")
                self.tspin_particles(p)
            elif sound:
                self.sfx.append("lock")
            if self.pending:
                self.apply_garbage()
            else:
                self.spawn()
            return

        n = len(full)
        self.combo += 1
        perfect = all(c is None for y in range(TOTAL_ROWS) if y not in full for c in self.grid[y])
        if tspin == "mini" and n >= 3:
            tspin = "full"
        difficult = n == 4 or tspin is not None
        back_to_back = difficult and self.b2b > 0
        self.b2b = self.b2b + 1 if difficult else 0
        gained = (TSPIN_SCORES[tspin][n] if tspin else LINE_SCORES[n]) * self.level
        if back_to_back:
            gained = gained * 3 // 2                # back-to-back: ×1.5
        if self.combo > 0:
            gained += 50 * self.combo * self.level
        if perfect:
            gained += PERFECT_SCORES[n] * self.level
        self.score += gained
        self.lines += n

        if tspin:
            name = ("МИНИ " if tspin == "mini" else "") + TSPIN_NAMES[n]
            self.add_popup("{}  +{}".format(name, gained), TSPIN_COLOR)
            self.tspin_particles(p)
        else:
            self.add_popup("{}  +{}".format(LINE_NAMES[n], gained), ACCENT if n == 4 else TEXT)
        if back_to_back:
            chain = self.b2b - 1
            self.add_popup("BACK-TO-BACK" + (" x{}".format(chain) if chain > 1 else ""), B2B_COLOR)
            self.sfx.append("b2b")
        if self.combo > 0:
            self.add_popup("КОМБО x{}".format(self.combo), (120, 230, 255))
        if perfect:
            self.add_popup("ИДЕАЛЬНАЯ ОЧИСТКА!", (255, 140, 235))
            self.sfx.append("perfect")
            self.shake = 0.25
            for _ in range(80):
                self.add_particle(random.uniform(0, COLS), random.uniform(HIDDEN, TOTAL_ROWS),
                                  random.choice(list(COLORS.values())[:7]), spread=9, up=12)
        elif tspin:
            self.sfx.append("tspin")
        else:
            self.sfx.append("tetris" if n == 4 else "clear{}".format(n))
        new_level = self.lines // 10 + 1
        if new_level > self.level:
            self.level = new_level
            self.add_popup("УРОВЕНЬ {}!".format(self.level), GOOD)
            self.sfx.append("levelup")

        if self.versus:
            attack = TSPIN_ATTACK[tspin][n] if tspin else LINE_ATTACK[n]
            attack += COMBO_ATTACK[min(self.combo, len(COMBO_ATTACK) - 1)]
            if back_to_back:
                attack += B2B_ATTACK
            if perfect:
                attack += PERFECT_ATTACK
            # сначала атака гасит свой входящий мусор, остаток летит сопернику
            while attack and self.pending:
                k = min(attack, self.pending[0])
                self.pending[0] -= k
                attack -= k
                if self.pending[0] == 0:
                    self.pending.pop(0)
            if attack:
                self.outgoing += attack
                self.sent += attack
                self.add_popup("АТАКА +{}".format(attack), (255, 120, 100))

        for y in full:
            for x in range(COLS):
                for _ in range(2):
                    self.add_particle(x, y, COLORS[self.grid[y][x]], spread=8, up=10)
        self.clearing = full
        self.clear_timer = CLEAR_TIME
        self.photo_events.append(n == 4 or tspin is not None or perfect)

    def tspin_particles(self, p):
        cx, cy = p.x + 1, p.y + 1
        for _ in range(40):
            self.add_particle(cx + random.uniform(-1, 1), cy + random.uniform(-1, 1),
                              lighten(TSPIN_COLOR, random.uniform(0, 0.5)), spread=7, up=9)
        self.shake = max(self.shake, 0.14)

    def finish_clear(self):
        cleared = set(self.clearing)
        kept = [i for i in range(TOTAL_ROWS) if i not in cleared]
        n = len(self.clearing)
        self.grid = [[None] * COLS for _ in range(n)] + [self.grid[i] for i in kept]
        # насколько каждая строка опустилась — для плавной анимации
        self.collapse_drop = [0] * n + [j + n - old for j, old in enumerate(kept)]
        self.collapse_total = self.collapse_timer = COLLAPSE_TIME
        self.clearing = []

    def receive_garbage(self, count):
        if count > 0 and not self.game_over:
            self.pending.append(count)

    def apply_garbage(self):
        rows = []
        for count in self.pending:
            hole = self.garbage_rng.randrange(COLS)
            for _ in range(count):
                row = ["G"] * COLS
                row[hole] = None
                rows.append(row)
        self.pending = []
        rows = rows[:TOTAL_ROWS]
        n = len(rows)
        overflow = any(c is not None for row in self.grid[:n] for c in row)
        self.grid = self.grid[n:] + rows
        self.collapse_drop = [-n] * TOTAL_ROWS
        self.collapse_total = self.collapse_timer = RISE_TIME
        self.shake = 0.15
        self.sfx.append("garbage")
        if overflow:
            self.end_game()

    def end_game(self):
        self.game_over = True
        self.piece = None
        self.clearing = []
        self.collapse_drop = None
        self.collapse_timer = 0.0
        self.sfx.append("gameover")

    # --- эффекты (координаты в клетках, чтобы работать при любом размере клетки)
    def add_particle(self, cx, cy, color, spread, up):
        px = cx + random.random()
        py = cy - HIDDEN + random.random()
        vx = random.uniform(-spread, spread)
        vy = random.uniform(-up, up * 0.2)
        life = random.uniform(0.4, 0.9)
        self.particles.append([px, py, vx, vy, life, life, color])

    def add_popup(self, text, color):
        self.popups.append([text, color, 1.2, 1.2])
        self.new_popups.append((text, color))

    # --- сеть: своё поле отправляем, поле соперника показываем по его снимкам
    def to_state(self):
        p = self.piece
        return {"t": "state", "grid": "".join(c or "." for row in self.grid for c in row),
                "piece": [p.kind, p.rot, p.x, p.y] if p else None, "hold": self.hold, "can_hold": self.can_hold,
                "queue": self.queue[:self.next_count], "score": self.score, "lines": self.lines,
                "level": self.level, "sent": self.sent, "pending": sum(self.pending), "b2b": self.b2b,
                "clearing": self.clearing}

    def apply_state(self, st):
        grid = st.get("grid")
        if isinstance(grid, str) and len(grid) == TOTAL_ROWS * COLS and all(ch == "." or ch in COLORS for ch in grid):
            self.grid = [[None if ch == "." else ch for ch in grid[y * COLS:(y + 1) * COLS]] for y in range(TOTAL_ROWS)]
        pc = st.get("piece")
        self.piece = None
        if isinstance(pc, list) and len(pc) == 4 and pc[0] in SHAPES:
            piece = Piece(pc[0])
            piece.rot = int(pc[1]) % 4
            piece.x = max(-3, min(COLS, int(pc[2])))
            piece.y = max(-3, min(TOTAL_ROWS, int(pc[3])))
            self.piece = piece
        self.hold = st.get("hold") if st.get("hold") in SHAPES else None
        self.can_hold = bool(st.get("can_hold", True))
        queue = [k for k in st.get("queue") or [] if k in SHAPES]
        if queue:
            self.queue = queue[:self.next_count]
        self.score = max(0, int(st.get("score", 0)))
        self.lines = max(0, int(st.get("lines", 0)))
        self.level = max(1, int(st.get("level", 1)))
        self.sent = max(0, int(st.get("sent", 0)))
        self.b2b = max(0, int(st.get("b2b", 0)))
        pending = max(0, int(st.get("pending", 0)))
        self.pending = [pending] if pending else []
        self.clearing = [y for y in st.get("clearing") or [] if isinstance(y, int) and 0 <= y < TOTAL_ROWS]
        self.clear_timer = CLEAR_TIME * 0.4 if self.clearing else 0.0

    def update_effects(self, dt):
        for p in self.particles:
            p[0] += p[2] * dt
            p[1] += p[3] * dt
            p[3] += 28 * dt
            p[4] -= dt
        self.particles = [p for p in self.particles if p[4] > 0]
        for pop in self.popups:
            pop[2] -= dt
        self.popups = [pop for pop in self.popups if pop[2] > 0]
        self.shake = max(0.0, self.shake - dt)

    # --- главный шаг
    def update(self, dt):
        if self.game_over or self.frozen:
            return
        self.time += dt

        if self.clearing:
            self.clear_timer -= dt
            if self.clear_timer <= 0:
                self.finish_clear()
            return

        if self.collapse_timer > 0:
            self.collapse_timer -= dt
            if self.collapse_timer <= 0:
                self.collapse_timer = 0.0
                self.collapse_drop = None
                self.spawn()
            return

        if self.piece is None:
            return

        if self.move_dir:
            self.das_timer += dt
            if self.das_timer >= DAS:
                self.arr_timer += dt
                while self.arr_timer >= ARR:
                    self.arr_timer -= ARR
                    if not self.try_move(self.move_dir, 0):
                        self.arr_timer = 0.0
                        break

        interval = gravity_interval(self.level)
        if self.soft_drop:
            interval = min(interval, SOFT_DROP_INTERVAL)
            # не даём накопленному таймеру гравитации сбросить фигуру на несколько клеток разом
            self.fall_timer = min(self.fall_timer, interval)
        self.fall_timer += dt
        while self.fall_timer >= interval:
            self.fall_timer -= interval
            if self.try_move(0, 1):
                if self.soft_drop:
                    self.score += 1
            else:
                self.fall_timer = 0.0
                break

        if self.on_ground():
            self.lock_timer += dt
            if self.lock_timer >= LOCK_DELAY:
                self.lock_piece()


# ---------------------------------------------------------------- управление
def key(code, scan=None):
    """Клавиша: код + физическое положение (чтобы буквы работали в русской раскладке)."""
    return code, getattr(pygame, scan, None) if scan else None


def matches(event, keys):
    sc = getattr(event, "scancode", None)
    return any(event.key == code or (scan is not None and sc == scan) for code, scan in keys)


def find_action(event, controls):
    for action, keys in controls.items():
        if matches(event, keys):
            return action
    return None


CONTROLS_SINGLE = {
    "left": [key(pygame.K_LEFT)],
    "right": [key(pygame.K_RIGHT)],
    "down": [key(pygame.K_DOWN)],
    "cw": [key(pygame.K_UP), key(pygame.K_x, "KSCAN_X")],
    "ccw": [key(pygame.K_LCTRL), key(pygame.K_RCTRL), key(pygame.K_z, "KSCAN_Z")],
    "drop": [key(pygame.K_SPACE)],
    "hold": [key(pygame.K_LSHIFT), key(pygame.K_RSHIFT), key(pygame.K_c, "KSCAN_C")],
}
CONTROLS_P1 = {
    "left": [key(pygame.K_a, "KSCAN_A")],
    "right": [key(pygame.K_d, "KSCAN_D")],
    "down": [key(pygame.K_s, "KSCAN_S")],
    "cw": [key(pygame.K_w, "KSCAN_W")],
    "ccw": [key(pygame.K_q, "KSCAN_Q")],
    "drop": [key(pygame.K_SPACE)],
    "hold": [key(pygame.K_e, "KSCAN_E")],
}
CONTROLS_P2 = {
    "left": [key(pygame.K_LEFT)],
    "right": [key(pygame.K_RIGHT)],
    "down": [key(pygame.K_DOWN)],
    "cw": [key(pygame.K_UP)],
    "ccw": [key(pygame.K_RCTRL), key(pygame.K_SLASH, "KSCAN_SLASH")],
    "drop": [key(pygame.K_RETURN), key(pygame.K_KP_ENTER)],
    "hold": [key(pygame.K_RSHIFT), key(pygame.K_PERIOD, "KSCAN_PERIOD")],
}
KEYS_PAUSE = [key(pygame.K_ESCAPE), key(pygame.K_p, "KSCAN_P")]
KEYS_MUSIC = [key(pygame.K_m, "KSCAN_M")]
KEYS_SFX = [key(pygame.K_n, "KSCAN_N")]
KEYS_OK = [key(pygame.K_RETURN), key(pygame.K_KP_ENTER)]
KEYS_RESTART = [key(pygame.K_r, "KSCAN_R")]
KEYS_QUIT_TO_MENU = [key(pygame.K_q, "KSCAN_Q")]
KEYS_UP = [key(pygame.K_UP), key(pygame.K_w, "KSCAN_W")]
KEYS_DOWN = [key(pygame.K_DOWN), key(pygame.K_s, "KSCAN_S")]
KEYS_LEFT = [key(pygame.K_LEFT), key(pygame.K_a, "KSCAN_A")]
KEYS_RIGHT = [key(pygame.K_RIGHT), key(pygame.K_d, "KSCAN_D")]

HELP_SINGLE = [
    ("← →", "движение"),
    ("↓", "ускорить"),
    ("↑  /  X", "поворот"),
    ("Z  /  Ctrl", "поворот назад"),
    ("Пробел", "сбросить вниз"),
    ("C  /  Shift", "в запас"),
    ("P  /  Esc", "пауза"),
]
HELP_P1 = [("A   D", "движение"), ("S", "ускорить"), ("W", "поворот"), ("Q", "поворот назад"),
           ("Пробел", "сбросить"), ("E", "в запас")]
HELP_ONLINE = [("← →", "движение"), ("↓", "ускорить"), ("↑  /  X", "поворот"), ("Z  /  Ctrl", "поворот назад"),
               ("Пробел", "сбросить"), ("C  /  Shift", "в запас")]
HELP_P2 = [("← →", "движение"), ("↓", "ускорить"), ("↑", "поворот"), ("Пр.Ctrl  или  /", "поворот назад"),
           ("Enter", "сбросить"), ("Пр.Shift  или  .", "в запас")]

View = namedtuple("View", "cell bx by left_x right_x side_w")
SINGLE_VIEW = View(CELL, BOARD_X, BOARD_Y, MARGIN, RIGHT_X, SIDE_W)
VS_VIEWS = []
for _i in range(2):
    _left = MARGIN + _i * (VS_PLAYER_W + VS_GAP)
    _bx = _left + VS_SIDE_W + 20
    VS_VIEWS.append(View(VS_CELL, _bx, VS_TOP, _left, _bx + COLS * VS_CELL + 12, VS_SIDE_W))


def board_rect(view):
    return pygame.Rect(view.bx, view.by, COLS * view.cell, ROWS * view.cell)


# ---------------------------------------------------------------- графика
def lighten(c, f):
    return tuple(min(255, int(v + (255 - v) * f)) for v in c)


def darken(c, f):
    return tuple(max(0, int(v * (1 - f))) for v in c)


def lerp_color(a, b, t):
    return tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))


def draw_block(surf, x, y, size, color):
    b = max(2, size // 7)
    light, dark = lighten(color, 0.5), darken(color, 0.45)
    s1 = size - 1
    pygame.draw.rect(surf, dark, (x, y, size, size))
    pygame.draw.polygon(surf, light, [(x, y), (x + s1, y), (x + s1 - b, y + b),
                                      (x + b, y + b), (x + b, y + s1 - b), (x, y + s1)])
    pygame.draw.rect(surf, color, (x + b, y + b, size - 2 * b, size - 2 * b))
    pygame.draw.rect(surf, lighten(color, 0.75), (x + b + 1, y + b + 1, b, b))


def draw_ghost(surf, x, y, size, color):
    s = pygame.Surface((size, size), pygame.SRCALPHA)
    s.fill((color[0], color[1], color[2], 40))
    pygame.draw.rect(s, (color[0], color[1], color[2], 190), (1, 1, size - 2, size - 2), 2, border_radius=4)
    surf.blit(s, (x, y))


def draw_mini(surf, kind, cx, cy, size, color=None, rot=0):
    cells = ROTATIONS[kind][rot]
    xs = [c[0] for c in cells]
    ys = [c[1] for c in cells]
    w = (max(xs) - min(xs) + 1) * size
    h = (max(ys) - min(ys) + 1) * size
    ox = cx - w / 2 - min(xs) * size
    oy = cy - h / 2 - min(ys) * size
    for x, y in cells:
        draw_block(surf, int(ox + x * size), int(oy + y * size), size, color or COLORS[kind])


def make_cursor(block, frame, hover):
    """Один кадр курсора. hover — золотая стрелка с бегущим бликом (над пунктом меню)."""
    cells = [(x, y) for y, row in enumerate(CURSOR_SHAPE) for x, c in enumerate(row) if c == "X"]
    w, h = len(CURSOR_SHAPE[0]) * block + 2, len(CURSOR_SHAPE) * block + 2
    surf = pygame.Surface((w, h), pygame.SRCALPHA)
    for x, y in cells:                                   # тёмная обводка, чтобы курсор был виден на любом фоне
        pygame.draw.rect(surf, (8, 6, 20), (x * block, y * block, block + 2, block + 2))
    rainbow = [COLORS[k] for k in "ZLOSIJT"]
    for x, y in cells:
        wave = (x + y - frame) % CURSOR_FRAMES
        color = lighten(ACCENT, 0.6 * (1 - wave / (CURSOR_FRAMES - 1))) if hover else rainbow[wave]
        draw_block(surf, x * block + 1, y * block + 1, block, color)
    return pygame.cursors.Cursor((1, 1), surf)


def make_font(size, bold=True):
    return pygame.font.SysFont("segoeui,arial,dejavusans", size, bold=bold)


def fit(img, max_w):
    if max_w and img.get_width() > max_w:
        h = max(1, int(img.get_height() * max_w / img.get_width()))
        img = pygame.transform.smoothscale(img, (max_w, h))
    return img


class Renderer:
    def __init__(self):
        self.screen = None
        self.f_small = make_font(15, bold=False)
        self.f_label = make_font(15)
        self.f_key = make_font(18)
        self.f_med = make_font(22)
        self.f_big = make_font(30)
        self.f_huge = make_font(42)
        self.f_title = make_font(78)
        self.f_count = make_font(110)
        self.bg_top = list(BG_PALETTES[0][0])
        self.bg_bottom = list(BG_PALETTES[0][1])
        self.bg_key = None
        self.background = None
        self.stars = []
        self.boards = {}

    def set_target(self, canvas, content_rect):
        """canvas — весь кадр (фон до краёв экрана), screen — область раскладки по центру."""
        self.canvas = canvas
        self.screen = canvas.subsurface(content_rect)
        self.bg_key = None
        w, h = canvas.get_size()
        rnd = random.Random(7)
        self.stars = [(rnd.randrange(w), rnd.randrange(h), rnd.randint(60, 140)) for _ in range(w * h // 5900)]

    # --- фон, плавно меняющий цвет с уровнем
    def draw_background(self, level, dt):
        top, bottom = BG_PALETTES[(level - 1) % len(BG_PALETTES)]
        k = min(1.0, dt * 2.0)
        for cur, target in ((self.bg_top, top), (self.bg_bottom, bottom)):
            for i in range(3):
                cur[i] += (target[i] - cur[i]) * k
        w, h = self.canvas.get_size()
        key_ = (w, h) + tuple(int(round(v)) for v in self.bg_top + self.bg_bottom)
        if key_ != self.bg_key:
            self.bg_key = key_
            top_c, bottom_c = key_[2:5], key_[5:8]
            column = pygame.Surface((1, h))
            for y in range(h):
                column.set_at((0, y), lerp_color(top_c, bottom_c, y / max(1, h - 1)))
            bg = pygame.transform.scale(column, (w, h))
            for x, y, v in self.stars:
                bg.set_at((x, y), (v, v, v + 40))
            self.background = bg
        self.canvas.blit(self.background, (0, 0))

    def text(self, font, s, color, pos, anchor="topleft", max_w=None, alpha=None):
        img = fit(font.render(s, True, color), max_w)
        if alpha is not None:
            img.set_alpha(alpha)
        rect = img.get_rect(**{anchor: pos})
        self.screen.blit(img, rect)
        return rect

    def panel(self, rect, title=None, border=PANEL_BORDER):
        pygame.draw.rect(self.screen, PANEL, rect, border_radius=10)
        pygame.draw.rect(self.screen, border, rect, 2, border_radius=10)
        if title:
            self.text(self.f_label, title, TEXT_DIM, (rect.x + 12, rect.y + 9), max_w=rect.w - 20)

    def title(self, cx, y, font):
        colors = [COLORS[k] for k in "ZLOSIT"]
        imgs = [font.render(ch, True, colors[i]) for i, ch in enumerate("ТЕТРИС")]
        total = sum(i.get_width() for i in imgs) + 2 * (len(imgs) - 1)
        x = cx - total // 2
        for img in imgs:
            self.screen.blit(img, (x, y))
            x += img.get_width() + 2

    def help_list(self, rect, items, step=44):
        y = rect.y + 34
        for k, action in items:
            self.text(self.f_key, k, TEXT, (rect.x + 12, y), max_w=rect.w - 24)
            self.text(self.f_small, action, TEXT_DIM, (rect.x + 12, y + 22), max_w=rect.w - 24)
            y += step

    # --- одиночная игра
    def draw_single_side(self, game, best, settings):
        x = MARGIN
        self.title(x + SIDE_W // 2, MARGIN - 4, self.f_huge)

        hold_rect = pygame.Rect(x, MARGIN + 66, SIDE_W, 120)
        self.panel(hold_rect, "ЗАПАС")
        if game.hold:
            color = None if game.can_hold else (95, 95, 115)
            draw_mini(self.screen, game.hold, hold_rect.centerx, hold_rect.y + 70, 26, color)

        ctrl_rect = pygame.Rect(x, MARGIN + 202, SIDE_W, HEIGHT - MARGIN - (MARGIN + 202))
        self.panel(ctrl_rect, "УПРАВЛЕНИЕ")
        self.help_list(ctrl_rect, HELP_SINGLE + [("M", "музыка: " + volume_text(settings, "music")),
                                                 ("N", "звуки: " + volume_text(settings, "sfx"))])

        x = RIGHT_X
        next_rect = pygame.Rect(x, MARGIN, SIDE_W, 370)
        self.panel(next_rect, "СЛЕДУЮЩИЕ")
        queue = game.queue[:game.next_count]
        if queue:
            draw_mini(self.screen, queue[0], next_rect.centerx, next_rect.y + 78, 28)
        for i, kind in enumerate(queue[1:]):
            draw_mini(self.screen, kind, next_rect.centerx, next_rect.y + 150 + i * 56, 20)

        stats = [
            ("СЧЁТ", format_score(game.score)),
            ("ЛИНИИ", str(game.lines)),
            ("УРОВЕНЬ", str(game.level)),
            ("РЕКОРД", format_score(max(best, game.score))),
        ]
        y = next_rect.bottom + 14
        for label, value in stats:
            r = pygame.Rect(x, y, SIDE_W, 56)
            self.panel(r)
            self.text(self.f_label, label, TEXT_DIM, (r.x + 14, r.centery), "midleft")
            self.text(self.f_big, value, ACCENT if label == "РЕКОРД" else TEXT, (r.right - 14, r.centery),
                      "midright", max_w=r.w - 90)
            y += 64

    # --- игра вдвоём
    def draw_versus_side(self, game, view, help_items, help_title="КЛАВИШИ"):
        w = view.side_w
        x = view.left_x
        hold_rect = pygame.Rect(x, view.by, w, 96)
        self.panel(hold_rect, "ЗАПАС")
        if game.hold:
            c = None if game.can_hold else (95, 95, 115)
            draw_mini(self.screen, game.hold, hold_rect.centerx, hold_rect.y + 58, 20, c)
        y = hold_rect.bottom + 10
        for label, value in (("СЧЁТ", format_score(game.score)), ("ЛИНИИ", str(game.lines)),
                             ("УРОВЕНЬ", str(game.level))):
            self.stat_box(pygame.Rect(x, y, w, 56), label, value)
            y += 64
        ctrl_rect = pygame.Rect(x, y, w, view.by + ROWS * view.cell - y)
        self.panel(ctrl_rect, help_title)
        self.help_list(ctrl_rect, help_items, step=42)

        x = view.right_x
        next_rect = pygame.Rect(x, view.by, w, 230)
        self.panel(next_rect, "СЛЕДУЮЩИЕ")
        queue = game.queue[:game.next_count]
        if queue:
            draw_mini(self.screen, queue[0], next_rect.centerx, next_rect.y + 70, 22)
        for i, kind in enumerate(queue[1:]):
            draw_mini(self.screen, kind, next_rect.centerx, next_rect.y + 135 + i * 48, 17)
        y = next_rect.bottom + 10
        self.stat_box(pygame.Rect(x, y, w, 56), "АТАКА", str(game.sent), (255, 140, 110))
        y += 64
        self.stat_box(pygame.Rect(x, y, w, 56), "ВХОДЯЩИЕ", str(sum(game.pending)),
                      BAD if game.pending else TEXT)

        # шкала входящего мусора слева от поля
        bh = ROWS * view.cell
        mx = view.bx - 17
        pygame.draw.rect(self.screen, PANEL, (mx, view.by, 8, bh), border_radius=3)
        n = min(sum(game.pending), ROWS)
        if n:
            pulse = 0.5 + 0.5 * math.sin(time.time() * 10) if n >= 6 else 0.0
            c = lerp_color((230, 60, 70), (255, 200, 200), pulse)
            pygame.draw.rect(self.screen, c, (mx, view.by + bh - n * view.cell, 8, n * view.cell), border_radius=3)

    def stat_box(self, r, label, value, color=TEXT):
        self.panel(r)
        self.text(self.f_label, label, TEXT_DIM, (r.x + 12, r.y + 6), max_w=r.w - 20)
        self.text(self.f_med, value, color, (r.right - 12, r.bottom - 6), "bottomright", max_w=r.w - 20)

    def draw_versus_header(self, wins, names=None):
        for i, view in enumerate(VS_VIEWS):
            cx = view.bx + COLS * view.cell // 2
            name = names[i] if names else "ИГРОК {}".format(i + 1)
            self.text(self.f_med, name, PLAYER_COLORS[i], (cx, MARGIN + 14), "center", max_w=COLS * view.cell)
        self.text(self.f_big, "{}  :  {}".format(*wins), ACCENT, (VS_WIDTH // 2, MARGIN + 14), "center")

    # --- поле
    def draw_board(self, game, view, frame=PANEL_BORDER):
        cell = view.cell
        bw, bh = COLS * cell, ROWS * cell
        b = self.boards.get((bw, bh))
        if b is None:
            b = self.boards[(bw, bh)] = pygame.Surface((bw, bh))
        b.fill(BOARD_BG)
        for cx in range(1, COLS):
            pygame.draw.line(b, GRID, (cx * cell, 0), (cx * cell, bh))
        for cy in range(1, ROWS):
            pygame.draw.line(b, GRID, (0, cy * cell), (bw, cy * cell))

        drop = game.collapse_drop
        ease = 0.0
        if drop:
            t = 1 - max(0.0, game.collapse_timer) / game.collapse_total
            ease = t * t                # ускорение, как при падении
        for y in range(TOTAL_ROWS):
            offset = drop[y] * (1 - ease) if drop else 0
            py = int((y - HIDDEN - offset) * cell)
            if py <= -cell or py >= bh:
                continue
            for x in range(COLS):
                kind = game.grid[y][x]
                if kind:
                    draw_block(b, x * cell, py, cell, COLORS[kind])

        if game.clearing:
            alpha = int(255 * (1 - max(0.0, game.clear_timer) / CLEAR_TIME))
            flash = pygame.Surface((bw, cell), pygame.SRCALPHA)
            flash.fill((255, 255, 255, alpha))
            for y in game.clearing:
                if y >= HIDDEN:
                    b.blit(flash, (0, (y - HIDDEN) * cell))

        p = game.piece
        if p and not game.game_over:
            gy = game.ghost_y()
            if gy != p.y:
                for x, y in p.cells(y=gy):
                    if y >= HIDDEN:
                        draw_ghost(b, x * cell, (y - HIDDEN) * cell, cell, COLORS[p.kind])
            for x, y in p.cells():
                if y >= HIDDEN:
                    draw_block(b, x * cell, (y - HIDDEN) * cell, cell, COLORS[p.kind])

        scale = cell / CELL
        for px, py, _, _, life, max_life, color in game.particles:
            size = max(1, int(6 * scale * life / max_life))
            pygame.draw.rect(b, lighten(color, 0.3), (int(px * cell), int(py * cell), size, size))

        for i, (text, color, life, max_life) in enumerate(game.popups):
            img = fit(self.f_big.render(text, True, color), bw - 16)
            img.set_alpha(int(255 * min(1.0, life / max_life * 2)))
            rise = (1 - life / max_life) * 50
            rect = img.get_rect(center=(bw // 2, int(bh * 0.4 + i * 40 - rise)))
            b.blit(img, rect)

        if game.b2b > 0 and not game.game_over:
            img = self.f_label.render("B2B", True, B2B_COLOR)      # серия активна: следующая сложная очистка ×1.5
            img.set_alpha(170 + int(60 * math.sin(time.time() * 4)))
            b.blit(img, (8, 6))

        offset_y = int(7 * game.shake / 0.12) if game.shake > 0 else 0
        pygame.draw.rect(self.screen, frame, (view.bx - 4, view.by - 4, bw + 8, bh + 8), 3, border_radius=6)
        self.screen.blit(b, (view.bx, view.by + offset_y))

    # --- надписи поверх поля
    def shade(self, rect, alpha):
        s = pygame.Surface(rect.size, pygame.SRCALPHA)
        s.fill((5, 5, 15, alpha))
        self.screen.blit(s, rect.topleft)

    def overlay(self, rect, lines, alpha=190):
        self.shade(rect, alpha)
        heights = [f.get_linesize() + 6 for _, f, _ in lines]
        y = rect.y + (rect.h - sum(heights)) // 2
        for (s, font, color), h in zip(lines, heights):
            if s:
                self.text(font, s, color, (rect.centerx, y + h // 2), "center", max_w=rect.w - 16)
            y += h

    def countdown(self, rect, value):
        self.shade(rect, 110)
        n = max(1, math.ceil(value))
        frac = value - (n - 1)          # от 1 к 0 внутри каждой секунды
        img = self.f_count.render(str(n), True, ACCENT)
        img = pygame.transform.rotozoom(img, 0, 1.0 + 0.5 * frac * frac)
        img.set_alpha(int(255 * min(1.0, frac * 3)))
        self.screen.blit(img, img.get_rect(center=rect.center))

    def go_flash(self, rect, t):
        self.text(self.f_huge, "СТАРТ!", GOOD, rect.center, "center", alpha=int(255 * min(1.0, t * 2)))

    def name_entry(self, rect, score, rank, name, blink):
        self.shade(rect, 200)
        cx = rect.centerx
        y = rect.y + 150
        self.text(self.f_big, "НОВЫЙ РЕКОРД!" if rank == 0 else "ТОП-10!", ACCENT, (cx, y), "center",
                  max_w=rect.w - 16)
        self.text(self.f_med, "Счёт: {}".format(format_score(score)), TEXT, (cx, y + 46), "center")
        self.text(self.f_med, "Место: {}".format(rank + 1), TEXT, (cx, y + 78), "center")
        self.text(self.f_med, "Введите имя:", TEXT_DIM, (cx, y + 140), "center")
        box = pygame.Rect(0, 0, rect.w - 50, 46)
        box.center = (cx, y + 190)
        pygame.draw.rect(self.screen, PANEL, box, border_radius=8)
        pygame.draw.rect(self.screen, ACCENT, box, 2, border_radius=8)
        r = self.text(self.f_med, name, TEXT, (box.x + 12, box.centery), "midleft", max_w=box.w - 30)
        if int(blink * 2) % 2 == 0:
            cursor_x = r.right + 2 if name else box.x + 12
            pygame.draw.line(self.screen, TEXT, (cursor_x, box.y + 10), (cursor_x, box.bottom - 10), 2)
        self.text(self.f_small, "Enter — сохранить", TEXT_DIM, (cx, y + 250), "center")
        self.text(self.f_small, "Esc — не сохранять", TEXT_DIM, (cx, y + 274), "center")

    # --- меню и рекорды
    def draw_decor(self, decor):
        for d in decor:
            draw_mini(self.canvas, d["kind"], int(d["x"]), int(d["y"]), d["size"],
                      darken(COLORS[d["kind"]], 0.6), d["rot"])

    def draw_menu(self, items, index, best, settings, title=None, subtitle=None, notes=(), top=MENU_TOP):
        w, h = self.screen.get_size()
        if title:
            self.text(self.f_huge, title, ACCENT, (w // 2, 110), "center", max_w=w - 40)
            self.text(self.f_small, subtitle or "", TEXT_DIM, (w // 2, 152), "center", max_w=w - 40)
        else:
            self.title(w // 2, 80, self.f_title)
            self.text(self.f_small, "классическая головоломка", TEXT_DIM, (w // 2, 190), "center")
        for i, (_, label) in enumerate(items):
            rect = menu_item_rect(i, w, top)
            y = rect.centery
            if i == index:
                pulse = 0.5 + 0.5 * math.sin(time.time() * 5)
                self.panel(rect, border=lerp_color(ACCENT, PANEL_BORDER, pulse * 0.6))
                for sx in (-1, 1):
                    tx = rect.centerx + sx * (rect.w // 2 - 22)
                    pygame.draw.polygon(self.screen, ACCENT,
                                        [(tx - 6 * sx, y - 8), (tx - 6 * sx, y + 8), (tx + 4 * sx, y)])
            self.text(self.f_med, label, ACCENT if i == index else TEXT, rect.center, "center")
        y = top + len(items) * MENU_STEP + 4
        for line in notes:
            self.text(self.f_small, line, TEXT_DIM, (w // 2, y), "center", max_w=w - 60)
            y += 23
        if title:
            self.text(self.f_small, "Мышь или ↑ ↓ — выбор    Enter — выбрать    Esc — назад",
                      TEXT_DIM, (w // 2, h - 34), "center", max_w=w - 40)
            return
        if best:
            self.text(self.f_label, "Рекорд: {} — {}".format(format_score(best["score"]), best["name"]),
                      ACCENT, (w // 2, h - 66), "center")
        self.text(self.f_small, "Мышь или ↑ ↓ — выбор    Enter — выбрать    ← → — громкость    "
                                "F11 — экран    Esc — выход",
                  TEXT_DIM, (w // 2, h - 34), "center", max_w=w - 40)

    # --- экраны игры по сети
    def draw_host(self, addresses, port, t):
        w, h = self.screen.get_size()
        self.text(self.f_huge, "ОЖИДАНИЕ СОПЕРНИКА", ACCENT, (w // 2, 70), "center", max_w=w - 40)
        dots = "." * (int(t * 2) % 4)
        r = self.text(self.f_med, "Ждём подключения", TEXT_DIM, (w // 2, 118), "center")
        self.text(self.f_med, dots, TEXT_DIM, (r.right + 2, r.y))
        shown = addresses[:5]
        rect = pygame.Rect(60, 160, w - 120, 64 + 46 * max(1, len(shown)))
        self.panel(rect, "СООБЩИТЕ ДРУГУ ВАШ АДРЕС")
        if not shown:
            self.text(self.f_med, "Не удалось определить адрес компьютера", BAD, (rect.centerx, rect.y + 60), "center")
        for i, (ip, label) in enumerate(shown):
            y = rect.y + 58 + i * 46
            self.text(self.f_big, ip, ACCENT if i == 0 else TEXT, (rect.x + 24, y), "midleft")
            self.text(self.f_small, label, TEXT_DIM, (rect.right - 20, y), "midright")
        y = rect.bottom + 22
        self.text(self.f_label, "Порт: {}".format(port), TEXT_DIM, (w // 2, y), "center")
        notes = ["Друг выбирает «Игра по сети → Подключиться» и вводит адрес.",
                 "Если Windows спросит про доступ к сети — нажмите «Разрешить доступ».",
                 "Через интернет: оба в одной сети Radmin VPN, ZeroTier или Tailscale —",
                 "тогда давайте другу адрес этой сети (он показан выше)."]
        y += 40
        for line in notes:
            self.text(self.f_small, line, TEXT_DIM, (w // 2, y), "center", max_w=w - 60)
            y += 23
        self.text(self.f_small, "Esc — отмена", TEXT_DIM, (w // 2, h - 34), "center")

    def draw_join(self, address, status, status_color, blink, busy):
        w, h = self.screen.get_size()
        self.text(self.f_huge, "ПОДКЛЮЧЕНИЕ", ACCENT, (w // 2, 90), "center")
        self.text(self.f_med, "Адрес соперника:", TEXT_DIM, (w // 2, 200), "center")
        box = pygame.Rect(0, 0, 460, 54)
        box.center = (w // 2, 252)
        pygame.draw.rect(self.screen, PANEL, box, border_radius=8)
        pygame.draw.rect(self.screen, ACCENT if not busy else PANEL_BORDER, box, 2, border_radius=8)
        r = self.text(self.f_big, address, TEXT, (box.x + 14, box.centery), "midleft", max_w=box.w - 30)
        if not busy and int(blink * 2) % 2 == 0:
            cx = r.right + 2 if address else box.x + 14
            pygame.draw.line(self.screen, TEXT, (cx, box.y + 12), (cx, box.bottom - 12), 2)
        if status:
            text = status + ("." * (int(blink * 2) % 4) if busy else "")
            self.text(self.f_med, text, status_color, (w // 2, 318), "center", max_w=w - 40)
        notes = ["Адрес показан на экране друга «Ожидание соперника».",
                 "Порт можно указать через двоеточие, например 26.10.20.30:47474."]
        y = 380
        for line in notes:
            self.text(self.f_small, line, TEXT_DIM, (w // 2, y), "center", max_w=w - 60)
            y += 23
        self.text(self.f_small, "Enter — подключиться     Ctrl+V — вставить     Esc — назад",
                  TEXT_DIM, (w // 2, h - 34), "center", max_w=w - 40)

    def draw_message(self, title, lines):
        w, h = self.screen.get_size()
        self.text(self.f_huge, title, BAD, (w // 2, 230), "center", max_w=w - 40)
        y = 300
        for line in lines:
            self.text(self.f_med, line, TEXT, (w // 2, y), "center", max_w=w - 60)
            y += 34
        self.text(self.f_small, "Enter — в меню", TEXT_DIM, (w // 2, h - 34), "center")

    def draw_records(self, table, highlight, from_game):
        w, h = self.screen.get_size()
        self.text(self.f_huge, "РЕКОРДЫ", ACCENT, (w // 2, 58), "center")
        self.text(self.f_small, "Марафон · один игрок", TEXT_DIM, (w // 2, 98), "center")
        rect = pygame.Rect(40, 126, w - 80, 480)
        self.panel(rect)
        cols = [("№", rect.x + 20, "midleft"), ("Имя", rect.x + 62, "midleft"),
                ("Счёт", rect.x + 360, "midright"), ("Линии", rect.x + 446, "midright"),
                ("Ур.", rect.x + 502, "midright"), ("Время", rect.x + 586, "midright"),
                ("Дата", rect.right - 18, "midright")]
        y = rect.y + 26
        for label, x, anchor in cols:
            self.text(self.f_label, label, TEXT_DIM, (x, y), anchor)
        pygame.draw.line(self.screen, PANEL_BORDER, (rect.x + 12, y + 18), (rect.right - 12, y + 18))
        if not table:
            self.text(self.f_med, "Пока пусто — сыграйте первую игру!", TEXT_DIM, rect.center, "center")
        y = rect.y + 70
        for i, row in enumerate(table):
            if i == highlight:
                hl = pygame.Rect(rect.x + 8, y - 18, rect.w - 16, 36)
                pulse = 0.5 + 0.5 * math.sin(time.time() * 4)
                pygame.draw.rect(self.screen, lerp_color((70, 60, 30), (110, 95, 40), pulse), hl, border_radius=6)
            color = ACCENT if i == 0 else TEXT
            values = [str(i + 1), row.get("name", ""), format_score(row["score"]),
                      "—" if row.get("lines") is None else str(row["lines"]),
                      "—" if row.get("level") is None else str(row["level"]),
                      format_time(row.get("time")), row.get("date") or "—"]
            for col, ((_, x, anchor), value) in enumerate(zip(cols, values)):
                font = self.f_med if col <= 2 else self.f_label     # №, имя и счёт крупнее
                self.text(font, value, color, (x, y), anchor, max_w=190 if col == 1 else None)
            y += 40
        hint = "Enter — играть снова     Esc — в меню" if from_game else "Enter / Esc — назад"
        self.text(self.f_small, hint, TEXT_DIM, (w // 2, h - 40), "center")


# ---------------------------------------------------------------- приложение
class App:
    def __init__(self):
        os.environ.setdefault("SDL_VIDEO_CENTERED", "1")
        self.dpi_scale = enable_dpi_awareness()
        pygame.mixer.pre_init(22050, -16, 1, 512)
        pygame.init()
        pygame.display.set_caption(WINDOW_TITLE)
        pygame.display.set_icon(make_icon(64))
        pygame.key.stop_text_input()
        self.clock = pygame.time.Clock()
        self.store = Storage()
        self.sound = SoundManager(self.store)
        self.renderer = Renderer()
        self.size = None            # размер раскладки текущего экрана (одиночная / вдвоём)
        self.display = None
        self.display_full = False
        self.canvas = None
        self.offset = (0, 0)
        self.cursor = None
        self.trail = []             # блоки, которые сыплются за курсором в меню
        self.trail_last = None
        block = max(4, round(5 * self.dpi_scale))
        try:
            self.cursor_frames = {hover: [make_cursor(block, f, hover) for f in range(CURSOR_FRAMES)]
                                  for hover in (False, True)}
        except (AttributeError, TypeError, pygame.error):
            self.cursor_frames = None   # старый pygame — обычный системный курсор
        self.set_size(WIDTH, HEIGHT)

        self.state = "menu"         # menu, records, play, name
        self.menu_index = 0
        self.pause_index = 0        # что регулируем на паузе: 0 — музыка, 1 — звуки
        self.mode = None            # single, versus
        self.games = []
        self.paused = False
        self.countdown = 0.0
        self.go_timer = 0.0
        self.finish_timer = 0.0
        self.wins = [0, 0]
        self.result = None          # в игре вдвоём: 0 / 1 — победитель, "draw" — ничья
        self.over_handled = False
        self.record_rank = None
        self.records_from_game = False
        self.name = ""
        self.name_rank = None
        self.name_delay = 0.0
        self.blink = 0.0
        self.menu_time = 0.0
        self.decor = [self.new_decor(random.uniform(-80, self.canvas.get_height())) for _ in range(22)]

        self.photos = PhotoLibrary(PHOTO_DIRS)
        self.photo_shows = {}       # место (номер игрока) → показываемое фото

        # игра по сети
        self.conn = None            # соединение с соперником
        self.listener = None        # ждём подключения (создали игру)
        self.connector = None       # подключаемся к сопернику
        self.is_host = False
        self.host_addresses = []
        self.address = self.store.settings["address"]
        self.net_status = ""
        self.net_status_color = TEXT_DIM
        self.net_message = ("", [])
        self.opp_name = ""
        self.ping_ms = None
        self.ping_timer = 0.0
        self.send_timer = 0.0
        self.local_over = self.remote_over = False
        self.over_grace = 0.0
        self.ready_local = self.ready_remote = False

    # --- экран: окно или полный экран; кадр рисуется на холсте и растягивается без искажений
    def set_size(self, w, h):
        if self.size != (w, h):
            self.size = (w, h)
            self.apply_display()

    def apply_display(self):
        lw, lh = self.size
        if self.store.settings["fullscreen"]:
            if self.display is None or not self.display_full:
                self.display = pygame.display.set_mode((0, 0), pygame.FULLSCREEN)
                self.display_full = True
        else:
            sizes = pygame.display.get_desktop_sizes() if hasattr(pygame.display, "get_desktop_sizes") else []
            dw, dh = sizes[0] if sizes else (lw, lh)
            k = max(0.5, min(self.dpi_scale, 0.95 * dw / lw, 0.88 * dh / lh))
            size = (round(lw * k), round(lh * k))
            if self.display is None or self.display_full or self.display.get_size() != size:
                self.display = pygame.display.set_mode(size)
                if self.display.get_size() != size:    # после полного экрана размер иногда не применяется сразу
                    self.display = pygame.display.set_mode(size)
                self.display_full = False
        dw, dh = self.display.get_size()
        s = min(dw / lw, dh / lh)
        cw, ch = max(lw, round(dw / s)), max(lh, round(dh / s))
        self.canvas = pygame.Surface((cw, ch)).convert(self.display)
        self.offset = ((cw - lw) // 2, (ch - lh) // 2)
        self.renderer.set_target(self.canvas, pygame.Rect(self.offset, (lw, lh)))

    def toggle_fullscreen(self):
        self.store.settings["fullscreen"] = not self.store.settings["fullscreen"]
        self.store.save()
        self.apply_display()
        self.cursor = None

    def present(self):
        size = self.display.get_size()
        if size == self.canvas.get_size():
            self.display.blit(self.canvas, (0, 0))
        else:
            pygame.transform.smoothscale(self.canvas, size, self.display)
        pygame.display.flip()

    def to_content(self, pos):
        """Координаты мыши на экране → координаты в раскладке."""
        sx = self.canvas.get_width() / self.display.get_width()
        sy = self.canvas.get_height() / self.display.get_height()
        return pos[0] * sx - self.offset[0], pos[1] * sy - self.offset[1]

    def update_cursor(self):
        """Курсор виден в меню и рекордах (над пунктом меню — золотой), в игре скрыт."""
        if self.state not in MENU_STATES:
            if self.cursor is not None:
                pygame.mouse.set_visible(False)
                self.cursor = None
            return
        hover = self.state in ("menu", "net_menu") and self.menu_hit(pygame.mouse.get_pos()) is not None
        frame = int(time.time() * CURSOR_FPS) % CURSOR_FRAMES
        state = (hover, frame)
        if state == self.cursor:
            return
        if self.cursor is None:
            pygame.mouse.set_visible(True)
        self.cursor = state
        try:
            if self.cursor_frames:
                pygame.mouse.set_cursor(self.cursor_frames[hover][frame])
            else:
                pygame.mouse.set_cursor(pygame.SYSTEM_CURSOR_HAND if hover else pygame.SYSTEM_CURSOR_ARROW)
        except (AttributeError, TypeError, pygame.error):
            pass

    def add_trail(self, pos, burst=False):
        sx = self.canvas.get_width() / self.display.get_width()
        sy = self.canvas.get_height() / self.display.get_height()
        x, y = pos[0] * sx, pos[1] * sy
        if not burst and self.trail_last and math.hypot(x - self.trail_last[0], y - self.trail_last[1]) < 7:
            return
        self.trail_last = (x, y)
        for _ in range(16 if burst else 2):
            speed = 160 if burst else 25
            life = random.uniform(0.5, 1.0)
            self.trail.append([x + random.uniform(-3, 3), y + random.uniform(-3, 3),
                               random.uniform(-speed, speed), random.uniform(-speed * 1.3, speed * 0.3),
                               life, life, COLORS[random.choice("IOTSZJL")], random.randint(7, 12)])
        del self.trail[:-TRAIL_LIMIT]

    def update_trail(self, dt):
        for p in self.trail:
            p[0] += p[2] * dt
            p[1] += p[3] * dt
            p[3] += 260 * dt
            p[4] -= dt
        self.trail = [p for p in self.trail if p[4] > 0]

    # --- фото при очистке линий
    def photo_area(self, slot):
        """Где показать фото (в координатах холста): пустые поля по бокам или панель управления."""
        ox, oy = self.offset
        cw, ch = self.canvas.get_size()
        if ox >= PHOTO_MIN_MARGIN:
            left = slot == 0 if self.mode != "single" else random.random() < 0.5
            x = 8 if left else cw - ox + 8
            return pygame.Rect(x, oy + 30, ox - 16, self.size[1] - 60)
        if self.mode == "single":
            top = MARGIN + 202
            rect = pygame.Rect(MARGIN, top, SIDE_W, HEIGHT - MARGIN - top)
        else:
            view = VS_VIEWS[slot]
            top = view.by + 96 + 10 + 3 * 64
            rect = pygame.Rect(view.left_x, top, view.side_w, view.by + ROWS * view.cell - top)
        return rect.move(ox, oy).inflate(-8, -8)

    def show_photo(self, slot, big):
        img = self.photos.next()
        if img is None:
            return
        area = self.photo_area(slot)
        scale = 1.0 if big else 0.92
        surf = make_polaroid(img, area.w * scale, area.h * scale, random.uniform(-7, 7))
        center = (area.centerx + random.randint(-6, 6), area.centery + random.randint(-area.h // 10, area.h // 10))
        self.photo_shows[slot] = {"surf": surf, "center": center, "t": 0.0,
                                  "dur": PHOTO_TIME_BIG if big else PHOTO_TIME}

    def update_photos(self, dt):
        for slot in list(self.photo_shows):
            show = self.photo_shows[slot]
            show["t"] += dt
            if show["t"] >= show["dur"]:
                del self.photo_shows[slot]

    def draw_photos(self):
        for show in self.photo_shows.values():
            t, dur, surf = show["t"], show["dur"], show["surf"]
            alpha, dy = 255, 0
            if t < 0.35:                            # «прилетает»: чуть больше и с отскоком
                p = t / 0.35
                scale = 1 + 0.25 * (1 - p) * math.cos(p * math.pi * 1.5)
                surf = pygame.transform.rotozoom(surf, 0, max(0.5, scale))
                alpha = int(255 * min(1.0, p * 2))
            elif t > dur - 0.45:                    # уходит вниз и тает
                p = (t - (dur - 0.45)) / 0.45
                alpha = int(255 * (1 - p))
                dy = int(40 * p * p)
            surf.set_alpha(alpha)
            self.canvas.blit(surf, surf.get_rect(center=(show["center"][0], show["center"][1] + dy)))
            surf.set_alpha(None)

    def draw_trail(self):
        for x, y, _, _, life, max_life, color, size in self.trail:
            s = max(2, int(size * life / max_life))
            if s >= 5:
                draw_block(self.canvas, int(x), int(y), s, color)
            else:
                pygame.draw.rect(self.canvas, lighten(color, 0.3), (int(x), int(y), s, s))

    def new_decor(self, y):
        return {"kind": random.choice("IOTSZJL"), "x": random.uniform(0, self.canvas.get_width()), "y": y,
                "speed": random.uniform(18, 55), "size": random.randint(14, 26), "rot": random.randrange(4)}

    # --- переходы между экранами
    def menu_items(self):
        if self.state == "net_menu":
            return [("host", "Создать игру"), ("join", "Подключиться"), ("back", "Назад")]
        s = self.store.settings
        return [("single", "Один игрок"), ("versus", "Два игрока"), ("online", "Игра по сети"), ("records", "Рекорды"),
                ("music", "Музыка: " + volume_text(s, "music")), ("sfx", "Звуки: " + volume_text(s, "sfx")),
                ("screen", "Экран: " + ("полный" if s["fullscreen"] else "окно")), ("quit", "Выход")]

    def menu_top(self):
        return NET_MENU_TOP if self.state == "net_menu" else MENU_TOP

    def go_menu(self):
        self.net_close(send_bye=True)
        self.set_size(WIDTH, HEIGHT)
        self.state = "menu"
        self.games = []
        self.paused = False
        pygame.key.stop_text_input()
        self.sound.restart_music()

    def start_single(self):
        self.set_size(WIDTH, HEIGHT)
        self.mode = "single"
        self.games = [Game()]
        self.begin_round()

    def start_versus(self, new_match):
        self.set_size(VS_WIDTH, VS_HEIGHT)
        self.mode = "versus"
        seed = random.randrange(1 << 30)
        self.games = [Game(seed, True, VS_NEXT_COUNT), Game(seed, True, VS_NEXT_COUNT)]
        if new_match:
            self.wins = [0, 0]
        self.begin_round()

    def begin_round(self):
        self.state = "play"
        self.paused = False
        self.result = None
        self.over_handled = False
        self.countdown = COUNTDOWN
        self.go_timer = 0.0
        self.sound.restart_music()
        self.sound.play("count")

    def finished(self):
        if self.mode == "single":
            return self.games[0].game_over
        return self.result is not None

    def toggle_pause(self, send=True):
        if self.paused:
            self.paused = False
            self.countdown = COUNTDOWN      # после паузы — снова отсчёт 3-2-1
            self.sound.play("count")
        else:
            self.paused = True
            for g in self.games:
                g.release_all()
        if send and self.mode == "online" and self.conn:
            self.conn.send({"t": "pause", "on": self.paused})

    def finish_versus(self, result):
        self.over_handled = True
        self.result = result
        if result != "draw":
            self.wins[result] += 1
        for g in self.games:
            g.frozen = True
        self.finish_timer = 0.0
        self.sound.play("win")

    # --- игра по сети
    def start_host(self):
        try:
            self.listener = net.Listener()
        except OSError:
            self.show_net_message("НЕ ПОЛУЧИЛОСЬ", ["Порт {} уже занят.".format(net.DEFAULT_PORT),
                                                    "Возможно, игра уже создана в другой копии."])
            return
        self.is_host = True
        self.host_addresses = net.local_addresses()
        self.state = "net_host"

    def open_join(self):
        self.state = "net_join"
        self.is_host = False
        self.net_status = ""
        pygame.key.start_text_input()

    def start_connect(self):
        address = self.address.strip()
        if not address or self.connector or self.conn:
            return
        self.store.settings["address"] = address
        self.store.save()
        self.connector = net.Connector(address)
        self.net_status = "Подключение"
        self.net_status_color = TEXT_DIM

    def attach(self, conn):
        self.conn = conn
        self.wins = [0, 0]
        self.opp_name = "Соперник"
        self.ping_ms = None
        self.ping_timer = self.send_timer = 0.0
        conn.send({"t": "hello", "v": net.PROTOCOL_VERSION, "name": self.store.settings["name"]})

    def net_close(self, send_bye=False):
        if self.conn:
            if send_bye and not self.conn.closed:
                self.conn.send({"t": "bye"})
                self.conn.flush()
            self.conn.close()
            self.conn = None
        if self.listener:
            self.listener.close()
            self.listener = None
        if self.connector:
            self.connector.cancel()
            self.connector = None

    def show_net_message(self, title, lines):
        self.net_close()
        self.set_size(WIDTH, HEIGHT)
        self.games = []
        self.paused = False
        pygame.key.stop_text_input()
        self.net_message = (title, lines)
        self.state = "net_msg"

    def start_online_round(self, seed):
        if self.is_host:
            self.conn.send({"t": "start", "seed": seed})
        pygame.key.stop_text_input()
        self.set_size(VS_WIDTH, VS_HEIGHT)
        self.mode = "online"
        self.games = [Game(seed, True, VS_NEXT_COUNT), Game(seed, True, VS_NEXT_COUNT)]
        self.games[1].frozen = True         # поле соперника только показываем, его считает его компьютер
        self.local_over = self.remote_over = False
        self.ready_local = self.ready_remote = False
        self.over_grace = 0.0
        self.begin_round()

    def want_rematch(self):
        if self.ready_local:
            return
        self.ready_local = True
        self.sound.play("select")
        self.conn.send({"t": "ready"})
        if self.is_host and self.ready_remote:
            self.start_online_round(random.randrange(1 << 30))

    def net_update(self, dt):
        if self.listener:
            accepted = self.listener.accept()
            if accepted:
                self.listener.close()
                self.listener = None
                self.attach(accepted[0])
        if self.connector:
            result = self.connector.poll()
            if result == "error":
                self.net_status, self.net_status_color = self.connector.error, BAD
                self.connector = None
            elif result:
                self.connector = None
                self.attach(result)
                self.net_status, self.net_status_color = "Подключено! Ждём начала игры", GOOD
        if not self.conn:
            return
        self.ping_timer += dt
        if self.ping_timer >= NET_PING_INTERVAL:
            self.ping_timer = 0.0
            self.conn.send({"t": "ping", "ts": time.time()})
        if self.mode == "online" and self.state == "play" and self.games:
            self.send_timer += dt
            if self.send_timer >= NET_SEND_INTERVAL:
                self.send_timer = 0.0
                self.conn.send(self.games[0].to_state())
        for msg in self.conn.pump():
            try:
                self.on_net(msg)
            except (KeyError, TypeError, ValueError, AttributeError):
                pass                        # битое сообщение — просто пропускаем
            if not self.conn:
                return
        if self.conn.closed:
            self.show_net_message("СВЯЗЬ ПРЕРВАНА", ["Соперник отключился."])
        elif time.time() - self.conn.last_recv > NET_TIMEOUT:
            self.show_net_message("СВЯЗЬ ПРЕРВАНА", ["От соперника нет ответа.", "Проверьте интернет или VPN."])

    def on_net(self, msg):
        kind = msg.get("t")
        online = self.mode == "online" and self.state == "play" and len(self.games) == 2
        if kind == "hello":
            if msg.get("v") != net.PROTOCOL_VERSION:
                self.show_net_message("РАЗНЫЕ ВЕРСИИ", ["У вас и у соперника разные версии игры.",
                                                        "Обновите обе копии до одинаковой."])
                return
            self.opp_name = str(msg.get("name") or "Соперник")[:MAX_NAME]
            if self.is_host:
                self.start_online_round(random.randrange(1 << 30))
        elif kind == "start" and not self.is_host:
            self.start_online_round(int(msg["seed"]))
        elif kind == "state" and online:
            self.games[1].apply_state(msg)
        elif kind == "garbage" and online and not self.over_handled:
            self.games[0].receive_garbage(max(1, min(20, int(msg["n"]))))
        elif kind == "popup" and online:
            color = msg.get("color")
            if isinstance(color, list) and len(color) == 3:
                self.games[1].add_popup(str(msg.get("text", ""))[:40], tuple(max(0, min(255, int(c))) for c in color))
        elif kind == "over" and online:
            self.remote_over = True
            self.games[1].game_over = True
            self.games[1].piece = None
        elif kind == "pause" and online and not self.finished():
            if bool(msg["on"]) != self.paused:
                self.toggle_pause(send=False)
        elif kind == "ready":
            self.ready_remote = True
            if self.is_host and self.ready_local and online and self.finished():
                self.start_online_round(random.randrange(1 << 30))
        elif kind == "ping":
            self.conn.send({"t": "pong", "ts": msg.get("ts")})
        elif kind == "pong":
            self.ping_ms = max(0, int((time.time() - float(msg["ts"])) * 1000))
        elif kind == "bye":
            self.show_net_message("ИГРА ОКОНЧЕНА", ["Соперник вышел из игры."])

    def on_single_over(self):
        g = self.games[0]
        self.finish_timer = 0.0
        rank = self.store.rank_for("marathon", g.score)
        if rank is not None:
            self.state = "name"
            self.name = self.store.settings["name"]
            self.name_rank = rank
            self.name_delay = 0.6
            pygame.key.start_text_input()

    def save_name(self):
        g = self.games[0]
        name = self.name.strip() or DEFAULT_NAME
        self.store.settings["name"] = name
        entry = {"name": name, "score": g.score, "lines": g.lines, "level": g.level,
                 "time": round(g.time, 1), "date": time.strftime("%d.%m.%Y")}
        pygame.key.stop_text_input()
        self.record_rank = self.store.add("marathon", entry)
        self.records_from_game = True
        self.state = "records"

    # --- ввод
    def handle_event(self, event):
        if event.type == pygame.QUIT:
            return False
        if self.state in MENU_STATES:
            if event.type == pygame.MOUSEMOTION:
                self.add_trail(event.pos)
            elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                self.add_trail(event.pos, burst=True)
        focus_lost = getattr(pygame, "WINDOWFOCUSLOST", None)
        if focus_lost is not None and event.type == focus_lost:
            if self.state == "play" and not self.paused and not self.finished():
                self.toggle_pause()
            for g in self.games:
                g.release_all()
            return True

        if event.type == pygame.KEYDOWN and (event.key == pygame.K_F11 or (
                event.key in (pygame.K_RETURN, pygame.K_KP_ENTER) and event.mod & pygame.KMOD_ALT)):
            self.toggle_fullscreen()
            return True

        if self.state == "name":
            return self.handle_name(event)
        if self.state == "net_join":
            return self.handle_join(event)

        if event.type == pygame.KEYDOWN:
            if matches(event, KEYS_MUSIC):
                self.sound.toggle("music")
                return True
            if matches(event, KEYS_SFX):
                self.sound.toggle("sfx")
                return True

        if self.state in ("menu", "net_menu"):
            return self.handle_menu(event)
        if self.state == "net_host":
            if event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
                self.net_close()
                self.state = "net_menu"
            return True
        if self.state == "net_msg":
            if (event.type == pygame.KEYDOWN and (matches(event, KEYS_OK) or event.key == pygame.K_ESCAPE)) or \
                    (event.type == pygame.MOUSEBUTTONDOWN and event.button == 1):
                self.go_menu()
            return True
        if self.state == "records":
            if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                self.go_menu()
            elif event.type == pygame.KEYDOWN:
                if matches(event, KEYS_OK) and self.records_from_game:
                    self.start_single()
                elif matches(event, KEYS_OK) or event.key == pygame.K_ESCAPE:
                    self.go_menu()
            return True
        if self.state == "play":
            self.handle_play(event)
        return True

    def menu_hit(self, pos):
        x, y = self.to_content(pos)
        for i in range(len(self.menu_items())):
            if menu_item_rect(i, self.size[0], self.menu_top()).collidepoint(x, y):
                return i
        return None

    def activate_menu(self, action):
        self.sound.play("select")
        if action == "single":
            self.start_single()
        elif action == "versus":
            self.start_versus(new_match=True)
        elif action == "records":
            self.state = "records"
            self.record_rank = None
            self.records_from_game = False
        elif action in ("music", "sfx"):
            self.sound.toggle(action)
        elif action == "screen":
            self.toggle_fullscreen()
        elif action == "online":
            self.state = "net_menu"
            self.menu_index = 0
        elif action == "host":
            self.start_host()
        elif action == "join":
            self.open_join()
        elif action == "back":
            self.state = "menu"
            self.menu_index = 2
        elif action == "quit":
            return False
        return True

    def handle_menu(self, event):
        items = self.menu_items()
        if event.type == pygame.MOUSEMOTION:
            i = self.menu_hit(event.pos)
            if i is not None and i != self.menu_index:
                self.menu_index = i
                self.sound.play("menu")
            return True
        if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            i = self.menu_hit(event.pos)
            if i is None:
                return True
            self.menu_index = i
            action = items[i][0]
            if action in ("music", "sfx"):
                rect = menu_item_rect(i, self.size[0], self.menu_top())
                x = self.to_content(event.pos)[0]
                if x < rect.x + MENU_ARROW_ZONE:
                    self.sound.change_volume(action, -1)
                    return True
                if x > rect.right - MENU_ARROW_ZONE:
                    self.sound.change_volume(action, 1)
                    return True
            return self.activate_menu(action)
        if event.type == pygame.MOUSEWHEEL:
            action = items[self.menu_index][0]
            if action in ("music", "sfx") and event.y:
                self.sound.change_volume(action, 1 if event.y > 0 else -1)
            return True
        if event.type != pygame.KEYDOWN:
            return True
        if event.key == pygame.K_ESCAPE:
            if self.state == "net_menu":
                return self.activate_menu("back")
            return False
        if matches(event, KEYS_UP):
            self.menu_index = (self.menu_index - 1) % len(items)
            self.sound.play("menu")
        elif matches(event, KEYS_DOWN):
            self.menu_index = (self.menu_index + 1) % len(items)
            self.sound.play("menu")
        elif matches(event, KEYS_LEFT) or matches(event, KEYS_RIGHT):
            action = items[self.menu_index][0]
            if action in ("music", "sfx"):
                self.sound.change_volume(action, 1 if matches(event, KEYS_RIGHT) else -1)
            elif action == "screen":
                self.toggle_fullscreen()
        elif matches(event, KEYS_OK) or event.key == pygame.K_SPACE:
            return self.activate_menu(items[self.menu_index][0])
        return True

    def handle_name(self, event):
        if event.type == pygame.TEXTINPUT and self.name_delay <= 0:
            for ch in event.text:
                if ch.isprintable() and len(self.name) < MAX_NAME:
                    self.name += ch
        elif event.type == pygame.KEYDOWN and self.name_delay <= 0:
            if event.key == pygame.K_BACKSPACE:
                self.name = self.name[:-1]
            elif matches(event, KEYS_OK):
                self.sound.play("select")
                self.save_name()
            elif event.key == pygame.K_ESCAPE:
                pygame.key.stop_text_input()
                self.state = "play"         # обычный экран "игра окончена"
        return True

    def handle_join(self, event):
        busy = self.connector is not None or self.conn is not None
        if event.type == pygame.TEXTINPUT and not busy:
            for ch in event.text:
                if ch in ADDRESS_CHARS and len(self.address) < 40:
                    self.address += ch
        elif event.type == pygame.KEYDOWN:
            if event.key == pygame.K_ESCAPE:
                self.net_close(send_bye=True)
                pygame.key.stop_text_input()
                self.state = "net_menu"
            elif busy:
                return True
            elif event.key == pygame.K_BACKSPACE:
                self.address = self.address[:-1]
            elif matches(event, KEYS_OK):
                self.start_connect()
            elif event.key == pygame.K_v and event.mod & pygame.KMOD_CTRL or \
                    (event.mod & pygame.KMOD_CTRL and getattr(event, "scancode", None) == getattr(pygame, "KSCAN_V", -1)):
                try:
                    pasted = pygame.scrap.get_text() if hasattr(pygame.scrap, "get_text") else ""
                except pygame.error:
                    pasted = ""
                self.address = "".join(ch for ch in (pasted or "") if ch in ADDRESS_CHARS)[:40] or self.address
        return True

    def handle_play(self, event):
        controls = [CONTROLS_P1, CONTROLS_P2] if self.mode == "versus" else [CONTROLS_SINGLE]
        if event.type == pygame.KEYUP:
            for g, ctrl in zip(self.games, controls):
                action = find_action(event, ctrl)
                if action:
                    g.key_up(action)
            return
        if event.type != pygame.KEYDOWN:
            return

        if self.finished():
            if self.finish_timer < FINISH_INPUT_DELAY:
                return
            if event.key == pygame.K_ESCAPE:
                self.go_menu()
            elif matches(event, KEYS_OK) or matches(event, KEYS_RESTART):
                if self.mode == "single":
                    self.start_single()
                elif self.mode == "online":
                    self.want_rematch()
                else:
                    self.start_versus(new_match=False)
            return
        if matches(event, KEYS_PAUSE):
            self.toggle_pause()
            return
        if self.paused:
            if matches(event, KEYS_UP) or matches(event, KEYS_DOWN):
                self.pause_index = 1 - self.pause_index
                self.sound.play("menu")
            elif matches(event, KEYS_LEFT) or matches(event, KEYS_RIGHT):
                self.sound.change_volume(("music", "sfx")[self.pause_index],
                                         1 if matches(event, KEYS_RIGHT) else -1)
            elif matches(event, KEYS_RESTART) and self.mode != "online":
                if self.mode == "single":
                    self.start_single()
                else:
                    self.start_versus(new_match=False)
            elif matches(event, KEYS_QUIT_TO_MENU):
                self.go_menu()
            return

        active = self.countdown <= 0
        for g, ctrl in zip(self.games, controls):
            action = find_action(event, ctrl)
            if action:
                g.key_down(action, active and not g.game_over)

    # --- шаг
    def update(self, dt):
        self.blink += dt
        self.net_update(dt)
        if self.state in MENU_STATES:
            self.menu_time += dt
            self.update_trail(dt)
            for i, d in enumerate(self.decor):
                d["y"] += d["speed"] * dt
                if d["y"] > self.canvas.get_height() + 80:
                    self.decor[i] = self.new_decor(-80)
        if self.state == "name":
            self.name_delay -= dt

        if self.state in ("play", "name"):
            for g in self.games:
                g.update_effects(dt)
            self.finish_timer += dt
            self.go_timer = max(0.0, self.go_timer - dt)
            if self.state == "play" and not self.paused and not self.over_handled:
                if self.countdown > 0:
                    before = math.ceil(self.countdown)
                    self.countdown -= dt
                    if self.countdown <= 0:
                        self.countdown = 0.0
                        self.go_timer = 0.7
                        self.sound.play("go")
                        for g in self.games:
                            g.resume_input()
                    elif math.ceil(self.countdown) != before:
                        self.sound.play("count")
                else:
                    self.step_games(dt)

        for i, g in enumerate(self.games):
            for name in g.sfx:
                self.sound.play(name)
            g.sfx.clear()
            if self.mode == "online" and i == 0 and self.conn:
                for text, color in g.new_popups:
                    self.conn.send({"t": "popup", "text": text, "color": list(color)})
            g.new_popups.clear()
            for big in g.photo_events:
                self.show_photo(i, big)
            g.photo_events.clear()
        if self.state in ("play", "name"):
            self.update_photos(dt)
        else:
            self.photo_shows.clear()

        level = self.current_level()
        want = self.state in MENU_STATES or (self.state == "play" and not self.finished())
        self.sound.update(dt, want, music_tier(level), self.state == "play" and self.paused)

    def step_games(self, dt):
        if self.mode == "online":
            self.step_online(dt)
            return
        for g in self.games:
            g.update(dt)
        if self.mode == "single":
            if self.games[0].game_over:
                self.over_handled = True
                self.on_single_over()
            return
        for i, g in enumerate(self.games):
            if g.outgoing:
                self.games[1 - i].receive_garbage(g.outgoing)
                g.outgoing = 0
        over = [g.game_over for g in self.games]
        if any(over):
            self.finish_versus("draw" if all(over) else (1 if over[0] else 0))

    def step_online(self, dt):
        g = self.games[0]
        g.update(dt)
        if not self.conn:
            return
        if g.outgoing:
            self.conn.send({"t": "garbage", "n": g.outgoing})
            g.outgoing = 0
        if g.game_over and not self.local_over:
            self.local_over = True
            self.over_grace = NET_OVER_GRACE
            self.conn.send(g.to_state())
            self.conn.send({"t": "over"})
        if self.local_over:
            # ждём чуть-чуть: если соперник проиграл почти одновременно — ничья
            self.over_grace -= dt
            if self.remote_over:
                self.finish_versus("draw")
            elif self.over_grace <= 0:
                self.finish_versus(1)
        elif self.remote_over:
            self.finish_versus(0)

    def current_level(self):
        if self.state in MENU_STATES:
            return 1 + int(self.menu_time / 6)    # в меню фон медленно перебирает все палитры
        return max((g.level for g in self.games), default=1)

    # --- отрисовка
    def draw(self, dt):
        r = self.renderer
        r.draw_background(self.current_level(), dt)
        if self.state in MENU_STATES:
            r.draw_decor(self.decor)
        if self.state == "menu":
            r.draw_menu(self.menu_items(), self.menu_index, self.store.best("marathon"), self.store.settings)
            self.draw_trail()
        elif self.state == "net_menu":
            r.draw_menu(self.menu_items(), self.menu_index, None, self.store.settings, title="ИГРА ПО СЕТИ",
                        subtitle="без сервера — компьютеры соединяются напрямую", top=NET_MENU_TOP, notes=[
                            "В одной Wi-Fi сети: один нажимает «Создать игру»,",
                            "второй — «Подключиться» и вводит адрес с экрана первого.",
                            "",
                            "Через интернет: установите оба бесплатную программу",
                            "Radmin VPN, ZeroTier или Tailscale и войдите в одну сеть.",
                            "Дальше — так же, по адресу этой сети.",
                            "",
                            "Управление как в одиночной игре: стрелки, X / Z, Пробел, C."])
            self.draw_trail()
        elif self.state == "net_host":
            r.draw_host(self.host_addresses, net.DEFAULT_PORT, self.blink)
            self.draw_trail()
        elif self.state == "net_join":
            r.draw_join(self.address, self.net_status, self.net_status_color, self.blink,
                        self.connector is not None)
            self.draw_trail()
        elif self.state == "net_msg":
            r.draw_message(*self.net_message)
            self.draw_trail()
        elif self.state == "records":
            r.draw_records(self.store.table("marathon"), self.record_rank, self.records_from_game)
            self.draw_trail()
        elif self.mode == "single":
            self.draw_single()
        else:
            self.draw_versus()
        if self.state in ("play", "name"):
            self.draw_photos()
        self.update_cursor()
        self.present()

    def draw_single(self):
        r = self.renderer
        g = self.games[0]
        best = self.store.best("marathon")
        r.draw_single_side(g, best["score"] if best else 0, self.store.settings)
        r.draw_board(g, SINGLE_VIEW)
        rect = board_rect(SINGLE_VIEW)
        if self.state == "name":
            r.name_entry(rect, g.score, self.name_rank, self.name, self.blink)
        elif g.game_over:
            r.overlay(rect, [("ИГРА ОКОНЧЕНА", r.f_big, BAD),
                             ("Счёт: {}".format(format_score(g.score)), r.f_med, TEXT),
                             ("", r.f_small, TEXT),
                             ("Enter — играть снова", r.f_med, TEXT_DIM),
                             ("Esc — в меню", r.f_med, TEXT_DIM)])
        else:
            self.draw_round_overlays(rect)

    def draw_versus(self):
        r = self.renderer
        online = self.mode == "online"
        if online:
            r.draw_versus_header(self.wins, [self.store.settings["name"] + " (вы)", self.opp_name])
        else:
            r.draw_versus_header(self.wins)
        for i, (g, view) in enumerate(zip(self.games, VS_VIEWS)):
            if not online:
                r.draw_versus_side(g, view, HELP_P1 if i == 0 else HELP_P2)
            elif i == 0:
                r.draw_versus_side(g, view, HELP_ONLINE)
            else:
                ping = "—" if self.ping_ms is None else "{} мс".format(self.ping_ms)
                r.draw_versus_side(g, view, [(ping, "пинг"), (self.opp_name, "соперник")],
                                   help_title="СВЯЗЬ")
            r.draw_board(g, view, frame=darken(PLAYER_COLORS[i], 0.35))
            rect = board_rect(view)
            if self.result is not None:
                if self.result == "draw":
                    head = ("НИЧЬЯ", r.f_huge, ACCENT)
                elif self.result == i:
                    head = ("ПОБЕДА!", r.f_huge, GOOD)
                else:
                    head = ("ПОРАЖЕНИЕ", r.f_big, BAD)
                if not online:
                    hint = [("Enter — реванш", r.f_med, TEXT_DIM)]
                elif self.ready_local:
                    hint = [("Ждём соперника…", r.f_med, ACCENT)]
                elif self.ready_remote:
                    hint = [("Соперник хочет реванш!", r.f_med, GOOD), ("Enter — играть", r.f_med, TEXT_DIM)]
                else:
                    hint = [("Enter — реванш", r.f_med, TEXT_DIM)]
                r.overlay(rect, [head,
                                 ("Счёт: {}".format(format_score(g.score)), r.f_med, TEXT),
                                 ("", r.f_small, TEXT)] + hint +
                          [("Esc — в меню", r.f_med, TEXT_DIM)])
            else:
                self.draw_round_overlays(rect)

    def draw_round_overlays(self, rect):
        r = self.renderer
        if self.paused:
            volume = []
            for i, (k, label) in enumerate((("music", "Музыка"), ("sfx", "Звуки"))):
                s = "{}: {}".format(label, volume_text(self.store.settings, k))
                volume.append(("‹  {}  ›".format(s), r.f_med, ACCENT) if i == self.pause_index
                              else (s, r.f_med, TEXT_DIM))
            restart = [] if self.mode == "online" else [("R — начать заново", r.f_med, TEXT_DIM)]
            r.overlay(rect, [("ПАУЗА", r.f_huge, TEXT),
                             ("P / Esc — продолжить", r.f_med, TEXT_DIM)] + restart +
                      [("Q — выйти в меню", r.f_med, TEXT_DIM),
                             ("", r.f_small, TEXT)] + volume +
                      [("↑ ↓  выбрать,  ← →  громкость", r.f_small, TEXT_DIM)])
        elif self.countdown > 0:
            r.countdown(rect, self.countdown)
        elif self.go_timer > 0:
            r.go_flash(rect, self.go_timer)

    def run(self):
        while True:
            dt = min(self.clock.tick(FPS) / 1000.0, 0.05)
            for event in pygame.event.get():
                if not self.handle_event(event):
                    self.net_close(send_bye=True)
                    return
            self.update(dt)
            self.draw(dt)


# ---------------------------------------------------------------- фото
def jpeg_orientation(path):
    """Поворот из EXIF (фото с телефона часто хранят его отдельно): 1 — как есть."""
    import struct
    try:
        with open(path, "rb") as f:
            data = f.read(256 * 1024)
        if data[:2] != b"\xff\xd8":
            return 1
        i = 2
        while i + 4 <= len(data) and data[i] == 0xFF:
            marker = data[i + 1]
            size = struct.unpack(">H", data[i + 2:i + 4])[0]
            if marker == 0xE1 and data[i + 4:i + 10] == b"Exif\x00\x00":
                tiff = data[i + 10:i + 2 + size]
                end = "<" if tiff[:2] == b"II" else ">"
                ifd = struct.unpack(end + "I", tiff[4:8])[0]
                count = struct.unpack(end + "H", tiff[ifd:ifd + 2])[0]
                for k in range(count):
                    e = ifd + 2 + k * 12
                    if struct.unpack(end + "H", tiff[e:e + 2])[0] == 0x0112:
                        value = struct.unpack(end + "H", tiff[e + 8:e + 10])[0]
                        return value if 1 <= value <= 8 else 1
                return 1
            if marker in (0xDA, 0xD9):
                return 1
            i += 2 + size
    except (OSError, struct.error, IndexError):
        pass
    return 1


def apply_orientation(surf, orientation):
    rot = pygame.transform.rotate
    flip = pygame.transform.flip
    if orientation == 2:
        return flip(surf, True, False)
    if orientation == 3:
        return rot(surf, 180)
    if orientation == 4:
        return flip(surf, False, True)
    if orientation == 5:
        return flip(rot(surf, -90), True, False)
    if orientation == 6:
        return rot(surf, -90)
    if orientation == 7:
        return flip(rot(surf, -90), False, True)
    if orientation == 8:
        return rot(surf, 90)
    return surf


def load_photo(path, max_side):
    surf = pygame.image.load(path)
    if surf.get_bitsize() not in (24, 32):          # палитровые PNG/GIF — в обычный цвет
        full = pygame.Surface(surf.get_size(), pygame.SRCALPHA, 32)
        full.blit(surf, (0, 0))
        surf = full
    if path.lower().endswith((".jpg", ".jpeg")):
        surf = apply_orientation(surf, jpeg_orientation(path))
    w, h = surf.get_size()
    k = max_side / max(w, h)
    if k < 1:
        surf = pygame.transform.smoothscale(surf, (max(1, int(w * k)), max(1, int(h * k))))
    return surf


def photo_files(dirs):
    files = []
    for d in dirs:
        try:
            names = sorted(os.listdir(d))
        except OSError:
            continue
        files += [os.path.join(d, n) for n in names if n.lower().endswith(PHOTO_EXTENSIONS)]
    return files


class PhotoLibrary:
    """Фото грузятся в фоне (большие снимки с телефона декодируются не мгновенно)."""

    def __init__(self, dirs):
        self.photos = []
        self.bag = []
        self.last = None
        files = photo_files(dirs)
        if files:
            threading.Thread(target=self._load, args=(files,), daemon=True).start()

    def _load(self, files):
        for path in files:
            try:
                self.photos.append(load_photo(path, PHOTO_MAX_SIDE))
            except (pygame.error, OSError, ValueError, MemoryError):
                pass                # битый или неподдерживаемый файл — пропускаем

    def next(self):
        """Случайный порядок без повторов: каждое фото по разу, потом новый круг."""
        n = len(self.photos)
        if not n:
            return None
        if not self.bag:
            self.bag = list(range(n))
            random.shuffle(self.bag)
            if n > 1 and self.bag[-1] == self.last:
                self.bag[0], self.bag[-1] = self.bag[-1], self.bag[0]
        self.last = self.bag.pop()
        return self.photos[self.last]


def make_polaroid(img, max_w, max_h, angle):
    """Фото в белой рамке «полароид» с тенью, повёрнутое на angle градусов."""
    max_w, max_h = max_w * 0.9, max_h * 0.9            # запас под поворот
    border = max(4, int(min(max_w, max_h) * 0.035))
    bottom = border * 3
    iw, ih = img.get_size()
    k = min((max_w - 2 * border) / iw, (max_h - border - bottom) / ih, 1.6)
    pw, ph = max(1, int(iw * k)), max(1, int(ih * k))
    w, h = pw + 2 * border, ph + border + bottom
    shadow = max(4, border)
    card = pygame.Surface((w + shadow, h + shadow), pygame.SRCALPHA)
    pygame.draw.rect(card, (0, 0, 0, 90), (shadow, shadow, w, h), border_radius=3)
    pygame.draw.rect(card, (246, 244, 236), (0, 0, w, h), border_radius=3)
    card.blit(pygame.transform.smoothscale(img, (pw, ph)), (border, border))
    return pygame.transform.rotozoom(card, angle, 1.0)


def prepare_photos(out_dir):
    """Для сборки .exe: уменьшенные и правильно повёрнутые копии фото из папки photos."""
    os.makedirs(out_dir, exist_ok=True)
    for name in os.listdir(out_dir):
        try:
            os.remove(os.path.join(out_dir, name))
        except OSError:
            pass
    count = 0
    for path in photo_files([os.path.join(BASE_DIR, "photos")]):
        try:
            surf = load_photo(path, PHOTO_BUILD_SIDE)
        except (pygame.error, OSError, ValueError, MemoryError):
            continue
        ext = ".png" if surf.get_flags() & pygame.SRCALPHA else ".jpg"
        pygame.image.save(surf, os.path.join(out_dir, "photo_{:03d}{}".format(count, ext)))
        count += 1
    with open(os.path.join(out_dir, "photos.txt"), "w", encoding="utf-8") as f:
        f.write(str(count))
    print("Фото для сборки:", count)


# ---------------------------------------------------------------- иконка и запуск
ICON_CELLS = [(1, 0, "T"), (0, 1, "T"), (1, 1, "T"), (2, 1, "T"), (3, 1, "O"),
              (0, 2, "J"), (1, 2, "J"), (2, 2, "S"), (3, 2, "O"),
              (0, 3, "I"), (1, 3, "I"), (2, 3, "I"), (3, 3, "I")]


def make_icon(size):
    big = 256
    surf = pygame.Surface((big, big), pygame.SRCALPHA)
    pygame.draw.rect(surf, BOARD_BG, (0, 0, big, big), border_radius=44)
    pygame.draw.rect(surf, PANEL_BORDER, (0, 0, big, big), 8, border_radius=44)
    cell = 52
    ox = oy = (big - 4 * cell) // 2
    for x, y, kind in ICON_CELLS:
        draw_block(surf, ox + x * cell, oy + y * cell, cell, COLORS[kind])
    return surf if size == big else pygame.transform.smoothscale(surf, (size, size))


def save_ico(path):
    """ICO-файл для ярлыка: 256 px в PNG, остальные размеры — классическим BMP (так понимают все версии Windows)."""
    import io
    import struct
    images = []
    for size in (256, 48, 32, 16):
        surf = make_icon(size)
        if size == 256:
            buf = io.BytesIO()
            pygame.image.save(surf, buf, "icon.png")
            images.append((size, buf.getvalue()))
            continue
        rows = []
        for y in range(size - 1, -1, -1):           # BMP хранит строки снизу вверх
            for x in range(size):
                r, g, b, a = surf.get_at((x, y))
                rows.append(struct.pack("<BBBB", b, g, r, a))
        mask = bytes(1) * (((size + 31) // 32) * 4 * size)
        header = struct.pack("<IiiHHIIiiII", 40, size, size * 2, 1, 32, 0, 0, 0, 0, 0, 0)
        images.append((size, header + b"".join(rows) + mask))
    data = struct.pack("<HHH", 0, 1, len(images))
    offset = 6 + 16 * len(images)
    for size, blob in images:
        data += struct.pack("<BBBBHHII", size % 256, size % 256, 0, 0, 1, 32, len(blob), offset)
        offset += len(blob)
    with open(path, "wb") as f:
        f.write(data + b"".join(blob for _, blob in images))


def enable_dpi_awareness():
    """Без этого Windows с масштабом 125 % растягивает картинку сама и она становится мыльной."""
    if sys.platform != "win32":
        return 1.0
    import ctypes
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except (AttributeError, OSError):
        try:
            ctypes.windll.user32.SetProcessDPIAware()
        except (AttributeError, OSError):
            return 1.0
    try:
        return ctypes.windll.user32.GetDpiForSystem() / 96.0
    except (AttributeError, OSError):
        return 1.0


_instance_lock = None


def another_copy_running():
    """Вторая копия игры не запускается (иначе играют две музыки) — вместо этого показываем первую."""
    global _instance_lock
    if sys.platform != "win32":
        return False
    import ctypes
    kernel32 = ctypes.WinDLL("kernel32", use_last_error=True)
    kernel32.CreateMutexW.restype = ctypes.c_void_p
    _instance_lock = kernel32.CreateMutexW(None, False, "Local\\TetrisPygameGame")
    if ctypes.get_last_error() != 183:      # ERROR_ALREADY_EXISTS
        return False
    user32 = ctypes.windll.user32
    hwnd = user32.FindWindowW(None, WINDOW_TITLE)
    if hwnd:
        user32.ShowWindow(hwnd, 9)          # SW_RESTORE
        user32.SetForegroundWindow(hwnd)
    return True


def report_error():
    """При запуске с ярлыка консоли нет — сохраняем ошибку в файл и показываем окно."""
    import traceback
    text = traceback.format_exc()
    try:
        os.makedirs(os.path.dirname(ERROR_LOG), exist_ok=True)
        with open(ERROR_LOG, "w", encoding="utf-8") as f:
            f.write(text)
    except OSError:
        pass
    if sys.platform == "win32":
        import ctypes
        ctypes.windll.user32.MessageBoxW(None, "Игра завершилась с ошибкой.\nПодробности: " + ERROR_LOG,
                                         WINDOW_TITLE, 0x10)
    else:
        sys.stderr.write(text)


def main():
    if "--prepare-photos" in sys.argv:
        prepare_photos(sys.argv[sys.argv.index("--prepare-photos") + 1])
        return
    selftest = os.environ.get("TETRIS_SELFTEST")
    if selftest:
        # проверка сборки: пара секунд меню и игры, затем отметка «ok» в указанный файл
        app = App()
        for step in range(150):
            if step == 60:
                app.start_single()
            app.update(1 / 60)
            app.draw(1 / 60)
        expected = len(photo_files(PHOTO_DIRS))
        deadline = time.time() + 5
        while len(app.photos.photos) < expected and time.time() < deadline:
            time.sleep(0.05)
        with open(selftest, "w", encoding="utf-8") as f:
            f.write("ok photos={}/{}".format(len(app.photos.photos), expected))
        return
    if "--make-icon" in sys.argv:
        save_ico(ICON_FILE)
        return
    if "--allow-second-copy" not in sys.argv and another_copy_running():
        return
    App().run()


if __name__ == "__main__":
    try:
        main()
    except Exception:
        report_error()
    finally:
        pygame.quit()
    sys.exit(0)
