"""
Dota Skin Changer — менеджер VPK-модов для Dota 2 (по типу Overplus).

ПРИНЦИП РАБОТЫ
  1. Скачивает catalog.json с удалённого сервера (URL задаётся ниже или в «Настройках»).
  2. Показывает карточки скинов с превью.
  3. По кнопке «Установить» скачивает VPK, проверяет его и кладёт в
     <Dota 2>/game/dota_<язык>/.
  4. Чтобы игра подхватила мод, в Steam → Dota 2 → Свойства → Параметры запуска
     нужно указать:  -language <язык>

ЧТО ПРИЛОЖЕНИЕ НЕ ДЕЛАЕТ
  * не читает и не пишет память игры, не инжектит DLL, не трогает античит;
  * не извлекает скины из установленной игры — только скачивает готовые VPK.

!!! ПРЕДУПРЕЖДЕНИЕ !!!
  Использование модов — на ваш риск. Модификация файлов клиента нарушает
  Пользовательское соглашение Steam, и Valve может заблокировать аккаунт.
  Приложение показывает это предупреждение при первом запуске.
"""

from __future__ import annotations

import copy
import hashlib
import json
import logging
import os
import queue
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import threading
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from io import BytesIO
from logging.handlers import RotatingFileHandler
from pathlib import Path
from tkinter import TclError, filedialog, messagebox
from typing import Callable

import customtkinter as ctk
import psutil
import requests
from PIL import Image, ImageOps

# =============================================================================
#  URL КАТАЛОГА ПО УМОЛЧАНИЮ — ЗАМЕНИТЕ НА СВОЙ!
#  Пример для GitHub: https://raw.githubusercontent.com/<user>/<repo>/main/catalog.json
#  Пользователь также может поменять его во вкладке «Настройки» (сохраняется в config.json).
# =============================================================================
DEFAULT_CATALOG_URL = "https://raw.githubusercontent.com/YOUR_USER/YOUR_REPO/main/catalog.json"

APP_NAME = "DotaSkinChanger"
APP_TITLE = "Dota Skin Changer"
APP_VERSION = "1.0.0"

DOTA_PROCESS_NAMES = {"dota2.exe"}
VPK_SIGNATURE = 0x55AA1234            # сигнатура заголовка *_dir.vpk (little-endian)
HTTP_TIMEOUT = (10, 60)               # (connect, read) секунд
MAX_PREVIEW_BYTES = 10 * 1024 * 1024  # 10 МБ на картинку превью
PREVIEW_SIZE = (220, 124)             # размер превью в карточке (16:9)
CATALOG_COLUMNS = 4

LANG_RE = re.compile(r"^[a-z0-9_]{2,32}$")
# Только имя файла, без путей — защита от записи за пределы папки модов (../ и т.п.)
FILE_NAME_RE = re.compile(r"^[A-Za-z0-9_.\-]+\.vpk$", re.IGNORECASE)
LANG_PRESETS = ["english", "russian", "ukrainian", "schinese", "brazilian", "spanish", "german"]

ALL_HEROES = "Все герои"
ALL_TYPES = "Все типы"

RISK_TEXT = (
    "Это приложение устанавливает сторонние VPK-моды в папку Dota 2.\n\n"
    "• Использование модов — полностью на ваш риск.\n"
    "• Модификация файлов клиента противоречит правилам Steam/Valve. "
    "Valve может заблокировать аккаунт за модификацию клиента, даже если мод "
    "меняет только внешний вид.\n"
    "• Изменённые скины видите только вы — другие игроки их не видят.\n"
    "• После обновления Dota 2 моды могут перестать работать или вызвать вылеты. "
    "В этом случае нажмите «Сбросить все моды» и проверьте целостность файлов в Steam.\n\n"
    "Приложение не лезет в память игры, не внедряет DLL и не обходит античит — "
    "оно только копирует файлы."
)


# =============================================================================
#  Пути: %APPDATA%/DotaSkinChanger
# =============================================================================
def _get_app_dir() -> Path:
    base = os.environ.get("APPDATA") or str(Path.home())
    app_dir = Path(base) / APP_NAME
    app_dir.mkdir(parents=True, exist_ok=True)
    return app_dir


APP_DIR = _get_app_dir()
CONFIG_PATH = APP_DIR / "config.json"
LOG_PATH = APP_DIR / "log.txt"
CACHE_DIR = APP_DIR / "cache"
PREVIEW_DIR = CACHE_DIR / "previews"
CATALOG_CACHE_PATH = CACHE_DIR / "catalog.json"
TEMP_DIR = Path(tempfile.gettempdir()) / APP_NAME

for _d in (CACHE_DIR, PREVIEW_DIR):
    _d.mkdir(parents=True, exist_ok=True)


# =============================================================================
#  Логирование: %APPDATA%/DotaSkinChanger/log.txt
# =============================================================================
def _setup_logging() -> logging.Logger:
    logger = logging.getLogger(APP_NAME)
    logger.setLevel(logging.INFO)
    handler = RotatingFileHandler(LOG_PATH, maxBytes=2 * 1024 * 1024, backupCount=2, encoding="utf-8")
    handler.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
    logger.addHandler(handler)
    if not getattr(sys, "frozen", False):
        console = logging.StreamHandler()
        console.setFormatter(logging.Formatter("[%(levelname)s] %(message)s"))
        logger.addHandler(console)
    return logger


log = _setup_logging()


class SkinChangerError(Exception):
    """Ошибка, текст которой можно показать пользователю как есть."""


# =============================================================================
#  Конфиг: %APPDATA%/DotaSkinChanger/config.json
# =============================================================================
DEFAULT_CONFIG = {
    "catalog_url": DEFAULT_CATALOG_URL,
    "dota_path": "",
    "language": "english",
    "accepted_risk": False,
    "auto_update_catalog": True,
    # id скина -> {name, hero, type, file_name, path, installed_at}
    "installed": {},
}


class Config:
    def __init__(self, path: Path):
        self.path = path
        self.data: dict = copy.deepcopy(DEFAULT_CONFIG)
        self.load()

    def load(self) -> None:
        if not self.path.exists():
            return
        try:
            loaded = json.loads(self.path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            log.error("Не удалось прочитать конфиг (%s), используются значения по умолчанию", exc)
            broken = self.path.with_suffix(".broken.json")
            try:
                shutil.copy2(self.path, broken)
            except OSError:
                log.warning("Не удалось сохранить копию повреждённого конфига")
            return
        if isinstance(loaded, dict):
            self.data.update(loaded)
        if not isinstance(self.data.get("installed"), dict):
            self.data["installed"] = {}

    def save(self) -> None:
        tmp = self.path.with_suffix(".tmp")
        try:
            tmp.write_text(json.dumps(self.data, ensure_ascii=False, indent=2), encoding="utf-8")
            os.replace(tmp, self.path)
        except OSError as exc:
            log.error("Не удалось сохранить конфиг: %s", exc)
            raise SkinChangerError(f"Не удалось сохранить настройки: {exc}") from exc

    def __getitem__(self, key: str):
        return self.data.get(key, DEFAULT_CONFIG.get(key))

    def __setitem__(self, key: str, value) -> None:
        self.data[key] = value

    @property
    def installed(self) -> dict:
        return self.data["installed"]


# =============================================================================
#  Dota 2: поиск папки, проверка процесса, папка модов
# =============================================================================
def is_valid_dota_path(path: str | Path) -> bool:
    if not path:
        return False
    root = Path(path)
    return (root / "game" / "bin" / "win64" / "dota2.exe").is_file() or (
        root / "game" / "dota" / "gameinfo.gi"
    ).is_file()


def _steam_install_dirs() -> list[Path]:
    result: list[Path] = []
    if sys.platform != "win32":
        return result
    import winreg

    keys = [
        (winreg.HKEY_CURRENT_USER, r"Software\Valve\Steam", "SteamPath"),
        (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\WOW6432Node\Valve\Steam", "InstallPath"),
        (winreg.HKEY_LOCAL_MACHINE, r"SOFTWARE\Valve\Steam", "InstallPath"),
    ]
    for hive, key, value in keys:
        try:
            with winreg.OpenKey(hive, key) as handle:
                steam_path = winreg.QueryValueEx(handle, value)[0]
                if steam_path:
                    result.append(Path(steam_path))
        except OSError:
            continue
    return result


def detect_dota_path() -> str | None:
    """Ищет Dota 2 через реестр Steam и libraryfolders.vdf."""
    libraries: list[Path] = []
    for steam in _steam_install_dirs():
        libraries.append(steam)
        vdf = steam / "steamapps" / "libraryfolders.vdf"
        if vdf.is_file():
            try:
                text = vdf.read_text(encoding="utf-8", errors="ignore")
            except OSError as exc:
                log.warning("Не удалось прочитать %s: %s", vdf, exc)
                text = ""
            for match in re.finditer(r'"path"\s+"([^"]+)"', text):
                libraries.append(Path(match.group(1).replace("\\\\", "\\")))

    candidates = [lib / "steamapps" / "common" / "dota 2 beta" for lib in libraries]
    for drive in ("C", "D", "E", "F"):
        candidates += [
            Path(f"{drive}:/Program Files (x86)/Steam/steamapps/common/dota 2 beta"),
            Path(f"{drive}:/Program Files/Steam/steamapps/common/dota 2 beta"),
            Path(f"{drive}:/Steam/steamapps/common/dota 2 beta"),
            Path(f"{drive}:/SteamLibrary/steamapps/common/dota 2 beta"),
        ]
    for candidate in candidates:
        if is_valid_dota_path(candidate):
            log.info("Dota 2 найдена: %s", candidate)
            return str(candidate)
    log.info("Dota 2 автоматически не найдена")
    return None


def is_dota_running() -> bool:
    for proc in psutil.process_iter(["name"]):
        try:
            name = (proc.info.get("name") or "").lower()
        except (psutil.NoSuchProcess, psutil.AccessDenied):
            continue
        if name in DOTA_PROCESS_NAMES:
            return True
    return False


def get_mods_dir(dota_path: str, language: str) -> Path:
    if not is_valid_dota_path(dota_path):
        raise SkinChangerError(
            "Путь к Dota 2 не указан или неверный.\n"
            "Откройте «Настройки» и укажите папку «dota 2 beta» "
            "(в ней должна быть game\\bin\\win64\\dota2.exe)."
        )
    if not LANG_RE.match(language or ""):
        raise SkinChangerError("Код языка должен состоять из латинских букв, цифр и «_» (2–32 символа).")
    return Path(dota_path) / "game" / f"dota_{language}"


def _assert_safe_mods_dir(directory: Path) -> None:
    """Никогда не трогаем основную папку game/dota и что-либо вне game/dota_*."""
    if directory.parent.name.lower() != "game" or not directory.name.lower().startswith("dota_"):
        raise SkinChangerError(f"Отказ: папка {directory} не похожа на папку модов (game/dota_<язык>).")


# =============================================================================
#  Сеть и каталог
# =============================================================================
_session = requests.Session()
_session.headers["User-Agent"] = f"{APP_NAME}/{APP_VERSION}"

REQUIRED_FIELDS = ("id", "name", "hero", "type", "preview_url", "vpk_url", "file_name", "file_size")


def _network_error(exc: Exception, what: str) -> SkinChangerError:
    if isinstance(exc, requests.Timeout):
        return SkinChangerError(f"{what}: сервер не ответил вовремя. Проверьте интернет и попробуйте ещё раз.")
    if isinstance(exc, requests.ConnectionError):
        return SkinChangerError(f"{what}: нет подключения к интернету или сервер недоступен.")
    if isinstance(exc, requests.HTTPError) and exc.response is not None:
        code = exc.response.status_code
        hint = " Файл не найден на сервере — проверьте URL." if code == 404 else ""
        return SkinChangerError(f"{what}: сервер вернул ошибку HTTP {code}.{hint}")
    return SkinChangerError(f"{what}: {exc}")


def parse_catalog(data) -> tuple[str, list[dict]]:
    if not isinstance(data, dict) or not isinstance(data.get("skins"), list):
        raise SkinChangerError("Неверный формат каталога: ожидается объект с массивом \"skins\".")
    skins: list[dict] = []
    seen: set[str] = set()
    for index, raw in enumerate(data["skins"]):
        if not isinstance(raw, dict):
            log.warning("Каталог: запись #%d не объект — пропущена", index)
            continue
        missing = [f for f in REQUIRED_FIELDS if f not in raw]
        if missing:
            log.warning("Каталог: запись #%d без полей %s — пропущена", index, missing)
            continue
        skin_id = str(raw["id"]).strip()
        file_name = str(raw["file_name"]).strip()
        if not skin_id or skin_id in seen:
            log.warning("Каталог: пустой или повторяющийся id «%s» — пропущен", skin_id)
            continue
        if not FILE_NAME_RE.match(file_name):
            log.warning("Каталог: недопустимое имя файла «%s» у %s — пропущено", file_name, skin_id)
            continue
        try:
            file_size = int(raw["file_size"])
        except (TypeError, ValueError):
            log.warning("Каталог: неверный file_size у %s — пропущено", skin_id)
            continue
        seen.add(skin_id)
        skins.append(
            {
                "id": skin_id,
                "name": str(raw["name"]),
                "hero": str(raw["hero"]),
                "type": str(raw["type"]),
                "preview_url": str(raw["preview_url"]),
                "vpk_url": str(raw["vpk_url"]),
                "file_name": file_name,
                "file_size": max(file_size, 0),
                "sha256": str(raw["sha256"]).lower() if raw.get("sha256") else None,
            }
        )
    return str(data.get("updated_at", "")), skins


def fetch_catalog(url: str) -> tuple[str, list[dict]]:
    log.info("Загрузка каталога: %s", url)
    try:
        response = _session.get(url, timeout=HTTP_TIMEOUT)
        response.raise_for_status()
        data = response.json()
    except ValueError as exc:
        raise SkinChangerError("Каталог по указанному URL не является корректным JSON.") from exc
    except requests.RequestException as exc:
        raise _network_error(exc, "Не удалось загрузить каталог") from exc
    result = parse_catalog(data)
    try:
        CATALOG_CACHE_PATH.write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")
    except OSError as exc:
        log.warning("Не удалось сохранить кэш каталога: %s", exc)
    log.info("Каталог загружен: %d скинов", len(result[1]))
    return result


def load_cached_catalog() -> tuple[str, list[dict]] | None:
    if not CATALOG_CACHE_PATH.is_file():
        return None
    try:
        return parse_catalog(json.loads(CATALOG_CACHE_PATH.read_text(encoding="utf-8")))
    except (OSError, json.JSONDecodeError, SkinChangerError) as exc:
        log.warning("Кэш каталога повреждён: %s", exc)
        return None


def download_file(url: str, dest: Path, expected_size: int, progress: Callable[[int, int], None]) -> None:
    part = dest.with_name(dest.name + ".part")
    log.info("Скачивание %s -> %s", url, dest)
    try:
        with _session.get(url, stream=True, timeout=HTTP_TIMEOUT) as response:
            response.raise_for_status()
            total = int(response.headers.get("Content-Length") or 0) or expected_size
            done = 0
            with open(part, "wb") as handle:
                for chunk in response.iter_content(chunk_size=256 * 1024):
                    if chunk:
                        handle.write(chunk)
                        done += len(chunk)
                        progress(done, total)
        os.replace(part, dest)
    except requests.RequestException as exc:
        part.unlink(missing_ok=True)
        raise _network_error(exc, "Не удалось скачать VPK") from exc
    except OSError as exc:
        part.unlink(missing_ok=True)
        raise SkinChangerError(f"Ошибка записи временного файла: {exc}") from exc


def verify_vpk(path: Path, skin: dict) -> None:
    if not path.is_file():
        raise SkinChangerError("Скачанный файл не найден.")
    if path.suffix.lower() != ".vpk" or not skin["file_name"].lower().endswith(".vpk"):
        raise SkinChangerError("Файл не является VPK (неверное расширение).")
    size = path.stat().st_size
    if size == 0:
        raise SkinChangerError("Скачанный файл пустой.")
    if skin["file_size"] and size != skin["file_size"]:
        raise SkinChangerError(
            f"Размер файла не совпадает с каталогом: получено {human_size(size)}, "
            f"ожидалось {human_size(skin['file_size'])}. Файл повреждён или каталог устарел."
        )
    if skin["file_name"].lower().endswith("_dir.vpk"):
        with open(path, "rb") as handle:
            header = handle.read(4)
        if len(header) < 4 or struct.unpack("<I", header)[0] != VPK_SIGNATURE:
            raise SkinChangerError("Файл не является корректным VPK (неверная сигнатура). Возможно, скачалась HTML-страница.")
    if skin.get("sha256"):
        digest = hashlib.sha256()
        with open(path, "rb") as handle:
            for block in iter(lambda: handle.read(1024 * 1024), b""):
                digest.update(block)
        if digest.hexdigest() != skin["sha256"]:
            raise SkinChangerError("Контрольная сумма SHA-256 не совпадает — файл повреждён.")


def load_preview_image(url: str) -> Image.Image:
    cache_file = PREVIEW_DIR / (hashlib.sha1(url.encode("utf-8")).hexdigest() + ".img")
    data: bytes | None = None
    if cache_file.is_file():
        try:
            data = cache_file.read_bytes()
            image = Image.open(BytesIO(data))
            image.load()
            return ImageOps.fit(image.convert("RGB"), PREVIEW_SIZE)
        except (OSError, Image.UnidentifiedImageError):
            cache_file.unlink(missing_ok=True)
    response = _session.get(url, timeout=HTTP_TIMEOUT)
    response.raise_for_status()
    data = response.content[: MAX_PREVIEW_BYTES + 1]
    if len(data) > MAX_PREVIEW_BYTES:
        raise SkinChangerError("Превью слишком большое")
    image = Image.open(BytesIO(data))
    image.load()
    try:
        cache_file.write_bytes(data)
    except OSError as exc:
        log.warning("Не удалось закэшировать превью: %s", exc)
    return ImageOps.fit(image.convert("RGB"), PREVIEW_SIZE)


# =============================================================================
#  Операции с файлами игры (выполняются в фоновом потоке)
# =============================================================================
def _permission_error(target: Path) -> SkinChangerError:
    return SkinChangerError(
        f"Нет прав на запись в {target}.\n"
        "Закройте Dota 2 и Steam или запустите приложение от имени администратора."
    )


def install_skin_files(
    skin: dict, mods_dir: Path, owned_files: set[str], progress: Callable[[int, int], None]
) -> Path:
    _assert_safe_mods_dir(mods_dir)
    try:
        TEMP_DIR.mkdir(parents=True, exist_ok=True)
    except OSError as exc:
        raise SkinChangerError(f"Не удалось создать временную папку: {exc}") from exc

    tmp_file = TEMP_DIR / f"{re.sub(r'[^A-Za-z0-9_.-]', '_', skin['id'])}__{skin['file_name']}"
    try:
        download_file(skin["vpk_url"], tmp_file, skin["file_size"], progress)
        verify_vpk(tmp_file, skin)

        target = mods_dir / skin["file_name"]
        staging = target.with_name(target.name + ".new")
        try:
            mods_dir.mkdir(parents=True, exist_ok=True)
            # Если в папке лежит чужой файл (например, официальная локализация Valve),
            # один раз делаем резервную копию, чтобы её можно было восстановить при удалении.
            if target.exists() and target.name.lower() not in owned_files:
                backup = target.with_name(target.name + ".bak")
                if not backup.exists():
                    shutil.copy2(target, backup)
                    log.info("Резервная копия чужого файла: %s", backup)
            shutil.copy2(tmp_file, staging)
            os.replace(staging, target)  # перезапись существующего файла
        except PermissionError as exc:
            staging.unlink(missing_ok=True)
            raise _permission_error(mods_dir) from exc
        except OSError as exc:
            staging.unlink(missing_ok=True)
            raise SkinChangerError(f"Ошибка копирования в папку игры: {exc}") from exc
        log.info("Установлен скин %s -> %s", skin["id"], target)
        return target
    finally:
        try:
            tmp_file.unlink(missing_ok=True)
        except OSError:
            log.warning("Не удалось удалить временный файл %s", tmp_file)


def remove_mod_file(target: Path) -> bool:
    """Удаляет VPK. Если есть .bak (оригинальный файл) — восстанавливает его. Возвращает True, если восстановлен бэкап."""
    _assert_safe_mods_dir(target.parent)
    backup = target.with_name(target.name + ".bak")
    try:
        if target.exists():
            target.unlink()
            log.info("Удалён мод %s", target)
        else:
            log.info("Файл мода уже отсутствует: %s", target)
        if backup.exists():
            os.replace(backup, target)
            log.info("Восстановлен оригинал %s", target)
            return True
    except PermissionError as exc:
        raise _permission_error(target.parent) from exc
    except OSError as exc:
        raise SkinChangerError(f"Не удалось удалить {target.name}: {exc}") from exc
    return False


def reset_mod_dirs(directories: set[Path]) -> tuple[int, int]:
    """Удаляет все *.vpk (и недокачанные .part/.new) из папок модов. Восстанавливает .bak."""
    removed = restored = 0
    for directory in directories:
        _assert_safe_mods_dir(directory)
        if not directory.is_dir():
            continue
        try:
            for item in directory.iterdir():
                name = item.name.lower()
                if item.is_file() and (name.endswith(".vpk") or name.endswith(".vpk.part") or name.endswith(".vpk.new")):
                    item.unlink()
                    removed += 1
                    log.info("Сброс: удалён %s", item)
            for backup in directory.glob("*.vpk.bak"):
                os.replace(backup, backup.with_name(backup.name[: -len(".bak")]))
                restored += 1
                log.info("Сброс: восстановлен %s", backup)
        except PermissionError as exc:
            raise _permission_error(directory) from exc
        except OSError as exc:
            raise SkinChangerError(f"Ошибка при сбросе модов в {directory}: {exc}") from exc
    return removed, restored


# =============================================================================
#  Утилиты
# =============================================================================
def human_size(size: int) -> str:
    value = float(size)
    for unit in ("Б", "КБ", "МБ", "ГБ"):
        if value < 1024 or unit == "ГБ":
            return f"{value:.0f} {unit}" if unit == "Б" else f"{value:.1f} {unit}"
        value /= 1024
    return f"{size} Б"


def open_folder(path: Path) -> None:
    if sys.platform == "win32":
        os.startfile(str(path))  # noqa: S606 — открываем папку в Проводнике
    elif sys.platform == "darwin":
        subprocess.Popen(["open", str(path)])
    else:
        subprocess.Popen(["xdg-open", str(path)])


# =============================================================================
#  Диалог первого запуска
# =============================================================================
class RiskDialog(ctk.CTkToplevel):
    def __init__(self, master: ctk.CTk):
        super().__init__(master)
        self.accepted = False
        self.title("Предупреждение")
        self.geometry("600x430")
        self.resizable(False, False)
        self.transient(master)

        ctk.CTkLabel(self, text="⚠  Моды — на ваш риск", font=ctk.CTkFont(size=20, weight="bold")).pack(pady=(20, 10))
        box = ctk.CTkTextbox(self, wrap="word", height=230, font=ctk.CTkFont(size=13))
        box.insert("1.0", RISK_TEXT)
        box.configure(state="disabled")
        box.pack(fill="both", expand=True, padx=20)

        self.agree_var = ctk.BooleanVar(value=False)
        ctk.CTkCheckBox(
            self, text="Я понимаю риски и принимаю их", variable=self.agree_var, command=self._toggle
        ).pack(pady=12)

        buttons = ctk.CTkFrame(self, fg_color="transparent")
        buttons.pack(pady=(0, 18))
        self.ok_button = ctk.CTkButton(buttons, text="Продолжить", state="disabled", command=self._accept)
        self.ok_button.pack(side="left", padx=8)
        ctk.CTkButton(buttons, text="Выйти", fg_color="gray30", hover_color="gray25", command=self._decline).pack(
            side="left", padx=8
        )
        self.protocol("WM_DELETE_WINDOW", self._decline)
        self.after(150, self._grab)

    def _grab(self) -> None:
        try:
            self.lift()
            self.focus_force()
            self.grab_set()
        except TclError:
            log.warning("Не удалось сделать окно предупреждения модальным")

    def _toggle(self) -> None:
        self.ok_button.configure(state="normal" if self.agree_var.get() else "disabled")

    def _accept(self) -> None:
        self.accepted = True
        self.destroy()

    def _decline(self) -> None:
        self.accepted = False
        self.destroy()


# =============================================================================
#  Главное окно
# =============================================================================
class SkinChangerApp(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.config_store = Config(CONFIG_PATH)
        self.skins: list[dict] = []
        self.catalog_updated_at = ""
        self.busy = False
        self.ui_queue: "queue.Queue[Callable[[], None]]" = queue.Queue()
        self.executor = ThreadPoolExecutor(max_workers=6, thread_name_prefix="preview")
        self.preview_images: dict[str, ctk.CTkImage] = {}
        self._search_job: str | None = None
        self._last_percent = -1

        self.title(f"{APP_TITLE} {APP_VERSION}")
        self.geometry("1180x760")
        self.minsize(980, 600)
        self.report_callback_exception = self._on_tk_exception
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        self._build_ui()
        self.after(50, self._process_queue)
        self.after(300, self._startup)

    # ---------- построение интерфейса ----------
    def _build_ui(self) -> None:
        self.grid_columnconfigure(0, weight=1)
        self.grid_rowconfigure(0, weight=1)

        self.tabs = ctk.CTkTabview(self)
        self.tabs.grid(row=0, column=0, sticky="nsew", padx=12, pady=(8, 0))
        self.tab_catalog = self.tabs.add("Каталог")
        self.tab_installed = self.tabs.add("Установленные")
        self.tab_settings = self.tabs.add("Настройки")

        self._build_catalog_tab()
        self._build_installed_tab()
        self._build_settings_tab()
        self._build_status_bar()

    def _build_catalog_tab(self) -> None:
        tab = self.tab_catalog
        tab.grid_columnconfigure(0, weight=1)
        tab.grid_rowconfigure(1, weight=1)

        bar = ctk.CTkFrame(tab, fg_color="transparent")
        bar.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        bar.grid_columnconfigure(0, weight=1)

        self.search_var = ctk.StringVar()
        search = ctk.CTkEntry(bar, textvariable=self.search_var, placeholder_text="Поиск по названию или герою…")
        search.grid(row=0, column=0, sticky="ew", padx=(0, 8))
        search.bind("<KeyRelease>", lambda _e: self._schedule_render())

        self.hero_var = ctk.StringVar(value=ALL_HEROES)
        self.hero_menu = ctk.CTkOptionMenu(bar, variable=self.hero_var, values=[ALL_HEROES], width=170,
                                           command=lambda _v: self.render_catalog())
        self.hero_menu.grid(row=0, column=1, padx=4)

        self.type_var = ctk.StringVar(value=ALL_TYPES)
        self.type_menu = ctk.CTkOptionMenu(bar, variable=self.type_var, values=[ALL_TYPES], width=150,
                                           command=lambda _v: self.render_catalog())
        self.type_menu.grid(row=0, column=2, padx=4)

        ctk.CTkButton(bar, text="⟳ Обновить", width=110, command=lambda: self.refresh_catalog(silent=False)).grid(
            row=0, column=3, padx=(4, 0)
        )

        self.catalog_frame = ctk.CTkScrollableFrame(tab)
        self.catalog_frame.grid(row=1, column=0, sticky="nsew")
        for col in range(CATALOG_COLUMNS):
            self.catalog_frame.grid_columnconfigure(col, weight=1)

        self.catalog_info = ctk.CTkLabel(tab, text="", anchor="w", text_color="gray60")
        self.catalog_info.grid(row=2, column=0, sticky="ew", pady=(4, 0))

    def _build_installed_tab(self) -> None:
        tab = self.tab_installed
        tab.grid_columnconfigure(0, weight=1)
        tab.grid_rowconfigure(1, weight=1)

        bar = ctk.CTkFrame(tab, fg_color="transparent")
        bar.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        ctk.CTkButton(bar, text="Обновить список", command=self.render_installed).pack(side="left")
        ctk.CTkButton(bar, text="Открыть папку модов", command=self.open_mods_folder).pack(side="left", padx=8)
        ctk.CTkButton(bar, text="Сбросить все моды", fg_color="#a83232", hover_color="#8a2828",
                      command=self.reset_all_mods).pack(side="right")

        self.installed_frame = ctk.CTkScrollableFrame(tab)
        self.installed_frame.grid(row=1, column=0, sticky="nsew")
        self.installed_frame.grid_columnconfigure(0, weight=1)

    def _build_settings_tab(self) -> None:
        tab = self.tab_settings
        tab.grid_columnconfigure(1, weight=1)
        pad = {"padx": 8, "pady": 8}

        # Путь к Dota 2
        ctk.CTkLabel(tab, text="Папка Dota 2:", anchor="w").grid(row=0, column=0, sticky="w", **pad)
        self.path_var = ctk.StringVar(value=self.config_store["dota_path"])
        ctk.CTkEntry(tab, textvariable=self.path_var).grid(row=0, column=1, sticky="ew", **pad)
        path_buttons = ctk.CTkFrame(tab, fg_color="transparent")
        path_buttons.grid(row=0, column=2, sticky="e", **pad)
        ctk.CTkButton(path_buttons, text="Обзор…", width=90, command=self._browse_dota).pack(side="left", padx=2)
        ctk.CTkButton(path_buttons, text="Найти", width=90, command=self._autodetect_dota).pack(side="left", padx=2)
        self.path_status = ctk.CTkLabel(tab, text="", anchor="w")
        self.path_status.grid(row=1, column=1, columnspan=2, sticky="w", padx=8)

        # Язык (папка dota_<код>)
        ctk.CTkLabel(tab, text="Язык (папка модов):", anchor="w").grid(row=2, column=0, sticky="w", **pad)
        self.lang_var = ctk.StringVar(value=self.config_store["language"])
        ctk.CTkComboBox(tab, variable=self.lang_var, values=LANG_PRESETS, width=200,
                        command=lambda _v: self._update_lang_hint()).grid(row=2, column=1, sticky="w", **pad)
        self.lang_var.trace_add("write", lambda *_a: self._update_lang_hint())
        self.lang_hint = ctk.CTkLabel(tab, text="", anchor="w", justify="left", text_color="gray70")
        self.lang_hint.grid(row=3, column=1, columnspan=2, sticky="w", padx=8)
        ctk.CTkButton(tab, text="Скопировать параметр запуска", command=self._copy_launch_option).grid(
            row=4, column=1, sticky="w", **pad
        )

        # URL каталога
        ctk.CTkLabel(tab, text="URL каталога:", anchor="w").grid(row=5, column=0, sticky="w", **pad)
        self.url_var = ctk.StringVar(value=self.config_store["catalog_url"])
        ctk.CTkEntry(tab, textvariable=self.url_var).grid(row=5, column=1, columnspan=2, sticky="ew", **pad)

        self.auto_update_var = ctk.BooleanVar(value=bool(self.config_store["auto_update_catalog"]))
        ctk.CTkCheckBox(tab, text="Обновлять каталог при запуске", variable=self.auto_update_var).grid(
            row=6, column=1, sticky="w", **pad
        )

        buttons = ctk.CTkFrame(tab, fg_color="transparent")
        buttons.grid(row=7, column=0, columnspan=3, sticky="w", padx=8, pady=(16, 8))
        ctk.CTkButton(buttons, text="Сохранить настройки", command=self.save_settings).pack(side="left", padx=4)
        ctk.CTkButton(buttons, text="Проверить обновления каталога",
                      command=lambda: self.refresh_catalog(silent=False)).pack(side="left", padx=4)
        ctk.CTkButton(buttons, text="Открыть папку модов", command=self.open_mods_folder).pack(side="left", padx=4)
        ctk.CTkButton(buttons, text="Открыть лог", fg_color="gray30", hover_color="gray25",
                      command=lambda: self._safe_open(APP_DIR)).pack(side="left", padx=4)

        self.catalog_date_label = ctk.CTkLabel(tab, text="", anchor="w", text_color="gray60")
        self.catalog_date_label.grid(row=8, column=0, columnspan=3, sticky="w", padx=8)

        ctk.CTkLabel(
            tab,
            text="⚠ Использование модов — на ваш риск. Valve может заблокировать аккаунт за модификацию клиента.",
            text_color="#e0a030", anchor="w",
        ).grid(row=9, column=0, columnspan=3, sticky="w", padx=8, pady=(20, 0))

        self._update_path_status()
        self._update_lang_hint()

    def _build_status_bar(self) -> None:
        bar = ctk.CTkFrame(self, height=36, corner_radius=0)
        bar.grid(row=1, column=0, sticky="ew", pady=(8, 0))
        bar.grid_columnconfigure(0, weight=1)
        self.status_label = ctk.CTkLabel(bar, text="Готово", anchor="w")
        self.status_label.grid(row=0, column=0, sticky="ew", padx=12, pady=6)
        self.progress = ctk.CTkProgressBar(bar, width=260)
        self.progress.set(0)
        self.progress.grid(row=0, column=1, padx=8)
        self.dota_label = ctk.CTkLabel(bar, text="Dota 2: проверка…", width=170, anchor="e")
        self.dota_label.grid(row=0, column=2, padx=12)

    # ---------- очередь UI и фоновые задачи ----------
    def _process_queue(self) -> None:
        try:
            while True:
                callback = self.ui_queue.get_nowait()
                try:
                    callback()
                except Exception:  # noqa: BLE001 — UI не должен падать из-за одного колбэка
                    log.exception("Ошибка в UI-колбэке")
        except queue.Empty:
            pass
        self.after(50, self._process_queue)

    def run_task(self, description: str, job: Callable[[], object],
                 on_success: Callable[[object], None] | None = None,
                 on_error: Callable[[str], None] | None = None) -> None:
        if self.busy:
            messagebox.showinfo(APP_TITLE, "Дождитесь окончания текущей операции.")
            return
        self.busy = True
        self._last_percent = -1
        self.set_status(description)
        self.progress.configure(mode="indeterminate")
        self.progress.start()

        def worker() -> None:
            try:
                result = job()
            except SkinChangerError as exc:
                log.error("%s — %s", description, exc)
                self.ui_queue.put(lambda msg=str(exc): self._task_failed(msg, on_error))
            except Exception as exc:  # noqa: BLE001
                log.exception("Непредвиденная ошибка: %s", description)
                self.ui_queue.put(lambda msg=f"Непредвиденная ошибка: {exc}": self._task_failed(msg, on_error))
            else:
                self.ui_queue.put(lambda res=result: self._task_done(res, on_success))

        threading.Thread(target=worker, daemon=True).start()

    def _finish_progress(self, value: float) -> None:
        self.progress.stop()
        self.progress.configure(mode="determinate")
        self.progress.set(value)
        self.busy = False

    def _task_done(self, result: object, on_success) -> None:
        self._finish_progress(1)
        if on_success:
            on_success(result)

    def _task_failed(self, message: str, on_error) -> None:
        self._finish_progress(0)
        self.set_status("Ошибка: " + message.splitlines()[0])
        if on_error:
            on_error(message)
        else:
            messagebox.showerror(APP_TITLE, message)

    def _progress_from_worker(self, done: int, total: int) -> None:
        if total <= 0:
            return
        percent = min(100, int(done * 100 / total))
        if percent != self._last_percent:
            self._last_percent = percent
            self.ui_queue.put(lambda d=done, t=total, p=percent: self._show_progress(d, t, p))

    def _show_progress(self, done: int, total: int, percent: int) -> None:
        if str(self.progress.cget("mode")) != "determinate":
            self.progress.stop()
            self.progress.configure(mode="determinate")
        self.progress.set(percent / 100)
        self.set_status(f"Скачивание: {human_size(done)} / {human_size(total)} ({percent}%)")

    def set_status(self, text: str) -> None:
        self.status_label.configure(text=text)

    # ---------- запуск ----------
    def _startup(self) -> None:
        if not self.config_store["accepted_risk"]:
            dialog = RiskDialog(self)
            self.wait_window(dialog)
            if not dialog.accepted:
                log.info("Пользователь отказался от условий — выход")
                self._on_close()
                return
            self.config_store["accepted_risk"] = True
            self._save_config_quiet()

        if not is_valid_dota_path(self.config_store["dota_path"]):
            found = detect_dota_path()
            if found:
                self.config_store["dota_path"] = found
                self.path_var.set(found)
                self._save_config_quiet()
        self._update_path_status()

        cached = load_cached_catalog()
        if cached:
            self._apply_catalog(cached, from_cache=True)
        else:
            self.render_catalog()
        self.render_installed()
        self._poll_dota()

        if self.config_store["auto_update_catalog"]:
            self.refresh_catalog(silent=cached is not None)
        elif not cached:
            self.set_status("Каталог не загружен. Нажмите «Обновить».")

        if not is_valid_dota_path(self.config_store["dota_path"]):
            messagebox.showwarning(APP_TITLE, "Dota 2 не найдена автоматически. Укажите путь во вкладке «Настройки».")
            self.tabs.set("Настройки")

    def _save_config_quiet(self) -> None:
        try:
            self.config_store.save()
        except SkinChangerError as exc:
            messagebox.showerror(APP_TITLE, str(exc))

    # ---------- каталог ----------
    def refresh_catalog(self, silent: bool = False) -> None:
        url = self.config_store["catalog_url"]

        def on_error(message: str) -> None:
            if self.skins:
                self.set_status("Не удалось обновить каталог — показана сохранённая версия.")
                if not silent:
                    messagebox.showwarning(APP_TITLE, message + "\n\nПоказана последняя сохранённая версия каталога.")
            else:
                messagebox.showerror(APP_TITLE, message)

        self.run_task("Загрузка каталога…", lambda: fetch_catalog(url),
                      lambda res: self._apply_catalog(res, from_cache=False), on_error)

    def _apply_catalog(self, result, from_cache: bool) -> None:
        self.catalog_updated_at, self.skins = result
        heroes = [ALL_HEROES] + sorted({s["hero"] for s in self.skins}, key=str.lower)
        types = [ALL_TYPES] + sorted({s["type"] for s in self.skins}, key=str.lower)
        self.hero_menu.configure(values=heroes)
        self.type_menu.configure(values=types)
        if self.hero_var.get() not in heroes:
            self.hero_var.set(ALL_HEROES)
        if self.type_var.get() not in types:
            self.type_var.set(ALL_TYPES)
        date = self.catalog_updated_at or "неизвестно"
        self.catalog_date_label.configure(text=f"Каталог обновлён на сервере: {date}")
        source = "из кэша" if from_cache else "с сервера"
        self.set_status(f"Каталог загружен {source}: {len(self.skins)} скинов")
        self.render_catalog()

    def _schedule_render(self) -> None:
        if self._search_job:
            self.after_cancel(self._search_job)
        self._search_job = self.after(300, self.render_catalog)

    def _filtered_skins(self) -> list[dict]:
        query = self.search_var.get().strip().lower()
        hero = self.hero_var.get()
        skin_type = self.type_var.get()
        result = []
        for skin in self.skins:
            if hero != ALL_HEROES and skin["hero"] != hero:
                continue
            if skin_type != ALL_TYPES and skin["type"] != skin_type:
                continue
            if query and query not in skin["name"].lower() and query not in skin["hero"].lower():
                continue
            result.append(skin)
        return result

    def render_catalog(self) -> None:
        self._search_job = None
        for widget in self.catalog_frame.winfo_children():
            widget.destroy()
        filtered = self._filtered_skins()
        if not filtered:
            text = "Ничего не найдено." if self.skins else "Каталог пуст или ещё не загружен."
            ctk.CTkLabel(self.catalog_frame, text=text, text_color="gray60").grid(
                row=0, column=0, columnspan=CATALOG_COLUMNS, pady=40)
        for index, skin in enumerate(filtered):
            card = self._build_card(skin)
            card.grid(row=index // CATALOG_COLUMNS, column=index % CATALOG_COLUMNS, padx=8, pady=8, sticky="n")
        self.catalog_info.configure(text=f"Показано {len(filtered)} из {len(self.skins)}")

    def _build_card(self, skin: dict) -> ctk.CTkFrame:
        card = ctk.CTkFrame(self.catalog_frame, corner_radius=10)
        image_label = ctk.CTkLabel(card, text="Загрузка…", width=PREVIEW_SIZE[0], height=PREVIEW_SIZE[1],
                                   fg_color=("gray78", "gray22"), corner_radius=6)
        image_label.pack(padx=8, pady=(8, 6))
        self._load_preview_async(skin["preview_url"], image_label)

        ctk.CTkLabel(card, text=skin["name"], font=ctk.CTkFont(size=14, weight="bold"),
                     wraplength=PREVIEW_SIZE[0], justify="center").pack(padx=8)
        ctk.CTkLabel(card, text=f"{skin['hero']} • {skin['type']}", text_color="gray65").pack(padx=8)
        size_text = human_size(skin["file_size"]) if skin["file_size"] else "размер неизвестен"
        ctk.CTkLabel(card, text=f"{skin['file_name']} • {size_text}", text_color="gray50",
                     font=ctk.CTkFont(size=11)).pack(padx=8)

        installed = skin["id"] in self.config_store.installed
        ctk.CTkButton(
            card,
            text="Переустановить" if installed else "Установить",
            fg_color="#2f7d46" if installed else None,
            hover_color="#256338" if installed else None,
            command=lambda s=skin: self.install_skin(s),
        ).pack(fill="x", padx=8, pady=(6, 10))
        return card

    def _load_preview_async(self, url: str, label: ctk.CTkLabel) -> None:
        if not url:
            label.configure(text="Нет превью")
            return
        if url in self.preview_images:
            label.configure(image=self.preview_images[url], text="")
            return

        def work() -> None:
            try:
                image = load_preview_image(url)
            except Exception as exc:  # noqa: BLE001 — превью не критично
                log.warning("Превью не загружено (%s): %s", url, exc)
                self.ui_queue.put(lambda: self._set_label(label, text="Нет превью"))
                return
            self.ui_queue.put(lambda: self._apply_preview(url, image, label))

        self.executor.submit(work)

    def _apply_preview(self, url: str, image: Image.Image, label: ctk.CTkLabel) -> None:
        if url not in self.preview_images:
            self.preview_images[url] = ctk.CTkImage(light_image=image, dark_image=image, size=PREVIEW_SIZE)
        self._set_label(label, image=self.preview_images[url], text="")

    @staticmethod
    def _set_label(label: ctk.CTkLabel, **kwargs) -> None:
        try:
            if label.winfo_exists():
                label.configure(**kwargs)
        except TclError:
            pass  # карточка уже удалена (пользователь сменил фильтр)

    # ---------- установка / удаление ----------
    def _require_mods_dir(self) -> Path | None:
        try:
            return get_mods_dir(self.config_store["dota_path"], self.config_store["language"])
        except SkinChangerError as exc:
            messagebox.showerror(APP_TITLE, str(exc))
            self.tabs.set("Настройки")
            return None

    def _ensure_dota_closed(self) -> bool:
        if is_dota_running():
            messagebox.showwarning(APP_TITLE, "Dota 2 запущена. Закройте игру перед изменением модов.")
            return False
        return True

    def install_skin(self, skin: dict) -> None:
        if self.busy:
            messagebox.showinfo(APP_TITLE, "Дождитесь окончания текущей операции.")
            return
        mods_dir = self._require_mods_dir()
        if mods_dir is None or not self._ensure_dota_closed():
            return

        installed = self.config_store.installed
        target = mods_dir / skin["file_name"]
        conflicts = [
            sid for sid, entry in installed.items()
            if sid != skin["id"] and Path(entry.get("path", "")).resolve() == target.resolve()
        ]
        if conflicts:
            names = ", ".join(f"«{installed[c]['name']}»" for c in conflicts)
            if not messagebox.askyesno(
                APP_TITLE,
                f"Файл {skin['file_name']} уже занят модом {names}.\n"
                "В одной папке может быть только один файл с этим именем — старый мод будет заменён.\n\nПродолжить?",
            ):
                return

        owned = {Path(e.get("path", "")).name.lower() for e in installed.values()
                 if Path(e.get("path", "")).parent == mods_dir}

        def job() -> Path:
            return install_skin_files(skin, mods_dir, owned, self._progress_from_worker)

        def done(result) -> None:
            for sid in conflicts:
                installed.pop(sid, None)
            installed[skin["id"]] = {
                "name": skin["name"],
                "hero": skin["hero"],
                "type": skin["type"],
                "file_name": skin["file_name"],
                "path": str(result),
                "installed_at": datetime.now().strftime("%Y-%m-%d %H:%M"),
            }
            self._save_config_quiet()
            self.render_catalog()
            self.render_installed()
            lang = self.config_store["language"]
            self.set_status(f"Установлено: {skin['name']} → {result}")
            messagebox.showinfo(
                APP_TITLE,
                f"«{skin['name']}» установлен.\n\nНе забудьте параметр запуска Dota 2 в Steam:\n-language {lang}",
            )

        self.run_task(f"Установка «{skin['name']}»…", job, done)

    def remove_skin(self, skin_id: str) -> None:
        entry = self.config_store.installed.get(skin_id)
        if entry is None or not self._ensure_dota_closed():
            return
        if not messagebox.askyesno(APP_TITLE, f"Удалить мод «{entry['name']}»?"):
            return
        target = Path(entry["path"])

        def done(restored) -> None:
            self.config_store.installed.pop(skin_id, None)
            self._save_config_quiet()
            self.render_installed()
            self.render_catalog()
            extra = " (оригинальный файл восстановлен)" if restored else ""
            self.set_status(f"Удалено: {entry['name']}{extra}")

        self.run_task(f"Удаление «{entry['name']}»…", lambda: remove_mod_file(target), done)

    def reset_all_mods(self) -> None:
        if not self._ensure_dota_closed():
            return
        directories: set[Path] = {Path(e["path"]).parent for e in self.config_store.installed.values() if e.get("path")}
        try:
            directories.add(get_mods_dir(self.config_store["dota_path"], self.config_store["language"]))
        except SkinChangerError:
            log.info("Текущая папка модов недоступна — сбрасываем только известные папки")
        if not directories:
            messagebox.showinfo(APP_TITLE, "Нет установленных модов и не задана папка игры.")
            return
        listing = "\n".join(str(d) for d in sorted(directories))
        if not messagebox.askyesno(APP_TITLE, f"Удалить ВСЕ .vpk из папок модов?\n\n{listing}"):
            return

        def done(result) -> None:
            removed, restored = result
            self.config_store.installed.clear()
            self._save_config_quiet()
            self.render_installed()
            self.render_catalog()
            self.set_status(f"Сброс выполнен: удалено файлов — {removed}, восстановлено оригиналов — {restored}")

        self.run_task("Сброс всех модов…", lambda: reset_mod_dirs(directories), done)

    def render_installed(self) -> None:
        for widget in self.installed_frame.winfo_children():
            widget.destroy()
        installed = self.config_store.installed
        if not installed:
            ctk.CTkLabel(self.installed_frame, text="Установленных модов нет.", text_color="gray60").grid(
                row=0, column=0, pady=40)
            return
        for row, (skin_id, entry) in enumerate(sorted(installed.items(), key=lambda kv: kv[1].get("name", ""))):
            path = Path(entry.get("path", ""))
            exists = path.is_file()
            item = ctk.CTkFrame(self.installed_frame)
            item.grid(row=row, column=0, sticky="ew", padx=4, pady=4)
            item.grid_columnconfigure(0, weight=1)
            ctk.CTkLabel(item, text=f"{entry.get('name', skin_id)}  —  {entry.get('hero', '')}",
                         font=ctk.CTkFont(size=14, weight="bold"), anchor="w").grid(
                row=0, column=0, sticky="w", padx=10, pady=(8, 0))
            status = "✓ установлен" if exists else "✗ файл отсутствует (удалён вручную или Steam восстановил файлы)"
            ctk.CTkLabel(item, text=f"{path}  •  {entry.get('installed_at', '')}  •  {status}",
                         text_color="gray60" if exists else "#d06060", anchor="w").grid(
                row=1, column=0, sticky="w", padx=10, pady=(0, 8))
            ctk.CTkButton(item, text="Удалить", width=100, fg_color="#a83232", hover_color="#8a2828",
                          command=lambda sid=skin_id: self.remove_skin(sid)).grid(
                row=0, column=1, rowspan=2, padx=10)

    # ---------- настройки ----------
    def _browse_dota(self) -> None:
        folder = filedialog.askdirectory(title="Выберите папку «dota 2 beta»")
        if folder:
            self.path_var.set(str(Path(folder)))
            self._update_path_status(self.path_var.get())

    def _autodetect_dota(self) -> None:
        found = detect_dota_path()
        if found:
            self.path_var.set(found)
            self._update_path_status(found)
            self.set_status("Dota 2 найдена. Нажмите «Сохранить настройки».")
        else:
            messagebox.showwarning(APP_TITLE, "Не удалось найти Dota 2 автоматически. Укажите папку вручную.")

    def _update_path_status(self, path: str | None = None) -> None:
        path = self.config_store["dota_path"] if path is None else path
        if is_valid_dota_path(path):
            self.path_status.configure(text="✓ Папка Dota 2 корректна", text_color="#4caf50")
        else:
            self.path_status.configure(text="✗ Dota 2 не найдена по этому пути", text_color="#d06060")

    def _update_lang_hint(self) -> None:
        lang = self.lang_var.get().strip().lower()
        if LANG_RE.match(lang):
            self.lang_hint.configure(
                text=f"Моды будут в: game\\dota_{lang}\\\n"
                     f"Параметр запуска в Steam (Dota 2 → Свойства → Параметры запуска):  -language {lang}")
        else:
            self.lang_hint.configure(text="Недопустимый код: только a–z, 0–9 и «_», 2–32 символа.")

    def _copy_launch_option(self) -> None:
        lang = self.lang_var.get().strip().lower()
        self.clipboard_clear()
        self.clipboard_append(f"-language {lang}")
        self.set_status(f"Скопировано: -language {lang}")

    def save_settings(self) -> None:
        path = self.path_var.get().strip().strip('"')
        lang = self.lang_var.get().strip().lower()
        url = self.url_var.get().strip()
        if path and not is_valid_dota_path(path):
            messagebox.showerror(APP_TITLE, "Неверный путь к Dota 2: не найден game\\bin\\win64\\dota2.exe.")
            return
        if not LANG_RE.match(lang):
            messagebox.showerror(APP_TITLE, "Неверный код языка: только a–z, 0–9 и «_», 2–32 символа.")
            return
        if not url.lower().startswith(("http://", "https://")):
            messagebox.showerror(APP_TITLE, "URL каталога должен начинаться с http:// или https://")
            return
        url_changed = url != self.config_store["catalog_url"]
        self.config_store["dota_path"] = path
        self.config_store["language"] = lang
        self.config_store["catalog_url"] = url
        self.config_store["auto_update_catalog"] = bool(self.auto_update_var.get())
        self._save_config_quiet()
        self._update_path_status()
        self.set_status("Настройки сохранены")
        log.info("Настройки сохранены: path=%s lang=%s url=%s", path, lang, url)
        if url_changed:
            self.refresh_catalog(silent=False)

    def open_mods_folder(self) -> None:
        mods_dir = self._require_mods_dir()
        if mods_dir is None:
            return
        try:
            mods_dir.mkdir(parents=True, exist_ok=True)
        except PermissionError:
            messagebox.showerror(APP_TITLE, str(_permission_error(mods_dir)))
            return
        except OSError as exc:
            messagebox.showerror(APP_TITLE, f"Не удалось создать папку: {exc}")
            return
        self._safe_open(mods_dir)

    def _safe_open(self, path: Path) -> None:
        try:
            open_folder(path)
        except OSError as exc:
            messagebox.showerror(APP_TITLE, f"Не удалось открыть папку {path}: {exc}")

    # ---------- статус Dota 2 ----------
    def _poll_dota(self) -> None:
        def work() -> None:
            try:
                running = is_dota_running()
            except psutil.Error as exc:
                log.warning("Не удалось проверить процессы: %s", exc)
                return
            self.ui_queue.put(lambda r=running: self.dota_label.configure(
                text="Dota 2: запущена ⚠" if r else "Dota 2: не запущена",
                text_color="#e0a030" if r else "gray60"))

        threading.Thread(target=work, daemon=True).start()
        self.after(5000, self._poll_dota)

    # ---------- завершение и ошибки ----------
    def _on_tk_exception(self, exc_type, exc_value, exc_tb) -> None:
        log.error("Необработанная ошибка UI", exc_info=(exc_type, exc_value, exc_tb))
        messagebox.showerror(APP_TITLE, f"Произошла ошибка: {exc_value}\nПодробности в {LOG_PATH}")

    def _on_close(self) -> None:
        self.executor.shutdown(wait=False, cancel_futures=True)
        log.info("Приложение закрыто")
        self.destroy()


def main() -> None:
    ctk.set_appearance_mode("dark")
    ctk.set_default_color_theme("blue")
    log.info("Запуск %s %s", APP_TITLE, APP_VERSION)
    app = SkinChangerApp()
    app.mainloop()


if __name__ == "__main__":
    main()
