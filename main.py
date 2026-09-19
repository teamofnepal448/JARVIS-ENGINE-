# -*- coding: utf-8 -*-
"""
JARVIS CORE v2 - agentic telegram operations system (fresh, 3-file project).

Pipeline (no fixed commands, goals only):
  UNDERSTAND -> CONTEXT -> RESOLVE -> DISCOVER TOOL -> PLAN -> VALIDATE
  -> EXECUTE -> VERIFY -> REMEMBER -> REPORT

Source files: main.py | index.html | requirements.txt
Runtime JSON (auto-created): data/
  accounts.json sessions.json brain.json workflows.json tasks.json
  monitors.json scheduled_jobs.json channel_memory.json runtime.json tools.json
"""
from __future__ import annotations

import asyncio
import json
import logging
import os
import re
import shutil
import sys
import time
import uuid
from collections import deque
from contextlib import asynccontextmanager
from dataclasses import dataclass, field
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Any, Awaitable, Callable, Optional

# ----------------------------------------------------------------------------
# 0. ENV / CONSTANTS  (Render: bind 0.0.0.0 + PORT)
# ----------------------------------------------------------------------------

ROOT = Path(__file__).resolve().parent
DATA_DIR = ROOT / "data"
DATA_DIR.mkdir(parents=True, exist_ok=True)

HOST = os.environ.get("JARVIS_HOST") or "0.0.0.0"
PORT = int(os.environ.get("PORT") or os.environ.get("JARVIS_PORT") or "8090")
ENV_API_ID = (os.environ.get("JARVIS_API_ID") or "").strip()
ENV_API_HASH = (os.environ.get("JARVIS_API_HASH") or "").strip()
OPENAI_BASE_URL = (os.environ.get("OPENAI_BASE_URL") or "https://api.openai.com/v1").rstrip("/")
OPENAI_API_KEY = (os.environ.get("OPENAI_API_KEY") or "").strip()
OPENAI_MODEL = os.environ.get("OPENAI_MODEL") or "gpt-4o-mini"

SCHEMA_VERSION = 2
CONTEXT_TTL = 30 * 60
CONFIRM_TTL = 90
KTM = timezone(timedelta(hours=5, minutes=45), name="Asia/Kathmandu")

MAX_ACCOUNTS = 6
MAX_ACTIVE_TASKS = 30
MAX_MONITORS = 30
MAX_SCHEDULES = 50
MAX_TARGETS = 60
MAX_ERRORS_PER_TASK = 6
TICK_SECONDS = 45
DIAG_BUFFER = 300

# task statuses
TS_PLANNING = "PLANNING"
TS_RUNNING = "RUNNING"
TS_WAITING = "WAITING"
TS_MONITORING = "MONITORING"
TS_PAUSED = "PAUSED"
TS_COMPLETED = "COMPLETED"
TS_FAILED = "FAILED"
TS_STOPPED = "STOPPED"
TS_EXPIRED = "EXPIRED"
TS_ACTIVE_SET = {TS_PLANNING, TS_RUNNING, TS_MONITORING}
TS_TERMINAL = {TS_COMPLETED, TS_FAILED, TS_STOPPED, TS_EXPIRED}
TS_CONTROLLABLE = TS_ACTIVE_SET | {TS_PAUSED, TS_WAITING}

# structured error codes
ERR_ENTITY_NOT_FOUND = "ENTITY_NOT_FOUND"
ERR_PERMISSION_DENIED = "PERMISSION_DENIED"
ERR_CHANNEL_PRIVATE = "CHANNEL_PRIVATE"
ERR_MESSAGE_NOT_FOUND = "MESSAGE_NOT_FOUND"
ERR_FLOOD_WAIT = "FLOOD_WAIT"
ERR_INVALID_PARAMETER = "INVALID_PARAMETER"
ERR_TOOL_UNAVAILABLE = "TOOL_UNAVAILABLE"
ERR_TOOL_DISABLED = "TOOL_DISABLED"
ERR_TASK_NOT_FOUND = "TASK_NOT_FOUND"
ERR_NOT_AUTHORIZED = "NOT_AUTHORIZED"
ERR_AMBIGUOUS = "AMBIGUOUS"
ERR_NOT_SUPPORTED = "NOT_SUPPORTED"
ERR_FOLDER_NOT_FOUND = "FOLDER_NOT_FOUND"
ERR_FOLDER_EMPTY = "FOLDER_EMPTY"
ERR_FOLDER_RESOLUTION_FAILED = "FOLDER_RESOLUTION_FAILED"
ERR_CONFIRMATION_REQUIRED = "CONFIRMATION_REQUIRED"
ERR_VERIFICATION_FAILED = "VERIFICATION_FAILED"
ERR_PROVIDER_UNAVAILABLE = "PROVIDER_UNAVAILABLE"
ERR_AI_PARSE_FAILED = "AI_PARSE_FAILED"
ERR_NO_VALID_TARGETS = "NO_VALID_TARGETS"
ERR_NO_ACTIVE_MONITOR = "NO_ACTIVE_MONITOR"

logging.basicConfig(level=logging.INFO,
                    format="%(asctime)s | %(levelname)-5s | %(name)s | %(message)s")
log = logging.getLogger("jarvis")

# ----------------------------------------------------------------------------
# optional deps
# ----------------------------------------------------------------------------

TELETHON_OK = True
TELETHON_ERR = ""
try:
    from telethon import TelegramClient, events, utils
    from telethon.sessions import StringSession
    from telethon.errors import (
        FloodWaitError, SessionPasswordNeededError, ChatAdminRequiredError,
        PhoneCodeInvalidError, RPCError, ChannelPrivateError,
    )
    try:
        from telethon.errors import ChatForwardsRestrictedError
    except Exception:
        class ChatForwardsRestrictedError(RPCError):  # type: ignore
            pass
    from telethon.tl import types as tl
    from telethon.tl import functions as fn
except Exception as exc:  # pragma: no cover
    TELETHON_OK = False
    TELETHON_ERR = str(exc)
    TelegramClient = None  # type: ignore
    tl = None  # type: ignore
    fn = None  # type: ignore

try:
    from fastapi import FastAPI, Request
    from fastapi.responses import FileResponse, JSONResponse
    import uvicorn
    import httpx
    WEB_OK = True
except Exception as exc:  # pragma: no cover
    WEB_OK = False
    log.error("fastapi/uvicorn/httpx missing: %s", exc)


# ----------------------------------------------------------------------------
# 1. TEXT NORMALIZATION / FUZZY MATCHING (typo-tolerant Hinglish)
# ----------------------------------------------------------------------------

_VOWELS = set("aeiou")


def squash_repeats(s: str) -> str:
    out, prev = [], ""
    for ch in s:
        if ch != prev:
            out.append(ch)
        prev = ch
    return "".join(out)


def norm_text(text: str) -> str:
    t = (text or "").lower()
    t = re.sub(r"[^a-z0-9@_\s\-]", " ", t)
    t = re.sub(r"\s+", " ", t).strip()
    return t


def skeleton(text: str) -> str:
    """squashed, vowel-free shape of normalized text: 'dhyan rakho' -> 'dhyn rkh'."""
    squashed = squash_repeats(norm_text(text))
    return " ".join("".join(c for c in w if c not in _VOWELS) for w in squashed.split())


def has_kw(normed: str, skel: str, phrases) -> bool:
    """exact normalized substring OR skeleton substring (min 4) - catches typos."""
    for p in phrases:
        pn = norm_text(p)
        if pn and pn in normed:
            return True
        ps = skeleton(pn)
        if len(ps) >= 4 and ps in skel:
            return True
    return False


def utc_now() -> float:
    return time.time()


def iso(ts: Optional[float] = None) -> str:
    return datetime.fromtimestamp(ts or utc_now(), tz=timezone.utc).isoformat(timespec="seconds")


def ktm_iso(ts: Optional[float] = None) -> str:
    return datetime.fromtimestamp(ts or utc_now(), tz=KTM).strftime("%d %b %Y %H:%M KTM")


def new_id(prefix: str) -> str:
    return f"{prefix}_{uuid.uuid4().hex[:10]}"


def human_delta(seconds: float) -> str:
    seconds = int(max(0, seconds))
    if seconds < 60:
        return f"{seconds}s"
    if seconds < 3600:
        return f"{seconds // 60}m"
    if seconds < 86400:
        return f"{seconds // 3600}h {seconds % 3600 // 60}m"
    return f"{seconds // 86400}d {seconds % 86400 // 3600}h"


def mask_phone(phone: str) -> str:
    d = re.sub(r"\D", "", phone or "")
    return f"+{d[:2]}...{d[-3:]}" if len(d) >= 5 else "***"


def short(text: str, n: int = 120) -> str:
    text = " ".join((text or "").split())
    return text if len(text) <= n else text[: n - 1] + "…"


def extract_ids(text: str) -> list[str]:
    return [x.lstrip("+") for x in re.findall(r"-?\d{7,}", text or "")]


def extract_usernames(text: str) -> list[str]:
    return re.findall(r"@[\w_]{5,}", text or "")


def strip_command(text: str) -> str:
    return re.sub(r"^/(?:ai|jarvis|cross)\b[:\s]*", "", (text or "").strip(), flags=re.I)


def looks_like_command(text: str) -> bool:
    return bool(re.match(r"^/(ai|jarvis|cross)\b", (text or "").strip(), flags=re.I))


def chunk_text(text: str, size: int = 3800) -> list[str]:
    if len(text) <= size:
        return [text]
    out, cur = [], ""
    for line in text.split("\n"):
        if len(cur) + len(line) + 1 > size:
            out.append(cur)
            cur = line
        else:
            cur = f"{cur}\n{line}" if cur else line
    if cur:
        out.append(cur)
    return out


# ----------------------------------------------------------------------------
# 1b. NATURAL LANGUAGE TIME - Asia/Kathmandu, absolute timestamps persisted
# ----------------------------------------------------------------------------

def parse_time_spec(text: str) -> dict:
    """Returns {kind: duration|at, sec|ts, desc} or {} when nothing found."""
    raw = (text or "").lower()
    t = norm_text(raw)
    sk = skeleton(raw)

    # "until I come back" family -> bounded safety default
    if has_kw(t, sk, ["jab tak main wapas", "jab tak wapas", "wapas na aau", "jab tak na aau",
                      "uthne tak", "jaag ne tak", "until i am back", "until i return", "till i come back"]):
        return {"kind": "duration", "sec": 8 * 3600,
                "desc": "until-you-return (auto-capped at 8h for safety)"}

    m = re.search(r"(\d+)\s*(minutes?|mins?|min|mint|minet|minute)\b", t)
    if m:
        sec = int(m.group(1)) * 60
        return {"kind": "duration", "sec": sec, "desc": human_delta(sec)}
    m = re.search(r"(\d+)\s*(hours?|hrs?|hr|ghante?|ghanta|h)\b", t)
    if m:
        sec = min(int(m.group(1)) * 3600, 7 * 86400)
        return {"kind": "duration", "sec": sec, "desc": human_delta(sec)}
    m = re.search(r"(\d+)\s*(days?|din|day)\b", t)
    if m or has_kw(t, sk, ["do din", "ek din"]):
        sec = int(m.group(1)) * 86400 if m else (172800 if "do din" in t else 86400)
        sec = min(sec, 14 * 86400)
        return {"kind": "duration", "sec": sec, "desc": human_delta(sec)}
    if has_kw(t, sk, ["aadha ghanta", "half hour"]):
        return {"kind": "duration", "sec": 1800, "desc": "30m"}

    now = datetime.now(tz=KTM)
    tomorrow = has_kw(t, sk, ["tomorrow", "kal", "agle din"])
    tonight = has_kw(t, sk, ["tonight", "aaj raat", "aj rat", "aaj hi raat"])
    morning = has_kw(t, sk, ["subah", "morning", "sabere"])
    evening = has_kw(t, sk, ["shaam", "evening", "raat", "night"])

    m = re.search(r"\b(\d{1,2})(?::(\d{2}))?\s*(baje|pm|am)\b", t)
    if m:
        hour = int(m.group(1))
        minute = int(m.group(2) or 0)
        mer = m.group(3)
        if mer == "pm" and hour < 12:
            hour += 12
        elif mer == "am" and hour == 12:
            hour = 0
        elif mer == "baje" and hour <= 11:
            # infer from daypart words or current KTM time
            if (evening or tonight) and hour <= 11:
                hour += 12 if hour != 12 else 0
            elif evening is False and morning is False and now.hour >= 12 and hour >= 1 and hour <= 11:
                hour += 12  # reasonable evening guess
        base = now.date() + timedelta(days=1 if tomorrow else 0)
        if tonight and not tomorrow and (hour < now.hour or (hour == now.hour and minute <= now.minute)):
            base = now.date() + timedelta(days=1)
        target = datetime(base.year, base.month, base.day, hour % 24, minute, tzinfo=KTM)
        if target.timestamp() <= now.timestamp() and not (tomorrow or tonight):
            target += timedelta(days=1)
        return {"kind": "at", "ts": target.timestamp(), "desc": ktm_iso(target.timestamp())}

    if tonight:
        target = now.replace(hour=21, minute=0, second=0)
        if target.timestamp() <= now.timestamp():
            target += timedelta(days=1)
        return {"kind": "at", "ts": target.timestamp(), "desc": ktm_iso(target.timestamp())}
    if tomorrow:
        target = (now + timedelta(days=1)).replace(hour=9, minute=0, second=0)
        return {"kind": "at", "ts": target.timestamp(), "desc": ktm_iso(target.timestamp())}
    return {}


AFFIRM = {"yes", "y", "haan", "ha", "han", "ok", "okay", "theek", "theek hai", "confirm",
          "kar do", "haan karo", "proceed", "go", "go ahead", "sure", "ha"}
DENY = {"no", "n", "nahi", "nhi", "nope", "cancel", "mat karo", "rehne do", "ruk", "ruko"}


# ----------------------------------------------------------------------------
# 2. PERSISTENCE - versioned JSON, atomic writes, corruption quarantine
# ----------------------------------------------------------------------------

class JSONStore:
    def __init__(self, path: Path, section: str):
        self.path = path
        self.section = section
        self.data: dict = {}
        self.load()

    def _default(self) -> dict:
        return {"schema_version": SCHEMA_VERSION, "created_at": iso(),
                "updated_at": iso(), self.section: {}}

    def load(self) -> None:
        if not self.path.exists():
            self.data = self._default()
            self.save()
            return
        try:
            raw = json.loads(self.path.read_text(encoding="utf-8"))
            if not isinstance(raw, dict):
                raise ValueError("top-level is not an object")
            base = self._default()
            for k, v in base.items():
                raw.setdefault(k, v)
            raw["schema_version"] = SCHEMA_VERSION
            self.data = raw
        except Exception as exc:
            bad = self.path.with_suffix(f".corrupt-{int(utc_now())}.json")
            try:
                shutil.copy2(self.path, bad)
            except Exception:
                pass
            log.warning("store %s malformed (%s) -> quarantined", self.path.name, exc)
            self.data = self._default()
            self.save()

    def save(self) -> None:
        self.data["updated_at"] = iso()
        tmp = self.path.with_suffix(".tmp")
        tmp.write_text(json.dumps(self.data, ensure_ascii=False, indent=1), encoding="utf-8")
        os.replace(tmp, self.path)


# ----------------------------------------------------------------------------
# 3. DIAGNOSTICS  (runtime.json) - never stores secrets
# ----------------------------------------------------------------------------

class Diagnostics:
    def __init__(self, store: JSONStore):
        self.store = store
        self.started_at = utc_now()
        self.events: deque[dict] = deque(maxlen=DIAG_BUFFER)
        for e in (store.data.get("diag", {}).get("events") or [])[-100:]:
            self.events.append(e)
        self.last_success: Optional[dict] = None
        self.last_failure: Optional[dict] = None

    def record(self, level: str, component: str, operation: str, message: str,
               account_id: Optional[str] = None, task_id: Optional[str] = None,
               error_code: Optional[str] = None) -> None:
        e = {"ts": iso(), "level": level, "component": component, "operation": operation,
             "message": short(str(message), 300), "account_id": account_id,
             "task_id": task_id, "error_code": error_code}
        self.events.append(e)
        if level == "SUCCESS":
            self.last_success = e
        elif level in ("ERROR", "WARN"):
            self.last_failure = e
        (log.warning if level in ("WARN", "ERROR") else log.info)(
            "[%s.%s] %s (acc=%s task=%s)", component, operation, e["message"],
            account_id or "-", task_id or "-")

    def ok(self, c, o, m, **kw): self.record("SUCCESS", c, o, m, **kw)
    def info(self, c, o, m, **kw): self.record("INFO", c, o, m, **kw)
    def warn(self, c, o, m, **kw): self.record("WARN", c, o, m, **kw)
    def err(self, c, o, m, **kw): self.record("ERROR", c, o, m, **kw)

    def persist(self) -> None:
        self.store.data["diag"] = {"events": list(self.events)[-100:]}
        self.store.save()

    def snapshot(self) -> dict:
        return {"uptime_sec": int(utc_now() - self.started_at), "started_at": iso(self.started_at),
                "events": list(self.events)[-60:], "last_success": self.last_success,
                "last_failure": self.last_failure}


# ----------------------------------------------------------------------------
# 4. TOOL RESULT STANDARD + EXCEPTIONS
# ----------------------------------------------------------------------------

@dataclass
class ToolResult:
    ok: bool
    status: str                      # SUCCESS / FAILED / WAITING / PERMISSION_REQUIRED / NOT_SUPPORTED
    data: Optional[dict] = None
    error: Optional[str] = None
    error_code: Optional[str] = None
    retryable: bool = False
    verification: Optional[dict] = None

    @staticmethod
    def success(data: Optional[dict] = None, verification: Optional[dict] = None) -> "ToolResult":
        return ToolResult(True, "SUCCESS", data or {}, None, None, False, verification)

    @staticmethod
    def failure(error: str, code: str = ERR_TOOL_UNAVAILABLE, retryable: bool = False,
                status: str = "FAILED") -> "ToolResult":
        return ToolResult(False, status, None, error, code, retryable, None)

    def to_dict(self) -> dict:
        return {"ok": self.ok, "status": self.status, "data": self.data, "error": self.error,
                "error_code": self.error_code, "retryable": self.retryable,
                "verification": self.verification}


class EntityResolutionError(Exception):
    pass


class ValidationError(Exception):
    def __init__(self, missing: list[str]):
        super().__init__("; ".join(missing))
        self.missing = missing


class AmbiguityError(Exception):
    def __init__(self, question: str, options: Optional[list[str]] = None):
        super().__init__(question)
        self.question = question
        self.options = options or []


class ToolDisabled(Exception):
    pass


# ----------------------------------------------------------------------------
# 5. MEMORY  (channel_memory.json) + BRAIN CONTEXT (brain.json)
# ----------------------------------------------------------------------------

class MemoryStore:
    def __init__(self, store: JSONStore):
        self.store = store

    def _acc(self, account_id: str) -> dict:
        return self.store.data["channel_memory"].setdefault(
            account_id, {"aliases": {}, "notes": [], "known_channels": {}, "prefs": {}})

    def learn_channel(self, account_id: str, ent_id: str, title: str, username: str = "") -> None:
        acc = self._acc(account_id)
        acc["known_channels"][str(ent_id)] = {"title": title, "username": username, "seen_at": iso()}
        if len(acc["known_channels"]) > 600:
            acc["known_channels"] = dict(list(acc["known_channels"].items())[-600:])
        if title:
            acc["aliases"].setdefault(title.strip().lower(), str(ent_id))
        self.store.save()

    def alias_lookup(self, account_id: str, name: str) -> Optional[str]:
        acc = self._acc(account_id)
        key = name.strip().lower()
        if key in acc["aliases"]:
            return acc["aliases"][key]
        nkey, nskel = norm_text(key), skeleton(key)
        for k, v in acc["aliases"].items():
            if (nkey and nkey in norm_text(k)) or (len(nskel) >= 4 and nskel in skeleton(k)):
                return v
        return None

    def set_alias(self, account_id: str, alias: str, ent_id: str) -> None:
        self._acc(account_id)["aliases"][alias.strip().lower()] = str(ent_id)
        self.store.save()

    def known(self, account_id: str) -> dict:
        return self._acc(account_id)["known_channels"]

    def add_note(self, account_id: str, note: str) -> None:
        notes = self._acc(account_id)["notes"]
        notes.append({"ts": iso(), "note": short(note, 200)})
        self._acc(account_id)["notes"] = notes[-200:]
        self.store.save()

    def prefs(self, account_id: str) -> dict:
        return self._acc(account_id)["prefs"]

    def public(self, account_id: str) -> dict:
        acc = self._acc(account_id)
        return {"aliases": acc["aliases"], "notes": acc["notes"][-20:],
                "known_channels_count": len(acc["known_channels"]), "prefs": acc["prefs"]}


class BrainContext:
    """Structured mini-brain context, JSON-backed (brain.json), volatile parts expire."""

    SECTIONS = ("channel", "folder", "account", "task", "monitor", "cross",
                "conversation", "workflow", "prefs")

    def __init__(self, store: JSONStore):
        self.store = store

    def _raw(self, account_id: str) -> dict:
        sec = self.store.data["brain"].setdefault(account_id, {})
        for s in self.SECTIONS:
            sec.setdefault(s, {} if s != "conversation" else {"recent": []})
        return sec

    def _volatile_ok(self, raw: dict) -> bool:
        return utc_now() - raw.get("ts", 0) <= CONTEXT_TTL

    def get(self, account_id: str, section: str) -> dict:
        raw = self._raw(account_id)
        if section in ("task", "channel", "folder", "monitor", "cross", "workflow", "account"):
            if not self._volatile_ok(raw):
                return {}
        return raw.get(section) or ({} if section != "conversation" else {"recent": []})

    def update(self, account_id: str, section: str, **kv) -> None:
        raw = self._raw(account_id)
        tgt = raw.setdefault(section, {})
        if isinstance(tgt, dict):
            for k, v in kv.items():
                if v is not None:
                    tgt[k] = v
        raw["ts"] = utc_now()
        self.store.save()

    def update_bulk(self, account_id: str, mapping: dict) -> None:
        for sec, kv in mapping.items():
            self.update(account_id, sec, **kv)

    def push_action(self, account_id: str, entry: dict) -> None:
        raw = self._raw(account_id)
        conv = raw.setdefault("conversation", {"recent": []})
        conv.setdefault("recent", []).append({"ts": iso(), **entry})
        conv["recent"] = conv["recent"][-25:]
        raw["ts"] = utc_now()
        self.store.save()

    def pending_choice(self, account_id: str) -> Optional[dict]:
        raw = self._raw(account_id)
        pc = raw.get("pending_choice")
        if pc and utc_now() - pc.get("ts", 0) <= CONTEXT_TTL:
            return pc
        return None

    def set_pending_choice(self, account_id: str, payload: Optional[dict]) -> None:
        raw = self._raw(account_id)
        if payload is None:
            raw.pop("pending_choice", None)
        else:
            payload["ts"] = utc_now()
            raw["pending_choice"] = payload
        self.store.save()


# ----------------------------------------------------------------------------
# 6. ACCOUNT MANAGER  (accounts.json + secure sessions.json)
# ----------------------------------------------------------------------------

@dataclass
class AccountRuntime:
    account_id: str
    client: Optional["TelegramClient"] = None
    self_id: Optional[int] = None
    self_name: str = ""
    self_username: str = ""
    authorized: bool = False
    connected: bool = False
    pending_login: Optional[dict] = None
    last_error: str = ""


class AccountManager:
    def __init__(self, store: JSONStore, session_store: JSONStore, diag: Diagnostics):
        self.store = store
        self.sessions = session_store
        self.diag = diag
        self.runtime: dict[str, AccountRuntime] = {
            aid: AccountRuntime(aid) for aid in self.store.data["accounts"]}
        try:
            os.chmod(self.sessions.path, 0o600)
        except Exception:
            pass

    def create(self, label: Optional[str], api_id: str = "", api_hash: str = "") -> dict:
        if len(self.store.data["accounts"]) >= MAX_ACCOUNTS:
            raise ValidationError([f"account limit reached ({MAX_ACCOUNTS})"])
        aid = new_id("acc")
        cfg = {"account_id": aid,
               "label": label or f"Account {len(self.store.data['accounts']) + 1}",
               "phone": "", "api_id": str(api_id or "").strip(),
               "api_hash": str(api_hash or "").strip(),
               "main_channels": [], "created_at": iso(), "updated_at": iso()}
        self.store.data["accounts"][aid] = cfg
        self.runtime[aid] = AccountRuntime(aid)
        self.store.save()
        self.diag.ok("accounts", "create", f"{cfg['label']} created", account_id=aid)
        return cfg

    def delete(self, account_id: str) -> None:
        rt = self.runtime.get(account_id)
        if rt and rt.client:
            asyncio.create_task(self._safe_disconnect(rt))
        self.store.data["accounts"].pop(account_id, None)
        self.sessions.data["sessions"].pop(account_id, None)
        self.store.save()
        self.sessions.save()
        self.runtime.pop(account_id, None)

    async def _safe_disconnect(self, rt: AccountRuntime) -> None:
        try:
            if rt.client:
                await rt.client.disconnect()
        except Exception:
            pass
        rt.connected = False
        rt.authorized = False
        rt.client = None

    def get(self, account_id: str) -> dict:
        cfg = self.store.data["accounts"].get(account_id)
        if not cfg:
            raise ValidationError([f"account not found: {account_id}"])
        return cfg

    def all(self) -> list[dict]:
        return list(self.store.data["accounts"].values())

    def resolve_ref(self, ref: Optional[str]) -> Optional[str]:
        accounts = self.all()
        if not accounts:
            return None
        if not ref:
            return accounts[0]["account_id"] if len(accounts) == 1 else None
        r = str(ref).strip().lower()
        m = re.search(r"(?:account|acc)\s*#?\s*(\d+)", r)
        if m and 0 < int(m.group(1)) <= len(accounts):
            return accounts[int(m.group(1)) - 1]["account_id"]
        for cfg in accounts:
            if cfg["account_id"] == ref or cfg["label"].lower() == r:
                return cfg["account_id"]
        if r.isdigit() and 0 < int(r) <= len(accounts):
            return accounts[int(r) - 1]["account_id"]
        return None

    def creds(self, cfg: dict) -> tuple[int, str]:
        api_id = cfg.get("api_id") or ENV_API_ID
        api_hash = cfg.get("api_hash") or ENV_API_HASH
        if not api_id or not api_hash:
            raise ValidationError([
                "api_id/api_hash missing - set JARVIS_API_ID & JARVIS_API_HASH env, "
                "or enter them in Web Control when creating the account"])
        return int(api_id), api_hash

    # ---- main channel config (single source of truth) ----
    def set_main_channels(self, account_id: str, channels: list[dict]) -> None:
        cfg = self.get(account_id)
        cfg["main_channels"] = channels[:MAX_TARGETS]
        cfg["updated_at"] = iso()
        self.store.save()

    def get_main_channels(self, account_id: str) -> list[dict]:
        return list(self.get(account_id).get("main_channels") or [])

    # ---- sessions ----
    def save_session(self, account_id: str, session_string: str) -> None:
        self.sessions.data["sessions"][account_id] = session_string
        self.sessions.save()
        try:
            os.chmod(self.sessions.path, 0o600)
        except Exception:
            pass

    def load_session(self, account_id: str) -> str:
        return self.sessions.data["sessions"].get(account_id, "")

    # ---- connection ----
    async def connect(self, account_id: str) -> AccountRuntime:
        if not TELETHON_OK:
            raise ValidationError([f"telethon unavailable: {TELETHON_ERR}"])
        cfg = self.get(account_id)
        api_id, api_hash = self.creds(cfg)
        rt = self.runtime.setdefault(account_id, AccountRuntime(account_id))
        if rt.client and rt.connected:
            return rt
        client = TelegramClient(StringSession(self.load_session(account_id)), api_id, api_hash)
        rt.client = client
        try:
            await asyncio.wait_for(client.connect(), timeout=20)
            rt.connected = True
            rt.authorized = await client.is_user_authorized()
            if rt.authorized:
                me = await client.get_me()
                rt.self_id = me.id
                rt.self_username = getattr(me, "username", "") or ""
                rt.self_name = f"{getattr(me, 'first_name', '') or ''} {getattr(me, 'last_name', '') or ''}".strip()
                cfg["phone"] = getattr(me, "phone", "") or cfg.get("phone", "")
                self.store.save()
                self.diag.ok("accounts", "connect",
                             f"{cfg['label']} online as {rt.self_name or rt.self_id}", account_id=aid_or(account_id))
            else:
                self.diag.warn("accounts", "connect",
                               f"{cfg['label']} connected but NOT authorized", account_id=account_id)
        except Exception as exc:
            rt.last_error = type(exc).__name__
            rt.connected = False
            self.diag.err("accounts", "connect", f"{cfg['label']}: {type(exc).__name__}",
                          account_id=account_id, error_code=ERR_NOT_AUTHORIZED)
            raise
        return rt

    async def disconnect(self, account_id: str) -> None:
        rt = self.runtime.get(account_id)
        if rt:
            await self._safe_disconnect(rt)

    async def start_login(self, account_id: str, phone: str) -> dict:
        rt = await self.connect(account_id)
        if rt.authorized:
            return {"already": True}
        sent = await rt.client.send_code_request(phone)
        rt.pending_login = {"phone": phone, "phone_code_hash": sent.phone_code_hash,
                            "ts": utc_now()}
        self.diag.info("accounts", "login.start", f"code sent to {mask_phone(phone)}",
                       account_id=account_id)
        return {"already": False, "code_sent": True, "phone": mask_phone(phone)}

    async def complete_login(self, account_id: str, code: str, password: str = "") -> dict:
        rt = await self.connect(account_id)
        if rt.authorized:
            return {"ok": True, "name": rt.self_name}
        pend = rt.pending_login
        if not pend:
            raise ValidationError(["no pending login - request a code first"])
        try:
            await rt.client.sign_in(phone=pend["phone"], code=code,
                                    phone_code_hash=pend["phone_code_hash"])
        except SessionPasswordNeededError:
            if not password:
                return {"ok": False, "need_password": True}
            await rt.client.sign_in(password=password)
        except PhoneCodeInvalidError:
            raise ValidationError(["invalid code - try again"])
        me = await rt.client.get_me()
        rt.self_id = me.id
        rt.self_username = getattr(me, "username", "") or ""
        rt.self_name = f"{getattr(me, 'first_name', '') or ''}".strip()
        rt.authorized = True
        rt.pending_login = None
        cfg = self.get(account_id)
        cfg["phone"] = getattr(me, "phone", "") or cfg.get("phone", "")
        self.save_session(account_id, rt.client.session.save())
        self.store.save()
        self.diag.ok("accounts", "login.complete",
                     f"{cfg['label']} authorized ({rt.self_name or rt.self_id})", account_id=account_id)
        return {"ok": True, "name": rt.self_name}

    async def import_session(self, account_id: str, session_string: str) -> dict:
        if not session_string or len(session_string.strip()) < 40:
            raise ValidationError(["session string looks invalid"])
        cfg = self.get(account_id)
        api_id, api_hash = self.creds(cfg)
        client = TelegramClient(StringSession(session_string.strip()), api_id, api_hash)
        await asyncio.wait_for(client.connect(), timeout=20)
        if not await client.is_user_authorized():
            await client.disconnect()
            raise ValidationError(["session string is not authorized"])
        me = await client.get_me()
        rt = self.runtime.setdefault(account_id, AccountRuntime(account_id))
        if rt.client:
            await self._safe_disconnect(rt)
        rt.client = client
        rt.connected = True
        rt.authorized = True
        rt.self_id = me.id
        rt.self_username = getattr(me, "username", "") or ""
        rt.self_name = f"{getattr(me, 'first_name', '') or ''}".strip()
        cfg["phone"] = getattr(me, "phone", "") or cfg.get("phone", "")
        self.save_session(account_id, session_string.strip())
        self.store.save()
        self.diag.ok("accounts", "session.import",
                     f"{cfg['label']} authorized via session", account_id=account_id)
        return {"ok": True, "name": rt.self_name}

    def public(self, account_id: str) -> dict:
        cfg = self.get(account_id)
        rt = self.runtime.get(account_id) or AccountRuntime(account_id)
        return {"account_id": account_id, "label": cfg.get("label"),
                "phone_masked": mask_phone(cfg.get("phone", "")) if cfg.get("phone") else "",
                "self_name": rt.self_name, "self_username": rt.self_username,
                "self_tg_id": rt.self_id if rt.authorized else None,
                "authorized": rt.authorized, "connected": rt.connected,
                "api_mode": "env" if not cfg.get("api_id") else "account",
                "pending_login": bool(rt.pending_login),
                "main_channels": cfg.get("main_channels") or [],
                "last_error": rt.last_error, "created_at": cfg.get("created_at")}


def aid_or(account_id: str) -> str:
    return account_id


# ----------------------------------------------------------------------------
# 7. ENTITY RESOLVER v2 - ids, usernames, replies, folders, memory, dialogs
# ----------------------------------------------------------------------------

@dataclass
class ResolvedEntity:
    id: int
    kind: str          # channel / group / user
    title: str
    username: str = ""
    entity: Any = None

    def brief(self) -> str:
        uname = f" @{self.username}" if self.username else ""
        return f"{self.title or 'untitled'}{uname} [{self.id}]"

    def brief_dict(self) -> dict:
        return {"id": self.id, "title": self.title, "username": self.username, "kind": self.kind}


@dataclass
class ReplyContext:
    entity: ResolvedEntity
    message_id: Optional[int]      # original channel_post id when forwarded
    via: str = "reply"
    text: str = ""
    has_media: bool = False


class EntityResolver:
    def __init__(self, accounts: AccountManager, memory: MemoryStore, diag: Diagnostics):
        self.accounts = accounts
        self.memory = memory
        self.diag = diag
        self._dialog_cache: dict[str, tuple[float, list]] = {}
        self._folder_cache: dict[str, tuple[float, list]] = {}

    async def _client(self, account_id: str) -> "TelegramClient":
        rt = await self.accounts.connect(account_id)
        if not rt.authorized:
            raise ValidationError([f"{self.accounts.get(account_id)['label']} is not authorized - login required"])
        return rt.client

    def id_candidates(self, ref_s: str) -> list[Any]:
        out: list[Any] = []
        m100 = re.fullmatch(r"-100(\d+)", ref_s)
        if m100:
            out += [int(m100.group(1)), int(ref_s)]
        elif ref_s.lstrip("-").isdigit():
            v = int(ref_s)
            out.append(v)
            if v > 0 and not ref_s.startswith("-"):
                out += [-v, -int(f"100{v}"), int(f"100{v}")]
        return out

    async def resolve(self, account_id: str, ref: Any) -> ResolvedEntity:
        client = await self._client(account_id)
        ref_s = str(ref).strip()
        candidates: list[Any] = []
        if ref_s.startswith("@") or re.fullmatch(r"[A-Za-z][\w_]{4,}", ref_s):
            candidates.append(ref_s.lstrip("@"))
        candidates += self.id_candidates(ref_s)
        last_exc: Optional[Exception] = None
        for cand in candidates:
            try:
                ent = await client.get_entity(cand)
                return self._wrap(ent, account_id)
            except Exception as exc:
                last_exc = exc
        aliased = self.memory.alias_lookup(account_id, ref_s)
        if aliased and aliased != ref_s:
            try:
                return await self.resolve(account_id, aliased)
            except EntityResolutionError:
                pass
        dialogs = await self._dialogs(account_id)
        if ref_s.lstrip("-").isdigit():
            stripped = ref_s.lstrip("-")
            for d in dialogs:
                comp = {str(d["id"]), str(d["id"]).lstrip("-"),
                        str(d["id"]).lstrip("-").replace("100", "", 1)}
                if stripped in comp:
                    return self._wrap(d["entity"], account_id)
        nref, sref = norm_text(ref_s), skeleton(ref_s)
        for d in dialogs:
            title_n = norm_text(d["title"] or "")
            if nref and (nref in title_n or title_n in nref and len(title_n) >= 4):
                return self._wrap(d["entity"], account_id)
            if len(sref) >= 4 and sref in skeleton(d["title"] or ""):
                return self._wrap(d["entity"], account_id)
        raise EntityResolutionError(
            f"cannot resolve '{short(ref_s, 40)}' - check the ID/username or open the chat once in Telegram")

    def _wrap(self, ent: Any, account_id: Optional[str] = None) -> ResolvedEntity:
        eid = utils.get_peer_id(ent)
        if tl is not None and isinstance(ent, tl.Channel):
            kind = "group" if getattr(ent, "megagroup", False) else "channel"
            title = getattr(ent, "title", "?")
        elif tl is not None and isinstance(ent, tl.Chat):
            kind, title = "group", getattr(ent, "title", "?")
        else:
            kind = "user"
            title = f"{getattr(ent, 'first_name', '') or ''} {getattr(ent, 'last_name', '') or ''}".strip() or "?"
        r = ResolvedEntity(eid, kind, title, getattr(ent, "username", "") or "", ent)
        if account_id:
            self.memory.learn_channel(account_id, str(eid), title, r.username)
        return r

    async def _dialogs(self, account_id: str, force: bool = False) -> list:
        ts, cache = self._dialog_cache.get(account_id, (0, []))
        if not force and utc_now() - ts < 120 and cache:
            return cache
        client = await self._client(account_id)
        try:
            dialogs = await asyncio.wait_for(client.get_dialogs(limit=200), timeout=30)
        except Exception:
            dialogs = []
        out = []
        for d in dialogs:
            ent = d.entity
            out.append({"id": utils.get_peer_id(ent),
                        "title": getattr(ent, "title", None) or
                        f"{getattr(ent, 'first_name', '') or ''} {getattr(ent, 'last_name', '') or ''}".strip(),
                        "username": getattr(ent, "username", "") or "", "entity": ent,
                        "folder_id": getattr(d.dialog, "folder_id", None)})
        self._dialog_cache[account_id] = (utc_now(), out)
        return out

    # ---- Telegram dialog folders ----
    async def get_folders(self, account_id: str, force: bool = False) -> list[dict]:
        ts, cache = self._folder_cache.get(account_id, (0, []))
        if not force and utc_now() - ts < 120 and cache:
            return cache
        client = await self._client(account_id)
        folders: list[dict] = []
        try:
            res = await client(fn.messages.GetDialogFiltersRequest())
            for f in res:
                if tl is None or not isinstance(f, tl.DialogFilter):
                    continue
                title = getattr(f, "title", "")
                if not isinstance(title, str):
                    title = getattr(title, "text", "") or str(title)
                peers = list(getattr(f, "include_peers", []) or [])
                folders.append({"id": getattr(f, "id", 0), "title": str(title), "peers": peers})
        except Exception as exc:
            self.diag.err("resolver", "folders", type(exc).__name__, account_id=account_id)
        self._folder_cache[account_id] = (utc_now(), folders)
        return folders

    async def resolve_folder(self, account_id: str, name: str) -> Optional[dict]:
        folders = await self.get_folders(account_id)
        nname, sname = norm_text(name), skeleton(name)
        for f in folders:
            if norm_text(f["title"]) == nname:
                return f
        for f in folders:
            fn_ = norm_text(f["title"])
            if nname and len(nname) >= 3 and (nname in fn_ or fn_ in nname):
                return f
        for f in folders:
            if len(sname) >= 4 and sname in skeleton(f["title"]):
                return f
        return None

    async def folder_peers(self, account_id: str, folder: dict) -> dict:
        client = await self._client(account_id)
        out = {"channels": [], "groups": [], "users": [], "unresolved": []}
        for peer in folder.get("peers", []):
            try:
                ent = await client.get_entity(peer)
                r = self._wrap(ent, account_id)
                key = "channels" if r.kind == "channel" else ("groups" if r.kind == "group" else "users")
                out[key].append(r.brief_dict())
            except Exception:
                try:
                    pid = utils.get_peer_id(peer)
                except Exception:
                    pid = str(peer)
                out["unresolved"].append({"id": pid})
        return out

    # ---- reply extraction (source chat + original message id) ----
    async def from_reply(self, account_id: str, reply_msg: Any) -> Optional[ReplyContext]:
        if reply_msg is None:
            return None
        text = short(getattr(reply_msg, "raw_text", "") or "", 180)
        has_media = bool(getattr(reply_msg, "media", None))
        fwd = getattr(reply_msg, "fwd_from", None)
        if fwd is not None:
            pid = getattr(fwd, "from_id", None)
            msg_id = getattr(fwd, "channel_post", None)
            if pid is not None:
                try:
                    client = await self._client(account_id)
                    ent = await client.get_entity(pid)
                    return ReplyContext(self._wrap(ent, account_id), msg_id,
                                        text=text, has_media=has_media)
                except Exception:
                    return ReplyContext(ResolvedEntity(
                        utils.get_peer_id(pid), "channel",
                        getattr(fwd, "from_name", "") or "source", ""), msg_id,
                        text=text, has_media=has_media)
        try:
            me_id = (self.accounts.runtime.get(account_id) or AccountRuntime(account_id)).self_id
            peer = getattr(reply_msg, "peer_id", None)
            if peer is not None and getattr(peer, "user_id", None) not in (None, me_id):
                client = await self._client(account_id)
                return ReplyContext(self._wrap(await client.get_entity(peer), account_id),
                                    getattr(reply_msg, "id", None),
                                    text=text, has_media=has_media)
        except Exception:
            pass
        return None


# ----------------------------------------------------------------------------
# 8. CONFIRMATION ENGINE - account/task bound, single-use, expiring
# ----------------------------------------------------------------------------

class ConfirmationEngine:
    def __init__(self, ctx: BrainContext, diag: Diagnostics):
        self.ctx = ctx
        self.diag = diag

    def require(self, account_id: str, action_desc: str, payload: dict,
                task_id: Optional[str] = None) -> None:
        self.ctx.update(account_id, "workflow", pending_confirmation={
            "token": new_id("cfm"), "desc": action_desc, "payload": payload,
            "task_id": task_id, "expires_at": utc_now() + CONFIRM_TTL})
        self.diag.info("confirm", "require", action_desc, account_id=account_id, task_id=task_id)

    def pending(self, account_id: str) -> Optional[dict]:
        wf = self.ctx.get(account_id, "workflow")
        p = (wf or {}).get("pending_confirmation")
        if not p:
            return None
        if utc_now() > p.get("expires_at", 0):
            wf.pop("pending_confirmation", None)
            self.ctx.update(account_id, "workflow")
            self.diag.warn("confirm", "expire", "confirmation expired", account_id=account_id)
            return None
        return p

    def matches(self, text: str) -> Optional[bool]:
        t = (text or "").strip().lower()
        if t in AFFIRM:
            return True
        if t in DENY:
            return False
        return None

    def consume(self, account_id: str) -> Optional[dict]:
        p = self.pending(account_id)
        wf = self.ctx.get(account_id, "workflow")
        if isinstance(wf, dict):
            wf.pop("pending_confirmation", None)
        self.ctx.update(account_id, "workflow")
        return p

    def public(self, account_id: str) -> Optional[dict]:
        p = self.pending(account_id)
        if not p:
            return None
        return {"desc": p["desc"], "expires_in": max(0, int(p["expires_at"] - utc_now())),
                "task_id": p.get("task_id")}


# ----------------------------------------------------------------------------
# 8b. AI PROVIDER ENGINE - multi-provider, ordered fallback, env-only secrets
# ----------------------------------------------------------------------------

AI_MODES = ("READ", "PLAN", "EXECUTE", "STOP", "CONFIGURE", "ASK")


@dataclass
class AIProvider:
    name: str
    kind: str                # openai_compat / gemini / anthropic
    base_url: str
    key: str
    model: str
    configured: bool
    last_success: str = ""
    last_error: str = ""
    last_used: str = ""

    def public(self, active: bool) -> dict:
        return {"name": self.name, "model": self.model or None,
                "configured": self.configured, "active": active,
                "last_success": self.last_success or None,
                "last_error": self.last_error or None,
                "last_used": self.last_used or None}


class AIEngine:
    """Real AI understanding layer. Providers configured ONLY via env.

    GROQ_API_KEY/GROQ_MODEL, GEMINI_API_KEY/GEMINI_MODEL, HF_TOKEN/HF_MODEL,
    OPENAI_API_KEY/OPENAI_MODEL/OPENAI_BASE_URL, OPENROUTER_API_KEY/OPENROUTER_MODEL,
    ANTHROPIC_API_KEY/ANTHROPIC_MODEL, AI_PROVIDER_ORDER.
    A provider is usable only when BOTH key and model are set (Gemini never assumes a model).
    """

    DEFS = {
        "groq":        ("openai_compat", "https://api.groq.com/openai/v1", "GROQ_API_KEY", "GROQ_MODEL"),
        "gemini":      ("gemini", "", "GEMINI_API_KEY", "GEMINI_MODEL"),
        "huggingface": ("openai_compat", "https://router.huggingface.co/v1", "HF_TOKEN", "HF_MODEL"),
        "openai":      ("openai_compat", OPENAI_BASE_URL, "OPENAI_API_KEY", "OPENAI_MODEL"),
        "openrouter":  ("openai_compat", "https://openrouter.ai/api/v1", "OPENROUTER_API_KEY", "OPENROUTER_MODEL"),
        "anthropic":   ("anthropic", "https://api.anthropic.com/v1", "ANTHROPIC_API_KEY", "ANTHROPIC_MODEL"),
    }

    def __init__(self, diag: "Diagnostics"):
        self.diag = diag
        order = os.environ.get("AI_PROVIDER_ORDER") or \
            "groq,gemini,huggingface,openai,openrouter,anthropic"
        self.providers: list[AIProvider] = []
        seen = set()
        for raw in order.split(","):
            name = raw.strip().lower()
            if not name or name in seen or name not in self.DEFS:
                continue
            seen.add(name)
            kind, base, key_env, model_env = self.DEFS[name]
            key = os.environ.get(key_env, "").strip()
            model = os.environ.get(model_env, "").strip()
            p = AIProvider(name, kind, base, key, model, configured=bool(key and model))
            if key and not model:
                p.last_error = f"{model_env} not set - provider skipped (no model assumed)"
            self.providers.append(p)
        self.active: Optional[str] = None

    def any_configured(self) -> bool:
        return any(p.configured for p in self.providers)

    def status_public(self) -> dict:
        return {"any_configured": self.any_configured(),
                "active": self.active,
                "providers": [p.public(self.active == p.name) for p in self.providers],
                "order": [p.name for p in self.providers]}

    @staticmethod
    def _extract_json(text: str) -> Optional[dict]:
        if not text:
            return None
        m = re.search(r"\{.*\}", text, re.S)
        if not m:
            return None
        try:
            data = json.loads(m.group(0))
            return data if isinstance(data, dict) else None
        except Exception:
            return None

    async def _chat_openai_compat(self, p: AIProvider, system: str, user: str) -> Optional[str]:
        headers = {"Authorization": f"Bearer {p.key}"}
        if p.name == "openrouter":
            headers["HTTP-Referer"] = "http://localhost"
        async with httpx.AsyncClient(timeout=30) as h:
            r = await h.post(f"{p.base_url}/chat/completions", headers=headers,
                             json={"model": p.model, "temperature": 0,
                                   "messages": [{"role": "system", "content": system},
                                                {"role": "user", "content": user}]})
        if r.status_code != 200:
            raise RuntimeError(f"http {r.status_code}")
        return r.json()["choices"][0]["message"]["content"]

    async def _chat_gemini(self, p: AIProvider, system: str, user: str) -> Optional[str]:
        url = (f"https://generativelanguage.googleapis.com/v1beta/models/"
               f"{p.model}:generateContent")
        async with httpx.AsyncClient(timeout=30) as h:
            r = await h.post(url, headers={"x-goog-api-key": p.key},
                             json={"systemInstruction": {"parts": [{"text": system}]},
                                   "contents": [{"role": "user", "parts": [{"text": user}]}],
                                   "generationConfig": {"temperature": 0,
                                                        "responseMimeType": "application/json"}})
        if r.status_code != 200:
            raise RuntimeError(f"http {r.status_code}")
        data = r.json()
        parts = data["candidates"][0]["content"]["parts"]
        return "".join(part.get("text", "") for part in parts)

    async def _chat_anthropic(self, p: AIProvider, system: str, user: str) -> Optional[str]:
        async with httpx.AsyncClient(timeout=30) as h:
            r = await h.post(f"{p.base_url}/messages",
                             headers={"x-api-key": p.key, "anthropic-version": "2023-06-01"},
                             json={"model": p.model, "max_tokens": 1400, "temperature": 0,
                                   "system": system,
                                   "messages": [{"role": "user", "content": user}]})
        if r.status_code != 200:
            raise RuntimeError(f"http {r.status_code}")
        data = r.json()
        return "".join(c.get("text", "") for c in data.get("content", []))

    async def decide(self, system: str, user: str) -> tuple[Optional[dict], str]:
        """Try providers in configured order; first valid JSON decision wins."""
        for p in self.providers:
            if not p.configured:
                continue
            try:
                if p.kind == "openai_compat":
                    raw = await self._chat_openai_compat(p, system, user)
                elif p.kind == "gemini":
                    raw = await self._chat_gemini(p, system, user)
                else:
                    raw = await self._chat_anthropic(p, system, user)
                data = self._extract_json(raw or "")
                if data is None:
                    raise ValueError("malformed AI JSON")
                p.last_success = iso()
                p.last_used = iso()
                p.last_error = ""
                self.active = p.name
                self.diag.info("AI_PROVIDER", "decision", f"{p.name} ok ({p.model})")
                return data, p.name
            except Exception as exc:
                p.last_error = f"{type(exc).__name__}: {short(str(exc), 120)}"
                self.diag.warn("AI_PROVIDER", "fallback",
                               f"{p.name} failed -> {type(exc).__name__}; trying next provider",
                               error_code=ERR_PROVIDER_UNAVAILABLE)
                continue
        return None, ""


# ----------------------------------------------------------------------------
# 9. TOOL REGISTRY v2 - discoverable, health-tracked, toggleable
# ----------------------------------------------------------------------------

@dataclass
class ToolSpec:
    name: str
    category: str
    description: str
    required_parameters: list[str]
    optional_parameters: list[str]
    permissions_required: list[str]
    read_only: bool
    destructive: bool
    confirmation_required: bool
    supports_background_task: bool
    supported_entities: list[str]
    result_schema: dict
    intents: list[str]                       # brain discovery keys
    handler: Optional[Callable[..., Awaitable[ToolResult]]] = None
    test: Optional[dict] = None              # canned params for safe web test


class ToolRegistry:
    def __init__(self, store: JSONStore, diag: Diagnostics):
        self.store = store                   # tools.json
        self.diag = diag
        self.specs: dict[str, ToolSpec] = {}

    def register(self, spec: ToolSpec) -> None:
        self.specs[spec.name] = spec
        st = self.store.data["tools"].setdefault(spec.name, {})
        st.setdefault("enabled", True)
        st.setdefault("last_used", None)
        st.setdefault("last_error", None)
        st.setdefault("use_count", 0)
        st.setdefault("health", "ok")
        self.store.save()

    def state(self, name: str) -> dict:
        return self.store.data["tools"].get(name, {"enabled": True})

    def is_enabled(self, name: str) -> bool:
        return bool(self.state(name).get("enabled", True))

    def toggle(self, name: str, enabled: bool) -> bool:
        if name not in self.specs:
            return False
        st = self.store.data["tools"].setdefault(name, {})
        st["enabled"] = bool(enabled)
        self.store.save()
        self.diag.info("tools", "toggle", f"{name} -> {'enabled' if enabled else 'disabled'}")
        return True

    def note_use(self, name: str, ok: bool, err: Optional[str] = None) -> None:
        st = self.store.data["tools"].setdefault(name, {})
        st["last_used"] = iso()
        st["use_count"] = st.get("use_count", 0) + 1
        st["last_error"] = None if ok else short(str(err or "error"), 160)
        st["health"] = "ok" if ok else "degraded"
        self.store.save()

    def get(self, name: str) -> Optional[ToolSpec]:
        return self.specs.get(name)

    def by_intent(self, intent: str) -> list[ToolSpec]:
        return [s for s in self.specs.values() if intent in s.intents]

    def search(self, text: str, limit: int = 8) -> list[ToolSpec]:
        """capability discovery: score specs by keyword overlap."""
        n, sk = norm_text(text), skeleton(text)
        scored = []
        for s in self.specs.values():
            hay = f"{s.name} {s.category} {s.description} {' '.join(s.intents)}"
            hn, hs = norm_text(hay), skeleton(hay)
            score = 0
            for w in set(n.split()):
                if len(w) >= 3 and w in hn:
                    score += 2
                ws = skeleton(w)
                if len(ws) >= 4 and ws in hs:
                    score += 1
            for k in s.intents:
                if skeleton(k).replace("_", " ") in sk or norm_text(k).replace("_", " ") in n:
                    score += 5
            if score > 0:
                scored.append((score, s))
        scored.sort(key=lambda x: -x[0])
        return [s for _, s in scored[:limit]]

    def list_public(self) -> list[dict]:
        out = []
        for s in sorted(self.specs.values(), key=lambda x: (x.category, x.name)):
            st = self.state(s.name)
            out.append({"name": s.name, "category": s.category, "description": s.description,
                        "required_parameters": s.required_parameters,
                        "optional_parameters": s.optional_parameters,
                        "permissions_required": s.permissions_required,
                        "read_only": s.read_only, "destructive": s.destructive,
                        "confirmation_required": s.confirmation_required,
                        "supports_background_task": s.supports_background_task,
                        "supported_entities": s.supported_entities,
                        "result_schema": s.result_schema,
                        "enabled": st.get("enabled", True),
                        "last_used": st.get("last_used"), "last_error": st.get("last_error"),
                        "use_count": st.get("use_count", 0), "health": st.get("health", "ok"),
                        "testable": bool(s.test) and s.read_only})
        return out


# ----------------------------------------------------------------------------
# 10. TASK ENGINE v2 - agentic long-running task registry
# ----------------------------------------------------------------------------

@dataclass
class Task:
    task_id: str
    account_id: str
    kind: str
    goal: str
    status: str = TS_PLANNING
    params: dict = field(default_factory=dict)
    progress: dict = field(default_factory=dict)
    rules: dict = field(default_factory=dict)
    allowed_workflows: list[str] = field(default_factory=list)
    start_time: Optional[float] = None
    end_time: Optional[float] = None
    current_action: str = ""
    last_action: str = ""
    next_action: str = ""
    last_error: str = ""
    last_error_code: str = ""
    created_at: float = field(default_factory=utc_now)
    updated_at: float = field(default_factory=utc_now)
    error_count: int = 0
    resumable: bool = True
    interval: int = TICK_SECONDS

    def public(self) -> dict:
        p = self.params or {}
        return {"task_id": self.task_id, "short_id": self.task_id[:12],
                "account_id": self.account_id, "kind": self.kind, "goal": self.goal,
                "status": self.status, "params": p, "progress": self.progress,
                "current_action": self.current_action, "last_action": self.last_action,
                "next_action": self.next_action, "last_error": self.last_error,
                "last_error_code": self.last_error_code, "created_at": iso(self.created_at),
                "updated_at": iso(self.updated_at),
                "start_time": ktm_iso(self.start_time) if self.start_time else None,
                "end_time": ktm_iso(self.end_time) if self.end_time else None,
                "end_ts": self.end_time, "error_count": self.error_count,
                "resumable": self.resumable,
                "targets": len(p.get("targets") or []),
                "source_title": (p.get("source") or {}).get("title", "")}


class TaskEngine:
    def __init__(self, store: JSONStore, diag: Diagnostics):
        self.store = store
        self.diag = diag
        self.runners: dict[str, asyncio.Task] = {}
        self.cancels: dict[str, asyncio.Event] = {}
        self.tick_handler: Optional[Callable[[Task], Awaitable[None]]] = None

    FIELDS = set(Task.__dataclass_fields__)

    def _mk(self, raw: dict) -> Task:
        defaults: dict[str, Any] = {"params": dict, "progress": dict, "rules": dict,
                                    "allowed_workflows": list}
        out = {}
        for k in self.FIELDS:
            v = raw.get(k)
            if v is None and k in defaults:
                v = defaults[k]()
            out[k] = v
        return Task(**out)

    def load_tasks(self) -> dict[str, Task]:
        out = {}
        for tid, raw in (self.store.data.get("tasks") or {}).items():
            try:
                out[tid] = self._mk(raw)
            except Exception:
                self.diag.warn("tasks", "load", f"malformed task skipped: {tid}")
        return out

    def save_task(self, task: Task) -> None:
        task.updated_at = utc_now()
        self.store.data["tasks"][task.task_id] = {k: getattr(task, k) for k in self.FIELDS}
        self.store.save()

    def get(self, task_id: str) -> Optional[Task]:
        raw = (self.store.data.get("tasks") or {}).get(task_id)
        if raw:
            return self._mk(raw)
        matches = [t for t in self.load_tasks().values() if t.task_id.startswith(str(task_id))]
        return matches[0] if len(matches) == 1 else None

    def list(self, account_id: Optional[str] = None) -> list[Task]:
        return [t for t in self.load_tasks().values() if not account_id or t.account_id == account_id]

    def active(self, account_id: Optional[str] = None) -> list[Task]:
        return [t for t in self.list(account_id) if t.status in TS_ACTIVE_SET]

    def create(self, account_id: str, kind: str, goal: str, params: dict,
               duration_sec: Optional[int] = None, end_ts: Optional[float] = None,
               resumable: bool = True, rules: Optional[dict] = None,
               dedup_key: Optional[str] = None, status: str = TS_RUNNING) -> Task:
        if dedup_key:
            for t in self.active(account_id):
                if t.params.get("dedup") == dedup_key:
                    return t
        if len(self.active()) >= MAX_ACTIVE_TASKS:
            raise ValidationError([f"active task limit reached ({MAX_ACTIVE_TASKS}) - stop something first"])
        now = utc_now()
        task = Task(task_id=new_id("task"), account_id=account_id, kind=kind, goal=goal,
                    status=status, params={**params, **({"dedup": dedup_key} if dedup_key else {})},
                    start_time=now,
                    end_time=end_ts or ((now + duration_sec) if duration_sec else None),
                    resumable=resumable, rules=rules or {},
                    progress={"steps": {}, "counters": {}})
        self.save_task(task)
        self.diag.ok("tasks", "create", f"{kind} {task.task_id[:12]} '{short(goal, 40)}'",
                     account_id=account_id, task_id=task.task_id)
        return task

    def start_runner(self, task: Task) -> None:
        r = self.runners.get(task.task_id)
        if r and not r.done():
            return
        cancel = asyncio.Event()
        self.cancels[task.task_id] = cancel
        self.runners[task.task_id] = asyncio.create_task(self._loop(task.task_id, cancel))

    def set_status(self, task: Task, status: str, note: str = "",
                   code: str = "") -> Task:
        task.status = status
        task.last_action = task.current_action or task.last_action
        if note:
            task.last_error = note
        if code:
            task.last_error_code = code
        self.save_task(task)
        self.diag.info("tasks", "status", f"{task.kind} {task.task_id[:12]} -> {status} {short(note, 80)}",
                       account_id=task.account_id, task_id=task.task_id,
                       error_code=code or None)
        if status in TS_TERMINAL | {TS_PAUSED, TS_WAITING}:
            ev = self.cancels.get(task.task_id)
            if ev and status != TS_PAUSED:
                ev.set()
        return task

    async def control(self, task_id: str, action: str) -> ToolResult:
        task = self.get(task_id)
        if task is None:
            return ToolResult.failure(f"task not found: {task_id}", ERR_TASK_NOT_FOUND)
        if action == "stop" or action == "cancel":
            self.set_status(task, TS_STOPPED, "stopped by user")
            return ToolResult.success({"task": task.public()})
        if action == "pause":
            if task.status not in TS_ACTIVE_SET:
                return ToolResult.failure(f"task is {task.status}, not running", ERR_INVALID_PARAMETER)
            self.set_status(task, TS_PAUSED, "paused by user")
            return ToolResult.success({"task": task.public()})
        if action == "resume":
            if task.status != TS_PAUSED:
                return ToolResult.failure(f"task is {task.status}, not PAUSED", ERR_INVALID_PARAMETER)
            task.status = TS_RUNNING
            self.save_task(task)
            self.start_runner(task)
            return ToolResult.success({"task": task.public()})
        if action == "retry":
            if task.status not in (TS_FAILED, TS_EXPIRED, TS_WAITING, TS_PAUSED, TS_STOPPED):
                return ToolResult.failure(f"task is {task.status} - nothing to retry", ERR_INVALID_PARAMETER)
            task.error_count = 0
            task.last_error = ""
            task.last_error_code = ""
            if task.status == TS_EXPIRED and task.end_time and task.end_time < utc_now():
                task.end_time = utc_now() + 6 * 3600
            task.status = TS_RUNNING
            self.save_task(task)
            self.start_runner(task)
            self.diag.ok("tasks", "retry", f"{task.kind} {task.task_id[:12]}",
                         account_id=task.account_id, task_id=task.task_id)
            return ToolResult.success({"task": task.public()})
        return ToolResult.failure(f"unknown action: {action}", ERR_INVALID_PARAMETER)

    async def _loop(self, task_id: str, cancel: asyncio.Event) -> None:
        errors = 0
        while True:
            task = self.get(task_id)
            if task is None or task.status in TS_TERMINAL or task.status == TS_WAITING:
                return
            if task.status != TS_PAUSED:
                if task.end_time and utc_now() > task.end_time:
                    self.set_status(task, TS_EXPIRED, "end time reached")
                    return
                try:
                    if self.tick_handler:
                        await self.tick_handler(task)
                    errors = 0
                    task.error_count = 0
                    task.last_error_code = ""
                    self.save_task(task)
                except asyncio.CancelledError:
                    return
                except FloodWaitError as fe:
                    errors += 1
                    task.error_count = errors
                    task.last_error = f"FloodWait {fe.seconds}s (respected exactly)"
                    task.last_error_code = ERR_FLOOD_WAIT
                    self.save_task(task)
                    self.diag.warn("tasks", "floodwait", f"sleep exactly {fe.seconds}s",
                                   account_id=task.account_id, task_id=task.task_id,
                                   error_code=ERR_FLOOD_WAIT)
                    try:
                        await asyncio.wait_for(cancel.wait(), timeout=fe.seconds)
                        return
                    except asyncio.TimeoutError:
                        continue
                except Exception as exc:
                    errors += 1
                    task.error_count = errors
                    task.last_error = f"{type(exc).__name__}: {short(str(exc), 150)}"
                    self.save_task(task)
                    self.diag.err("tasks", "loop", task.last_error,
                                  account_id=task.account_id, task_id=task.task_id)
                    if errors >= MAX_ERRORS_PER_TASK:
                        self.set_status(task, TS_FAILED, "error limit reached",
                                        ERR_TOOL_UNAVAILABLE)
                        return
                backoff = min(5 * (2 ** max(errors, 0)), 300)
                interval = task.interval if errors == 0 else backoff
            else:
                interval = 10
            try:
                await asyncio.wait_for(cancel.wait(), timeout=max(3, interval))
                return
            except asyncio.TimeoutError:
                continue

    def resume_all(self) -> None:
        for task in self.list():
            if task.status in TS_ACTIVE_SET and task.resumable:
                self.start_runner(task)

    async def shutdown(self) -> None:
        for ev in self.cancels.values():
            ev.set()
        for r in self.runners.values():
            r.cancel()
        await asyncio.sleep(0.3)


# ----------------------------------------------------------------------------
# 11. SCHEDULER (scheduled_jobs.json) - absolute KTM timestamps persisted
# ----------------------------------------------------------------------------

class Scheduler:
    def __init__(self, store: JSONStore, diag: Diagnostics):
        self.store = store
        self.diag = diag
        self.runner: Optional[asyncio.Task] = None
        self.execute_handler: Optional[Callable[[dict], Awaitable[ToolResult]]] = None

    def add(self, account_id: str, run_at: float, payload: dict) -> dict:
        items = self.store.data["schedules"]
        if len([i for i in items.values() if i.get("status") == "PENDING"]) >= MAX_SCHEDULES:
            raise ValidationError([f"schedule limit reached ({MAX_SCHEDULES})"])
        sid = new_id("sch")
        items[sid] = {"schedule_id": sid, "account_id": account_id, "run_at": run_at,
                      "run_at_ktm": ktm_iso(run_at), "payload": payload, "status": "PENDING",
                      "created_at": iso(), "error": None, "error_code": None}
        self.store.save()
        self.diag.ok("scheduler", "add", f"{sid} at {ktm_iso(run_at)}", account_id=account_id)
        return items[sid]

    def cancel(self, sid: str) -> bool:
        item = self.store.data["schedules"].get(sid)
        if item and item.get("status") == "PENDING":
            item["status"] = "CANCELLED"
            self.store.save()
            return True
        return False

    def pending(self, account_id: Optional[str] = None) -> list[dict]:
        return sorted([i for i in self.store.data["schedules"].values()
                       if i.get("status") == "PENDING"
                       and (not account_id or i.get("account_id") == account_id)],
                      key=lambda x: x["run_at"])

    async def _loop(self) -> None:
        while True:
            try:
                for item in [i for i in self.store.data["schedules"].values()
                             if i.get("status") == "PENDING" and i.get("run_at", 0) <= utc_now()]:
                    item["status"] = "RUNNING"
                    self.store.save()
                    try:
                        res = await self.execute_handler(item) if self.execute_handler else \
                            ToolResult.failure("no handler", ERR_TOOL_UNAVAILABLE)
                        item["status"] = "DONE" if res.ok else "FAILED"
                        item["error"] = None if res.ok else res.error
                        item["error_code"] = None if res.ok else res.error_code
                    except Exception as exc:
                        item["status"] = "FAILED"
                        item["error"] = type(exc).__name__
                    self.store.save()
                    self.diag.info("scheduler", "execute", f"{item['schedule_id']} -> {item['status']}",
                                   account_id=item.get("account_id"),
                                   error_code=item.get("error_code"))
            except Exception as exc:
                self.diag.err("scheduler", "loop", type(exc).__name__)
            await asyncio.sleep(4)

    def start(self) -> None:
        if self.runner is None or self.runner.done():
            self.runner = asyncio.create_task(self._loop())


# ----------------------------------------------------------------------------
# 12. MONITOR ENGINE v2 (monitors.json)
# ----------------------------------------------------------------------------

class MonitorEngine:
    def __init__(self, store: JSONStore, diag: Diagnostics):
        self.store = store
        self.diag = diag

    def add(self, account_id: str, channel: dict, condition: str, action: str,
            end_ts: float, task_id: Optional[str], alert_destination: str = "saved_messages",
            goal: str = "") -> dict:
        items = self.store.data["monitors"]
        for m in items.values():
            if m.get("status") == "ACTIVE" and m["account_id"] == account_id and \
                    int(m["channel_id"]) == int(channel["id"]) and m["condition"] == condition:
                return m
        active = [m for m in items.values() if m.get("status") == "ACTIVE"]
        if len(active) >= MAX_MONITORS:
            raise ValidationError([f"monitor limit reached ({MAX_MONITORS})"])
        mid = new_id("mon")
        items[mid] = {"monitor_id": mid, "account_id": account_id,
                      "channel_id": int(channel["id"]), "title": channel.get("title", ""),
                      "kind": channel.get("kind", "channel"), "condition": condition,
                      "action": action, "alert_destination": alert_destination,
                      "start_time": iso(), "end_time": iso(end_ts), "end_ts": end_ts,
                      "end_ktm": ktm_iso(end_ts), "last_processed_id": 0, "status": "ACTIVE",
                      "error_count": 0, "task_id": task_id, "hits": 0, "goal": goal,
                      "last_error": ""}
        self.store.save()
        self.diag.ok("monitors", "add", f"{mid} '{channel.get('title')}' ({condition}) -> {action}",
                     account_id=account_id, task_id=task_id)
        return items[mid]

    def stop(self, monitor_id: str) -> bool:
        m = self.store.data["monitors"].get(monitor_id)
        if m and m.get("status") == "ACTIVE":
            m["status"] = "STOPPED"
            self.store.save()
            self.diag.info("monitors", "stop", monitor_id, account_id=m.get("account_id"))
            return True
        return False

    def stop_all(self, account_id: str) -> int:
        n = 0
        for m in self.store.data["monitors"].values():
            if m.get("account_id") == account_id and m.get("status") == "ACTIVE":
                m["status"] = "STOPPED"
                n += 1
        self.store.save()
        return n

    def update(self, monitor_id: str, **kv) -> Optional[dict]:
        m = self.store.data["monitors"].get(monitor_id)
        if not m:
            return None
        for k, v in kv.items():
            if v is not None and k in ("condition", "action", "end_ts", "status"):
                m[k] = v
                if k == "end_ts":
                    m["end_time"] = iso(v)
                    m["end_ktm"] = ktm_iso(v)
        self.store.save()
        return m

    def active_for(self, account_id: str, chat_id: int) -> list[dict]:
        out = []
        for m in self.store.data["monitors"].values():
            if m.get("status") != "ACTIVE":
                continue
            if m.get("end_ts") and utc_now() > m["end_ts"]:
                m["status"] = "EXPIRED"
                continue
            if m.get("account_id") == account_id and int(m["channel_id"]) == int(chat_id):
                out.append(m)
        return out

    def active_all(self, account_id: Optional[str] = None) -> list[dict]:
        now = utc_now()
        out = []
        for m in self.store.data["monitors"].values():
            if m.get("status") == "ACTIVE" and m.get("end_ts") and now > m["end_ts"]:
                m["status"] = "EXPIRED"
            if m.get("status") == "ACTIVE" and (not account_id or m.get("account_id") == account_id):
                out.append(m)
        return out

    def mark_processed(self, monitor_id: str, msg_id: int, hit: bool = False) -> None:
        m = self.store.data["monitors"].get(monitor_id)
        if not m:
            return
        m["last_processed_id"] = max(m.get("last_processed_id", 0), int(msg_id))
        if hit:
            m["hits"] = m.get("hits", 0) + 1
        self.store.save()


# ----------------------------------------------------------------------------
# 13. CROSS ENGINE v2 - workflow with target queue, persisted per-target
# ----------------------------------------------------------------------------

class CrossEngine:
    def __init__(self, tasks: TaskEngine, accounts: AccountManager,
                 resolver: EntityResolver, diag: Diagnostics):
        self.tasks = tasks
        self.accounts = accounts
        self.resolver = resolver
        self.diag = diag

    def active_for(self, account_id: str, chat_id: int) -> list[Task]:
        return [t for t in self.tasks.list(account_id)
                if t.kind == "cross" and t.status in TS_ACTIVE_SET
                and int((t.params.get("source") or {}).get("id", 0) or 0) == int(chat_id)]

    async def _forward_or_copy(self, client, tgt_ent, src_ent, msg) -> Any:
        try:
            return await client.forward_messages(tgt_ent, msg.id, from_peer=src_ent)
        except ChatForwardsRestrictedError:
            if (getattr(msg, "message", "") or "") or getattr(msg, "media", None):
                return await client.send_message(tgt_ent, msg.message or "", file=msg.media)
            raise

    async def deliver_to_target(self, task: Task, target: dict, src_ent, msg) -> dict:
        account_id = task.account_id
        client = await self.resolver._client(account_id)
        tgt_ent = await self.resolver.resolve(account_id, str(target["id"]))
        res = await self._forward_or_copy(client, tgt_ent.entity, src_ent, msg)
        if isinstance(res, list):
            res = res[0] if res else None
        ok = res is not None
        verified = False
        if ok:
            got = await client.get_messages(tgt_ent.entity, ids=res.id)
            verified = got is not None
        return {"target": target["id"], "sent": ok, "verified": verified,
                "message_id": getattr(res, "id", None)}

    async def deliver(self, task: Task, msg: Any) -> None:
        """one source message -> all queued targets (cursor dedupe)."""
        prog = task.progress
        cursor = int(prog.get("cursor", 0) or 0)
        if msg.id <= cursor:
            return
        processed = deque(prog.get("processed") or [], maxlen=500)
        if msg.id in processed:
            prog["cursor"] = max(cursor, msg.id)
            self.tasks.save_task(task)
            return
        account_id = task.account_id
        src_ent = await self.resolver.resolve(account_id, str(task.params["source"]["id"]))
        counters = prog.setdefault("counters", {})
        for tgt in (task.params.get("targets") or []):
            key = str(tgt["id"])
            stat = counters.setdefault(key, {"title": tgt.get("title", ""), "sent": 0,
                                             "verified": 0, "failed": 0, "last_error": ""})
            task.current_action = f"cross -> {tgt.get('title')}"
            try:
                r = await self.deliver_to_target(task, tgt, src_ent, msg)
                if r["sent"]:
                    stat["sent"] += 1
                    if r["verified"]:
                        stat["verified"] += 1
                    else:
                        stat["failed"] += 1
                        stat["last_error"] = "verification failed"
            except FloodWaitError:
                prog["current_target"] = tgt["id"]
                self.tasks.save_task(task)
                raise
            except ChatAdminRequiredError:
                stat["failed"] += 1
                stat["last_error"] = "no post permission"
            except Exception as exc:
                stat["failed"] += 1
                stat["last_error"] = type(exc).__name__
        processed.append(msg.id)
        prog["processed"] = list(processed)
        prog["cursor"] = max(cursor, msg.id)
        prog["last_delivery_at"] = iso()
        task.last_action = f"delivered msg #{msg.id}"
        self.tasks.save_task(task)

    async def tick(self, task: Task) -> None:
        """workflow queue: initial replied message delivery, then cursor backfill."""
        account_id = task.account_id
        client = await self.resolver._client(account_id)
        src_ent = await self.resolver.resolve(account_id, str(task.params["source"]["id"]))
        prog = task.progress
        smid = task.params.get("source_msg_id")
        if smid and not prog.get("initial_done"):
            msg = await client.get_messages(src_ent.entity, ids=int(smid))
            if msg is None:
                prog["initial_done"] = True
                prog["initial_error"] = ERR_MESSAGE_NOT_FOUND
                self.diag.warn("cross", "initial", "source message not found, continuing live",
                               account_id=account_id, task_id=task.task_id,
                               error_code=ERR_MESSAGE_NOT_FOUND)
            else:
                completed = set(prog.get("completed_targets") or [])
                skipped = prog.setdefault("skipped_targets", [])
                sk_ids = {str(s.get("id")) for s in skipped}
                for tgt in (task.params.get("targets") or []):
                    key = str(tgt["id"])
                    if key in completed or key in sk_ids:
                        continue
                    prog["current_target"] = tgt["id"]
                    task.current_action = f"initial delivery -> {tgt.get('title')}"
                    self.tasks.save_task(task)
                    try:
                        r = await self.deliver_to_target(task, tgt, src_ent, msg)
                        if r["sent"] and r["verified"]:
                            completed.add(key)
                        elif r["sent"]:
                            completed.add(key)
                            skipped.append({"id": tgt["id"], "reason": "delivered but verification failed"})
                        else:
                            skipped.append({"id": tgt["id"], "reason": "send failed"})
                    except FloodWaitError:
                        prog["completed_targets"] = list(completed)
                        self.tasks.save_task(task)
                        raise
                    except ChatAdminRequiredError:
                        skipped.append({"id": tgt["id"], "reason": "no post permission"})
                    except Exception as exc:
                        skipped.append({"id": tgt["id"], "reason": type(exc).__name__})
                    prog["completed_targets"] = list(completed)
                    self.tasks.save_task(task)
                prog["initial_done"] = True
                prog["current_target"] = None
                self.tasks.save_task(task)
        cursor = int(prog.get("cursor", 0) or 0)
        if not cursor:
            recent = await client.get_messages(src_ent.entity, limit=1)
            if recent:
                prog["cursor"] = recent[0].id
                self.tasks.save_task(task)
            return
        batch = await client.get_messages(src_ent.entity, min_id=cursor, limit=30)
        msgs = [m for m in (batch or []) if getattr(m, "id", None) and m.id > cursor]
        for m in reversed(msgs):
            await self.deliver(task, m)

    def reset(self, task: Task) -> Task:
        task.progress = {"steps": {}, "counters": {}, "cursor": 0, "processed": [],
                         "completed_targets": [], "skipped_targets": [], "initial_done": False}
        task.error_count = 0
        task.last_error = ""
        task.status = TS_RUNNING
        self.tasks.save_task(task)
        self.tasks.start_runner(task)
        self.diag.ok("cross", "reset", task.task_id[:12], account_id=task.account_id,
                     task_id=task.task_id)
        return task


# ----------------------------------------------------------------------------
# 14. TOOL IMPLEMENTATIONS (Telethon) - one controlled handler set
# ----------------------------------------------------------------------------

class ToolImpl:
    def __init__(self, accounts: AccountManager, resolver: EntityResolver,
                 memory: MemoryStore, diag: Diagnostics, tasks: TaskEngine,
                 monitors: MonitorEngine, scheduler: Scheduler, cross: CrossEngine,
                 ctx: BrainContext):
        self.accounts = accounts
        self.resolver = resolver
        self.memory = memory
        self.diag = diag
        self.tasks = tasks
        self.monitors = monitors
        self.scheduler = scheduler
        self.cross = cross
        self.ctx = ctx

    async def _client(self, account_id: str) -> "TelegramClient":
        return await self.resolver._client(account_id)

    async def _ent(self, account_id: str, ref: Any) -> ResolvedEntity:
        if isinstance(ref, dict):
            ref = ref.get("id")
        return await self.resolver.resolve(account_id, str(ref))

    async def _admin_rights(self, client: "TelegramClient", ent: ResolvedEntity) -> Optional[dict]:
        try:
            me = await client.get_me()
            from telethon.tl.types import ChannelParticipantsAdmins
            async for p in client.iter_participants(ent.entity, limit=100,
                                                    filter=ChannelParticipantsAdmins()):
                if p.id == me.id:
                    ar = getattr(p.participant, "admin_rights", None)
                    if ar is None:
                        return {"is_admin": True, "is_creator": True}
                    return {"is_admin": True,
                            "post": getattr(ar, "post_messages", True),
                            "edit": getattr(ar, "edit_messages", True),
                            "delete": getattr(ar, "delete_messages", True),
                            "ban": getattr(ar, "ban_users", True),
                            "invite": getattr(ar, "invite_users", True),
                            "is_creator": getattr(p.participant, "creator", False) or False}
            return {"is_admin": False}
        except Exception:
            return None

    async def _verify(self, client, entity, msg_id: int) -> bool:
        try:
            got = await client.get_messages(entity, ids=msg_id)
            return got is not None and getattr(got, "id", None) == msg_id
        except Exception:
            return False

    # ---------------- ACCOUNT ----------------
    async def account_info(self, account_id: str) -> ToolResult:
        rt = await self.accounts.connect(account_id)
        cfg = self.accounts.get(account_id)
        data = {"label": cfg["label"], "managed_account_id": account_id,
                "connected": rt.connected, "authorized": rt.authorized,
                "api_mode": "env" if not cfg.get("api_id") else "account",
                "main_channels": len(cfg.get("main_channels") or [])}
        if rt.authorized:
            me = await rt.client.get_me()
            data.update({"name": rt.self_name, "username": rt.self_username,
                         "telegram_id": rt.self_id, "phone": mask_phone(getattr(me, "phone", "") or ""),
                         "premium": bool(getattr(me, "premium", False)),
                         "bot": bool(getattr(me, "bot", False))})
        data["note"] = "secrets (api hash, session, passwords, OTP, keys) are never exposed"
        return ToolResult.success(data, verification={"source": "get_me + local state"})

    async def connection_status(self, account_id: str) -> ToolResult:
        rt = self.accounts.runtime.get(account_id) or AccountRuntime(account_id)
        data = {"label": self.accounts.get(account_id)["label"], "connected": rt.connected,
                "authorized": rt.authorized, "last_error": rt.last_error or None}
        if rt.connected and rt.authorized:
            t0 = utc_now()
            try:
                await rt.client.get_me()
                data["round_trip_ms"] = int((utc_now() - t0) * 1000)
            except Exception as exc:
                data["round_trip_ms"] = None
                data["probe_error"] = type(exc).__name__
        return ToolResult.success(data)

    async def account_permissions(self, account_id: str) -> ToolResult:
        client = await self._client(account_id)
        out = []
        for ch in self.accounts.get_main_channels(account_id):
            try:
                ent = await self.resolver.resolve(account_id, str(ch["id"]))
                rights = await self._admin_rights(client, ent)
                out.append({"channel": ent.brief(), "rights": rights})
            except EntityResolutionError as exc:
                out.append({"channel": str(ch["id"]), "rights": None, "error": short(str(exc), 80)})
        return ToolResult.success({"main_channel_rights": out})

    async def account_sessions(self, account_id: str) -> ToolResult:
        client = await self._client(account_id)
        try:
            res = await client(fn.account.GetAuthorizationsRequest())
            auths = [{"current": getattr(a, "current", False),
                      "device": getattr(a, "device_model", "?"),
                      "app": f"{getattr(a, 'app_name', '?')} {getattr(a, 'app_version', '')}".strip(),
                      "active": iso(getattr(a, "date_active", 0) or 0)}
                     for a in res.authorizations[:10]]
            return ToolResult.success({"sessions": auths, "count": len(res.authorizations)})
        except Exception as exc:
            return ToolResult.failure(f"sessions unavailable: {type(exc).__name__}", ERR_NOT_SUPPORTED)

    # ---------------- DIALOGS ----------------
    async def list_dialogs(self, account_id: str, limit: int = 25) -> ToolResult:
        dialogs = await self.resolver._dialogs(account_id)
        items = []
        for d in dialogs[:int(limit)]:
            ent = d["entity"]
            kind = ("channel" if tl is not None and isinstance(ent, tl.Channel) and not ent.megagroup
                    else "group" if tl is not None and isinstance(ent, (tl.Channel, tl.Chat)) else "user")
            items.append({"id": d["id"], "title": d["title"], "username": d["username"], "kind": kind})
            if kind in ("channel", "group"):
                self.memory.learn_channel(account_id, str(d["id"]), d["title"], d["username"])
        return ToolResult.success({"dialogs": items, "count": len(items)})

    async def list_channels(self, account_id: str) -> ToolResult:
        r = await self.list_dialogs(account_id, limit=200)
        chans = [d for d in r.data["dialogs"] if d["kind"] in ("channel", "group")]
        return ToolResult.success({"channels": chans[:80], "count": len(chans)})

    async def inspect_channel(self, account_id: str, ref: Any) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        rights = await self._admin_rights(client, ent)
        msgs = []
        async for m in client.iter_messages(ent.entity, limit=20):
            if getattr(m, "id", None) is None:
                continue
            sender = ""
            try:
                if getattr(m, "fwd_from", None):
                    sender = "forwarded"
                elif m.sender:
                    sender = getattr(m.sender, "title", None) or getattr(m.sender, "first_name", "") or str(m.sender_id)
            except Exception:
                pass
            msgs.append({"id": m.id, "date": iso(m.date.timestamp()) if m.date else None,
                         "text": short(getattr(m, "raw_text", "") or
                                       (f"[{m.media.__class__.__name__}]" if getattr(m, "media", None) else ""), 90),
                         "sender": short(sender, 40), "views": getattr(m, "views", None)})
        participants = None
        try:
            full = await client(fn.channels.GetFullChannelRequest(ent.entity))
            participants = full.full_chat.participants_count
        except Exception:
            pass
        self.memory.learn_channel(account_id, str(ent.id), ent.title, ent.username)
        named = [m for m in msgs if m.get("sender") and m["sender"] != "forwarded"]
        return ToolResult.success(
            {"id": ent.id, "title": ent.title, "username": ent.username, "kind": ent.kind,
             "participants": participants, "rights": rights,
             "message_count_sampled": len(msgs), "named_senders_in_sample": len(named),
             "last_messages": msgs},
            verification={"fetched": True, "sampled": len(msgs)})

    async def inspect_chat(self, account_id: str, ref: Any) -> ToolResult:
        return await self.inspect_channel(account_id, ref)

    async def resolve_entity(self, account_id: str, ref: Any) -> ToolResult:
        ent = await self.resolver.resolve(account_id, str(ref))
        return ToolResult.success(ent.brief_dict())

    async def resolve_username(self, account_id: str, username: str) -> ToolResult:
        return await self.resolve_entity(account_id, username)

    async def resolve_numeric_id(self, account_id: str, ref: Any) -> ToolResult:
        return await self.resolve_entity(account_id, ref)

    # ---------------- FOLDERS ----------------
    async def list_folders(self, account_id: str) -> ToolResult:
        folders = await self.resolver.get_folders(account_id, force=False)
        return ToolResult.success({"folders": [{"id": f["id"], "title": f["title"],
                                                "peer_count": len(f.get("peers", []))}
                                               for f in folders],
                                   "count": len(folders)})

    async def resolve_folder_by_name(self, account_id: str, name: str) -> ToolResult:
        f = await self.resolver.resolve_folder(account_id, name)
        if not f:
            return ToolResult.failure(f"no Telegram dialog folder matches '{short(name, 40)}'",
                                      ERR_ENTITY_NOT_FOUND)
        return ToolResult.success({"id": f["id"], "title": f["title"],
                                   "peer_count": len(f.get("peers", []))})

    async def inspect_folder(self, account_id: str, name: str = "",
                             folder_id: Optional[int] = None) -> ToolResult:
        folders = await self.resolver.get_folders(account_id)
        folder = None
        if folder_id is not None:
            folder = next((f for f in folders if f["id"] == int(folder_id)), None)
        elif name:
            folder = await self.resolver.resolve_folder(account_id, name)
        if not folder:
            return ToolResult.failure(f"folder not found: '{short(name or str(folder_id), 40)}'",
                                      ERR_FOLDER_NOT_FOUND)
        peers = await self.resolver.folder_peers(account_id, folder)
        resolved_n = sum(len(peers[k]) for k in ("channels", "groups", "users"))
        if len(folder.get("peers", [])) == 0:
            return ToolResult.failure(f"folder '{folder['title']}' contains no chats",
                                      ERR_FOLDER_EMPTY)
        if resolved_n == 0 and folder.get("peers"):
            return ToolResult.failure(f"folder '{folder['title']}' peers could not be resolved from this account",
                                      ERR_FOLDER_RESOLUTION_FAILED)
        return ToolResult.success({"id": folder["id"], "title": folder["title"],
                                   "channels": peers["channels"], "groups": peers["groups"],
                                   "users": peers["users"], "unresolved": peers["unresolved"],
                                   "total_peers": len(folder.get("peers", []))},
                                  verification={"resolved_peers": sum(len(peers[k]) for k in
                                                                      ("channels", "groups", "users"))})

    async def list_folder_channels(self, account_id: str, name: str) -> ToolResult:
        r = await self.inspect_folder(account_id, name=name)
        if not r.ok:
            return r
        chans = r.data["channels"]
        if not chans:
            return ToolResult.failure(f"folder '{r.data['title']}' has no channels",
                                      ERR_FOLDER_EMPTY)
        return ToolResult.success({"folder": r.data["title"], "channels": chans,
                                   "count": len(chans)})

    # ---------------- MESSAGES ----------------
    async def get_message(self, account_id: str, ref: Any, message_id: int) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        m = await client.get_messages(ent.entity, ids=int(message_id))
        if m is None:
            return ToolResult.failure(f"message #{message_id} not found in {ent.title}",
                                      ERR_MESSAGE_NOT_FOUND)
        return ToolResult.success({"id": m.id, "date": iso(m.date.timestamp()) if m.date else None,
                                   "text": short(getattr(m, "raw_text", "") or "", 300),
                                   "has_media": bool(getattr(m, "media", None)),
                                   "views": getattr(m, "views", None)},
                                  verification={"fetched": True})

    async def get_recent_messages(self, account_id: str, ref: Any, limit: int = 8) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        out = []
        async for m in client.iter_messages(ent.entity, limit=min(int(limit), 30)):
            if getattr(m, "id", None) is not None:
                out.append({"id": m.id, "date": iso(m.date.timestamp()) if m.date else None,
                            "text": short(getattr(m, "raw_text", "") or
                                          (f"[{m.media.__class__.__name__}]" if getattr(m, "media", None) else ""), 110),
                            "views": getattr(m, "views", None)})
        return ToolResult.success({"entity": ent.brief(), "messages": out, "count": len(out)})

    async def search_messages(self, account_id: str, ref: Any, query: str, limit: int = 8) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        out = []
        async for m in client.iter_messages(ent.entity, limit=min(int(limit), 25), search=query):
            if getattr(m, "id", None) is not None:
                out.append({"id": m.id,
                            "date": iso(m.date.timestamp()) if m.date else None,
                            "text": short(getattr(m, "raw_text", "") or "", 140)})
        return ToolResult.success({"entity": ent.brief(), "query": query,
                                   "matches": out, "count": len(out)})

    async def send_message(self, account_id: str, ref: Any, text: str) -> ToolResult:
        client = await self._client(account_id)
        tgt = await self._ent(account_id, ref)
        m = await client.send_message(tgt.entity, text)
        verified = await self._verify(client, tgt.entity, m.id)
        self.diag.ok("tool.msg", "send_message", f"posted to {tgt.title} #{m.id} verified={verified}",
                     account_id=account_id)
        return ToolResult.success({"target": tgt.brief(), "message_id": m.id},
                                  verification={"verified": verified})

    async def forward_message(self, account_id: str, source: Any, target: Any,
                              message_ids: Optional[list] = None, count: int = 1) -> ToolResult:
        client = await self._client(account_id)
        src = await self._ent(account_id, source)
        tgt = await self._ent(account_id, target)
        ids = [int(i) for i in (message_ids or [])]
        if not ids:
            async for m in client.iter_messages(src.entity, limit=min(int(count), 50)):
                if getattr(m, "id", None) is not None:
                    ids.append(m.id)
            ids.reverse()
        sent, verified, failed, last_error = 0, 0, 0, ""
        for chunk_start in range(0, len(ids), 50):
            chunk = ids[chunk_start:chunk_start + 50]
            try:
                res = await client.forward_messages(tgt.entity, chunk, from_peer=src.entity)
                res_list = res if isinstance(res, list) else [res]
                for r in res_list:
                    if r is not None:
                        sent += 1
                        if await self._verify(client, tgt.entity, r.id):
                            verified += 1
            except ChatForwardsRestrictedError:
                for mid in chunk:
                    m = await client.get_messages(src.entity, ids=mid)
                    if not m:
                        failed += 1
                        continue
                    r = await client.send_message(tgt.entity, m.message or "", file=m.media)
                    if r is not None:
                        sent += 1
                        if await self._verify(client, tgt.entity, r.id):
                            verified += 1
            except FloodWaitError:
                raise
            except Exception as exc:
                failed += len(chunk)
                last_error = type(exc).__name__
        self.diag.ok("tool.msg", "forward_message",
                     f"{sent}/{len(ids)} {src.title} -> {tgt.title} verified={verified}",
                     account_id=account_id)
        return ToolResult.success({"source": src.brief(), "target": tgt.brief(),
                                   "requested": len(ids), "sent": sent, "failed": failed,
                                   "last_error": last_error or None},
                                  verification={"verified": verified})

    async def delete_message(self, account_id: str, ref: Any, message_ids: Optional[list] = None,
                             count: int = 5) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        ids = [int(i) for i in (message_ids or [])]
        if not ids:
            rights = await self._admin_rights(client, ent)
            if rights is not None and not rights.get("is_admin"):
                me = await client.get_me()
                async for m in client.iter_messages(ent.entity, limit=int(count), from_user=me.id):
                    ids.append(m.id)
                if not ids:
                    return ToolResult.failure(
                        f"I can access {ent.title} but I don't have permission to delete others' "
                        f"messages there, and found no own messages to delete.",
                        ERR_PERMISSION_DENIED, status="PERMISSION_REQUIRED")
            else:
                async for m in client.iter_messages(ent.entity, limit=int(count)):
                    if getattr(m, "id", None) is not None:
                        ids.append(m.id)
        if not ids:
            return ToolResult.failure(f"no messages found to delete in {ent.title}",
                                      ERR_MESSAGE_NOT_FOUND)
        deleted, gone, failed = 0, 0, 0
        for i in range(0, len(ids), 50):
            chunk = ids[i:i + 50]
            try:
                await client.delete_messages(ent.entity, chunk)
                deleted += len(chunk)
                back = await client.get_messages(ent.entity, ids=chunk)
                back_list = back if isinstance(back, list) else [back]
                gone += sum(1 for g in back_list if g is None)
            except FloodWaitError:
                raise
            except ChatAdminRequiredError:
                return ToolResult.failure(
                    f"I can access {ent.title} but I don't have permission to delete messages there.",
                    ERR_PERMISSION_DENIED, status="PERMISSION_REQUIRED")
            except Exception as exc:
                failed += len(chunk)
                self.diag.err("tool.msg", "delete_message", type(exc).__name__, account_id=account_id)
        self.diag.ok("tool.msg", "delete_message",
                     f"{deleted}/{len(ids)} deleted in {ent.title} (gone {gone})", account_id=account_id)
        return ToolResult.success({"entity": ent.brief(), "requested": len(ids),
                                   "deleted": deleted, "failed": failed},
                                  verification={"verified_gone": gone})

    async def edit_message(self, account_id: str, ref: Any, message_id: int, text: str) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        m = await client.edit_message(ent.entity, int(message_id), text)
        verified = False
        back = await client.get_messages(ent.entity, ids=int(message_id))
        if back is not None and (getattr(back, "raw_text", "") or "") == text:
            verified = True
        return ToolResult.success({"entity": ent.brief(), "message_id": getattr(m, "id", None)},
                                  verification={"verified": verified})

    # ---------------- MEDIA ----------------
    async def inspect_media(self, account_id: str, ref: Any, message_id: int) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        m = await client.get_messages(ent.entity, ids=int(message_id))
        if m is None:
            return ToolResult.failure(f"message #{message_id} not found", ERR_MESSAGE_NOT_FOUND)
        media = getattr(m, "media", None)
        if media is None:
            return ToolResult.success({"entity": ent.brief(), "message_id": int(message_id),
                                       "media_type": None})
        size = None
        try:
            size = getattr(getattr(media, "document", None), "size", None)
        except Exception:
            size = None
        return ToolResult.success({"entity": ent.brief(), "message_id": int(message_id),
                                   "media_type": media.__class__.__name__, "size_bytes": size})

    async def send_media(self, account_id: str, target: Any, source: Any,
                         source_message_id: int) -> ToolResult:
        client = await self._client(account_id)
        src = await self._ent(account_id, source)
        tgt = await self._ent(account_id, target)
        m = await client.get_messages(src.entity, ids=int(source_message_id))
        if m is None:
            return ToolResult.failure(f"source message #{source_message_id} not found",
                                      ERR_MESSAGE_NOT_FOUND)
        if not getattr(m, "media", None):
            return ToolResult.failure(f"source message #{source_message_id} has no media",
                                      ERR_INVALID_PARAMETER)
        r = await client.send_message(tgt.entity, m.message or "", file=m.media)
        verified = await self._verify(client, tgt.entity, r.id) if r else False
        return ToolResult.success({"target": tgt.brief(), "message_id": getattr(r, "id", None)},
                                  verification={"verified": verified})

    # ---------------- MONITORING ----------------
    async def create_monitor(self, account_id: str, channel: Any, condition: str = "all",
                             action: str = "alert_only", end_ts: Optional[float] = None,
                             duration_sec: Optional[int] = None, goal: str = "") -> ToolResult:
        if action not in ("alert_only",):
            action = "alert_only"
        ent = await self._ent(account_id, channel)
        if not end_ts:
            end_ts = utc_now() + int(duration_sec or 12 * 3600)
        if end_ts <= utc_now():
            return ToolResult.failure("monitor end time is already in the past",
                                      ERR_INVALID_PARAMETER)
        chan = {"id": ent.id, "title": ent.title, "kind": ent.kind}
        task = self.tasks.create(account_id, "monitor",
                                 goal or f"monitor {ent.title} ({condition})",
                                 {"channel": chan, "condition": condition, "action": action},
                                 end_ts=end_ts, resumable=True, status=TS_MONITORING,
                                 dedup_key=f"mon:{account_id}:{ent.id}:{condition}",
                                 rules={"alert_destination": "saved_messages",
                                        "no_destructive_actions": True})
        mon = self.monitors.add(account_id, chan, condition, action, end_ts, task.task_id,
                                goal=goal)
        task.params["monitor_id"] = mon["monitor_id"]
        task.progress["steps"] = {"channel_resolved": "done", "watch_registered": "done",
                                  "alerts": "listening"}
        self.tasks.save_task(task)
        self.tasks.start_runner(task)
        self.memory.learn_channel(account_id, str(ent.id), ent.title, ent.username)
        return ToolResult.success({"monitor_id": mon["monitor_id"], "task_id": task.task_id,
                                   "channel": ent.brief(), "condition": condition, "action": action,
                                   "end_ktm": ktm_iso(end_ts),
                                   "alert_destination": "saved_messages"},
                                  verification={"monitor_registered": True})

    async def list_monitors(self, account_id: str) -> ToolResult:
        mons = self.monitors.active_all(account_id)
        return ToolResult.success({"monitors": mons, "count": len(mons)})

    async def stop_monitor(self, account_id: str, monitor_id: str = "",
                           channel: Any = None) -> ToolResult:
        stopped = 0
        ids: list[str] = []
        if monitor_id:
            m = self.monitors.store.data["monitors"].get(str(monitor_id))
            if not m:
                return ToolResult.failure(f"monitor not found: {monitor_id}", ERR_TASK_NOT_FOUND)
            if self.monitors.stop(str(monitor_id)):
                stopped += 1
                ids.append(str(monitor_id))
        elif channel is not None:
            ent = await self._ent(account_id, channel)
            for m in self.monitors.active_all(account_id):
                if int(m["channel_id"]) == int(ent.id):
                    self.monitors.stop(m["monitor_id"])
                    stopped += 1
                    ids.append(m["monitor_id"])
        else:
            for m in self.monitors.active_all(account_id):
                if self.monitors.stop(m["monitor_id"]):
                    stopped += 1
                    ids.append(m["monitor_id"])
        for t in self.tasks.list(account_id):
            if t.kind == "monitor" and t.status in (TS_MONITORING, TS_RUNNING, TS_PAUSED):
                mid = t.params.get("monitor_id", "")
                m = self.monitors.store.data["monitors"].get(mid)
                if not m or m.get("status") != "ACTIVE":
                    self.tasks.set_status(t, TS_STOPPED, "monitor stopped")
        if stopped == 0 and (monitor_id or channel is not None):
            return ToolResult.failure("no active monitor matches that target - nothing was stopped",
                                      ERR_NO_ACTIVE_MONITOR)
        return ToolResult.success({"stopped": stopped, "ids": ids,
                                   "verified": all(
                                       self.monitors.store.data["monitors"].get(i, {}).get("status") == "STOPPED"
                                       for i in ids)},
                                  verification={"stopped_ids": ids})

    async def update_monitor(self, account_id: str, monitor_id: str, condition: str = "",
                             action: str = "", end_ts: Optional[float] = None) -> ToolResult:
        m = self.monitors.update(str(monitor_id), condition=condition or None,
                                 action=action or None, end_ts=end_ts)
        if not m:
            return ToolResult.failure(f"monitor not found: {monitor_id}", ERR_TASK_NOT_FOUND)
        return ToolResult.success({"monitor": m})

    async def monitor_new_posts(self, account_id: str, channel: Any, **kw) -> ToolResult:
        kw["condition"] = "all"
        return await self.create_monitor(account_id, channel, **kw)

    async def monitor_unknown_sender(self, account_id: str, channel: Any, **kw) -> ToolResult:
        kw["condition"] = "unknown"
        return await self.create_monitor(account_id, channel, **kw)

    async def alert_saved_messages(self, account_id: str, text: str) -> ToolResult:
        try:
            client = await self._client(account_id)
            m = await client.send_message("me", text)
            return ToolResult.success({"message_id": m.id}, verification={"verified": True})
        except FloodWaitError:
            raise
        except Exception as exc:
            return ToolResult.failure(type(exc).__name__, ERR_TOOL_UNAVAILABLE, retryable=True)

    # ---------------- TASKS ----------------
    async def list_tasks(self, account_id: str, include_done: bool = False) -> ToolResult:
        keep = TS_CONTROLLABLE | {TS_COMPLETED} if include_done else TS_CONTROLLABLE
        items = [t.public() for t in sorted(self.tasks.list(account_id), key=lambda x: -x.updated_at)
                 if t.status in keep]
        return ToolResult.success({"tasks": items, "count": len(items)})

    async def _task_action(self, account_id: str, task_id: str, action: str) -> ToolResult:
        t = self.tasks.get(str(task_id))
        if not t:
            return ToolResult.failure(f"task not found: {task_id}", ERR_TASK_NOT_FOUND)
        if t.account_id != account_id:
            return ToolResult.failure("task belongs to a different account (isolation)",
                                      ERR_PERMISSION_DENIED)
        if action in ("stop", "cancel") and t.params.get("monitor_id"):
            self.monitors.stop(t.params["monitor_id"])
        return await self.tasks.control(t.task_id, action)

    async def pause_task(self, account_id: str, task_id: str) -> ToolResult:
        return await self._task_action(account_id, task_id, "pause")

    async def resume_task(self, account_id: str, task_id: str) -> ToolResult:
        return await self._task_action(account_id, task_id, "resume")

    async def stop_task(self, account_id: str, task_id: str) -> ToolResult:
        return await self._task_action(account_id, task_id, "stop")

    async def cancel_task(self, account_id: str, task_id: str) -> ToolResult:
        return await self._task_action(account_id, task_id, "cancel")

    async def retry_task(self, account_id: str, task_id: str) -> ToolResult:
        return await self._task_action(account_id, task_id, "retry")

    async def task_status(self, account_id: str, task_id: str = "") -> ToolResult:
        if not task_id:
            acts = self.tasks.active(account_id)
            return ToolResult.success({"active": [t.public() for t in acts],
                                       "count": len(acts)})
        t = self.tasks.get(str(task_id))
        if not t or t.account_id != account_id:
            return ToolResult.failure(f"task not found: {task_id}", ERR_TASK_NOT_FOUND)
        return ToolResult.success({"task": t.public()})

    # ---------------- SCHEDULING ----------------
    async def schedule_action(self, account_id: str, text: str = "", kind: str = "post_main",
                              run_at: Optional[float] = None, in_sec: Optional[int] = None) -> ToolResult:
        ts = run_at or (utc_now() + int(in_sec or 0))
        if not run_at and not in_sec:
            return ToolResult.failure("when should it run? (give time or duration)",
                                      ERR_INVALID_PARAMETER)
        item = self.scheduler.add(account_id, ts, {"type": kind, "text": text})
        return ToolResult.success({"schedule_id": item["schedule_id"],
                                   "run_at_ktm": item["run_at_ktm"], "kind": kind})

    async def list_schedules(self, account_id: str) -> ToolResult:
        return ToolResult.success({"schedules": self.scheduler.pending(account_id)})

    async def cancel_schedule(self, account_id: str, schedule_id: str = "",
                              all_: bool = False) -> ToolResult:
        cancelled = 0
        if all_:
            for item in self.scheduler.pending(account_id):
                if self.scheduler.cancel(item["schedule_id"]):
                    cancelled += 1
        else:
            if not schedule_id:
                return ToolResult.failure("which schedule id?", ERR_INVALID_PARAMETER)
            cancelled = 1 if self.scheduler.cancel(str(schedule_id)) else 0
            if not cancelled:
                return ToolResult.failure(f"schedule not found: {schedule_id}", ERR_TASK_NOT_FOUND)
        return ToolResult.success({"cancelled": cancelled})

    # ---------------- CROSS ----------------
    async def resolve_cross_source(self, account_id: str, ref: Any = None,
                                   reply_hint: Optional[dict] = None) -> ToolResult:
        if reply_hint and reply_hint.get("id"):
            return ToolResult.success({"source": reply_hint, "via": "reply"})
        if ref is None:
            return ToolResult.failure("no reply context and no explicit source given",
                                      ERR_ENTITY_NOT_FOUND)
        ent = await self._ent(account_id, ref)
        self.memory.learn_channel(account_id, str(ent.id), ent.title, ent.username)
        return ToolResult.success({"source": ent.brief_dict(), "via": "explicit"})

    async def resolve_cross_targets(self, account_id: str, mode: str = "main",
                                    folder_name: str = "") -> ToolResult:
        if mode == "folder":
            fr = await self.list_folder_channels(account_id, folder_name)
            if not fr.ok:
                return fr
            targets = fr.data["channels"]
            via = f"folder '{fr.data['folder']}'"
        else:
            targets = self.accounts.get_main_channels(account_id)
            via = "configured main channels"
        return ToolResult.success({"targets": targets, "count": len(targets), "via": via})

    async def validate_cross(self, account_id: str, source_id: Any,
                             targets: list) -> ToolResult:
        client = await self._client(account_id)
        valid, skipped = [], []
        seen = set()
        for t in targets:
            t_id = t.get("id") if isinstance(t, dict) else t
            if int(t_id) == int(source_id):
                skipped.append({"id": t_id, "title": (t.get("title") if isinstance(t, dict) else ""),
                                "reason": "target equals source"})
                continue
            if str(t_id) in seen:
                skipped.append({"id": t_id, "reason": "duplicate"})
                continue
            try:
                ent = await self.resolver.resolve(account_id, str(t_id))
            except EntityResolutionError as exc:
                skipped.append({"id": t_id, "reason": short(str(exc), 90)})
                continue
            rights = await self._admin_rights(client, ent)
            perm = "unknown"
            if rights is not None:
                if rights.get("is_admin") and rights.get("post") is False:
                    skipped.append({"id": ent.id, "title": ent.title,
                                    "reason": "admin but post_messages disabled"})
                    continue
                perm = "ok" if rights.get("is_admin") else "member"
            seen.add(str(ent.id))
            valid.append({"id": ent.id, "title": ent.title, "username": ent.username,
                          "permission": perm})
        return ToolResult.success({"valid": valid, "skipped": skipped,
                                   "valid_count": len(valid)},
                                  verification={"resolved": len(valid)})

    async def create_cross_plan(self, account_id: str, source: dict, targets: list,
                                source_msg_id: Optional[int] = None) -> ToolResult:
        plan = {"plan_id": new_id("xplan"), "account_id": account_id, "created_at": iso(),
                "source": source, "source_msg_id": source_msg_id, "targets": targets}
        self.ctx.update(account_id, "cross", last_plan=plan)
        return ToolResult.success({"plan": plan})

    async def start_cross(self, account_id: str, source: dict, targets: list,
                          source_msg_id: Optional[int] = None,
                          duration_sec: Optional[int] = None,
                          end_ts: Optional[float] = None) -> ToolResult:
        for t in self.tasks.list(account_id):
            if t.kind == "cross" and t.status in TS_ACTIVE_SET and \
                    int((t.params.get("source") or {}).get("id", 0) or 0) == int(source["id"]):
                return ToolResult.failure(
                    f"cross already active for {source.get('title')} "
                    f"(task {t.task_id[:12]}) - stop or reset it first",
                    ERR_INVALID_PARAMETER)
        task = self.tasks.create(
            account_id, "cross", f"cross {source.get('title')} -> {len(targets)} targets",
            {"source": dict(source), "targets": targets, "source_msg_id": source_msg_id,
             "skipped": []},
            duration_sec=duration_sec, end_ts=end_ts, resumable=True, status=TS_RUNNING,
            dedup_key=f"cross:{account_id}:{source['id']}",
            rules={"verify_each_delivery": True, "floodwait": "honor exactly",
                   "never_source_equals_target": True})
        task.progress["steps"] = {"source_resolved": "done", "targets_validated": "done",
                                  "delivery": "waiting"}
        task.next_action = "initial delivery" if source_msg_id else "watch live posts"
        self.tasks.save_task(task)
        self.tasks.start_runner(task)
        return ToolResult.success({"task_id": task.task_id, "source": source,
                                   "targets": len(targets),
                                   "source_msg_id": source_msg_id,
                                   "end_ktm": ktm_iso(task.end_time) if task.end_time else None},
                                  verification={"task_created": True})

    async def stop_cross(self, account_id: str, task_id: str = "") -> ToolResult:
        stopped = 0
        ids = []
        for t in self.tasks.list(account_id):
            if t.kind == "cross" and t.status in TS_ACTIVE_SET | {TS_PAUSED} and \
                    (not task_id or t.task_id == str(task_id) or t.task_id.startswith(str(task_id))):
                self.tasks.set_status(t, TS_STOPPED, "cross stopped by user")
                stopped += 1
                ids.append(t.task_id)
        if not stopped:
            return ToolResult.failure("no active cross task found", ERR_TASK_NOT_FOUND)
        return ToolResult.success({"stopped": stopped, "task_ids": ids})

    async def reset_cross(self, account_id: str, task_id: str = "") -> ToolResult:
        task = None
        for t in self.tasks.list(account_id):
            if t.kind == "cross" and (not task_id or t.task_id == str(task_id)
                                      or t.task_id.startswith(str(task_id))):
                task = t
                break
        if not task:
            return ToolResult.failure("no cross task found to reset", ERR_TASK_NOT_FOUND)
        self.cross.reset(task)
        return ToolResult.success({"task_id": task.task_id, "state": "cursor + queue cleared"})

    async def cross_status(self, account_id: str) -> ToolResult:
        items = []
        for t in self.tasks.list(account_id):
            if t.kind == "cross":
                p = t.progress or {}
                items.append({"task_id": t.task_id, "status": t.status,
                              "source": (t.params.get("source") or {}).get("title"),
                              "targets": len(t.params.get("targets") or []),
                              "completed_targets": p.get("completed_targets") or [],
                              "skipped_targets": p.get("skipped_targets") or [],
                              "current_target": p.get("current_target"),
                              "queue_initial_done": p.get("initial_done"),
                              "cursor": p.get("cursor"), "counters": p.get("counters")})
        return ToolResult.success({"cross_tasks": items, "count": len(items)})

    # ---------------- ADMIN / PERMISSIONS ----------------
    async def inspect_admin_rights(self, account_id: str, ref: Any) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        from telethon.tl.types import ChannelParticipantsAdmins
        try:
            admins = []
            async for p in client.iter_participants(ent.entity, limit=100,
                                                    filter=ChannelParticipantsAdmins()):
                admins.append({"id": p.id,
                               "name": f"{getattr(p, 'first_name', '') or ''} {getattr(p, 'last_name', '') or ''}".strip(),
                               "username": getattr(p, "username", "") or "",
                               "creator": getattr(p.participant, "creator", False)})
            return ToolResult.success({"entity": ent.brief(), "admins": admins,
                                       "count": len(admins)})
        except ChatAdminRequiredError:
            return ToolResult.failure("admin list hidden - I am not an admin there",
                                      ERR_PERMISSION_DENIED, status="PERMISSION_REQUIRED")

    async def inspect_permissions(self, account_id: str, ref: Any) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        rights = await self._admin_rights(client, ent)
        abilities = {"entity": ent.brief(), "kind": ent.kind}
        if rights is None:
            abilities.update({"is_admin": "unknown", "can_post": "likely (member)",
                              "can_delete_others": "no (not admin or unknown)"})
        elif rights.get("is_admin"):
            abilities.update({"is_admin": True, "can_post": rights.get("post"),
                              "can_delete_others": rights.get("delete"),
                              "can_ban": rights.get("ban"), "is_creator": rights.get("is_creator")})
        else:
            abilities.update({"is_admin": False, "can_post": "member-level",
                              "can_delete_others": False})
        return ToolResult.success(abilities)

    async def request_admin_action(self, account_id: str, action: str = "") -> ToolResult:
        supported = "currently supported authorized admin action: delete messages (with your explicit confirmation)"
        return ToolResult(True, "NOT_SUPPORTED",
                          {"requested": action or "(unspecified)", "supported": supported,
                           "how": "say e.g. 'delete last 3 messages from this channel' - I will ask for confirmation first"},
                          None, ERR_NOT_SUPPORTED, False, None)

    async def execute_authorized_admin_action(self, account_id: str, ref: Any,
                                              action: str = "delete", count: int = 1) -> ToolResult:
        if action != "delete":
            return ToolResult.failure(f"admin action '{action}' is not registered",
                                      ERR_NOT_SUPPORTED, status="NOT_SUPPORTED")
        return await self.delete_message(account_id, ref, count=int(count))

    # ---------------- ANALYTICS ----------------
    async def channel_activity(self, account_id: str, ref: Any, limit: int = 50) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        dates, views = [], []
        async for m in client.iter_messages(ent.entity, limit=min(int(limit), 60)):
            if getattr(m, "id", None) is None:
                continue
            if m.date:
                dates.append(m.date.timestamp())
            v = getattr(m, "views", None)
            if v is not None:
                views.append(v)
        span_days = 0.0
        per_day = None
        if len(dates) >= 2:
            span_days = max((max(dates) - min(dates)) / 86400, 0.04)
            per_day = round(len(dates) / span_days, 2)
        return ToolResult.success({"entity": ent.brief(), "sampled": len(dates),
                                   "span_days": round(span_days, 2),
                                   "approx_posts_per_day": per_day,
                                   "avg_views": round(sum(views) / len(views)) if views else None,
                                   "max_views": max(views) if views else None,
                                   "latest_post_at": iso(max(dates)) if dates else None})

    async def accessible_activity_metrics(self, account_id: str, ref: Any,
                                          limit: int = 30) -> ToolResult:
        return await self.channel_activity(account_id, ref, limit)

    async def compare_measurable_activity(self, account_id: str, ref_a: Any, ref_b: Any) -> ToolResult:
        ra = await self.channel_activity(account_id, ref_a)
        rb = await self.channel_activity(account_id, ref_b)
        if not ra.ok or not rb.ok:
            bad = ra if not ra.ok else rb
            return ToolResult.failure(bad.error, bad.error_code)
        return ToolResult.success({"a": ra.data, "b": rb.data,
                                   "more_active": "a" if (ra.data.get("approx_posts_per_day") or 0)
                                                 >= (rb.data.get("approx_posts_per_day") or 0) else "b"})

    async def join_request_metrics(self, account_id: str, ref: Any) -> ToolResult:
        client = await self._client(account_id)
        ent = await self._ent(account_id, ref)
        try:
            res = await client(fn.messages.GetChatInviteImportersRequest(
                peer=ent.entity, requested=True, offset_date=0,
                offset_user=tl.InputUserEmpty(), limit=50, link=""))
            return ToolResult.success({"entity": ent.brief(),
                                       "pending_join_requests": len(res.importers)})
        except Exception as exc:
            return ToolResult(True, "NOT_SUPPORTED",
                              {"entity": ent.brief(),
                               "reason": "Telegram exposes join requests only to admins of the chat; "
                                         f"not available here ({type(exc).__name__})"},
                              None, ERR_NOT_SUPPORTED, False, None)

    # ---------------- DIAGNOSTICS ----------------
    async def system_status(self, account_id: str) -> ToolResult:
        diag = self.diag.snapshot()
        return ToolResult.success({
            "uptime_sec": diag["uptime_sec"],
            "accounts": len(self.accounts.all()),
            "tasks_active": len(self.tasks.active()),
            "tasks_controllable": len([t for t in self.tasks.list() if t.status in TS_CONTROLLABLE]),
            "monitors_active": len(self.monitors.active_all()),
            "schedules_pending": len(self.scheduler.pending()),
            "last_success": diag["last_success"], "last_failure": diag["last_failure"],
            "ktm_now": ktm_iso()})

    async def telegram_status(self, account_id: str) -> ToolResult:
        out = []
        for a in self.accounts.all():
            rt = self.accounts.runtime.get(a["account_id"]) or AccountRuntime(a["account_id"])
            out.append({"label": a["label"], "connected": rt.connected,
                        "authorized": rt.authorized, "self": rt.self_name or None,
                        "last_error": rt.last_error or None})
        return ToolResult.success({"accounts": out})

    async def tool_health(self, account_id: str) -> ToolResult:
        pub = (self.tool_registry.list_public() if getattr(self, "tool_registry", None) else [])
        bad = [t for t in pub if t["health"] != "ok" or not t["enabled"]]
        return ToolResult.success({"total_tools": len(pub), "degraded_or_disabled": bad})

    async def task_health(self, account_id: str) -> ToolResult:
        bad = [t.public() for t in self.tasks.list()
               if t.error_count > 0 or t.status in (TS_FAILED, TS_WAITING, TS_EXPIRED)]
        return ToolResult.success({"unhealthy": bad, "count": len(bad)})

    async def monitor_health(self, account_id: str) -> ToolResult:
        bad = [m for m in self.monitors.store.data["monitors"].values()
               if m.get("error_count", 0) > 0 or m.get("status") in ("EXPIRED", "STOPPED")]
        return ToolResult.success({"attention": bad[-20:], "count": len(bad)})

    async def error_report(self, account_id: str, limit: int = 20) -> ToolResult:
        evs = [e for e in self.diag.events if e["level"] in ("ERROR", "WARN")]
        return ToolResult.success({"recent_errors": evs[-int(limit):]})

    explain_capabilities_data: dict = {}

    # ---------------- HELP ----------------
    async def explain_capabilities(self, account_id: str, category: str = "") -> ToolResult:
        pub = self.tool_registry.list_public() if getattr(self, "tool_registry", None) else []
        cats: dict[str, list[str]] = {}
        for t in pub:
            if category and t["category"] != category:
                continue
            cats.setdefault(t["category"], []).append(t["name"])
        return ToolResult.success({"categories": cats, "total": len(pub)})

    async def explain_current_task(self, account_id: str) -> ToolResult:
        tctx = self.ctx.get(account_id, "task") or {}
        tid = tctx.get("task_id")
        if not tid:
            return ToolResult.failure("no current task in conversation context", ERR_TASK_NOT_FOUND)
        return await self.task_status(account_id, tid)

    async def explain_required_info(self, account_id: str, topic: str = "cross") -> ToolResult:
        reqs = {
            "cross": [
                "SOURCE: one reachable channel/chat - replied message, @username, numeric ID, alias or current context",
                "SOURCE MESSAGE (optional): the exact forwarded post in your reply carries the original message id",
                "TARGETS: configured Main Channels OR a folder name - resolved one by one",
                "targets equal to the source are skipped; if none remain, cross will NOT start",
                "PERMISSIONS: I must be able to read the source and post in every target",
                "FLOOD CONTROL: Telegram FloodWait is honored exactly; deliveries are verified by re-fetch",
                "PERSISTENCE: queue progress (completed/skipped/current target) is saved after every target",
            ],
            "monitor": [
                "CHANNEL: which channel/chat to watch (id/@username/reply/context/main channel)",
                "CONDITION: all new posts or unknown (non-admin) senders",
                "WINDOW: duration or end time (default 12h if unspecified)",
                "ACTION: alert_only to your Saved Messages - nothing destructive unless you ask",
            ],
            "delete": [
                "CHANNEL + COUNT (or exact message ids)",
                "my admin right 'delete messages' in that chat (else only my own messages)",
                "your one-time confirmation before I touch anything",
            ],
            "schedule": ["CONTENT: text to post (or a stored goal)",
                         "TARGET: main channels or a specific chat",
                         "TIME: 'in 2 hours', 'kal 9 baje', '4 pm' - Asia/Kathmandu"],
        }
        return ToolResult.success({"topic": topic, "required": reqs.get(topic, reqs["cross"])})

    # ---------------- main channel helpers / latest message / saved ----------------
    async def resolve_main_channel(self, account_id: str) -> ToolResult:
        mains = self.accounts.get_main_channels(account_id)
        if not mains:
            return ToolResult.failure("no Main Channel configured", ERR_ENTITY_NOT_FOUND)
        skipped = []
        for ch in mains:
            try:
                ent = await self.resolver.resolve(account_id, str(ch["id"]))
                return ToolResult.success(ent.brief_dict() | {"via": "configured main channel"})
            except EntityResolutionError as exc:
                skipped.append(f"{ch.get('title') or ch['id']}: {short(str(exc), 60)}")
        return ToolResult.failure("configured Main Channel(s) unreachable: " + "; ".join(skipped[:3]),
                                  ERR_ENTITY_NOT_FOUND)

    async def get_latest_message(self, account_id: str, ref: Any = None,
                                 use_main_channel: bool = False) -> ToolResult:
        client = await self._client(account_id)
        if use_main_channel or ref is None:
            mc = await self.resolve_main_channel(account_id)
            if not mc.ok:
                return mc
            ent = await self._ent(account_id, mc.data["id"])
        else:
            ent = await self._ent(account_id, ref)
        latest = None
        async for m in client.iter_messages(ent.entity, limit=1):
            latest = m
        if latest is None or getattr(latest, "id", None) is None:
            return ToolResult.failure(f"no messages in {ent.title}", ERR_MESSAGE_NOT_FOUND)
        media_type = getattr(getattr(latest, "media", None), "__class__", type(None)).__name__ \
            if getattr(latest, "media", None) else None
        return ToolResult.success({"entity": ent.brief(), "entity_id": ent.id,
                                   "message_id": latest.id,
                                   "date": iso(latest.date.timestamp()) if latest.date else None,
                                   "date_ktm": ktm_iso(latest.date.timestamp()) if latest.date else None,
                                   "text": short(getattr(latest, "raw_text", "") or "", 400),
                                   "has_media": bool(getattr(latest, "media", None)),
                                   "media_type": media_type,
                                   "views": getattr(latest, "views", None)},
                                  verification={"fetched": True, "read_only": True})

    async def forward_to_saved(self, account_id: str, ref: Any, message_id: int) -> ToolResult:
        client = await self._client(account_id)
        src = await self._ent(account_id, ref)
        m = await client.get_messages(src.entity, ids=int(message_id))
        if m is None:
            return ToolResult.failure(f"message #{message_id} not found in {src.title}",
                                      ERR_MESSAGE_NOT_FOUND)
        try:
            res = await client.forward_messages("me", m.id, from_peer=src.entity)
        except ChatForwardsRestrictedError:
            res = await client.send_message("me", m.message or "", file=m.media)
        if isinstance(res, list):
            res = res[0] if res else None
        if res is None:
            return ToolResult.failure("forward returned nothing", ERR_TOOL_UNAVAILABLE, retryable=True)
        got = await client.get_messages("me", ids=res.id)
        if got is None:
            return ToolResult.failure("destination verification failed in Saved Messages",
                                      ERR_VERIFICATION_FAILED)
        self.diag.ok("VERIFICATION", "forward_to_saved",
                     f"{src.title}#{m.id} -> saved #{res.id}", account_id=account_id)
        return ToolResult.success({"source": src.brief(), "source_message_id": m.id,
                                   "destination": "saved_messages",
                                   "saved_message_id": res.id},
                                  verification={"verified": True})

    async def heal_system(self, account_id: str) -> ToolResult:
        if getattr(self, "core", None) is None:
            return ToolResult.failure("healing backend not wired", ERR_TOOL_UNAVAILABLE)
        return await self.core.run_healing(account_id)


# ----------------------------------------------------------------------------
# 15. TOOL REGISTRATION TABLE - register once, discoverable forever
# ----------------------------------------------------------------------------

def S(name, category, desc, req=None, opt=None, perms=None, read_only=True, destructive=False,
      confirm=False, background=False, ents=None, intents=(), test=None):
    return ToolSpec(name=name, category=category, description=desc,
                    required_parameters=req or [], optional_parameters=opt or [],
                    permissions_required=perms or [], read_only=read_only,
                    destructive=destructive, confirmation_required=confirm,
                    supports_background_task=background, supported_entities=ents or ["channel", "group"],
                    result_schema={"ok": "bool", "status": "str", "data": "dict",
                                   "error": "str|null", "error_code": "str|null",
                                   "verification": "dict|null"},
                    intents=list(intents), test=test)


def register_all_tools(reg: ToolRegistry, impl: ToolImpl) -> None:
    R, H = reg, impl
    # ACCOUNT
    R.register(S("account_info", "account", "Safe profile/authorization report of the connected Telegram account.", intents=["ACCOUNT_INFO"], test={})); R.specs["account_info"].handler = H.account_info
    R.register(S("connection_status", "account", "Connection + authorization probe for the managed account.", intents=["ACCOUNT_INFO", "SYSTEM_STATUS"], test={})); R.specs["connection_status"].handler = H.connection_status
    R.register(S("account_permissions", "account", "Your admin rights across configured Main Channels.", intents=["ACCOUNT_INFO", "ADMIN_RIGHTS"])); R.specs["account_permissions"].handler = H.account_permissions
    R.register(S("account_sessions", "account", "Active Telegram sessions/devices of the account (safe summary).", intents=["ACCOUNT_INFO"])); R.specs["account_sessions"].handler = H.account_sessions
    # DIALOGS
    R.register(S("list_dialogs", "dialogs", "Recent dialogs/chats visible to the account.", opt=["limit"], intents=["LIST_DIALOGS"], read_only=True, test={})); R.specs["list_dialogs"].handler = H.list_dialogs
    R.register(S("list_channels", "dialogs", "Channels and groups of the account.", intents=["LIST_CHANNELS"], test={})); R.specs["list_channels"].handler = H.list_channels
    R.register(S("inspect_channel", "dialogs", "Deep read: meta, your rights, recent posts, named senders.", req=["ref"], intents=["INSPECT_CHANNEL"])); R.specs["inspect_channel"].handler = H.inspect_channel
    R.register(S("inspect_chat", "dialogs", "Inspect any chat (group/channel) by id/username/alias.", req=["ref"], intents=["INSPECT_CHANNEL"])); R.specs["inspect_chat"].handler = H.inspect_chat
    R.register(S("resolve_entity", "dialogs", "Resolve @username / numeric id / alias / title to an entity.", req=["ref"], intents=["RESOLVE"])); R.specs["resolve_entity"].handler = H.resolve_entity
    R.register(S("resolve_username", "dialogs", "Resolve an @username.", req=["username"], intents=["RESOLVE"])); R.specs["resolve_username"].handler = H.resolve_username
    R.register(S("resolve_numeric_id", "dialogs", "Resolve numeric/-100 ids to entities.", req=["ref"], intents=["RESOLVE"])); R.specs["resolve_numeric_id"].handler = H.resolve_numeric_id
    # FOLDERS
    R.register(S("list_folders", "folders", "Telegram dialog folders of the account.", intents=["LIST_FOLDERS"], test={})); R.specs["list_folders"].handler = H.list_folders
    R.register(S("inspect_folder", "folders", "Resolve a folder by title; enumerate its channels/groups/users.", req=["name"], intents=["INSPECT_FOLDER", "FOLDER_CHANNELS"])); R.specs["inspect_folder"].handler = H.inspect_folder
    R.register(S("list_folder_channels", "folders", "Only the channels inside a folder.", req=["name"], intents=["FOLDER_CHANNELS"])); R.specs["list_folder_channels"].handler = H.list_folder_channels
    R.register(S("resolve_folder_by_name", "folders", "Find a dialog folder by exact/normalized/fuzzy title.", req=["name"], intents=["RESOLVE", "INSPECT_FOLDER"])); R.specs["resolve_folder_by_name"].handler = H.resolve_folder_by_name
    R.register(S("resolve_main_channel", "dialogs", "Resolve the configured Main Channel to a real entity.", intents=["RESOLVE", "MAIN_CHANNEL_CONFIG", "LATEST_MESSAGE", "FORWARD_LATEST_SAVED"], test={})); R.specs["resolve_main_channel"].handler = H.resolve_main_channel
    R.register(S("get_latest_message", "messages", "Fetch the actual latest message of a chat (read-only).", opt=["ref", "use_main_channel"], intents=["LATEST_MESSAGE", "RECENT_MESSAGES", "FORWARD_LATEST_SAVED"])); R.specs["get_latest_message"].handler = H.get_latest_message
    R.register(S("forward_to_saved", "messages", "Forward an exact message into Saved Messages + verify destination.", req=["ref", "message_id"], read_only=False, intents=["FORWARD_LATEST_SAVED", "FORWARD"])); R.specs["forward_to_saved"].handler = H.forward_to_saved
    R.register(S("heal_system", "diagnostics", "Controlled self-repair: JSON salvage, cache refresh, orphan reconcile, reconnect.", read_only=False, confirm=True, intents=["HEAL_SYSTEM", "SYSTEM_STATUS", "HEAL"])); R.specs["heal_system"].handler = H.heal_system
    # MESSAGES
    R.register(S("get_message", "messages", "Fetch one message by id.", req=["ref", "message_id"], intents=["GET_MESSAGE"])); R.specs["get_message"].handler = H.get_message
    R.register(S("get_recent_messages", "messages", "Recent messages of a chat.", req=["ref"], opt=["limit"], intents=["RECENT_MESSAGES", "LIST"])); R.specs["get_recent_messages"].handler = H.get_recent_messages
    R.register(S("search_messages", "messages", "Search text inside a chat.", req=["ref", "query"], intents=["SEARCH_MESSAGES", "SEARCH"])); R.specs["search_messages"].handler = H.search_messages
    R.register(S("send_message", "messages", "Post a text message.", req=["ref", "text"], perms=["send rights"], read_only=False, intents=["SEND_MESSAGE", "POST"])); R.specs["send_message"].handler = H.send_message
    R.register(S("forward_message", "messages", "Forward/copy messages source -> target with verification.", req=["source", "target"], opt=["message_ids", "count"], read_only=False, intents=["FORWARD", "FORWARD_TO_MAIN"])); R.specs["forward_message"].handler = H.forward_message
    R.register(S("delete_message", "messages", "Delete messages (confirmation protected).", req=["ref"], opt=["message_ids", "count"], perms=["delete_messages admin right"], read_only=False, destructive=True, confirm=True, intents=["DELETE", "DELETE_MESSAGES"])); R.specs["delete_message"].handler = H.delete_message
    R.register(S("edit_message", "messages", "Edit an own message.", req=["ref", "message_id", "text"], read_only=False, intents=["EDIT_MESSAGE"])); R.specs["edit_message"].handler = H.edit_message
    # MEDIA
    R.register(S("inspect_media", "media", "Media type/size of a message.", req=["ref", "message_id"], intents=["INSPECT_MEDIA"])); R.specs["inspect_media"].handler = H.inspect_media
    R.register(S("send_media", "media", "Copy media of a source message to a target.", req=["target", "source", "source_message_id"], read_only=False, intents=["SEND_MEDIA", "FORWARD"])); R.specs["send_media"].handler = H.send_media
    # MONITORING
    R.register(S("create_monitor", "monitoring", "Event-driven watch with Saved Messages alerts (alert_only by design).", req=["channel"], opt=["condition", "action", "end_ts", "duration_sec", "goal"], read_only=False, background=True, intents=["MONITOR_START", "WATCH", "UNKNOWN_SENDER_WATCH"])); R.specs["create_monitor"].handler = H.create_monitor
    R.register(S("list_monitors", "monitoring", "Active monitors with cursors and hits.", intents=["MONITOR_LIST", "LIST", "TASK_LIST"], test={})); R.specs["list_monitors"].handler = H.list_monitors
    R.register(S("stop_monitor", "monitoring", "Stop one monitor (or all when no id given).", opt=["monitor_id", "channel"], read_only=False, intents=["MONITOR_STOP", "STOP"])); R.specs["stop_monitor"].handler = H.stop_monitor
    R.register(S("update_monitor", "monitoring", "Change condition/action/end time of a monitor.", req=["monitor_id"], opt=["condition", "action", "end_ts"], read_only=False, intents=["MONITOR_UPDATE"])); R.specs["update_monitor"].handler = H.update_monitor
    R.register(S("monitor_new_posts", "monitoring", "Watch: all new posts -> alert.", req=["channel"], read_only=False, background=True, intents=["MONITOR_START"])); R.specs["monitor_new_posts"].handler = H.monitor_new_posts
    R.register(S("monitor_unknown_sender", "monitoring", "Watch: unknown (non-admin) senders -> alert.", req=["channel"], read_only=False, background=True, intents=["MONITOR_START", "UNKNOWN_SENDER_WATCH"])); R.specs["monitor_unknown_sender"].handler = H.monitor_unknown_sender
    R.register(S("alert_saved_messages", "monitoring", "Push an alert note into your Saved Messages.", req=["text"], read_only=False, intents=["ALERT"])); R.specs["alert_saved_messages"].handler = H.alert_saved_messages
    # TASKS
    R.register(S("list_tasks", "tasks", "Task registry listing with real states.", opt=["include_done"], intents=["TASK_LIST", "LIST"], test={})); R.specs["list_tasks"].handler = H.list_tasks
    R.register(S("pause_task", "tasks", "Pause a running task.", req=["task_id"], read_only=False, intents=["TASK_CONTROL", "PAUSE"])); R.specs["pause_task"].handler = H.pause_task
    R.register(S("resume_task", "tasks", "Resume a paused task.", req=["task_id"], read_only=False, intents=["TASK_CONTROL", "RESUME"])); R.specs["resume_task"].handler = H.resume_task
    R.register(S("stop_task", "tasks", "Stop a task.", req=["task_id"], read_only=False, intents=["TASK_CONTROL", "STOP"])); R.specs["stop_task"].handler = H.stop_task
    R.register(S("cancel_task", "tasks", "Cancel a task (alias of stop).", req=["task_id"], read_only=False, intents=["TASK_CONTROL", "CANCEL"])); R.specs["cancel_task"].handler = H.cancel_task
    R.register(S("retry_task", "tasks", "Retry a failed/expired/waiting task.", req=["task_id"], read_only=False, intents=["TASK_CONTROL", "RETRY"])); R.specs["retry_task"].handler = H.retry_task
    R.register(S("task_status", "tasks", "Status of one task or all active tasks.", opt=["task_id"], intents=["TASK_STATUS", "TASK_LIST"])); R.specs["task_status"].handler = H.task_status
    # SCHEDULING
    R.register(S("schedule_action", "scheduling", "Persisted action at an absolute time (Asia/Kathmandu).", req=["text"], opt=["kind", "run_at", "in_sec"], read_only=False, background=True, intents=["SCHEDULE", "SCHEDULE_POST"])); R.specs["schedule_action"].handler = H.schedule_action
    R.register(S("list_schedules", "scheduling", "Pending scheduled jobs.", intents=["SCHEDULE_LIST", "LIST"], test={})); R.specs["list_schedules"].handler = H.list_schedules
    R.register(S("cancel_schedule", "scheduling", "Cancel a scheduled job.", opt=["schedule_id", "all_"], read_only=False, intents=["SCHEDULE_CANCEL", "CANCEL"])); R.specs["cancel_schedule"].handler = H.cancel_schedule
    # CROSS
    R.register(S("resolve_cross_source", "cross", "Resolve the cross source from reply/explicit ref.", opt=["ref", "reply_hint"], intents=["CROSS_PLAN", "RESOLVE"])); R.specs["resolve_cross_source"].handler = H.resolve_cross_source
    R.register(S("resolve_cross_targets", "cross", "Targets from configured Main Channels or a folder.", opt=["mode", "folder_name"], intents=["CROSS_PLAN", "FOLDER_TO_MAIN", "MAIN_CHANNEL_CONFIG"])); R.specs["resolve_cross_targets"].handler = H.resolve_cross_targets
    R.register(S("validate_cross", "cross", "Validate targets: exclude source==target, check reachability + permissions.", req=["source_id", "targets"], intents=["CROSS_PLAN"])); R.specs["validate_cross"].handler = H.validate_cross
    R.register(S("create_cross_plan", "cross", "Persist a cross execution plan (no execution).", req=["source", "targets"], opt=["source_msg_id"], intents=["CROSS_PLAN"])); R.specs["create_cross_plan"].handler = H.create_cross_plan
    R.register(S("start_cross", "cross", "Start the cross workflow task (queue + live delivery, verified).", req=["source", "targets"], opt=["source_msg_id", "duration_sec", "end_ts"], read_only=False, background=True, confirm=True, intents=["CROSS_START"])); R.specs["start_cross"].handler = H.start_cross
    R.register(S("stop_cross", "cross", "Stop cross task(s).", opt=["task_id"], read_only=False, intents=["CROSS_STOP", "STOP", "TASK_CONTROL"])); R.specs["stop_cross"].handler = H.stop_cross
    R.register(S("reset_cross", "cross", "Clear cursor + queues and restart the cross workflow.", opt=["task_id"], read_only=False, intents=["CROSS_RESET"])); R.specs["reset_cross"].handler = H.reset_cross
    R.register(S("cross_status", "cross", "Workflow state: completed/skipped/current target, cursor, counters.", intents=["CROSS_STATUS", "TASK_LIST"], test={})); R.specs["cross_status"].handler = H.cross_status
    # ADMIN / PERMISSIONS
    R.register(S("inspect_admin_rights", "admin", "List admins of a chat.", req=["ref"], perms=["admin visibility"], intents=["ADMIN_RIGHTS", "INSPECT_CHANNEL"])); R.specs["inspect_admin_rights"].handler = H.inspect_admin_rights
    R.register(S("inspect_permissions", "admin", "What I am allowed to do in a chat.", req=["ref"], intents=["ADMIN_RIGHTS", "PERMISSIONS"])); R.specs["inspect_permissions"].handler = H.inspect_permissions
    R.register(S("request_admin_action", "admin", "Explain/request an admin-capable action.", opt=["action"], destructive=False, confirm=True, intents=["ADMIN_ACTION"])); R.specs["request_admin_action"].handler = H.request_admin_action
    R.register(S("execute_authorized_admin_action", "admin", "Execute an allowlisted admin action (delete) with confirmation.", req=["ref"], opt=["action", "count"], read_only=False, destructive=True, confirm=True, perms=["delete_messages"], intents=["ADMIN_ACTION", "DELETE"])); R.specs["execute_authorized_admin_action"].handler = H.execute_authorized_admin_action
    # ANALYTICS
    R.register(S("channel_activity", "analytics", "Activity metrics: posts/day, views, latest post.", req=["ref"], opt=["limit"], intents=["CHANNEL_ACTIVITY", "ANALYTICS"])); R.specs["channel_activity"].handler = H.channel_activity
    R.register(S("accessible_activity_metrics", "analytics", "Accessible activity metrics for a chat.", req=["ref"], opt=["limit"], intents=["CHANNEL_ACTIVITY"])); R.specs["accessible_activity_metrics"].handler = H.accessible_activity_metrics
    R.register(S("compare_measurable_activity", "analytics", "Compare two chats on measurable activity.", req=["ref_a", "ref_b"], intents=["COMPARE_ACTIVITY", "ANALYTICS"])); R.specs["compare_measurable_activity"].handler = H.compare_measurable_activity
    R.register(S("join_request_metrics", "analytics", "Pending join requests where Telegram exposes them (admins only).", req=["ref"], perms=["admin"], intents=["JOIN_METRICS", "ANALYTICS"])); R.specs["join_request_metrics"].handler = H.join_request_metrics
    # DIAGNOSTICS
    R.register(S("system_status", "diagnostics", "Whole-system status snapshot.", intents=["SYSTEM_STATUS", "STATUS"], test={})); R.specs["system_status"].handler = H.system_status
    R.register(S("telegram_status", "diagnostics", "Per-account telegram connection state.", intents=["SYSTEM_STATUS", "ACCOUNT_INFO"])); R.specs["telegram_status"].handler = H.telegram_status
    R.register(S("tool_health", "diagnostics", "Tool registry health/degraded list.", intents=["TOOL_HEALTH", "SYSTEM_STATUS"], test={})); R.specs["tool_health"].handler = H.tool_health
    R.register(S("task_health", "diagnostics", "Unhealthy/failed/waiting tasks.", intents=["TASK_HEALTH", "SYSTEM_STATUS"])); R.specs["task_health"].handler = H.task_health
    R.register(S("monitor_health", "diagnostics", "Monitors needing attention.", intents=["MONITOR_HEALTH", "SYSTEM_STATUS"])); R.specs["monitor_health"].handler = H.monitor_health
    R.register(S("error_report", "diagnostics", "Recent classified errors.", opt=["limit"], intents=["ERROR_REPORT", "SYSTEM_STATUS"], test={})); R.specs["error_report"].handler = H.error_report
    # HELP
    R.register(S("explain_capabilities", "help", "What I can do, grouped by category.", opt=["category"], intents=["HELP", "CAPABILITIES"], test={})); R.specs["explain_capabilities"].handler = H.explain_capabilities
    R.register(S("explain_current_task", "help", "Explain the task in current conversation context.", intents=["EXPLAIN_TASK", "HELP"])); R.specs["explain_current_task"].handler = H.explain_current_task
    R.register(S("explain_required_info", "help", "Information I must verify before an operation (cross/monitor/delete/schedule).", opt=["topic"], intents=["EXPLAIN_REQUIREMENTS", "CROSS_REQUIREMENTS_EXPLAIN", "HELP"], test={})); R.specs["explain_required_info"].handler = H.explain_required_info


# ----------------------------------------------------------------------------
# 16. NLU - feature extraction + declarative intent scoring (no fixed commands)
# ----------------------------------------------------------------------------

KW = {
    "info": ["batao", "btaiye", "info", "information", "detail", "details", "tell me", "show me",
             "ke baare me", "ke bare me", "jankari", "jaankari", "show", "diktavo"],
    "list": ["list", "dikhao", "dikha", "de dikhao", "sabhi", "saare", "saari", "all",
             "enumer", "batao kon kon"],
    "watch": ["dhyan rakh", "dhyan", "nazar", "nigrani", "watch", "monitor", "sambhal",
              "sambhalna", "observe", "keep an eye", "dekh te reh", "dekhte raho", "dekhna",
              "dekho", "track", "dhyan dena"],
    "sleep_away": ["sona", "so raha", "so rha", "so rahi", "sone ja", "sone ja rha", "sleeping",
                   "sleep", "busy", "vyast", "wapas", "office", "bahar ja", "meeting", "thak gaya",
                   "thk", "aaram"],
    "inspect": ["inspect", "jaanch", "check", "analyse", "analyze", "scan", "report banao"],
    "stop": ["stop", "band", "bnd", "ruk", "ruko", "khatam", "basa"],
    "pause": ["pause", "hold", "rok do", "thambe"],
    "resume": ["resume", "continue", "waps chalu", "fir se chalu", "phir se chalu"],
    "retry": ["retry", "dobara try", "phir se try", "dobara"],
    "delete": ["delete", "hata do", "saaf karo", "saaf", "mita", "remove message", "delete kar"],
    "folder": ["folder", "fldr"],
    "main_channel": ["main channel", "main chanel", "mainchannel", "main chennal",
                     "main channels", "cross target"],
    "task": ["task", "kaam", "kam", "work", "job"],
    "monitor_word": ["monitor", "monitoring", "watch", "nigrani", "wardega"],
    "schedule": ["schedule", "baad me bhej", "remind", "later"],
    "forward": ["forward", "bhej", "send", "fwd"],
    "post": ["post kar", "daal do", "post"],
    "alert": ["alert", "inform", "notify", "bata dena", "bata denge", "pata chale", "khabar"],
    "question": ["kya ", "kaise", "kyun", "kyu", "why", "how", "explain", "samjhao", "kya verify",
                 "requirement", "requirements", "kya verify karna", "zaroori", "matlab", "konsa",
                 "kaun si", "kya karna", "kya chahiye", "batyo ke"],
    "unknown_sender": ["unknown", "anjaan", "anjan", "naya sender", "new sender", "astrange"],
    "negation": ["mat karna", "mat karo", "don't", "do not", "nahi karna", "bina delete",
                 "change mat", "kuch mat", "kuch change mat", "kuch bhi mat", "mat"],
    "latest": ["latest", "naya post", "recent", "aakhri", "last", "sabse naya"],
    "config_verb": ["set kar", "bana do", "configure", "set karo", "update kar", "hain", " hai",
                    "banao", "rakh do", "jod do", "add kar", "daal do", "target banao"],
    "help": ["help", "madad", "kya kar sakte", "capabilities", "kya kya kar"],
    "status_word": ["status", "health", "haalat", "chaltu hai"],
    "search": ["search", "dhundo", "dhundho", "find", "khojo", "khoj"],
    "activity": ["activity", "stats", "statistics", "metrics", "analytics", "views", "growth"],
    "admin": ["admin", "permission", "permissions", "rights", "adhikar", "sessions", "devices"],
    "search_recent": ["recent", "latest messages", "aakhri message", "last messages", "naya"],
    "account_word": ["account", "telegram account", "profile", "mera telegram"],
    "imperative": ["karo", "kar do", "chalu", "start", "shuru", "lagao", "laga do", "banao",
                   "do it", "chala do", "suru", "chalau"],
    "verify_words": ["verify", "check karna hoga", "pehle kya", "pahle kya", "before",
                     "requirements", "kya chahiye", "kya verify karna"],
    "plan_words": ["plan", "resolve karo", "targets resolve", "steps", "tyari", "tayari"],
    "reset_words": ["reset", "fresh start", "dobara shuru"],
    "alias_words": ["yaad rakh", "remember", "alias"],
    "messages_word": ["message", "messages", "post", "posts", "msg", "sms"],
    "target_words": ["target", "targets", "destination"],
}

FOLDER_FILLERS = {"me", "mere", "mujhe", "ko", "ke", "ki", "ka", "in", "the", "a", "an",
                  "please", "plz", "inspect", "check", "karo", "karna", "list", "dikhao",
                  "dikha", "batao", "sabhi", "saare", "saari", "all", "of", "show", "de",
                  "do", "hai", "hain", "channels", "channel", "se", "me", "and", "aur",
                  "available", "jo", "hai", "unga", "main", "mera", "hum"}


@dataclass
class NLUResult:
    intent: Optional[str]
    score: int
    features: dict
    debug: dict


def extract_folder_name(text: str) -> Optional[str]:
    t = norm_text(text)
    cand = ""
    m = re.search(r"(.+?)\s+(?:folder|fldr)\b", t)
    if m:
        cand = m.group(1)
    else:
        m2 = re.search(r"\b(?:folder|fldr)\s+(.+)$", t)
        if m2:
            cand = m2.group(1)
    if not cand:
        return None
    toks = [w for w in cand.split() if w not in FOLDER_FILLERS]
    cand = " ".join(toks).strip()
    if len(cand) < 2:
        return None
    # keep at most the trailing 6 tokens (folder names are short)
    return " ".join(cand.split()[-6:]) or None


class NLU:
    """Goal understanding: normalize -> features -> score intents declaratively."""

    def features(self, account_id: str, text: str, has_reply: bool,
                 main_count: int) -> dict:
        raw = strip_command(text)
        n, sk = norm_text(raw), skeleton(raw)
        low = raw.lower()
        ids = extract_ids(raw)
        usernames = extract_usernames(raw)
        quoted = None
        mq = re.search(r"[\"'](.{3,280}?)[\"']", raw)
        if mq:
            quoted = mq.group(1)
        f = {
            "raw": raw, "norm": n, "skel": sk,
            "ids": ids, "usernames": usernames, "quoted": quoted,
            "folder_name": extract_folder_name(raw),
            "has_reply": has_reply,
            "main_count": main_count,
            "time": parse_time_spec(raw),
            "cross_word": bool(re.search(r"\bcross\b", low)),
            "has_channel_word": bool(re.search(r"\b(channel|chanel|chennal|group|chat)\b", low)),
        }
        f["is_question"] = raw.strip().endswith("?") or has_kw(n, sk, KW["question"])
        f["imperative"] = has_kw(n, sk, KW["imperative"])
        f["read_only"] = has_kw(n, sk, KW["negation"])
        f["ctx_ref"] = bool(re.search(
            r"\b(is|isse|isko|isme|ye|yeh|us|usi|usko|usme|wo|woh|it|this|that)\b", low))
        for key in KW:
            f[f"kw_{key}"] = has_kw(n, sk, KW[key])
        return f

    def classify(self, f: dict) -> NLUResult:
        sc: dict[str, int] = {}

        def bump(intent: str, pts: int) -> None:
            sc[intent] = sc.get(intent, 0) + pts

        n, sk, q = f["norm"], f["skel"], f["is_question"]
        has_ref = bool(f["ids"] or f["usernames"])
        imp = f["imperative"]

        # ---- account ----
        if f["kw_account_word"] and (f["kw_info"] or q or f["kw_list"]):
            bump("ACCOUNT_INFO", 6 + (1 if f["kw_admin"] and "session" in n else 0))
        if f["kw_config_verb"] and f["kw_target_words"] and "channel" in n:
            bump("FOLDER_TO_MAIN", 4)
        if "session" in n or "devices" in n:
            if f["kw_account_word"] or f["kw_admin"]:
                bump("ACCOUNT_SESSIONS", 5)
        # ---- folders ----
        if f["folder_name"]:
            if f["kw_config_verb"] and (f["kw_target_words"] or f["kw_main_channel"]):
                bump("FOLDER_TO_MAIN", 8)
            elif f["kw_list"] and "channel" in n:
                bump("FOLDER_CHANNELS", 7)
            elif f["kw_inspect"] or f["kw_list"] or f["kw_info"] or True:
                bump("INSPECT_FOLDER", 5)
        elif f["kw_folder"] and f["kw_list"]:
            bump("LIST_FOLDERS", 6)
        # ---- main channel configuration ----
        if f["kw_main_channel"]:
            if f["kw_config_verb"] and has_ref:
                bump("MAIN_CHANNEL_CONFIG", 8)
            elif f["kw_info"] or f["kw_list"] or q:
                bump("MAIN_CHANNEL_LIST", 6)
            if f["kw_watch"] or (f["kw_sleep_away"] and f["has_channel_word"]):
                bump("MONITOR_START", 7)
        # ---- reply identification / healing ----
        if f["has_reply"] and ("identify" in n or "pehchano" in n or "kis channel" in n
                               or "kaunsa channel" in n or "kaun si channel" in n or "replied" in n) \
                and not ("source" in n or f["kw_target_words"] or f["cross_word"]):
            bump("IDENTIFY_REPLY", 8)
        if "heal" in n or ("repair" in n and "system" in n):
            bump("HEAL_SYSTEM", 8)
        if "diagnostic" in n:
            bump("SYSTEM_DIAGNOSTICS", 6)

        # ---- monitoring ----
        if (f["kw_watch"] or (f["kw_sleep_away"] and (f["has_channel_word"] or f["kw_main_channel"]))) \
                and not f["kw_stop"]:
            bump("MONITOR_START", 6 + (2 if f["kw_unknown_sender"] else 0) + (1 if f["time"] else 0))
        if (f["kw_monitor_word"] and f["kw_stop"]) or (f["kw_stop"] and f["kw_monitor_word"]):
            bump("MONITOR_STOP", 7)
        if f["kw_monitor_word"] and f["kw_list"] and not f["kw_watch"]:
            bump("TASK_LIST", 4)
        # ---- source/target chaining without the literal word 'cross' ----
        if "source" in n and f["kw_target_words"] and (f["has_reply"] or f["folder_name"]
                                                       or f["kw_main_channel"]):
            bump("CROSS_PLAN", 6)

        # ---- cross ----
        if f["cross_word"]:
            if f["kw_stop"]:
                bump("CROSS_STOP", 7)
            elif f["kw_reset_words"]:
                bump("CROSS_RESET", 6)
            elif f["kw_status_word"] and not imp:
                bump("CROSS_STATUS", 5)
            if (q or f["kw_verify_words"]) and not (re.search(r"\b(start|chalu|shuru)\b", n) and not q):
                bump("CROSS_REQUIREMENTS_EXPLAIN", 9)
            elif f["kw_plan_words"] or (f["kw_target_words"] and not imp) or \
                    (f["kw_config_verb"] and "source" in n) or ("source banao" in n):
                bump("CROSS_PLAN", 7)
            elif re.search(r"\b(start|chalu|shuru|chalao|suru)\b", n):
                bump("CROSS_START", 6)
        # ---- inspect / discover ----
        if f["kw_inspect"] and not f["folder_name"]:
            bump("INSPECT_CHANNEL", 6)
        # ---- messages ----
        if f["kw_delete"] and not f["read_only"]:
            bump("DELETE_MESSAGES", 6 + (1 if f["kw_latest"] else 0))
        if f["kw_search"] and (f["kw_messages_word"] or has_ref or f["ctx_ref"]):
            bump("SEARCH_MESSAGES", 6)
        if (f["kw_forward"] or ("saved" in n and has_kw(n, sk, ["bhej", "bhejo", "send karo"]))) \
                and "saved" in n and not f["kw_delete"] and not f["kw_watch"]:
            if f["kw_latest"] or f["kw_messages_word"] or f["has_reply"]:
                bump("FORWARD_LATEST_SAVED", 9)
        if f["kw_latest"] and (f["kw_messages_word"] or "post" in n) and not f["kw_delete"] \
                and not f["kw_forward"]:
            bump("LATEST_MESSAGE", 8)
        elif f["kw_latest"] and f["kw_messages_word"] and not f["kw_delete"]:
            bump("RECENT_MESSAGES", 5)
        if (f["kw_forward"] or (f["kw_post"] and f["kw_main_channel"])) and f["kw_main_channel"]:
            bump("FORWARD_TO_MAIN", 6)
        if f["quoted"] and f["kw_post"]:
            bump("SCHEDULE_POST" if f["time"] else "POST_MAIN_NOW", 7)
        # ---- tasks ----
        if f["kw_list"] and (f["kw_task"] or f["kw_monitor_word"] or "running" in n or "chal raha" in n
                             or "currently" in n):
            bump("TASK_LIST", 7)
        if "running" in n and ("kaam" in n or "work" in n or "task" in n or "kya" in n):
            bump("TASK_LIST", 6)
        for verb, act in (("kw_stop", "stop"), ("kw_pause", "pause"),
                          ("kw_resume", "resume"), ("kw_retry", "retry")):
            if f[verb]:
                bump("TASK_CONTROL", 4)
                f["task_action"] = act
                break
        # ---- schedules ----
        if f["kw_schedule"] and f["kw_list"]:
            bump("SCHEDULE_LIST", 6)
        # ---- admin / activity / status / help ----
        if f["kw_admin"] and f["has_channel_word"] and (f["kw_info"] or f["kw_inspect"] or q):
            bump("ADMIN_RIGHTS", 6)
        if f["kw_activity"] and (f["has_channel_word"] or has_ref or f["ctx_ref"]):
            ids_n = len(f["ids"] + f["usernames"])
            bump("COMPARE_ACTIVITY" if ids_n >= 2 else "CHANNEL_ACTIVITY", 6)
        if f["kw_status_word"] and not f["cross_word"]:
            bump("SYSTEM_STATUS", 5)
        if f["kw_help"]:
            bump("HELP", 6)
        if f["kw_alias_words"] and "=" in f["raw"]:
            bump("SET_ALIAS", 8)
        if f["kw_list"] and "dialog" in n:
            bump("LIST_DIALOGS", 6)
        if f["kw_list"] and "channel" in n and not (f["kw_main_channel"] or f["folder_name"]):
            bump("LIST_CHANNELS", 5)

        best_intent, best_score = (None, 0)
        if sc:
            best_intent, best_score = max(sc.items(), key=lambda kv: kv[1])
        return NLUResult(best_intent, best_score, f, sc)


# ----------------------------------------------------------------------------
# 17. PLANNER - builds validated, inspectable plans over registered tools
# ----------------------------------------------------------------------------

def new_plan(account_id: str, intent: str) -> dict:
    return {"plan_id": new_id("plan"), "account_id": account_id, "intent": intent,
            "summary": "", "entities": [], "steps": [], "risk": "low",
            "confirmation_required": False, "report_only": False,
            "missing": [], "notes": [], "created_ts": utc_now()}


def plan_step(tool: str, note: str, **params) -> dict:
    return {"tool": tool, "note": note, "params": params}


class Planner:
    """Intent + features + context -> concrete plan using the registry (discovery)."""

    def __init__(self, core: "JarvisCore"):
        self.core = core

    async def _resolve_channel(self, account_id: str, f: dict,
                               reply_ctx: Optional[ReplyContext],
                               allow_ctx: bool = True,
                               allow_main: bool = True) -> tuple[Optional[ResolvedEntity], str]:
        """priority: explicit -> reply -> memory/title -> context -> main channel."""
        refs = f.get("ids") or [] + f.get("usernames") or []
        if refs:
            try:
                return await self.core.resolver.resolve(account_id, refs[0]), "explicit"
            except EntityResolutionError:
                raise
        if reply_ctx is not None:
            return reply_ctx.entity, "reply"
        if f.get("folder_name"):
            return None, "folder"   # caller handles folders explicitly
        if f.get("raw"):
            ent = await self.core.try_resolve_title(account_id, f["raw"])
            if ent is not None:
                return ent, "name"
        ch_ctx = self.core.ctx.get(account_id, "channel") if allow_ctx else {}
        if ch_ctx and ch_ctx.get("id"):
            try:
                return await self.core.resolver.resolve(account_id, str(ch_ctx["id"])), "context"
            except Exception:
                pass
        if allow_main and (f.get("kw_main_channel") or f.get("kw_sleep_away")):
            mains = self.core.accounts.get_main_channels(account_id)
            if mains:
                try:
                    return await self.core.resolver.resolve(account_id, str(mains[0]["id"])), "main channel"
                except EntityResolutionError:
                    return None, "main-unreachable"
        return None, ""

    async def _folder_from_text(self, account_id: str, f: dict) -> Optional[str]:
        """discover a folder title mentioned in free text even without the word 'folder'."""
        try:
            folders = await self.core.resolver.get_folders(account_id)
        except Exception:
            return None
        if not folders:
            return None
        n_, sk_ = f.get("norm", ""), f.get("skel", "")
        for fo in folders:
            fn_ = norm_text(fo["title"])
            fsk = skeleton(fo["title"])
            if (fn_ and fn_ in n_) or (len(fsk) >= 4 and fsk in sk_):
                return fo["title"]
        return None

    async def build(self, account_id: str, result: NLUResult,
                    reply_ctx: Optional[ReplyContext]) -> dict:
        f = result.features
        intent = result.intent or ""
        core = self.core
        plan = new_plan(account_id, intent)

        # ---------- identify replied message (READ, zero mutation) ----------
        if intent == "IDENTIFY_REPLY":
            plan["report_only"] = True
            if reply_ctx is None:
                plan["missing"].append("a replied message - reply to a message and ask again")
                return plan
            plan["summary"] = "Identify replied message origin (read-only)"
            plan["entities"] = [
                f"channel: {reply_ctx.entity.brief()}",
                f"channel id: {reply_ctx.entity.id}",
                "message id: " + (str(reply_ctx.message_id) if reply_ctx.message_id is not None
                                  else "not exposed (replied item was not a channel forward)"),
                f'text: "{reply_ctx.text or "[no text]"}"'
                + (" | media: yes" if reply_ctx.has_media else " | media: no"),
            ]
            return plan

        # ---------- healing / diagnostics ----------
        if intent == "HEAL_SYSTEM":
            plan["steps"].append(plan_step("heal_system", "diagnostics + safe repairs"))
            plan["summary"] = "Run system diagnostics and apply safe healing"
            plan["risk"] = "low"
            return plan
        if intent == "SYSTEM_DIAGNOSTICS":
            for probe in ("system_status", "telegram_status", "task_health",
                          "monitor_health", "tool_health"):
                plan["steps"].append(plan_step(probe, "probe"))
            plan["summary"] = "Full system diagnostics (read-only)"
            return plan

        # ---------- informational: cross requirements (NO EXECUTION) ----------
        if intent == "CROSS_REQUIREMENTS_EXPLAIN":
            plan["report_only"] = True
            plan["summary"] = "Explain what must be verified before Cross starts"
            r = await core.impl.explain_required_info(account_id, "cross")
            plan["notes"] = r.data["required"]
            src_txt = "not resolved yet (no reply/ID in this message)"
            tgt_txt = ""
            try:
                if reply_ctx is not None:
                    src_txt = (f"your replied post -> {reply_ctx.entity.brief()}"
                               + (f" (message #{reply_ctx.message_id})" if reply_ctx.message_id else ""))
                elif (f.get("ids") or f.get("usernames")):
                    ent = await core.resolver.resolve(account_id, (f["ids"] + f["usernames"])[0])
                    src_txt = f"explicit source -> {ent.brief()}"
                mains = core.accounts.get_main_channels(account_id)
                tgt_txt = (f"targets -> {len(mains)} configured Main Channel(s) "
                           + (", ".join(c.get("title", str(c['id'])) for c in mains[:4]) or "none"))
                if not mains:
                    tgt_txt = "targets -> NONE configured yet (required before starting)"
            except Exception:
                pass
            plan["entities"] = [src_txt, tgt_txt]
            return plan

        # ---------- folder family ----------
        if intent in ("LIST_FOLDERS", "INSPECT_FOLDER", "FOLDER_CHANNELS", "FOLDER_TO_MAIN"):
            if intent == "LIST_FOLDERS":
                plan["steps"].append(plan_step("list_folders", "read Telegram dialog folders"))
                plan["summary"] = "List all Telegram folders"
                return plan
            name = f.get("folder_name") or await self._folder_from_text(account_id, f) or ""
            if not name:
                plan["missing"].append("folder name")
                return plan
            plan["entities"].append(f"folder '{name}'")
            if intent == "INSPECT_FOLDER":
                plan["steps"].append(plan_step("inspect_folder", "resolve folder + enumerate peers",
                                               name=name))
                plan["summary"] = f"Inspect folder '{name}'"
                return plan
            if intent == "FOLDER_CHANNELS":
                plan["steps"].append(plan_step("list_folder_channels", "channels inside the folder",
                                               name=name))
                plan["summary"] = f"List channels of folder '{name}'"
                return plan
            # FOLDER_TO_MAIN
            plan["steps"].append(plan_step("list_folder_channels", "resolve folder channels",
                                           name=name))
            plan["steps"].append(plan_step("validate_cross", "validate as targets",
                                           source_id=-1, targets=[]) )  # filled at execute-time
            plan["summary"] = f"Make folder '{name}' channels the configured targets"
            plan["risk"] = "medium"
            return plan

        # ---------- account ----------
        if intent in ("ACCOUNT_INFO", "ACCOUNT_SESSIONS", "SYSTEM_STATUS"):
            tool = {"ACCOUNT_INFO": "account_info", "ACCOUNT_SESSIONS": "account_sessions"}.get(intent)
            if tool:
                plan["steps"].append(plan_step(tool, "safe account report"))
                plan["summary"] = "Report safe account information"
                return plan
            plan["steps"].append(plan_step("system_status", "system snapshot"))
            plan["steps"].append(plan_step("telegram_status", "per-account connection state"))
            plan["summary"] = "System + telegram status"
            return plan

        if intent in ("LIST_DIALOGS", "LIST_CHANNELS", "HELP"):
            if intent == "LIST_CHANNELS":
                fname = await self._folder_from_text(account_id, f)
                if fname:
                    plan["intent"] = "FOLDER_CHANNELS"
                    plan["entities"].append(f"folder '{fname}' (matched in text)")
                    plan["steps"].append(plan_step("list_folder_channels",
                                                   "real Telegram folder channels", name=fname))
                    plan["summary"] = f"List channels of folder '{fname}'"
                    return plan
            tool = {"LIST_DIALOGS": "list_dialogs", "LIST_CHANNELS": "list_channels",
                    "HELP": "explain_capabilities"}[intent]
            plan["steps"].append(plan_step(tool, "read-only listing"))
            plan["summary"] = tool.replace("_", " ")
            return plan

        if intent in ("TASK_LIST",):
            plan["steps"].extend([plan_step("list_tasks", "task registry snapshot"),
                                  plan_step("list_monitors", "monitor registry snapshot"),
                                  plan_step("list_schedules", "scheduler queue"),
                                  plan_step("cross_status", "cross workflow state")])
            plan["summary"] = "Full registry: tasks + monitors + schedules + cross"
            return plan

        if intent == "SCHEDULE_LIST":
            plan["steps"].append(plan_step("list_schedules", "scheduler queue"))
            plan["summary"] = "List scheduled jobs"
            return plan

        if intent == "MONITOR_LIST":
            plan["steps"].append(plan_step("list_monitors", "monitor registry"))
            return plan

        # ---------- inspection / messages ----------
        if intent in ("INSPECT_CHANNEL", "RECENT_MESSAGES", "SEARCH_MESSAGES", "LATEST_MESSAGE",
                      "CHANNEL_ACTIVITY", "COMPARE_ACTIVITY", "ADMIN_RIGHTS"):
            refs = (f.get("ids") or []) + (f.get("usernames") or [])
            plan["_refs"] = refs
            tool = {"INSPECT_CHANNEL": "inspect_channel", "RECENT_MESSAGES": "get_recent_messages",
                    "SEARCH_MESSAGES": "search_messages", "CHANNEL_ACTIVITY": "channel_activity",
                    "COMPARE_ACTIVITY": "compare_measurable_activity",
                    "LATEST_MESSAGE": "get_latest_message",
                    "ADMIN_RIGHTS": "inspect_admin_rights"}[intent]
            if intent == "COMPARE_ACTIVITY" and len(refs) >= 2:
                plan["steps"].append(plan_step(tool, "compare two channels",
                                               ref_a=refs[0], ref_b=refs[1]))
                plan["summary"] = "Compare channel activity"
                return plan
            ent, via = await self._resolve_channel(account_id, f, reply_ctx,
                                                   allow_main=bool(f.get("kw_main_channel")))
            if ent is None:
                plan["missing"].append("which channel/chat (id, @username, reply, or context)")
                return plan
            plan["entities"].append(f"{ent.brief()} ({via or 'resolved'})")
            params: dict = {"ref": ent.id}
            if intent == "SEARCH_MESSAGES":
                params["query"] = f.get("quoted") or self._query_from_text(f["raw"]) or ""
                if not params["query"]:
                    plan["missing"].append("search text (quote it, e.g. 'giveaway')")
                    return plan
            plan["steps"].append(plan_step(tool, f"{tool.replace('_', ' ')} on {ent.title}",
                                           **params))
            plan["summary"] = f"{tool.replace('_', ' ')}: {ent.title}"
            return plan

        # ---------- monitoring ----------
        if intent == "MONITOR_START":
            ent, via = await self._resolve_channel(
                account_id, f, reply_ctx,
                allow_main=bool(f.get("kw_main_channel") or f.get("kw_sleep_away") or True))
            if ent is None:
                if via == "main-unreachable":
                    plan["missing"].append("configured Main Channel is not reachable - fix the ID first")
                else:
                    plan["missing"].append("which channel to watch (id/@username/reply/main channel)")
                return plan
            condition = "unknown" if f.get("kw_unknown_sender") else "all"
            tspec = f.get("time") or {}
            end_ts = None
            duration_sec = None
            if tspec.get("kind") == "at":
                end_ts = tspec["ts"]
            elif tspec.get("kind") == "duration":
                duration_sec = tspec["sec"]
                end_ts = utc_now() + duration_sec
            elif f.get("kw_sleep_away"):
                end_ts = utc_now() + 8 * 3600
                plan["notes"].append("no duration given while you sleep -> auto window 8h")
            else:
                end_ts = utc_now() + 12 * 3600
                plan["notes"].append("no duration given -> default window 12h")
            goal_txt = short(f["raw"], 90)
            plan["entities"].append(f"{ent.brief()} ({via or 'resolved'})")
            plan["steps"].append(plan_step(
                "monitor_unknown_sender" if condition == "unknown" else "monitor_new_posts",
                f"create bounded monitor on {ent.title} ({condition}, alert only)",
                channel={"id": ent.id, "title": ent.title, "kind": ent.kind},
                action="alert_only", end_ts=end_ts, goal=goal_txt))
            plan["risk"] = "low"
            plan["summary"] = (f"Monitor {ent.title} ({'unknown senders' if condition == 'unknown' else 'all posts'}"
                               f" until {ktm_iso(end_ts)}, alert only")
            return plan

        if intent == "MONITOR_STOP":
            stop_all = ("sab" in f["norm"] or " saare" in f["norm"] or "all" in f["norm"])
            if stop_all:
                plan["steps"].append(plan_step("stop_monitor", "stop ALL active monitors"))
                plan["summary"] = "Stop all running monitors"
                plan["confirmation_required"] = True
                plan["risk"] = "medium"
                return plan
            ent, via = await self._resolve_channel(account_id, f, reply_ctx, allow_main=True)
            if ent is None:
                plan["missing"].append("which channel's monitor to stop (or 'stop all monitors')")
                return plan
            plan["entities"].append(f"{ent.brief()} ({via or 'resolved'})")
            plan["steps"].append(plan_step("stop_monitor",
                                           f"find + stop active monitor on {ent.title} (never create one)",
                                           channel=ent.id))
            plan["summary"] = f"Stop monitoring {ent.title}"
            return plan

        # ---------- forward latest post to saved messages (chained) ----------
        if intent == "FORWARD_LATEST_SAVED":
            ent, via = await self._resolve_channel(account_id, f, reply_ctx,
                                                   allow_main=bool(f.get("kw_main_channel") or True))
            if ent is None:
                plan["missing"].append("which channel's post to forward")
                return plan
            plan["entities"].append(f"{ent.brief()} ({via or 'resolved'})")
            if reply_ctx is not None and reply_ctx.message_id is not None \
                    and not f.get("kw_latest") and int(ent.id) == int(reply_ctx.entity.id):
                plan["steps"].append(plan_step(
                    "forward_to_saved", "forward the exact replied message to Saved Messages",
                    ref=ent.id, message_id=reply_ctx.message_id))
            else:
                plan["steps"].append(plan_step("get_latest_message",
                                               "fetch the ACTUAL latest message", ref=ent.id))
                step2 = plan_step("forward_to_saved",
                                  "forward that exact message to Saved Messages + verify destination",
                                  ref=ent.id,
                                  message_id={"from_step": 0, "key": "message_id"})
                step2["depends_on"] = [0]
                plan["steps"].append(step2)
            plan["summary"] = f"Forward latest post of {ent.title} to Saved Messages"
            plan["risk"] = "low"
            return plan

        # ---------- delete (destructive, confirmation) ----------
        if intent == "DELETE_MESSAGES":
            ent, via = await self._resolve_channel(account_id, f, reply_ctx,
                                                   allow_main=bool(f.get("kw_main_channel")))
            if ent is None:
                plan["missing"].append("which channel to delete from")
                return plan
            count = 1 if f.get("kw_latest") else 5
            m = re.search(r"(\d{1,4})\s*(?:messages?|msg|sms|posts?)", f["norm"])
            if m:
                count = max(1, min(int(m.group(1)), 200))
            plan["entities"].append(f"{ent.brief()} ({via or 'resolved'})")
            plan["steps"].append(plan_step("delete_message",
                                           f"delete {count} message(s) from {ent.title} + verify gone",
                                           ref=ent.id, count=count))
            plan["risk"] = "high"
            plan["confirmation_required"] = True
            plan["summary"] = f"Delete {count} message(s) from {ent.title}"
            return plan

        # ---------- forward/post to main ----------
        if intent in ("FORWARD_TO_MAIN", "POST_MAIN_NOW"):
            mains = core.accounts.get_main_channels(account_id)
            if not mains:
                plan["missing"].append("no Main Channels configured")
                return plan
            if intent == "POST_MAIN_NOW":
                plan["steps"].append(plan_step("_post_to_main", "post text to all main channels",
                                               text=f.get("quoted") or ""))
                plan["summary"] = f"Post quoted text to {len(mains)} main channels"
                plan["risk"] = "medium"
                plan["confirmation_required"] = len(mains) > 3
                return plan
            ent, via = await self._resolve_channel(account_id, f, reply_ctx)
            if ent is None:
                plan["missing"].append("source of the message (reply/id/@username)")
                return plan
            count = 1
            m = re.search(r"(\d{1,3})\s*(?:messages?|msg|posts?)", f["norm"])
            if m:
                count = max(1, min(int(m.group(1)), 50))
            plan["entities"].append(f"source {ent.brief()} ({via or 'resolved'})")
            plan["steps"].append(plan_step("_forward_to_main", "forward to all main channels",
                                           source=ent.id, count=count))
            plan["risk"] = "medium"
            plan["confirmation_required"] = (count * len(mains)) > 10
            plan["summary"] = f"Forward {count} message(s) from {ent.title} to {len(mains)} main channels"
            return plan

        if intent == "SCHEDULE_POST":
            tspec = f.get("time") or {}
            if not tspec:
                plan["missing"].append("when to post (e.g. 'in 2 hours', 'kal 6 baje')")
                return plan
            plan["steps"].append(plan_step(
                "schedule_action", "persist scheduled post", text=f.get("quoted") or "",
                kind="post_main",
                run_at=tspec.get("ts") if tspec["kind"] == "at" else None,
                in_sec=tspec.get("sec") if tspec["kind"] == "duration" else None))
            plan["summary"] = f"Schedule post ({tspec.get('desc')})"
            return plan

        # ---------- cross ----------
        if intent in ("CROSS_PLAN", "CROSS_START"):
            source_hint: Optional[dict] = None
            source_msg_id: Optional[int] = None
            via = ""
            if reply_ctx is not None:
                ent = reply_ctx.entity
                try:
                    ent = await core.resolver.resolve(account_id, str(ent.id))
                except Exception:
                    pass
                source_hint = ent.brief_dict()
                source_msg_id = reply_ctx.message_id
                via = "reply"
            elif (f.get("ids") or f.get("usernames")):
                ent = await core.resolver.resolve(account_id,
                                                  (f.get("ids") or f.get("usernames"))[0])
                source_hint = ent.brief_dict()
                via = "explicit"
            else:
                ch_ctx = core.ctx.get(account_id, "channel") or {}
                if ch_ctx.get("id"):
                    ent = await core.resolver.resolve(account_id, str(ch_ctx["id"]))
                    source_hint = ent.brief_dict()
                    via = "context"
            if not source_hint:
                plan["missing"].append(
                    "cross source - reply to a source message in Saved Messages, or give id/@username")
                return plan
            # targets: folder or main channel config
            folder_hint = f.get("folder_name") or await self._folder_from_text(account_id, f)
            if folder_hint:
                fr = await core.impl.list_folder_channels(account_id, folder_hint)
                if not fr.ok:
                    plan["missing"].append(fr.error or "folder not found")
                    return plan
                targets = fr.data["channels"]
                t_via = f"folder '{fr.data['folder']}'"
            else:
                targets = core.accounts.get_main_channels(account_id)
                t_via = "configured main channels"
                if not targets:
                    plan["missing"].append(
                        "cross targets - configure Main Channels or point me to a folder")
                    return plan
            vres = await core.impl.validate_cross(account_id, source_hint["id"], targets)
            valid = vres.data["valid"]
            skipped = vres.data["skipped"]
            if not valid:
                plan["missing"].append("No different reachable target found. "
                                       + "; ".join(f"{s.get('title') or s['id']}: {s['reason']}"
                                                   for s in skipped[:4]))
                return plan
            plan["entities"].append(f"source {source_hint.get('title')} [{source_hint['id']}] ({via})"
                                    + (f" msg #{source_msg_id}" if source_msg_id else ""))
            plan["entities"].append(f"targets: {len(valid)} valid via {t_via}"
                                    + (f", {len(skipped)} skipped" if skipped else ""))
            tspec = f.get("time") or {}
            end_ts = (tspec.get("ts") if tspec.get("kind") == "at"
                      else (utc_now() + tspec["sec"] if tspec.get("kind") == "duration"
                            else utc_now() + 24 * 3600))
            if intent == "CROSS_PLAN":
                plan["report_only"] = True
                plan["steps"].append(plan_step("create_cross_plan", "persist plan only",
                                               source=source_hint, targets=valid,
                                               source_msg_id=source_msg_id))
                plan["summary"] = (f"CROSS PLAN: {source_hint.get('title')} -> {len(valid)} targets "
                                   f"(validated, source excluded)")
                plan["notes"] = [f"skipped: {s.get('title') or s['id']} - {s['reason']}"
                                 for s in skipped[:5]]
                return plan
            plan["steps"].append(plan_step("start_cross", "start cross workflow task",
                                           source=source_hint, targets=valid,
                                           source_msg_id=source_msg_id, end_ts=end_ts))
            plan["risk"] = "medium"
            plan["confirmation_required"] = len(valid) > 5
            plan["summary"] = (f"Cross {source_hint.get('title')} -> {len(valid)} targets "
                               f"(queue + live, verified), window until {ktm_iso(end_ts)}")
            plan["notes"] = [f"skipped: {s.get('title') or s['id']} - {s['reason']}"
                             for s in skipped[:5]]
            return plan

        if intent == "CROSS_STOP":
            plan["steps"].append(plan_step("stop_cross", "stop cross workflow(s)"))
            plan["summary"] = "Stop cross"
            return plan
        if intent == "CROSS_RESET":
            plan["steps"].append(plan_step("reset_cross", "reset cross workflow state"))
            plan["summary"] = "Reset cross"
            return plan
        if intent == "CROSS_STATUS":
            plan["steps"].append(plan_step("cross_status", "workflow state"))
            plan["summary"] = "Cross status"
            return plan

        # ---------- main channel config ----------
        if intent in ("MAIN_CHANNEL_CONFIG", "MAIN_CHANNEL_LIST"):
            if intent == "MAIN_CHANNEL_LIST":
                plan["steps"].append(plan_step("_main_channels_report", "read config",
                                               op="list"))
                plan["summary"] = "Show configured Main Channels"
                return plan
            refs = (f.get("ids") or []) + (f.get("usernames") or [])
            op = "add"
            if f.get("kw_stop") or "hata" in f["norm"] or "remove" in f["norm"]:
                op = "remove"
            elif re.search(r"\b(hai|hain|set|rakh)\b", f["norm"]):
                op = "set"
            if not refs and reply_ctx is not None:
                refs = [str(reply_ctx.entity.id)]
            if not refs:
                plan["missing"].append("channel ids/@usernames to configure")
                return plan
            plan["steps"].append(plan_step("_main_channels_report",
                                           f"{op} main channels", op=op, refs=refs))
            plan["summary"] = f"{op.title()} {len(refs)} main channel(s)"
            return plan

        # ---------- task control ----------
        if intent == "TASK_CONTROL":
            plan["_features"] = f
            plan["summary"] = f"Task control: {f.get('task_action', 'stop')}"
            return plan

        # ---------- alias ----------
        if intent == "SET_ALIAS":
            m = re.search(r"(.+?)\s*=\s*(.+)$", strip_command(f["raw"]))
            if m:
                plan["steps"].append(plan_step("_set_alias", "store alias",
                                               alias=m.group(1).strip(), value=m.group(2).strip()))
                plan["summary"] = "Store alias"
            else:
                plan["missing"].append("alias mapping (format: name = @username_or_id)")
            return plan

        plan["missing"].append("a mapped capability (try 'help' to see the toolbox)")
        return plan

    @staticmethod
    def _query_from_text(raw: str) -> str:
        m = re.search(r"(?:search|dhundo|dhundho|khojo|find)\s+(?:for\s+)?(.+?)(?:\s+(?:in|me|mein)\b.*)?$",
                      raw, re.I)
        return (m.group(1).strip() if m else "")[:80]


# ----------------------------------------------------------------------------
# 18. JARVIS CORE - orchestration of the full agentic pipeline
# ----------------------------------------------------------------------------

def respond(reply: str, status: str = "SUCCESS", intent: str = "",
            data: Optional[dict] = None, plan: Optional[dict] = None) -> dict:
    out = {"ok": status == "SUCCESS", "status": status, "reply": reply,
           "intent": intent, "data": data or {}}
    if plan is not None:
        out["plan"] = plan
    return out


INFO_INTENTS = {"CROSS_REQUIREMENTS_EXPLAIN", "HELP", "SYSTEM_STATUS"}

MUTATING_INTENTS = {"DELETE_MESSAGES", "FORWARD_TO_MAIN", "POST_MAIN_NOW", "SCHEDULE_POST",
                    "CROSS_START", "MONITOR_START", "MAIN_CHANNEL_CONFIG", "FOLDER_TO_MAIN",
                    "TASK_CONTROL", "CROSS_STOP", "CROSS_RESET", "MONITOR_STOP", "SET_ALIAS",
                    "FORWARD_LATEST_SAVED", "HEAL_SYSTEM"}

PLAN_ONLY_RE = re.compile(
    r"(do not execute|don'?t execute|no execution|without executing|plan only|plan -only|"
    r"read only|sirf plan|plan banao|abhi nahi chalana|mat chalao|execute mat karo|"
    r"abhi execute mat|abhi run mat|kuch change mat|change mat karna|kuch mat karna|"
    r"kuch bhi mat karo|modify mat|do not modify|nothing change|nothing modify)", re.I)

EXECUTE_PLAN_RE = re.compile(
    r"^(ab\s+)?(execute|run|chala do|chalao)( the plan| it| karo| kar do| ab| do)?[.!]?$|"
    r"^(ab\s+)?plan (execute|chala do|chalao)( karo| kar do)?[.!]?$|"
    r"^go ahead[.!]?$|^execute karo ab[.!]?$|^ab execute[.!]?$", re.I)


def detect_mode(text: str) -> Optional[str]:
    """explicit non-execution phrases force PLAN mode (never mutated)."""
    t = strip_command(text).lower()
    if PLAN_ONLY_RE.search(t):
        return "PLAN"
    n, sk = norm_text(t), skeleton(t)
    if has_kw(n, sk, ["run mat karo", "abhi mat karo"]):
        return "PLAN"
    return None


class JarvisCore:


class JarvisCore:
    def __init__(self) -> None:
        st = lambda name, section: JSONStore(DATA_DIR / f"{name}.json", section)
        self.accounts_store = st("accounts", "accounts")
        self.sessions_store = st("sessions", "sessions")
        self.brain_store = st("brain", "brain")
        self.workflows_store = st("workflows", "workflows")
        self.tasks_store = st("tasks", "tasks")
        self.monitors_store = st("monitors", "monitors")
        self.schedules_store = st("scheduled_jobs", "schedules")
        self.memory_store = st("channel_memory", "channel_memory")
        self.runtime_store = st("runtime", "runtime")
        self.tools_store = st("tools", "tools")

        self.diag = Diagnostics(self.runtime_store)
        self.memory = MemoryStore(self.memory_store)
        self.ctx = BrainContext(self.brain_store)
        self.accounts = AccountManager(self.accounts_store, self.sessions_store, self.diag)
        self.resolver = EntityResolver(self.accounts, self.memory, self.diag)
        self.confirm = ConfirmationEngine(self.ctx, self.diag)
        self.tasks = TaskEngine(self.tasks_store, self.diag)
        self.scheduler = Scheduler(self.schedules_store, self.diag)
        self.monitors = MonitorEngine(self.monitors_store, self.diag)
        self.cross = CrossEngine(self.tasks, self.accounts, self.resolver, self.diag)
        self.registry = ToolRegistry(self.tools_store, self.diag)
        self.impl = ToolImpl(self.accounts, self.resolver, self.memory, self.diag,
                             self.tasks, self.monitors, self.scheduler, self.cross, self.ctx)
        register_all_tools(self.registry, self.impl)
        self.impl.tool_registry = self.registry
        self.impl.core = self
        self.nlu = NLU()
        self.planner = Planner(self)
        self.tasks.tick_handler = self._task_tick
        self.scheduler.execute_handler = self._schedule_execute
        self.admin_cache: dict[tuple, tuple[float, set]] = {}
        self._handler_clients: dict[str, Any] = {}
        self.ai = AIEngine(self.diag)
        self.ai_available = self.ai.any_configured()

    # ---------------- tool dispatch with classified errors ----------------
    async def call_tool(self, name: str, account_id: str, **params) -> ToolResult:
        spec = self.registry.get(name)
        if spec is None or spec.handler is None:
            return ToolResult.failure(f"tool unavailable: {name}", ERR_TOOL_UNAVAILABLE)
        if not self.registry.is_enabled(name):
            return ToolResult.failure(f"tool disabled: {name}", ERR_TOOL_DISABLED)
        try:
            r = await spec.handler(account_id, **params)
        except FloodWaitError as fe:
            r = ToolResult.failure(f"FloodWait {fe.seconds}s (honor exactly)", ERR_FLOOD_WAIT,
                                   retryable=True)
        except EntityResolutionError as exc:
            r = ToolResult.failure(str(exc), ERR_ENTITY_NOT_FOUND)
        except ChatAdminRequiredError:
            r = ToolResult.failure("admin permission required for that chat",
                                   ERR_PERMISSION_DENIED, status="PERMISSION_REQUIRED")
        except ChannelPrivateError:
            r = ToolResult.failure("channel is private and not accessible from this account",
                                   ERR_CHANNEL_PRIVATE)
        except ValidationError as ve:
            r = ToolResult.failure("; ".join(ve.missing), ERR_INVALID_PARAMETER)
        except TypeError as exc:
            self.diag.err("tools", f"{name}.typeerror", f"TypeError: {short(str(exc), 200)}",
                          account_id=account_id, error_code=ERR_TOOL_UNAVAILABLE)
            r = ToolResult.failure(f"internal TypeError (logged): {short(str(exc), 120)}",
                                   ERR_TOOL_UNAVAILABLE)
        except Exception as exc:
            self.diag.err("tools", name, f"{type(exc).__name__}: {short(str(exc), 200)}",
                          account_id=account_id, error_code=ERR_TOOL_UNAVAILABLE)
            r = ToolResult.failure(f"{type(exc).__name__}: {short(str(exc), 150)}",
                                   ERR_TOOL_UNAVAILABLE, retryable=True)
        self.registry.note_use(name, r.ok, r.error)
        if r.ok:
            self.diag.ok("tools", name, short(str(list((r.data or {}).keys()))[:5], 100),
                         account_id=account_id)
        else:
            self.diag.warn("tools", name, short(str(r.error), 140),
                           account_id=account_id, error_code=r.error_code)
        return r

    # ---------------- small helpers ----------------
    async def try_resolve_title(self, account_id: str, raw: str) -> Optional[ResolvedEntity]:
        t = norm_text(raw)
        t = re.sub(r"\b(account|acc|ke|ko|ka|ki|mein|main|channel|channels|chennal|bana|do|kar|add|"
                   r"jod|daal|cross|target|hain|hai|rakh|inspect|check|karo|please|plz|isko|isse|"
                   r"isme|ye|yeh|set|to|the|a|an|of|in|on|for|pe|par|se|aur|and|watch|dhyan|rakhna|"
                   r"rakh|monitor|karna|list|dikhao|sabhi|all|me|mere|mujhe|folder|delete|hata)\b",
                   " ", t)
        t = re.sub(r"\d+", " ", t)
        t = " ".join(t.split())
        if len(t) < 3:
            return None
        try:
            return await self.resolver.resolve(account_id, t)
        except Exception:
            return None

    def _pick_account(self, account_hint: Optional[str], text: str):
        probe = None
        m = re.search(r"(?:account|acc)\s*#?\s*(\d+)", (text or "").lower())
        if m:
            probe = f"account {m.group(1)}"
        aid = self.accounts.resolve_ref(account_hint) or self.accounts.resolve_ref(probe)
        if aid:
            return aid, None
        accs = self.accounts.all()
        if not accs:
            return None, respond(
                "SIR, no account exists yet.\nCreate one in Web Control (Accounts panel) or say: "
                "create account <label>", "MISSING_CONTEXT")
        if len(accs) == 1:
            return accs[0]["account_id"], None
        names = ", ".join(f"{i+1}) {a['label']}" for i, a in enumerate(accs))
        return None, respond(f"SIR, multiple accounts exist. Which one?\n{names}", "MISSING_CONTEXT")

    # ---------------- pending plans (web goal console) ----------------
    def store_plan(self, plan: dict) -> None:
        plans = self.workflows_store.data["workflows"].setdefault("pending_plans", {})
        for pid, p in list(plans.items()):
            if utc_now() - p.get("created_ts", 0) > CONTEXT_TTL:
                plans.pop(pid, None)
        plans[plan["plan_id"]] = plan
        self.workflows_store.save()

    def pop_plan(self, plan_id: str) -> Optional[dict]:
        plans = self.workflows_store.data["workflows"].setdefault("pending_plans", {})
        plan = plans.pop(plan_id, None)
        self.workflows_store.save()
        if plan and utc_now() - plan.get("created_ts", 0) > CONTEXT_TTL:
            return None
        return plan

    # ---------------- the pipeline ----------------
    async def handle_goal(self, account_hint: Optional[str], text: str, source: str = "web",
                          reply_msg: Any = None, plan_only: bool = False) -> dict:
        text = (text or "").strip()
        if not text:
            return respond("SIR, empty goal.", "FAILED")
        aid, err = self._pick_account(account_hint, text)
        if err:
            return err

        # confirmations (account-bound, single-use, expiring)
        answer = self.confirm.matches(text)
        pend = self.confirm.pending(aid)
        if pend is not None and answer is not None:
            if not answer:
                self.confirm.consume(aid)
                return respond("Cancelled, SIR. Nothing was executed.", "WAITING",
                               (pend.get("payload", {}).get("plan") or {}).get("intent", ""))
            payload = self.confirm.consume(aid) or {}
            plan = payload.get("plan")
            if not plan:
                return respond("SIR, that confirmation payload is gone - repeat the goal.", "FAILED")
            return await self.execute_plan(plan, confirmed=True)
        if answer is not None and pend is None:
            return respond("SIR, nothing is awaiting confirmation.", "WAITING")

        # pending choices (ambiguity menus)
        pc = self.ctx.pending_choice(aid)
        if pc:
            pick = None
            t_low = text.strip().lower()
            if re.fullmatch(r"\d+", t_low):
                idx = int(t_low) - 1
                if 0 <= idx < len(pc.get("options", [])):
                    pick = pc["options"][idx]
            else:
                for opt in pc.get("options", []):
                    if opt.get("label") and opt["label"].lower() in t_low:
                        pick = opt
                        break
            if pick:
                self.ctx.set_pending_choice(aid, None)
                text = pick["goal_text"]

        # pre-directives (account lifecycle)
        low = strip_command(text).strip().lower()
        m = re.match(r"create account(?:\s+(?P<label>.+))?$", low)
        if m:
            try:
                cfg = self.accounts.create((m.group("label") or "").strip() or None)
                return respond(f"YES SIR. '{cfg['label']}' created ({cfg['account_id']}).\nNext: "
                               f"'login account {len(self.accounts.all())} +91xxxxxxxxxx' or connect in Web Control.",
                               "SUCCESS", "CREATE_ACCOUNT", {"account_id": cfg["account_id"]})
            except ValidationError as ve:
                return respond("SIR, " + "; ".join(ve.missing), "FAILED", "CREATE_ACCOUNT")
        m = re.match(r"login\s+(?:account\s+)?(\d+)\s+(\+?[\d\s-]{8,16})$", low)
        if m:
            aid2 = self.accounts.resolve_ref(f"account {m.group(1)}") or aid
            try:
                r = await self.accounts.start_login(aid2, re.sub(r"[^\d+]", "", m.group(2)))
                self.ensure_handlers(aid2)
                return respond("SIR, code sent to " + r.get("phone", "your number") +
                               ".\nReply with: code 12345" if not r.get("already")
                               else "SIR, that account is already authorized.",
                               "WAITING", "LOGIN")
            except ValidationError as ve:
                return respond("SIR, " + "; ".join(ve.missing), "FAILED", "LOGIN")
        m = re.match(r"(?:code|otp)\s+(\d{4,10})$", low)
        if m:
            target = None
            for a in self.accounts.all():
                rt = self.accounts.runtime.get(a["account_id"])
                if rt and rt.pending_login:
                    target = a["account_id"]
                    break
            if not target:
                return respond("SIR, no login is pending.", "FAILED", "LOGIN")
            r = await self.accounts.complete_login(target, m.group(1))
            if r.get("need_password"):
                return respond("SIR, 2FA is ON - enter the password in Web Control "
                               "(Accounts panel), not in chat.", "WAITING", "LOGIN")
            self.ensure_handlers(target)
            return respond(f"YES SIR. Authorized as {r.get('name') or 'user'}.", "SUCCESS", "LOGIN")

        # run a previously stored PLAN_ONLY plan
        if EXECUTE_PLAN_RE.match(low):
            plan = self.latest_plan(aid)
            if plan is None:
                return respond("SIR, no stored plan to execute.", "FAILED", "EXECUTE_PLAN")
            self.pop_plan(plan["plan_id"])
            if plan.get("confirmation_required"):
                self.confirm.require(aid, plan["summary"], {"plan": plan})
                return respond(f"SIR, this plan is {plan['risk']} risk and needs confirmation.\n"
                               f"{plan['summary']}\nReply 'yes' within {CONFIRM_TTL}s.",
                               "WAITING", plan["intent"], plan=self._plan_public(plan))
            return await self.execute_plan(plan, confirmed=False)

        # reply context
        reply_ctx: Optional[ReplyContext] = None
        if reply_msg is not None:
            try:
                reply_ctx = await self.resolver.from_reply(aid, reply_msg)
                if reply_ctx:
                    self.diag.info("context", "reply",
                                   f"reply -> {reply_ctx.entity.brief()} msg={reply_ctx.message_id}",
                                   account_id=aid)
            except Exception:
                reply_ctx = None

        # ---- understanding: deterministic NLU + validated AI brain ----
        self.diag.info("NL_INPUT", "goal", short(strip_command(text), 140), account_id=aid)
        mains = self.accounts.get_main_channels(aid)
        feats = self.nlu.features(aid, text, reply_ctx is not None, len(mains))
        nres = self.nlu.classify(feats)
        intent = nres.intent
        if self.ai.any_configured():
            decision = await self.ai_decide(aid, strip_command(text), feats, reply_ctx, mains)
            if decision:
                intent = decision["intent"] or intent
                self._apply_ai_entities(feats, decision.get("entities") or {})
                feats["ai"] = decision
        self.diag.info("INTENT", "decide",
                       f"{intent} (nlu_score={nres.score}{', ai:' + (feats.get('ai') or {}).get('provider', '') if feats.get('ai') else ', deterministic'})",
                       account_id=aid)
        if intent is None:
            # real discovery: search registry by capability
            candidates = self.registry.search(strip_command(text), limit=4)
            if candidates:
                lines = ["SIR, that goal is ambiguous, but these registered tools look relevant:"]
                for s in candidates[:4]:
                    lines.append(f"- {s.name} ({s.category}): {short(s.description, 70)}")
                lines.append("Say it with a bit more detail (channel/folder/time), and I'll plan it.")
                return respond("\n".join(lines), "WAITING", "DISCOVERY",
                               {"candidates": [s.name for s in candidates]})
            return respond(
                "SIR, I could not understand the goal even after NLU + context + toolbox discovery.\n"
                "Ask for 'help' to see every registered capability.", "FAILED", "UNMAPPED")

        nres.intent = intent
        try:
            plan = await self.planner.build(aid, nres, reply_ctx)
        except EntityResolutionError as exc:
            return respond(f"SIR, entity resolution failed: [{ERR_ENTITY_NOT_FOUND}] "
                           f"{short(str(exc), 200)}", "FAILED", intent,
                           {"error_code": ERR_ENTITY_NOT_FOUND})
        except Exception as exc:
            self.diag.err("planner", "build", f"{type(exc).__name__}: {short(str(exc), 150)}",
                          account_id=aid)
            return respond(f"SIR, planning failed ({type(exc).__name__}). "
                           f"Details are in diagnostics.", "FAILED", intent)
        plan["source_surface"] = source
        explicit_mode = detect_mode(text)
        ai_mode = (feats.get("ai") or {}).get("mode") or None
        mode = explicit_mode or ai_mode or \
            ("EXECUTE" if intent in MUTATING_INTENTS else "READ")
        plan["mode"] = mode
        self.diag.info("MODE", "select", f"{mode}{' (explicit)' if explicit_mode else ''}",
                       account_id=aid)

        # execute or only preview
        if plan_only:
            self.store_plan(plan)
            return respond(self._plan_preview_text(plan), "WAITING", intent, plan=self._plan_public(plan))
        if plan["missing"]:
            return respond("SIR, missing exactly:\n- " + "\n- ".join(plan["missing"]),
                           "MISSING_CONTEXT", intent, plan=self._plan_public(plan))
        mutating_plan = intent in MUTATING_INTENTS or any(
            (self.registry.get(s["tool"]) is not None and not self.registry.get(s["tool"]).read_only)
            for s in plan["steps"])
        if plan.get("mode") == "PLAN" and mutating_plan:
            self.store_plan(plan)
            txt = self._plan_preview_text(plan) + \
                "\nMODE: PLAN ONLY - nothing was executed.\nSay 'execute the plan' to run it" + \
                (" (confirmation will still be required)." if plan["confirmation_required"] else ".")
            self.diag.info("PLAN", "hold", f"{intent} held as PLAN ONLY", account_id=aid)
            return respond(txt, "WAITING", intent, plan=self._plan_public(plan))
        if plan["confirmation_required"]:
            self.confirm.require(aid, plan["summary"], {"plan": plan})
            return respond(
                f"SIR, confirmation required:\n{plan['summary']}\n"
                f"Reply 'yes' within {CONFIRM_TTL}s (single-use) to proceed.",
                "WAITING", intent, plan=self._plan_public(plan))
        return await self.execute_plan(plan, confirmed=False)

    def _plan_public(self, plan: dict) -> dict:
        return {"plan_id": plan["plan_id"], "intent": plan["intent"], "summary": plan["summary"],
                "entities": plan["entities"], "steps": plan["steps"], "risk": plan["risk"],
                "mode": plan.get("mode", "READ"),
                "confirmation_required": plan["confirmation_required"],
                "missing": plan["missing"], "report_only": plan["report_only"],
                "notes": plan["notes"]}

    def _plan_preview_text(self, plan: dict) -> str:
        lines = [f"PLAN [{plan['intent']}] {plan['summary'] or '(no summary)'}"]
        if plan["entities"]:
            lines.append("Entities: " + " | ".join(plan["entities"]))
        for i, s in enumerate(plan["steps"], 1):
            lines.append(f"{i}) {s['tool']} - {s['note']}")
        lines.append(f"Risk: {plan['risk']} | confirmation: "
                     f"{'required' if plan['confirmation_required'] else 'not required'}")
        if plan["missing"]:
            lines.append("Missing: " + "; ".join(plan["missing"]))
        return "\n".join(lines)

    # ---------------- executor ----------------
    async def execute_plan(self, plan: dict, confirmed: bool) -> dict:
        account_id = plan["account_id"]
        intent = plan["intent"]
        ctx_updates: dict[str, dict] = {}

        def fin(reply: str, status: str = "SUCCESS", data: Optional[dict] = None) -> dict:
            if ctx_updates:
                self.ctx.update_bulk(account_id, ctx_updates)
            self.ctx.push_action(account_id, {"intent": intent, "status": status,
                                              "summary": plan.get("summary", "")})
            return respond(reply, status, intent, data)

        # task control resolves against the live registry
        if intent == "TASK_CONTROL":
            f = plan.get("_features") or {}
            action = f.get("task_action") or "stop"
            reply, status, data = await self._task_control_exec(account_id, action, f)
            return fin(reply, status, data)

        # informational / report-only plans
        if intent == "IDENTIFY_REPLY":
            lines = ["YES SIR. Replied-message identification (read-only, nothing changed):"]
            lines += [f"- {e}" for e in plan["entities"]]
            return fin("\n".join(lines))

        if intent == "CROSS_REQUIREMENTS_EXPLAIN":
            lines = ["SIR, before Cross starts I verify all of this:"]
            lines += [f"{i+1}) {n}" for i, n in enumerate(plan["notes"])]
            if plan.get("entities"):
                lines.append("Right now from context:")
                lines += [f"- {e}" for e in plan["entities"] if e]
            lines.append("Nothing was executed - this was an information/planning answer.")
            return fin("\n".join(lines))
        if intent == "CROSS_PLAN" and plan["report_only"]:
            r = await self.call_tool("create_cross_plan", account_id, **plan["steps"][0]["params"])
            if not r.ok:
                return fin(f"SIR, plan failed validation: {r.error}", "FAILED")
            lines = [f"YES SIR. Cross plan ready (not started).",
                     f"Source: {plan['entities'][0] if plan['entities'] else '?'}",
                     f"{plan['entities'][1] if len(plan['entities']) > 1 else ''}"]
            lines += plan["notes"]
            lines.append("Say 'Cross start karo' to execute this plan.")
            return fin("\n".join(lines))

        # generic step execution (ordered chain; depends_on placeholders resolved)
        outputs: list[ToolResult] = []
        for idx, step in enumerate(plan["steps"]):
            tool = step["tool"]
            params = dict(step.get("params") or {})
            for pk, pv in list(params.items()):
                if isinstance(pv, dict) and "from_step" in pv:
                    si = int(pv["from_step"])
                    if si >= len(outputs) or not outputs[si].ok \
                            or (outputs[si].data or {}).get(pv.get("key")) is None:
                        dep_code = outputs[si].error_code if si < len(outputs) else ERR_TOOL_UNAVAILABLE
                        dep_err = outputs[si].error if si < len(outputs) else "step output missing"
                        step["status"] = "SKIPPED"
                        self.diag.err("EXECUTION", "chain",
                                      f"aborted at step {idx+1}; dependency step {si+1} failed",
                                      account_id=account_id, error_code=dep_code)
                        return fin(f"FAILED, SIR. Plan chain aborted at step {idx+1} "
                                   f"(depends on step {si+1}).\n[{dep_code}] {dep_err}",
                                   "FAILED", {"aborted_at": idx + 1, "dependency": si + 1})
                    params[pk] = (outputs[si].data or {}).get(pv.get("key"))
            step["params"] = params
            step["status"] = "RUNNING"
            if tool == "_post_to_main":
                mains = self.accounts.get_main_channels(account_id)
                if not mains:
                    return fin("SIR, no Main Channels configured.", "FAILED")
                lines, bad = [], 0
                for ch in mains:
                    r = await self.call_tool("send_message", account_id, ref=ch["id"],
                                             text=step["params"]["text"])
                    if r.ok:
                        lines.append(f"+ {ch.get('title')}: posted #{r.data.get('message_id')} "
                                     f"(verified {(r.verification or {}).get('verified')})")
                    else:
                        bad += 1
                        lines.append(f"x {ch.get('title')}: {r.error_code} - {short(r.error or '', 60)}")
                return fin(("DONE, SIR." if bad == 0 else "PARTIAL/FAILED, SIR.") + "\n" +
                           "\n".join(lines[:12]),
                           "SUCCESS" if bad == 0 else "FAILED")
            if tool == "_forward_to_main":
                mains = self.accounts.get_main_channels(account_id)
                lines, bad = [], 0
                for ch in mains:
                    r = await self.call_tool("forward_message", account_id,
                                             source=step["params"]["source"], target=ch["id"],
                                             count=step["params"]["count"])
                    if r.ok:
                        lines.append(f"+ {ch.get('title')}: {r.data.get('sent')} sent "
                                     f"(verified {(r.verification or {}).get('verified')})")
                    else:
                        bad += 1
                        lines.append(f"x {ch.get('title')}: {r.error_code} - {short(r.error or '', 60)}")
                return fin(("DONE, SIR." if bad == 0 else "PARTIAL/FAILED, SIR.") + "\n" +
                           "\n".join(lines[:12]),
                           "SUCCESS" if bad == 0 else "FAILED")
            if tool == "_main_channels_report":
                return fin(await self._main_channels_exec(account_id, step["params"]))
            if tool == "_set_alias":
                alias = step["params"]["alias"]
                value = step["params"]["value"]
                try:
                    ent = await self.resolver.resolve(account_id, value)
                except EntityResolutionError as exc:
                    return fin(f"SIR, cannot map alias: {exc}", "FAILED")
                self.memory.set_alias(account_id, alias, str(ent.id))
                return fin(f"YES SIR. '{alias}' now means {ent.title} [{ent.id}].")
            r = await self.call_tool(tool, account_id, **step["params"])
            outputs.append(r)
            step["status"] = "DONE" if r.ok else "FAILED"
            self.diag.info("EXECUTION", "step",
                           f"{idx+1}/{len(plan['steps'])} {tool} -> "
                           f"{'DONE' if r.ok else 'FAILED ' + str(r.error_code)}",
                           account_id=account_id)
            if not r.ok and intent not in ("TASK_LIST",):
                return fin(self._failure_text(intent, step, r),
                           "FAILED" if r.status != "PERMISSION_REQUIRED" else "PERMISSION_REQUIRED",
                           r.to_dict())

        return fin(*self._format_success(account_id, plan, outputs, ctx_updates))

    def _failure_text(self, intent: str, step: dict, r: ToolResult) -> str:
        base = {"ENTITY_NOT_FOUND": "I could not resolve the entity",
                "PERMISSION_DENIED": "I don't have permission",
                "CHANNEL_PRIVATE": "That channel is private/inaccessible",
                "MESSAGE_NOT_FOUND": "The message does not exist",
                "FLOOD_WAIT": "Telegram rate-limit active - I must wait",
                "TOOL_DISABLED": "That tool is disabled in the toolbox",
                "TASK_NOT_FOUND": "I could not find that in the registry"}.get(
                    r.error_code, "Execution failed")
        return (f"FAILED, SIR. {base}.\n[{r.error_code}] {r.error}\n"
                f"(while running '{step['tool']}')")

    def _format_success(self, account_id: str, plan: dict, outputs: list[ToolResult],
                        ctx_updates: dict) -> tuple[str, str, Optional[dict]]:
        intent = plan["intent"]
        by_tool = {s["tool"]: r for s, r in zip(plan["steps"], outputs)}

        def need(name: str) -> ToolResult:
            return by_tool.get(name) or ToolResult.failure("step missing", ERR_TOOL_UNAVAILABLE)

        if intent == "ACCOUNT_INFO":
            d = need("account_info").data
            lines = ["YES SIR. Safe account report:",
                     f"Label: {d['label']} (managed id {d['managed_account_id']})",
                     f"Connection: {'online' if d['connected'] else 'OFFLINE'} | "
                     f"Authorized: {'yes' if d['authorized'] else 'NO'}",
                     f"API mode: {d['api_mode']} | Main channels configured: {d['main_channels']}"]
            if d.get("authorized"):
                lines.append(f"Name: {d.get('name') or '?'} | @{d.get('username') or '-'} | "
                             f"Telegram ID: {d.get('telegram_id')} | {d.get('phone')}")
            lines.append(d["note"])
            return "\n".join(lines), "SUCCESS", d

        if intent == "ACCOUNT_SESSIONS":
            d = need("account_sessions").data
            lines = [f"YES SIR. {d['count']} active session(s):"]
            for s in d["sessions"]:
                lines.append(f"- {'THIS DEVICE' if s['current'] else 'session'}: {s['device']} ({s['app']})")
            return "\n".join(lines), "SUCCESS", d

        if intent == "SYSTEM_STATUS":
            d = need("system_status").data
            tg = need("telegram_status").data
            lines = ["YES SIR. Systems report:"]
            for a in tg["accounts"]:
                lines.append(f"- {a['label']}: {'online+authorized' if a['authorized'] else ('connected, NOT authorized' if a['connected'] else 'offline')}"
                             + (f" ({a['last_error']})" if a.get("last_error") else ""))
            lines += [f"Tasks active: {d['tasks_active']} | controllable: {d['tasks_controllable']} | "
                      f"monitors: {d['monitors_active']} | schedules: {d['schedules_pending']}",
                      f"Uptime: {human_delta(d['uptime_sec'])} | KTM: {d['ktm_now']}"]
            if d.get("last_failure"):
                lf = d["last_failure"]
                lines.append(f"Last failure: {lf['component']}.{lf['operation']}: {short(lf['message'], 70)}")
            return "\n".join(lines), "SUCCESS", d

        if intent == "LIST_FOLDERS":
            d = need("list_folders").data
            if not d["count"]:
                return "SIR, this account has no Telegram folders.", "SUCCESS", d
            lines = [f"YES SIR. {d['count']} folder(s):"]
            lines += [f"- {f['title']} [{f['id']}] ({f['peer_count']} chats)" for f in d["folders"]]
            ctx_updates["folder"] = {"name": d["folders"][0]["title"], "id": d["folders"][0]["id"]}
            return "\n".join(lines), "SUCCESS", d

        if intent in ("INSPECT_FOLDER", "FOLDER_CHANNELS"):
            r = need("inspect_folder") if intent == "INSPECT_FOLDER" else need("list_folder_channels")
            d = r.data
            if intent == "FOLDER_CHANNELS":
                lines = [f"YES SIR. Folder '{d['folder']}' - {d['count']} channel(s):"]
                for c in d["channels"]:
                    lines.append(f"- {c['title']} [{c['id']}]" + (f" @{c['username']}" if c.get("username") else ""))
                ctx_updates["folder"] = {"name": d["folder"]}
                if d["channels"]:
                    ctx_updates["channel"] = {"id": d["channels"][0]["id"],
                                              "title": d["channels"][0]["title"]}
                return "\n".join(lines), "SUCCESS", d
            lines = [f"YES SIR. Folder '{d['title']}' [{d['id']}] - {d['total_peers']} chat(s):"]
            for c in d["channels"]:
                lines.append(f"  [channel] {c['title']} [{c['id']}]" + (f" @{c['username']}" if c.get("username") else ""))
            for g in d["groups"]:
                lines.append(f"  [group] {g['title']} [{g['id']}]")
            for u in d["users"]:
                lines.append(f"  [user] {u['title']} [{u['id']}]")
            for u in d["unresolved"][:4]:
                lines.append(f"  [unresolved peer] {u['id']}")
            lines.append("Nothing was changed - read-only inspection.")
            ctx_updates["folder"] = {"name": d["title"], "id": d["id"]}
            return "\n".join(lines), "SUCCESS", d

        if intent == "FOLDER_TO_MAIN":
            r = need("list_folder_channels")
            chans = r.data["channels"]
            if not chans:
                return "SIR, that folder has no channels to target.", "FAILED", None
            vres = need("validate_cross")
            mains = [{"id": c["id"], "title": c["title"], "username": c.get("username", ""),
                      "added_at": iso(), "via": f"folder '{r.data['folder']}'"}
                     for c in chans[:MAX_TARGETS]]
            self.accounts.set_main_channels(account_id, mains)
            ctx_updates["folder"] = {"name": r.data["folder"]}
            lines = [f"YES SIR. {len(mains)} channel(s) from folder '{r.data['folder']}' are now the "
                     f"Main Channel targets:"]
            lines += [f"+ {c['title']} [{c['id']}]" for c in mains[:12]]
            lines.append("Web Control reflects this immediately.")
            return "\n".join(lines), "SUCCESS", {"main_channels": mains}

        if intent == "TASK_LIST":
            t = need("list_tasks").data
            m = need("list_monitors").data
            s = need("list_schedules").data
            x = need("cross_status").data
            lines = []
            if t["count"]:
                lines.append(f"TASKS ({t['count']}):")
                for task in t["tasks"]:
                    lines.append(f"- [{task['kind']}] {task['short_id']} {task['status']} "
                                 f"'{short(task.get('goal') or '', 30)}'"
                                 + (f" -> {task['targets']} tgts" if task.get("targets") else "")
                                 + (f" | err {task['error_count']}" if task.get("error_count") else "")
                                 + (f" | ends {task['end_time']}" if task.get("end_time") else ""))
            if m["count"]:
                lines.append(f"MONITORS ({m['count']}):")
                for mon in m["monitors"]:
                    lines.append(f"- {mon['title']} [{mon['channel_id']}] {mon['condition']} -> {mon['action']}"
                                 f" | hits {mon.get('hits', 0)} | until {mon.get('end_ktm', '?')}")
            if s["schedules"]:
                lines.append(f"SCHEDULED ({len(s['schedules'])}):")
                for sc in s["schedules"]:
                    lines.append(f"- {sc['schedule_id']} at {sc.get('run_at_ktm')} ({sc['payload'].get('type')})")
            if x["count"]:
                lines.append(f"CROSS WORKFLOWS ({x['count']}):")
                for c in x["cross_tasks"]:
                    lines.append(f"- {c['task_id'][:12]} {c['status']}: {c['source']} -> {c['targets']} tgts "
                                 f"| queue {len(c['completed_targets'])}/{c['targets']} done | cursor {c['cursor']}")
            if not lines:
                return "SIR, nothing is running. No tasks, monitors, schedules or workflows.", "SUCCESS", None
            return "\n".join(lines), "SUCCESS", {"tasks": t["tasks"], "monitors": m["monitors"],
                                                 "schedules": s["schedules"], "cross": x["cross_tasks"]}

        if intent == "MONITOR_START":
            r = outputs[-1]
            d = r.data
            ctx_updates["channel"] = {"id": d["channel"].split("[")[-1].rstrip("]"),
                                      "title": d["channel"].split(" [")[0]}
            ctx_updates["monitor"] = {"monitor_id": d["monitor_id"]}
            ctx_updates["task"] = {"task_id": d["task_id"]}
            cond_lbl = "unknown (non-admin) senders" if d["condition"] == "unknown" else "all new posts"
            lines = ["YES SIR. Monitoring active.",
                     f"Channel: {d['channel']}",
                     f"Condition: {cond_lbl}.",
                     f"Action: ALERT ONLY -> your Saved Messages (no deletions).",
                     f"Window: until {d['end_ktm']}."]
            lines += plan["notes"]
            return "\n".join(lines), "SUCCESS", d

        if intent == "MONITOR_STOP":
            r = outputs[-1]
            d = r.data or {}
            ids = d.get("ids") or []
            if not d.get("stopped"):
                return "SIR, no active monitor matched that target - nothing was stopped.", \
                    "FAILED", r.to_dict()
            lines = [f"YES SIR. Stopped {d['stopped']} monitor(s): {', '.join(ids[:6])}.",
                     f"Verification: persisted STOPPED = {'yes' if d.get('verified') else 'no'}.",
                     "No new monitor was created."]
            ctx_updates["monitor"] = {}
            return "\n".join(lines), "SUCCESS", d

        if intent == "LATEST_MESSAGE":
            d = need("get_latest_message").data
            lines = ["YES SIR. Latest post (read-only):",
                     f"Channel: {d['entity']}",
                     f"Message ID: {d['message_id']}",
                     f"Date: {d.get('date_ktm') or d.get('date')}",
                     f"Text: \"{d.get('text') or '[no text]'}\"",
                     f"Media: {'yes (' + str(d.get('media_type')) + ')' if d.get('has_media') else 'no'}"
                     + (f" | Views: {d.get('views')}" if d.get('views') is not None else ""),
                     "Nothing was modified."]
            ctx_updates["channel"] = {"id": d["entity_id"],
                                      "title": d["entity"].split(" [")[0]}
            ctx_updates["conversation"] = {}
            return "\n".join(lines), "SUCCESS", d

        if intent == "FORWARD_LATEST_SAVED":
            r = need("forward_to_saved")
            d = r.data
            lines = ["DONE, SIR - verified delivery.",
                     f"Source: {d['source']} (message #{d['source_message_id']})",
                     f"Destination: your Saved Messages (message #{d['saved_message_id']})",
                     "Verification: destination re-fetch confirmed."]
            return "\n".join(lines), "SUCCESS", d

        if intent == "SCHEDULE_LIST":
            d = need("list_schedules").data
            if not d["schedules"]:
                return "SIR, scheduler queue is empty.", "SUCCESS", d
            lines = [f"YES SIR. {len(d['schedules'])} scheduled job(s):"]
            for sc in d["schedules"]:
                lines.append(f"- {sc['schedule_id']} at {sc.get('run_at_ktm')} "
                             f"({sc['payload'].get('type')}: {short(sc['payload'].get('text', ''), 40)})")
            return "\n".join(lines), "SUCCESS", d

        if intent == "MONITOR_LIST":
            d = need("list_monitors").data
            if not d["count"]:
                return "SIR, no active monitors.", "SUCCESS", d
            lines = [f"YES SIR. {d['count']} active monitor(s):"]
            for mon in d["monitors"]:
                lines.append(f"- {mon['title']} [{mon['channel_id']}] {mon['condition']} "
                             f"| hits {mon.get('hits', 0)} | until {mon.get('end_ktm')}")
            return "\n".join(lines), "SUCCESS", d

        if intent == "INSPECT_CHANNEL":
            d = need("inspect_channel").data
            rights = d.get("rights") or {}
            lines = ["CHANNEL REPORT",
                     f"{d['title']} [{d['id']}]{(' @' + d['username']) if d.get('username') else ''} ({d['kind']})",
                     f"Members: {d.get('participants') if d.get('participants') is not None else 'unknown'} | "
                     f"I am admin: {'yes' if rights.get('is_admin') else 'no/unknown'}",
                     f"My rights: post={'y' if rights.get('post') else 'n'} "
                     f"delete={'y' if rights.get('delete') else 'n'} ban={'y' if rights.get('ban') else 'n'}",
                     f"Sampled {d.get('message_count_sampled')} posts; named senders: {d.get('named_senders_in_sample')}. Recent:"]
            for m0 in d.get("last_messages", [])[:8]:
                tag = f" ({m0['sender']})" if m0.get("sender") else ""
                lines.append(f"  [#{m0['id']}] {m0['text']}{tag}")
            ctx_updates["channel"] = {"id": d["id"], "title": d["title"]}
            return "\n".join(lines), "SUCCESS", d

        if intent == "RECENT_MESSAGES":
            d = need("get_recent_messages").data
            lines = [f"YES SIR. Recent from {d['entity']}:"]
            lines += [f"  [#{m0['id']}] {m0['text']}" for m0 in d["messages"]]
            return "\n".join(lines), "SUCCESS", d

        if intent == "SEARCH_MESSAGES":
            d = need("search_messages").data
            if not d["count"]:
                return f"SIR, no matches for '{d['query']}' in {d['entity']}.", "SUCCESS", d
            lines = [f"YES SIR. {d['count']} match(es) for '{d['query']}' in {d['entity']}:"]
            lines += [f"  [#{m0['id']}] {m0['text']}" for m0 in d["matches"]]
            return "\n".join(lines), "SUCCESS", d

        if intent in ("CHANNEL_ACTIVITY", "COMPARE_ACTIVITY"):
            tool = "channel_activity" if intent == "CHANNEL_ACTIVITY" else "compare_measurable_activity"
            d = need(tool).data
            if intent == "COMPARE_ACTIVITY":
                a, b = d["a"], d["b"]
                lines = [f"YES SIR. Activity comparison:",
                         f"A {a['entity']}: ~{a.get('approx_posts_per_day')} posts/day, avg views {a.get('avg_views')}",
                         f"B {b['entity']}: ~{b.get('approx_posts_per_day')} posts/day, avg views {b.get('avg_views')}",
                         f"More active: {'A' if d['more_active'] == 'a' else 'B'}"]
                return "\n".join(lines), "SUCCESS", d
            lines = [f"YES SIR. Activity for {d['entity']}:",
                     f"~{d.get('approx_posts_per_day')} posts/day over {d.get('span_days')}d sample, "
                     f"avg views {d.get('avg_views')}, latest at {d.get('latest_post_at')}"]
            return "\n".join(lines), "SUCCESS", d

        if intent == "ADMIN_RIGHTS":
            d = need("inspect_admin_rights").data
            lines = [f"YES SIR. {d['count']} admin(s) in {d['entity']}:"]
            lines += [f"- {a['name'] or a['id']}{' @' + a['username'] if a.get('username') else ''}"
                      f"{' (creator)' if a['creator'] else ''}" for a in d["admins"][:15]]
            return "\n".join(lines), "SUCCESS", d

        if intent == "DELETE_MESSAGES":
            d = outputs[-1].data
            lines = [f"DONE, SIR.",
                     f"Deleted {d.get('deleted')}/{d.get('requested')} in {d.get('entity')}.",
                     f"Verification: {(outputs[-1].verification or {}).get('verified_gone')} confirmed gone by re-fetch."]
            return "\n".join(lines), "SUCCESS", d

        if intent == "SCHEDULE_POST":
            d = need("schedule_action").data
            return (f"YES SIR. Scheduled. Post lands in your Main Channels at {d['run_at_ktm']}.\n"
                    f"Schedule id: {d['schedule_id']}", "SUCCESS", d)

        if intent == "CROSS_START":
            d = outputs[-1].data
            ctx_updates["channel"] = {"id": d["source"]["id"], "title": d["source"].get("title", "")}
            ctx_updates["cross"] = {"task_id": d["task_id"]}
            ctx_updates["task"] = {"task_id": d["task_id"]}
            lines = ["YES SIR. Cross started.",
                     f"Source: {d['source'].get('title')} [{d['source']['id']}]"
                     + (f" msg #{d['source_msg_id']}" if d.get("source_msg_id") else ""),
                     f"Targets: {d['targets']} validated channel(s)."]
            lines += plan["notes"]
            lines.append(f"Window: until {d.get('end_ktm')}. Queue + live deliveries verified before counting.")
            return "\n".join(lines), "SUCCESS", d

        if intent == "CROSS_STOP":
            d = outputs[-1].data
            return f"YES SIR. Cross stopped ({d.get('stopped')} task(s)).", "SUCCESS", d
        if intent == "CROSS_RESET":
            d = outputs[-1].data
            return f"YES SIR. Cross workflow reset (cursor + queues cleared).", "SUCCESS", d
        if intent == "CROSS_STATUS":
            d = need("cross_status").data
            if not d["count"]:
                return "SIR, no cross workflows exist yet.", "SUCCESS", d
            lines = [f"YES SIR. Cross workflows ({d['count']}):"]
            for c in d["cross_tasks"]:
                lines.append(f"- {c['task_id'][:12]} {c['status']}: {c['source']} -> {c['targets']} tgts | "
                             f"queue {len(c['completed_targets'])}/{c['targets']} | cursor {c['cursor']} "
                             f"| skipped {len(c['skipped_targets'])}")
            return "\n".join(lines), "SUCCESS", d

        if intent == "LIST_DIALOGS":
            d = need("list_dialogs").data
            lines = [f"YES SIR. {d['count']} recent dialog(s):"]
            for it in d["dialogs"][:15]:
                lines.append(f"- [{it['kind']}] {it['title']} [{it['id']}]"
                             + (f" @{it['username']}" if it.get("username") else ""))
            return "\n".join(lines), "SUCCESS", d

        if intent == "LIST_CHANNELS":
            d = need("list_channels").data
            lines = [f"YES SIR. {d['count']} channel/group(s):"]
            for it in d["channels"][:18]:
                lines.append(f"- [{it['kind']}] {it['title']} [{it['id']}]")
            return "\n".join(lines), "SUCCESS", d

        if intent == "HELP":
            d = need("explain_capabilities").data
            lines = ["YES SIR. Registered toolbox (speak naturally; I discover tools by capability):"]
            for cat, names in sorted(d["categories"].items()):
                lines.append(f"[{cat.upper()}] {', '.join(names)}")
            lines.append("Context (reply/context/main channel/folder/memory) fills parameters.")
            return "\n".join(lines), "SUCCESS", d

        if intent == "SYSTEM_DIAGNOSTICS":
            lines = ["YES SIR. System diagnostics:"]
            for step_r, step in zip(outputs, plan["steps"]):
                d = step_r.data or {}
                if step["tool"] == "system_status":
                    lines.append(f"- uptime {human_delta(d.get('uptime_sec', 0))} | tasks {d.get('tasks_active')} active | "
                                 f"monitors {d.get('monitors_active')} | schedules {d.get('schedules_pending')}")
                elif step["tool"] == "telegram_status":
                    for a in d.get("accounts", []):
                        lines.append(f"- {a['label']}: {'online+authorized' if a['authorized'] else ('connected, NOT authorized' if a['connected'] else 'offline')}"
                                     + (f" ({a['last_error']})" if a.get('last_error') else ""))
                elif step["tool"] == "task_health":
                    lines.append(f"- unhealthy tasks: {d.get('count')}")
                elif step["tool"] == "monitor_health":
                    lines.append(f"- monitors needing attention: {d.get('count')}")
                elif step["tool"] == "tool_health":
                    bad = d.get("degraded_or_disabled") or []
                    lines.append(f"- tools {d.get('total_tools')} registered | degraded/disabled: {len(bad)}")
            lines.append("Say 'heal the system' to apply safe repairs.")
            return "\n".join(lines), "SUCCESS", None

        if intent == "HEAL_SYSTEM":
            d = outputs[-1].data or {}
            lines = ["HEALING REPORT (safe, predefined repairs only):"]
            for op in d.get("ops", []):
                lines.append(f"- {op.get('op')}: {op.get('detail')}")
            lines.append(f"Healed at {d.get('healed_at')}. No secrets touched, no destructive actions.")
            return "\n".join(lines), "SUCCESS", d

        # generic
        last = outputs[-1]
        pretty = json.dumps(last.data or {}, ensure_ascii=False, indent=1)[:1200]
        return (f"YES SIR.\n{pretty}", "SUCCESS", last.data)

    async def _task_control_exec(self, account_id: str, action: str, f: dict):
        raw_low = (f.get("raw") or "").lower()
        n, sk = f.get("norm", ""), f.get("skel", "")
        m = re.search(r"(task_[a-z0-9]{6,})", raw_low)
        task = None
        if m:
            task = self.tasks.get(m.group(1))
            if task and task.account_id != account_id:
                return ("SIR, that task belongs to a different account.", "FAILED", None)
        if task is None:
            pool = []
            for t in self.tasks.list(account_id):
                if action == "retry":
                    if t.status in (TS_FAILED, TS_EXPIRED, TS_WAITING, TS_PAUSED, TS_STOPPED):
                        pool.append(t)
                elif t.status in TS_ACTIVE_SET | {TS_PAUSED}:
                    pool.append(t)
            kind_pref = None
            if re.search(r"\bcross\b", raw_low):
                kind_pref = "cross"
            elif has_kw(n, sk, ["monitor", "monitoring", "nigrani", "watch"]):
                kind_pref = "monitor"
            if kind_pref:
                kp = [t for t in pool if t.kind == kind_pref]
                if kp:
                    pool = kp
            if has_kw(n, sk, ["sab", "saare", "sari", "all", "sb"]) and action in ("stop",):
                stopped = 0
                for t in pool:
                    r = await self.impl._task_action(account_id, t.task_id, "stop")
                    if r.ok:
                        stopped += 1
                mons = self.monitors.stop_all(account_id) if kind_pref == "monitor" or not kind_pref else 0
                self.ctx.update(account_id, "monitor")
                return (f"YES SIR. Stopped {stopped} task(s) and {mons} monitor(s).",
                        "SUCCESS", {"stopped": stopped, "monitors": mons})
            tctx = self.ctx.get(account_id, "task") or {}
            ctx_tid = tctx.get("task_id")
            ctx_task = next((t for t in pool if t.task_id == ctx_tid), None)
            if ctx_task is not None:
                task = ctx_task
            elif len(pool) == 1:
                task = pool[0]
            elif not pool:
                extra = " Nothing is running right now." if action != "retry" \
                    else " Nothing is FAILED/WAITING to retry."
                return ("SIR, no matching task found in the registry." + extra, "FAILED", None)
            else:
                opts = []
                for t in pool[:5]:
                    src = (t.params.get("source") or t.params.get("channel") or {})
                    label = f"{t.kind} '{short(src.get('title') or t.goal or t.task_id, 26)}' ({t.status})"
                    opts.append({"label": label, "goal_text": f"{action} {t.task_id}"})
                self.ctx.set_pending_choice(account_id, {"options": opts})
                lines = [f"SIR, I found {len(opts)} matching tasks:"]
                for i, o in enumerate(opts, 1):
                    lines.append(f"{i}) {o['label']}")
                lines.append(f"Which one should I {action}? (say: 1 / 2 / ...)")
                return ("\n".join(lines), "MISSING_CONTEXT", {"options": opts})
        r = await self.impl._task_action(account_id, task.task_id, action)
        if not r.ok:
            return (f"SIR, could not {action}: [{r.error_code}] {r.error}", "FAILED", r.to_dict())
        pub = (r.data or {}).get("task") or {}
        self.ctx.update(account_id, "task", task_id=task.task_id)
        return (f"YES SIR. {task.kind.title()} {task.task_id[:12]} -> {pub.get('status')}.",
                "SUCCESS", r.to_dict())

    async def _main_channels_exec(self, account_id: str, params: dict) -> str:
        op = params.get("op", "list")
        if op == "list":
            mains = self.accounts.get_main_channels(account_id)
            if not mains:
                return ("SIR, no Main Channels configured.\n"
                        "Tell me: 'main channel set karo -100xxxxxxxxxx' or use Web Control.")
            lines = [f"YES SIR. Configured Main Channels ({len(mains)}):"]
            for i, c in enumerate(mains, 1):
                lines.append(f"{i}) {c.get('title') or '?'} [{c['id']}]"
                             + (f" @{c['username']}" if c.get("username") else ""))
            ctx = self.ctx.get(account_id, "account")
            return "\n".join(lines)
        cur = {str(c["id"]): c for c in self.accounts.get_main_channels(account_id)}
        changed, notes = [], []
        if op == "set":
            cur = {}
        for ref in params.get("refs") or []:
            try:
                ent = await self.resolver.resolve(account_id, ref)
            except EntityResolutionError as exc:
                notes.append(f"skip {ref}: {short(str(exc), 80)}")
                continue
            key = str(ent.id)
            if op == "remove":
                if key in cur:
                    cur.pop(key)
                    changed.append(f"- {ent.title} [{ent.id}]")
                continue
            cur[key] = {"id": ent.id, "title": ent.title, "username": ent.username,
                        "added_at": iso(), "via": "jarvis"}
            changed.append(f"+ {ent.title} [{ent.id}]")
        out = list(cur.values())[:MAX_TARGETS]
        self.accounts.set_main_channels(account_id, out)
        lines = [f"YES SIR. Main Channels updated ({len(out)} total)."]
        lines += changed[:10]
        if notes:
            lines.append("Notes: " + "; ".join(notes[:4]))
        lines.append("Same state visible in Web Control.")
        return "\n".join(lines)

    # ---------------- real AI brain (validated decisions, never execution) ----------------
    AI_EXTRA_INTENTS = {
        "IDENTIFY_REPLY", "MAIN_CHANNEL_LIST", "MAIN_CHANNEL_CONFIG", "TASK_LIST", "TASK_CONTROL",
        "LIST_CHANNELS", "LIST_FOLDERS", "LIST_DIALOGS", "HELP", "STATUS", "SET_ALIAS",
        "FORWARD_LATEST_SAVED", "LATEST_MESSAGE", "ACCOUNT_SESSIONS", "CROSS_STATUS",
        "COMPARE_ACTIVITY", "CHANNEL_ACTIVITY", "RECENT_MESSAGES", "SEARCH_MESSAGES",
        "SCHEDULE_LIST", "SCHEDULE_CANCEL", "CROSS_REQUIREMENTS_EXPLAIN", "MONITOR_LIST",
        "MONITOR_STOP", "CROSS_PLAN", "HEAL_SYSTEM", "SYSTEM_DIAGNOSTICS", "SYSTEM_STATUS",
    }

    def latest_plan(self, account_id: str) -> Optional[dict]:
        plans = self.workflows_store.data["workflows"].setdefault("pending_plans", {})
        cands = [(p.get("created_ts", 0), p) for p in plans.values()
                 if p.get("account_id") == account_id
                 and utc_now() - p.get("created_ts", 0) <= CONTEXT_TTL]
        if not cands:
            return None
        cands.sort(key=lambda x: -x[0])
        return cands[0][1]

    def _validate_ai_decision(self, data: Any, allowed: set) -> Optional[dict]:
        if not isinstance(data, dict):
            return None
        intent = str(data.get("intent") or "")
        if intent not in allowed:
            return None
        mode = str(data.get("mode") or "").upper()
        if mode not in AI_MODES:
            mode = ""
        ents = data.get("entities") if isinstance(data.get("entities"), dict) else {}
        missing = [short(str(x), 80) for x in data.get("missing")][:6] \
            if isinstance(data.get("missing"), list) else []
        return {"intent": intent, "mode": mode, "entities": ents, "missing": missing,
                "confirmation_required": bool(data.get("confirmation_required")),
                "reason": short(str(data.get("reason") or ""), 180)}

    def _apply_ai_entities(self, feats: dict, ents: dict) -> None:
        for key in ("source", "target", "targets", "channel"):
            v = ents.get(key)
            v = str(v).strip() if v is not None else ""
            if not v or v.lower() in ("null", "none", ""):
                continue
            lowv = v.lower()
            if lowv in ("main_channel", "main channel", "main_channels"):
                feats["kw_main_channel"] = True
            elif lowv.startswith("folder:"):
                feats["folder_name"] = v.split(":", 1)[1].strip()
            elif lowv.startswith("folder "):
                feats["folder_name"] = v[7:].strip()
            elif re.fullmatch(r"-?\d{7,}", v) and v not in feats["ids"]:
                feats["ids"].append(v)
            elif re.fullmatch(r"@[\w_]{5,}", v) and v not in feats["usernames"]:
                feats["usernames"].append(v)

    async def ai_decide(self, account_id: str, goal: str, feats: dict,
                        reply_ctx: Optional[ReplyContext], mains: list) -> Optional[dict]:
        cfg = self.accounts.get(account_id)
        rt = self.accounts.runtime.get(account_id)
        folder_titles = []
        try:
            folder_titles = [f["title"] for f in await self.resolver.get_folders(account_id)][:12]
        except Exception:
            folder_titles = []
        active_tasks = [{"kind": t.kind, "status": t.status,
                         "title": (t.params.get("source") or t.params.get("channel") or {}).get("title", t.goal[:28])}
                        for t in self.tasks.active(account_id)][:8]
        active_mons = [{"title": m["title"], "condition": m["condition"], "until": m.get("end_ktm")}
                       for m in self.monitors.active_all(account_id)][:8]
        relevant = [s.name for s in self.registry.search(goal, limit=14)]
        pkg = {
            "goal": goal, "ktm_now": ktm_iso(),
            "account": {"label": cfg["label"], "authorized": bool(rt and rt.authorized)},
            "main_channels": [{"id": c["id"], "title": c.get("title", "")} for c in mains][:10],
            "folder_titles": folder_titles,
            "reply": ({"channel": reply_ctx.entity.brief(), "channel_id": reply_ctx.entity.id,
                       "message_id": reply_ctx.message_id, "text": reply_ctx.text,
                       "has_media": reply_ctx.has_media} if reply_ctx else None),
            "active_tasks": active_tasks, "active_monitors": active_mons,
            "relevant_tools": relevant,
        }
        allowed = sorted({i for s in self.registry.specs.values() for i in s.intents}
                         | self.AI_EXTRA_INTENTS)
        system = (
            "You are DEVIL JARVIS, the understanding+planning brain of a Telegram operations agent. "
            "Understand the goal (English/Hindi/Hinglish/mixed, short or long, follow-up) and output "
            "STRICT JSON ONLY with keys: intent (one of ALLOWED_INTENTS), mode "
            "(READ|PLAN|EXECUTE|STOP|CONFIGURE|ASK), entities {source, targets}, missing [], "
            "confirmation_required bool, reason short string.\n"
            "Rules: pure information/display question -> READ; user says do-not-execute/plan-only/only-plan -> PLAN; "
            "deletion/stop/destructive -> confirmation_required true; insufficient info -> list missing + mode ASK; "
            "never invent channels or ids; 'replied' refers to CONTEXT.reply; folder names come from CONTEXT.folder_titles; "
            "main channel means CONTEXT.main_channels[0].\n"
            "ALLOWED_INTENTS: " + json.dumps(allowed))
        try:
            data, provider = await self.ai.decide(system, json.dumps(pkg, ensure_ascii=False))
        except Exception as exc:
            self.diag.warn("AI_PROVIDER", "decision", type(exc).__name__,
                           error_code=ERR_PROVIDER_UNAVAILABLE)
            return None
        if data is None:
            self.diag.info("AI_PROVIDER", "decision",
                           "no usable provider answer; deterministic NLU continues")
            return None
        valid = self._validate_ai_decision(data, set(allowed))
        if valid is None:
            self.diag.warn("AI_PROVIDER", "validate",
                           "malformed/unsafe AI output ignored",
                           error_code=ERR_AI_PARSE_FAILED)
            return None
        valid["provider"] = provider
        self.diag.info("AI_PROVIDER", "accepted", f"{valid['intent']} via {provider}",
                       account_id=account_id)
        return valid

    # ---------------- engine hooks ----------------
    async def _task_tick(self, task: Task) -> None:
        if task.kind == "cross":
            await self.cross.tick(task)
        elif task.kind == "monitor":
            mon = self.monitors.store.data["monitors"].get(task.params.get("monitor_id", ""))
            if not mon:
                self.tasks.set_status(task, TS_FAILED, "monitor record missing", ERR_TASK_NOT_FOUND)
                return
            if mon.get("end_ts") and utc_now() > mon["end_ts"]:
                mon["status"] = "EXPIRED"
                self.monitors.store.save()
                self.tasks.set_status(task, TS_EXPIRED, "monitor window over")
                try:
                    await self.call_tool("alert_saved_messages", task.account_id,
                                         text=f"MONITOR ENDED [{mon['monitor_id'][-6:]}]\n"
                                              f"{mon['title']} - window over ({mon['hits']} alert(s)).")
                except Exception:
                    pass
                return
            if mon.get("status") == "STOPPED":
                self.tasks.set_status(task, TS_STOPPED, "monitor stopped")

    async def _schedule_execute(self, item: dict) -> ToolResult:
        payload = item.get("payload") or {}
        account_id = item.get("account_id")
        if payload.get("type") == "post_main":
            sent, failed, errs = 0, 0, []
            for ch in self.accounts.get_main_channels(account_id):
                r = await self.call_tool("send_message", account_id, ref=ch["id"],
                                         text=payload.get("text", ""))
                if r.ok:
                    sent += 1
                else:
                    failed += 1
                    errs.append(f"{ch.get('title')}: {r.error_code}")
            return ToolResult(sent > 0 and failed == 0,
                              "SUCCESS" if sent and not failed else "FAILED",
                              {"sent": sent, "failed": failed}, "; ".join(errs[:3]) or None)
        if payload.get("type") == "goal":
            res = await self.handle_goal(account_id, payload.get("text", ""), source="scheduler")
            return ToolResult(res["ok"], res["status"], {"reply": res["reply"]},
                              None if res["ok"] else res["reply"])
        return ToolResult.failure("unknown schedule payload", ERR_INVALID_PARAMETER)

    # ---------------- telegram surface ----------------
    def ensure_handlers(self, account_id: str) -> None:
        if not TELETHON_OK:
            return
        rt = self.accounts.runtime.get(account_id)
        if not rt or not rt.client or not rt.connected or not rt.authorized:
            return
        if self._handler_clients.get(account_id) is rt.client:
            return
        self._handler_clients[account_id] = rt.client

        async def handler(event, aid=account_id):
            await self._on_tg_message(aid, event)

        rt.client.add_event_handler(handler, events.NewMessage())
        self.diag.ok("telegram", "handlers", f"event handlers live for {account_id}",
                     account_id=account_id)

    async def _on_tg_message(self, account_id: str, event: Any) -> None:
        msg = event.message
        if msg is None:
            return
        try:
            rt = self.accounts.runtime.get(account_id)
            text = (msg.raw_text or "").strip()
            me_id = rt.self_id if rt else None
            if msg.out and text and me_id and getattr(msg.peer_id, "user_id", None) == me_id:
                is_cmd = looks_like_command(text)
                is_conf = (self.confirm.matches(text) is not None
                           and self.confirm.pending(account_id) is not None)
                if is_cmd or is_conf:
                    reply_msg = None
                    if msg.is_reply:
                        try:
                            reply_msg = await msg.get_reply_message()
                        except Exception:
                            reply_msg = None
                    asyncio.create_task(self._tg_process(account_id, text, reply_msg))
                    return
            chat_id = msg.chat_id
            if chat_id is None:
                return
            for mon in self.monitors.active_for(account_id, chat_id):
                if int(msg.id) > int(mon.get("last_processed_id") or 0):
                    asyncio.create_task(self._monitor_event(account_id, mon, msg))
            for task in self.cross.active_for(account_id, chat_id):
                if int(msg.id) > int(task.progress.get("cursor") or 0):
                    fresh = self.tasks.get(task.task_id)
                    if fresh:
                        asyncio.create_task(self._cross_event(fresh.task_id, msg))
        except Exception as exc:
            self.diag.err("telegram", "dispatch", type(exc).__name__, account_id=account_id)

    async def _monitor_event(self, account_id: str, mon: dict, msg: Any) -> None:
        mid = mon["monitor_id"]
        try:
            hit = False
            if mon.get("condition") == "unknown":
                if not msg.out:
                    hit = not await self._is_known_sender(account_id, msg.chat_id, msg.sender_id)
            else:
                hit = True
            if hit:
                sender_line = ""
                try:
                    if msg.sender:
                        sender_line = (getattr(msg.sender, "title", None) or
                                       getattr(msg.sender, "first_name", "") or str(msg.sender_id))
                except Exception:
                    sender_line = str(msg.sender_id or "?")
                await self.call_tool("alert_saved_messages", account_id,
                                     text=f"MONITOR ALERT [{mid[-6:]}]\n"
                                          f"{mon['title']} [{mon['channel_id']}]\n"
                                          f"{'Unknown sender' if mon['condition'] == 'unknown' else 'New post'}: "
                                          f"{short(sender_line, 40)}\n"
                                          f"#{msg.id}: {short(msg.raw_text or '[media]', 160)}")
            self.monitors.mark_processed(mid, msg.id, hit)
        except FloodWaitError:
            raise
        except Exception as exc:
            mon["error_count"] = mon.get("error_count", 0) + 1
            mon["last_error"] = type(exc).__name__
            self.monitors.store.save()
            self.diag.err("monitors", "event", type(exc).__name__, account_id=account_id)

    async def _is_known_sender(self, account_id: str, chat_id: int, sender_id: Optional[int]) -> bool:
        if sender_id is None:
            return True
        rt = self.accounts.runtime.get(account_id)
        if rt and rt.self_id == sender_id:
            return True
        key = (account_id, chat_id)
        ts, known = self.admin_cache.get(key, (0, set()))
        if utc_now() - ts > 600:
            ids: set = set()
            try:
                from telethon.tl.types import ChannelParticipantsAdmins
                client = await self.resolver._client(account_id)
                ent = await self.resolver.resolve(account_id, str(chat_id))
                async for p in client.iter_participants(ent.entity, limit=200,
                                                        filter=ChannelParticipantsAdmins()):
                    ids.add(p.id)
            except Exception:
                ids = known or set()
            self.admin_cache[key] = (utc_now(), ids)
            known = ids
        return sender_id in known

    async def _cross_event(self, task_id: str, msg: Any) -> None:
        task = self.tasks.get(task_id)
        if not task or task.status not in TS_ACTIVE_SET:
            return
        try:
            await self.cross.deliver(task, msg)
        except FloodWaitError as fe:
            await asyncio.sleep(fe.seconds)
        except Exception as exc:
            self.diag.err("cross", "event", type(exc).__name__, account_id=task.account_id,
                          task_id=task.task_id)

    async def _tg_process(self, account_id: str, text: str, reply_msg: Any) -> None:
        try:
            res = await self.handle_goal(account_id, text, source="telegram", reply_msg=reply_msg)
            rt = self.accounts.runtime.get(account_id)
            if not rt or not rt.client:
                return
            for chunk in chunk_text(res.get("reply") or "..."):
                try:
                    await rt.client.send_message("me", chunk)
                except FloodWaitError as fe:
                    await asyncio.sleep(fe.seconds)
                    try:
                        await rt.client.send_message("me", chunk)
                    except Exception:
                        pass
                except Exception as exc:
                    self.diag.err("telegram", "respond", type(exc).__name__, account_id=account_id)
                    break
        except Exception as exc:
            self.diag.err("telegram", "process", f"{type(exc).__name__}: {short(str(exc), 120)}",
                          account_id=account_id)

    # ---------------- controlled healing ----------------
    async def run_healing(self, account_id: Optional[str] = None) -> ToolResult:
        self.diag.info("HEALING", "start", "controlled healing begins", account_id=account_id)
        ops: list[dict] = []
        # 1. reload + salvage JSON stores (quarantine already built into JSONStore)
        for store in (self.accounts_store, self.sessions_store, self.brain_store,
                      self.workflows_store, self.tasks_store, self.monitors_store,
                      self.schedules_store, self.memory_store, self.runtime_store,
                      self.tools_store):
            try:
                store.load()
                ops.append({"op": f"json:{store.path.name}", "detail": "reloaded OK"})
            except Exception as exc:
                ops.append({"op": f"json:{store.path.name}", "detail": f"reload failed {type(exc).__name__}"})
        # 2. clear stale context + expired confirmations
        cleared = 0
        brain = self.brain_store.data["brain"]
        for raw in brain.values():
            if utc_now() - raw.get("ts", 0) > CONTEXT_TTL:
                for sec in ("channel", "folder", "task", "monitor", "cross"):
                    raw[sec] = {}
            wf = raw.get("workflow") or {}
            p = wf.get("pending_confirmation")
            if p and utc_now() > p.get("expires_at", 0):
                wf.pop("pending_confirmation", None)
                cleared += 1
        self.brain_store.save()
        ops.append({"op": "context.prune",
                    "detail": f"stale context cleared, {cleared} expired confirmation(s) dropped"})
        # 3. reconcile orphaned monitors/tasks
        fixed_m = fixed_t = 0
        for m in self.monitors.store.data["monitors"].values():
            tid = m.get("task_id")
            if m.get("status") == "ACTIVE" and tid:
                t = self.tasks.get(tid)
                if t is None or t.status in TS_TERMINAL:
                    m["status"] = "STOPPED"
                    fixed_m += 1
        for t in self.tasks.list():
            if t.kind == "monitor" and t.status in TS_ACTIVE_SET:
                m = self.monitors.store.data["monitors"].get(t.params.get("monitor_id", ""))
                if not m or m.get("status") != "ACTIVE":
                    self.tasks.set_status(t, TS_WAITING, "healed: orphaned monitor task",
                                          ERR_TASK_NOT_FOUND)
                    fixed_t += 1
        self.monitors.store.save()
        ops.append({"op": "orphans.reconcile",
                    "detail": f"monitors fixed: {fixed_m}, tasks fixed: {fixed_t}"})
        # 4. refresh caches
        self.resolver._dialog_cache.clear()
        self.resolver._folder_cache.clear()
        ops.append({"op": "cache.refresh", "detail": "dialog + folder caches cleared"})
        # 5. reconnect clients (best-effort, bounded, never blocking web)
        for a in self.accounts.all():
            aid = a["account_id"]
            if account_id and aid != account_id:
                continue
            rt = self.accounts.runtime.get(aid)
            if rt and not rt.connected and self.accounts.load_session(aid):
                try:
                    await asyncio.wait_for(self.accounts.connect(aid), timeout=25)
                    self.ensure_handlers(aid)
                    ops.append({"op": f"reconnect:{a['label']}", "detail": "reconnected"})
                except Exception as exc:
                    ops.append({"op": f"reconnect:{a['label']}",
                                "detail": f"failed: {type(exc).__name__}"})
        # 6. restart eligible runners / mark WAITING where account offline
        resumed = 0
        for t in self.tasks.list():
            if t.status in TS_ACTIVE_SET and t.resumable:
                rt = self.accounts.runtime.get(t.account_id)
                if rt and rt.authorized:
                    self.tasks.start_runner(t)
                    resumed += 1
                else:
                    t.status = TS_WAITING
                    t.last_error = "healed: account offline, waiting for login"
                    self.tasks.save_task(t)
        ops.append({"op": "runners.reconcile", "detail": f"{resumed} runner(s) restarted"})
        self.diag.ok("HEALING", "complete", f"{len(ops)} safe operations applied",
                     account_id=account_id)
        self.diag.persist()
        return ToolResult.success({"ops": ops, "healed_at": iso()},
                                  verification={"operations": len(ops)})

    # ---------------- snapshots ----------------
    def status_snapshot(self) -> dict:
        diag = self.diag.snapshot()
        accounts = []
        for a in self.accounts.all():
            pub = self.accounts.public(a["account_id"])
            pub["memory_aliases"] = len(self.memory.public(a["account_id"])["aliases"])
            pub["known_channels"] = self.memory.public(a["account_id"])["known_channels_count"]
            accounts.append(pub)
        tasks = [t.public() for t in sorted(self.tasks.list(), key=lambda x: -x.updated_at)][:80]
        confirmations = []
        for a in self.accounts.all():
            c = self.confirm.public(a["account_id"])
            if c:
                c["account_id"] = a["account_id"]
                confirmations.append(c)
        persistence = {n: (DATA_DIR / f"{n}.json").exists()
                       for n in ("accounts", "sessions", "brain", "workflows", "tasks",
                                 "monitors", "scheduled_jobs", "channel_memory", "runtime", "tools")}
        return {"ok": True, "time": iso(), "ktm": ktm_iso(),
                "uptime_sec": diag["uptime_sec"], "telethon": TELETHON_OK,
                "ai_available": self.ai_available, "ai": self.ai.status_public(),
                "accounts": accounts, "tasks": tasks,
                "monitors": self.monitors.active_all(),
                "schedules": self.scheduler.pending(),
                "confirmations": confirmations, "diag": diag, "persistence": persistence,
                "tools_summary": {"total": len(self.registry.specs),
                                  "enabled": sum(1 for s in self.registry.specs.values()
                                                 if self.registry.is_enabled(s.name))},
                "limits": {"tasks": MAX_ACTIVE_TASKS, "monitors": MAX_MONITORS,
                           "schedules": MAX_SCHEDULES}}

    # ---------------- lifecycle ----------------
    async def startup(self) -> None:
        self.diag.info("boot", "start", "startup validation running")
        if not TELETHON_OK:
            self.diag.err("boot", "deps", f"telethon missing: {TELETHON_ERR}")
        self.scheduler.start()
        asyncio.create_task(self._restore_accounts())
        self.diag.ok("boot", "complete", f"uptime begins; {len(self.accounts.all())} account(s), "
                                         f"{len(self.registry.specs)} tools registered")
        self.diag.persist()

    async def _restore_accounts(self) -> None:
        for a in self.accounts.all():
            aid = a["account_id"]
            try:
                rt = await self.accounts.connect(aid)
                if rt.authorized:
                    self.ensure_handlers(aid)
                    for t in self.tasks.list(aid):
                        if t.status in TS_ACTIVE_SET and t.resumable:
                            self.tasks.start_runner(t)
                else:
                    for t in self.tasks.list(aid):
                        if t.status in TS_ACTIVE_SET:
                            self.tasks.set_status(t, TS_WAITING,
                                                  "account not authorized at boot - login then retry",
                                                  ERR_NOT_AUTHORIZED)
            except Exception as exc:
                self.diag.err("boot", "account.restore", f"{a['label']}: {type(exc).__name__}",
                              account_id=aid, error_code=ERR_NOT_AUTHORIZED)
                for t in self.tasks.list(aid):
                    if t.status in TS_ACTIVE_SET:
                        self.tasks.set_status(t, TS_WAITING,
                                              f"account offline at boot ({type(exc).__name__})",
                                              ERR_NOT_AUTHORIZED)

    async def shutdown(self) -> None:
        self.diag.info("boot", "shutdown", "graceful stop")
        for t in self.tasks.list():
            if t.status in TS_ACTIVE_SET:
                self.tasks.save_task(t)
        await self.tasks.shutdown()
        for a in self.accounts.all():
            await self.accounts.disconnect(a["account_id"])
        self.diag.persist()


CORE: Optional[JarvisCore] = None


# ----------------------------------------------------------------------------
# 19. WEB API - same brain/state as Telegram + toolbox management
# ----------------------------------------------------------------------------

def build_app() -> "FastAPI":
    @asynccontextmanager
    async def lifespan(_app: "FastAPI"):
        global CORE
        CORE = JarvisCore()
        await CORE.startup()
        yield
        await CORE.shutdown()

    app = FastAPI(title="JARVIS CORE v2", docs_url=None, redoc_url=None, openapi_url=None,
                  lifespan=lifespan)

    async def body(request: "Request") -> dict:
        try:
            data = await request.json()
            return data if isinstance(data, dict) else {}
        except Exception:
            return {}

    def guard() -> Optional["JSONResponse"]:
        if CORE is None:
            return JSONResponse({"ok": False, "error": "core booting"}, status_code=503)
        return None

    @app.get("/")
    async def index() -> "FileResponse":
        return FileResponse(ROOT / "index.html", headers={"Cache-Control": "no-store"})

    @app.get("/healthz")
    async def healthz() -> "JSONResponse":
        return JSONResponse({"ok": True, "up": True, "time": iso()})

    @app.get("/api/status")
    async def api_status() -> "JSONResponse":
        g = guard()
        if g:
            return g
        return JSONResponse(CORE.status_snapshot())

    # ---- goal console ----
    @app.post("/api/goal")
    async def api_goal(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        text = str(b.get("text") or "").strip()
        if not text:
            return JSONResponse({"ok": False, "error": "empty goal"}, status_code=400)
        plan_only = bool(b.get("plan_only"))
        t_low = text.lower()
        wrapped = text if (looks_like_command(text) or t_low in AFFIRM or t_low in DENY) \
            else f"/AI {text}"
        res = await CORE.handle_goal(b.get("account_ref") or b.get("account_id"),
                                     wrapped, source="web", plan_only=plan_only)
        return JSONResponse(res)

    @app.post("/api/goal/execute")
    async def api_goal_execute(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        plan = CORE.pop_plan(str(b.get("plan_id") or ""))
        if not plan:
            return JSONResponse({"ok": False, "status": "FAILED",
                                 "reply": "plan expired or unknown - describe the goal again"})
        if plan.get("confirmation_required"):
            CORE.confirm.require(plan["account_id"], plan["summary"], {"plan": plan})
            res = await CORE.execute_plan(plan, confirmed=True)
        else:
            res = await CORE.execute_plan(plan, confirmed=False)
        return JSONResponse(res)

    # ---- ai / heal / selftest / probes ----
    @app.get("/api/ai")
    async def api_ai() -> "JSONResponse":
        g = guard()
        if g:
            return g
        return JSONResponse({"ok": True, **CORE.ai.status_public()})

    @app.post("/api/heal")
    async def api_heal() -> "JSONResponse":
        g = guard()
        if g:
            return g
        r = await CORE.run_healing(None)
        return JSONResponse(r.to_dict())

    @app.post("/api/selftest")
    async def api_selftest() -> "JSONResponse":
        g = guard()
        if g:
            return g
        out = run_selftest(CORE)
        CORE.diag.info("HEALING", "selftest", f"{out['pass']} passed, {out['fail']} failed")
        return JSONResponse({"ok": out["fail"] == 0, **out})

    @app.get("/api/folders")
    async def api_folders(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        aid = CORE.accounts.resolve_ref(request.query_params.get("aid"))
        if not aid and CORE.accounts.all():
            aid = CORE.accounts.all()[0]["account_id"]
        if not aid:
            return JSONResponse({"ok": False, "error": "no account configured"}, status_code=400)
        r = await CORE.call_tool("list_folders", aid)
        return JSONResponse(r.to_dict())

    @app.post("/api/folders/inspect")
    async def api_folder_inspect(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        aid = CORE.accounts.resolve_ref(str(b.get("aid") or ""))
        if not aid and CORE.accounts.all():
            aid = CORE.accounts.all()[0]["account_id"]
        if not aid:
            return JSONResponse({"ok": False, "error": "no account configured"}, status_code=400)
        r = await CORE.call_tool("inspect_folder", aid, name=str(b.get("name") or ""))
        return JSONResponse(r.to_dict())

    @app.post("/api/channels/latest")
    async def api_channel_latest(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        aid = CORE.accounts.resolve_ref(str(b.get("aid") or ""))
        if not aid and CORE.accounts.all():
            aid = CORE.accounts.all()[0]["account_id"]
        if not aid:
            return JSONResponse({"ok": False, "error": "no account configured"}, status_code=400)
        ref = str(b.get("ref") or "").strip()
        r = await CORE.call_tool("get_latest_message", aid,
                                 ref=(ref or None), use_main_channel=not bool(ref))
        return JSONResponse(r.to_dict())

    @app.post("/api/channels/inspect")
    async def api_channel_inspect(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        aid = CORE.accounts.resolve_ref(str(b.get("aid") or ""))
        if not aid and CORE.accounts.all():
            aid = CORE.accounts.all()[0]["account_id"]
        if not aid or not str(b.get("ref") or "").strip():
            return JSONResponse({"ok": False, "error": "account/ref required"}, status_code=400)
        r = await CORE.call_tool("inspect_channel", aid, ref=str(b.get("ref")).strip())
        return JSONResponse(r.to_dict())

    # ---- toolbox ----
    @app.get("/api/tools")
    async def api_tools() -> "JSONResponse":
        g = guard()
        if g:
            return g
        return JSONResponse({"ok": True, "tools": CORE.registry.list_public(),
                             "intents": sorted({i for s in CORE.registry.specs.values()
                                                for i in s.intents})})

    @app.post("/api/tools/refresh")
    async def api_tools_refresh() -> "JSONResponse":
        g = guard()
        if g:
            return g
        CORE.diag.ok("tools", "refresh", f"{len(CORE.registry.specs)} tools in registry")
        return JSONResponse({"ok": True, "tools": CORE.registry.list_public()})

    @app.post("/api/tools/{name}/toggle")
    async def api_tool_toggle(name: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        ok = CORE.registry.toggle(name, bool(b.get("enabled", True)))
        if not ok:
            return JSONResponse({"ok": False, "error": "unknown tool"}, status_code=404)
        return JSONResponse({"ok": True, "enabled": bool(b.get("enabled", True))})

    @app.post("/api/tools/{name}/test")
    async def api_tool_test(name: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        spec = CORE.registry.get(name)
        if not spec:
            return JSONResponse({"ok": False, "error": "unknown tool"}, status_code=404)
        if spec.destructive or not spec.read_only or spec.test is None:
            return JSONResponse({"ok": False, "error":
                                 "this tool is not safe to test from web (read-only tools only)"},
                                status_code=400)
        accs = CORE.accounts.all()
        if not accs:
            return JSONResponse({"ok": False, "error": "no account configured yet"}, status_code=400)
        r = await CORE.call_tool(name, accs[0]["account_id"], **spec.test)
        return JSONResponse(r.to_dict())

    # ---- accounts ----
    @app.post("/api/accounts")
    async def api_account_create(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        try:
            cfg = CORE.accounts.create(str(b.get("label") or "").strip() or None,
                                       str(b.get("api_id") or ""), str(b.get("api_hash") or ""))
        except ValidationError as ve:
            return JSONResponse({"ok": False, "error": "; ".join(ve.missing)}, status_code=400)
        return JSONResponse({"ok": True, "account": CORE.accounts.public(cfg["account_id"])})

    @app.post("/api/accounts/{aid}/login/start")
    async def api_login_start(aid: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        try:
            r = await CORE.accounts.start_login(aid, str(b.get("phone") or ""))
            CORE.ensure_handlers(aid)
            return JSONResponse({"ok": True, **r})
        except Exception as exc:
            name = type(exc).__name__
            msg = "; ".join(exc.missing) if isinstance(exc, ValidationError) else name
            return JSONResponse({"ok": False, "error": msg}, status_code=400)

    @app.post("/api/accounts/{aid}/login/complete")
    async def api_login_complete(aid: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        try:
            r = await CORE.accounts.complete_login(aid, str(b.get("code") or ""),
                                                   str(b.get("password") or ""))
            CORE.ensure_handlers(aid)
            return JSONResponse({"ok": bool(r.get("ok")), **r})
        except Exception as exc:
            msg = "; ".join(exc.missing) if isinstance(exc, ValidationError) else type(exc).__name__
            return JSONResponse({"ok": False, "error": msg}, status_code=400)

    @app.post("/api/accounts/{aid}/session")
    async def api_session_import(aid: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        try:
            r = await CORE.accounts.import_session(aid, str(b.get("session_string") or ""))
            CORE.ensure_handlers(aid)
            return JSONResponse({"ok": True, **r})
        except Exception as exc:
            msg = "; ".join(exc.missing) if isinstance(exc, ValidationError) else type(exc).__name__
            return JSONResponse({"ok": False, "error": msg}, status_code=400)

    @app.post("/api/accounts/{aid}/connect")
    async def api_connect(aid: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        try:
            rt = await CORE.accounts.connect(aid)
            CORE.ensure_handlers(aid)
            return JSONResponse({"ok": True, "authorized": rt.authorized, "connected": rt.connected})
        except Exception as exc:
            msg = "; ".join(exc.missing) if isinstance(exc, ValidationError) else type(exc).__name__
            return JSONResponse({"ok": False, "error": msg}, status_code=400)

    @app.post("/api/accounts/{aid}/disconnect")
    async def api_disconnect(aid: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        await CORE.accounts.disconnect(aid)
        return JSONResponse({"ok": True})

    @app.delete("/api/accounts/{aid}")
    async def api_delete_account(aid: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        CORE.accounts.delete(aid)
        return JSONResponse({"ok": True})

    @app.post("/api/accounts/{aid}/config")
    async def api_config(aid: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        refs = b.get("main_channels")
        if not isinstance(refs, list):
            return JSONResponse({"ok": False, "error": "main_channels must be a list"},
                                status_code=400)
        out, notes = [], []
        for ref in refs[:MAX_TARGETS]:
            try:
                ent = await CORE.resolver.resolve(aid, str(ref).strip())
                out.append({"id": ent.id, "title": ent.title, "username": ent.username,
                            "added_at": iso(), "via": "web"})
                CORE.memory.learn_channel(aid, str(ent.id), ent.title, ent.username)
            except Exception as exc:
                notes.append(f"{ref}: {short(str(exc), 70)}")
        CORE.accounts.set_main_channels(aid, out)
        return JSONResponse({"ok": True, "main_channels": out, "notes": notes})

    # ---- registries control ----
    @app.post("/api/tasks/{tid}/action")
    async def api_task_action(tid: str, request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        task = CORE.tasks.get(tid)
        if not task:
            return JSONResponse({"ok": False, "error": "task not found"}, status_code=404)
        accs = CORE.accounts.all()
        r = await CORE.impl._task_action(task.account_id, task.task_id,
                                         str(b.get("action") or ""))
        return JSONResponse(r.to_dict())

    @app.post("/api/monitors/{mid}/stop")
    async def api_monitor_stop(mid: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        return JSONResponse({"ok": CORE.monitors.stop(mid)})

    @app.post("/api/schedules/{sid}/cancel")
    async def api_schedule_cancel(sid: str) -> "JSONResponse":
        g = guard()
        if g:
            return g
        return JSONResponse({"ok": CORE.scheduler.cancel(sid)})

    @app.post("/api/confirm")
    async def api_confirm(request: "Request") -> "JSONResponse":
        g = guard()
        if g:
            return g
        b = await body(request)
        answer = "yes" if b.get("answer") in (True, "yes", "YES", "haan") else "no"
        res = await CORE.handle_goal(b.get("account_id"), answer, source="web")
        return JSONResponse(res)

    return app


app = build_app() if WEB_OK else None


# ----------------------------------------------------------------------------
# 20. ENTRYPOINT (Render: 0.0.0.0 + PORT)
# ----------------------------------------------------------------------------

# ----------------------------------------------------------------------------
# 21. OFFLINE SELFTEST - python main.py selftest | POST /api/selftest
# ----------------------------------------------------------------------------

def run_selftest(core: Optional["JarvisCore"]) -> dict:
    results: list[dict] = []

    def check(name: str, ok: bool, detail: str = "") -> None:
        results.append({"name": name, "pass": bool(ok), "detail": short(str(detail), 200)})

    try:
        compile((ROOT / "main.py").read_text(encoding="utf-8"), "main.py", "exec")
        check("SYNTAX", True)
    except Exception as exc:
        check("SYNTAX", False, f"{type(exc).__name__}: {exc}")

    try:
        import fastapi as _f, uvicorn as _u, httpx as _h  # noqa: F401
        check("IMPORTS", TELETHON_OK, "ok" if TELETHON_OK else TELETHON_ERR)
    except Exception as exc:
        check("IMPORTS", False, type(exc).__name__)

    if core is not None:
        try:
            bad = [s.name for s in core.registry.specs.values()
                   if s.handler is None or not s.intents or not s.description]
            n = len(core.registry.specs)
            check("TOOL REGISTRY", not bad and n >= 40,
                  f"{n} tools, intents wired" + (f"; INVALID: {bad}" if bad else ""))
        except Exception as exc:
            check("TOOL REGISTRY", False, type(exc).__name__)
    else:
        check("TOOL REGISTRY", False, "no core")

    try:
        cases = {"for 1 hour": 3600, "30 minutes": 1800, "2 ghante": 7200, "5 minute": 300}
        ok = all(parse_time_spec(k).get("sec") == v for k, v in cases.items())
        u10 = parse_time_spec("until 10 PM")
        ok = ok and u10.get("kind") == "at" and datetime.fromtimestamp(u10["ts"], tz=KTM).hour == 22
        k7 = parse_time_spec("kal subah 7 baje")
        ok = ok and k7.get("kind") == "at" and datetime.fromtimestamp(k7["ts"], tz=KTM).hour == 7
        r10 = parse_time_spec("raat 10 baje")
        ok = ok and r10.get("kind") == "at" and datetime.fromtimestamp(r10["ts"], tz=KTM).hour == 22
        check("NL TIME (KTM)", ok)
    except Exception as exc:
        check("NL TIME (KTM)", False, type(exc).__name__)

    try:
        plan_phrases = ["do not execute", "abhi execute mat karo", "plan only",
                        "kuch change mat karo", "plan banao, execute mat karna", "read only"]
        ok = all(detect_mode(p) == "PLAN" for p in plan_phrases)
        ok = ok and detect_mode("start cross") is None and detect_mode("monitor karo") is None
        check("MODE DETECTION", ok)
    except Exception as exc:
        check("MODE DETECTION", False, type(exc).__name__)

    nlu = NLU()
    regressions = [
        ("Show my configured Main Channel.", False, {"MAIN_CHANNEL_LIST"}),
        ("Show the latest post from my Main Channel. Do not modify anything.", False, {"LATEST_MESSAGE"}),
        ("Forward the latest post from my Main Channel to Saved Messages.", False, {"FORWARD_LATEST_SAVED"}),
        ("Stop monitoring my Main Channel.", False, {"MONITOR_STOP"}),
        ("List every channel in RAN X CROXX.", False, {"LIST_CHANNELS", "FOLDER_CHANNELS"}),
        ("Identify the exact channel and message ID of the message I replied to.", True, {"IDENTIFY_REPLY"}),
        ("Create a Cross plan using my replied message as source and RAN X CROXX as targets for 1 hour. Do not execute.", True, {"CROSS_PLAN"}),
        ("Start Cross.", False, {"CROSS_START"}),
        ("Delete the latest post from my Main Channel.", False, {"DELETE_MESSAGES"}),
        ("List all currently running tasks and monitors.", False, {"TASK_LIST"}),
        ("Show safe information about my Telegram account.", False, {"ACCOUNT_INFO"}),
        ("Main channel ko watch karo, unknown sender aaye to Saved Messages me alert karo.", False, {"MONITOR_START"}),
        ("Main channel ko watch karo. Main sone ja raha hoon. Dhyan rakhna.", False, {"MONITOR_START"}),
        ("RAN X CROXX folder inspect karo aur channels ki list do.", False, {"FOLDER_CHANNELS", "INSPECT_FOLDER"}),
        ("Replied message ko source rakho aur RAN X CROXX folder ko target rakho.", True, {"CROSS_PLAN", "FOLDER_TO_MAIN"}),
        ("me sona ja rha hu thk chanel dhyn rkhna", False, {"MONITOR_START"}),
        ("Stop all running monitors.", False, {"MONITOR_STOP", "TASK_CONTROL"}),
    ]
    fails = []
    for text, has_reply, expects in regressions:
        try:
            feats = nlu.features("acc_selftest", text, has_reply, 1)
            got = nlu.classify(feats).intent
            if got not in expects:
                fails.append(f"'{short(text, 36)}' -> {got} (want {sorted(expects)})")
        except Exception as exc:
            fails.append(f"'{short(text, 28)}' err {type(exc).__name__}")
    check("NLU REGRESSIONS (17)", not fails,
          "; ".join(fails[:6]) if fails else f"{len(regressions)}/{len(regressions)} mapped")

    if core is not None:
        try:
            allowed = {i for s in core.registry.specs.values() for i in s.intents} | core.AI_EXTRA_INTENTS
            bad1 = core._validate_ai_decision({"intent": "INVENTED_INTENT"}, allowed)
            bad2 = core._validate_ai_decision("garbage", allowed)
            good = core._validate_ai_decision({"intent": "LATEST_MESSAGE", "mode": "READ",
                                               "entities": {"source": "main_channel"},
                                               "missing": [], "confirmation_required": False}, allowed)
            check("AI OUTPUT VALIDATOR", bad1 is None and bad2 is None and bool(good))
        except Exception as exc:
            check("AI OUTPUT VALIDATOR", False, type(exc).__name__)

    try:
        tmp = DATA_DIR / "_selftest_tmp.json"
        JSONStore(tmp, "x")
        tmp.write_text("{corrupt :", encoding="utf-8")
        st = JSONStore(tmp, "x")
        ok = isinstance(st.data, dict) and "x" in st.data
        for f in DATA_DIR.glob("_selftest_tmp*"):
            try:
                f.unlink()
            except Exception:
                pass
        check("JSON CORRUPTION RECOVERY", ok)
    except Exception as exc:
        check("JSON CORRUPTION RECOVERY", False, type(exc).__name__)

    try:
        tmpstore = JSONStore(DATA_DIR / "_selftest_brain.json", "brain")
        ctx2 = BrainContext(tmpstore)
        cf = ConfirmationEngine(ctx2, Diagnostics(tmpstore))
        cf.require("acc_t", "test-op", {"plan": {}})
        ok = cf.pending("acc_t") is not None and cf.matches("yes") is True
        consumed = cf.consume("acc_t")
        ok = ok and bool(consumed) and consumed.get("desc") == "test-op"
        ok = ok and cf.consume("acc_t") is None
        cf.require("acc_t", "test-op-2", {"plan": {}})
        wf = ctx2.get("acc_t", "workflow") or {}
        if isinstance(wf.get("pending_confirmation"), dict):
            wf["pending_confirmation"]["expires_at"] = utc_now() - 1
            tmpstore.save()
        ok = ok and cf.pending("acc_t") is None
        (DATA_DIR / "_selftest_brain.json").unlink(missing_ok=True)
        check("CONFIRMATION (single-use + expiry)", ok)
    except Exception as exc:
        check("CONFIRMATION", False, type(exc).__name__)

    try:
        sample = "me sona ja rha hu thk chanel dhyn rkhna"
        n, sk = norm_text(sample), skeleton(sample)
        ok = has_kw(n, sk, KW["watch"]) and has_kw(n, sk, KW["sleep_away"]) \
            and bool(re.search(r"\b(channel|chanel|chennal|group|chat)\b", sample))
        check("FUZZY NLU (typos)", ok)
    except Exception as exc:
        check("FUZZY NLU", False, type(exc).__name__)

    try:
        check("FOLDER NAME EXTRACTION",
              extract_folder_name("RAN X CROXX folder ko inspect karo") == "ran x croxx",
              extract_folder_name("RAN X CROXX folder ko inspect karo") or "none")
    except Exception as exc:
        check("FOLDER NAME EXTRACTION", False, type(exc).__name__)

    missing = [n for n in ("accounts", "sessions", "brain", "workflows", "tasks", "monitors",
                           "scheduled_jobs", "channel_memory", "runtime", "tools")
               if not (DATA_DIR / f"{n}.json").exists()]
    check("PERSISTENCE FILES", not missing, f"missing: {missing}" if missing else "all present")

    if core is not None:
        try:
            st = core.ai.status_public()
            conf = [p["name"] for p in st["providers"] if p["configured"]]
            notc = [p["name"] for p in st["providers"] if not p["configured"]]
            check("AI PROVIDERS STATUS", True,
                  f"configured: {conf or 'NONE'} | NOT CONFIGURED: {notc}")
        except Exception as exc:
            check("AI PROVIDERS STATUS", False, type(exc).__name__)

    passed = sum(1 for r in results if r["pass"])
    return {"pass": passed, "fail": len(results) - passed,
            "total": len(results), "results": results}


# ----------------------------------------------------------------------------
# 22. ENTRYPOINT (Render: 0.0.0.0 + PORT)
# ----------------------------------------------------------------------------

def banner() -> None:
    print("=" * 66)
    print(" JARVIS CORE v2 - goal-driven mini brain + telegram toolbox")
    print("=" * 66)
    print(f" bind        : 0.0.0.0:{PORT}  (PORT env: {'set -> ' + os.environ['PORT'] if os.environ.get('PORT') else 'not set, using fallback 8090'})")
    print(f" data dir    : {DATA_DIR}")
    print(f" telethon    : {'ok' if TELETHON_OK else 'MISSING - ' + TELETHON_ERR}")
    print(f" ai provider : {'configured (' + OPENAI_MODEL + ')' if OPENAI_API_KEY else 'not configured (deterministic NLU)'}")
    print(f" api creds   : {'env set' if (ENV_API_ID and ENV_API_HASH) else 'configure later in Web UI (web starts anyway)'}")
    print("=" * 66)


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1].lower() == "selftest":
        _core = JarvisCore()
        out = run_selftest(_core)
        print("=" * 66)
        print(" JARVIS OFFLINE SELFTEST")
        print("=" * 66)
        for r in out["results"]:
            line = f" [{'PASS' if r['pass'] else 'FAIL'}] {r['name']}"
            if r["detail"]:
                line += f" - {r['detail']}"
            print(line)
        print("-" * 66)
        print(f" RESULT: {out['pass']} passed, {out['fail']} failed of {out['total']}")
        sys.exit(0 if out["fail"] == 0 else 1)
    banner()
    if not WEB_OK:
        print("FATAL: fastapi/uvicorn/httpx missing. pip install -r requirements.txt")
        sys.exit(1)
    print(f" STARTING HTTP SERVER on 0.0.0.0:{PORT} ...", flush=True)
    try:
        uvicorn.run(app, host=HOST, port=PORT, log_level="info", proxy_headers=True)
    except Exception as exc:
        print(f"FATAL: http server failed to start: {type(exc).__name__}: {exc}")
        sys.exit(1)

