import imaplib
import smtplib
import email
import os
import re
import sys
import json
import base64
import time
import threading
import queue
import mimetypes
import webbrowser
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog, simpledialog
from contextlib import contextmanager
from email.header import decode_header, make_header, Header
from email.mime.text import MIMEText
from email.mime.base import MIMEBase
from email.mime.multipart import MIMEMultipart
from email.utils import parseaddr, formataddr, getaddresses
from email import encoders
from html.parser import HTMLParser
from datetime import datetime

IMAP_HOST, IMAP_PORT = "imap.163.com", 993
SMTP_HOST, SMTP_PORT = "smtp.163.com", 465
TIMEOUT = 20
PAGE_SIZE = 20

CFG_NAME = "163pbgui.cfg"          # 缓存文件名
CFG_HIDDEN_ATTR = 0x02             # Windows FILE_ATTRIBUTE_HIDDEN

imaplib.Commands["ID"] = ("AUTH",)
URL_RE = re.compile(r"(?:https?://|mailto:)[^\s<>\"']+")
URL_TAIL = ".,;:!?)]}'\"，。；：！？）】》"

ROLE_LABELS = {
    "inbox": "收件箱",
    "sent": "已发送",
    "drafts": "草稿箱",
    "trash": "垃圾箱",
    "junk": "垃圾邮件",
}

# ---------- 彩蛋常量 ----------
EASTER_EGG_163 = (
    "  █   █████ █████\n"
    " ██   █         █\n"
    "  █   █████ █████\n"
    "  █   █   █     █\n"
    "█████ █████ █████"
)
KONAMI_SEQ = "<Up><Up><Down><Down><Left><Right><Left><Right>BA"
EASTER_KEY_TIMEOUT = 5.0
EASTER_KEY_BUFFER_MAX = 40


# ===================== 编码与工具 =====================
def imap_utf7_encode(text: str) -> str:
    result, buf = [], []

    def flush():
        if not buf:
            return
        b = "".join(buf).encode("utf-16-be")
        enc = base64.b64encode(b).decode().rstrip("=").replace("/", ",")
        result.append(f"&{enc}-")
        buf.clear()

    for ch in text:
        if 0x20 <= ord(ch) <= 0x7E:
            flush()
            result.append("&" if ch == "&" else ch)
        else:
            buf.append(ch)
    flush()
    return "".join(result)


def imap_utf7_decode(encoded: str) -> str:
    result, i = [], 0
    while i < len(encoded):
        ch = encoded[i]
        if ch != "&":
            result.append(ch)
            i += 1
            continue
        j = encoded.find("-", i)
        if j == -1:
            result.append("&")
            break
        part = encoded[i + 1:j]
        if not part:
            result.append("&")
        else:
            b64 = part.replace(",", "/")
            b64 += "=" * (-len(b64) % 4)
            try:
                result.append(base64.b64decode(b64).decode("utf-16-be"))
            except Exception:
                result.append(f"&{part}-")
        i = j + 1
    return "".join(result)


def clean_url(url: str) -> str:
    return url.rstrip(URL_TAIL)


def decode_mime_header(header_value):
    if not header_value:
        return ""
    try:
        return str(make_header(decode_header(header_value)))
    except Exception:
        out = []
        for content, charset in decode_header(header_value):
            if isinstance(content, bytes):
                out.append(content.decode(charset or "utf-8", errors="replace"))
            else:
                out.append(str(content))
        return "".join(out)


def parse_people(field_value):
    pairs = getaddresses([field_value or ""])
    return ", ".join(decode_mime_header(n) or a for n, a in pairs if a or n)


def human_size(n):
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} TB"


# ===================== HTML / MIME 解析 =====================
class _HTMLTextExtractor(HTMLParser):
    SKIP = {"script", "style"}
    BREAK = {"br", "p", "div", "li", "tr", "h1", "h2", "h3", "h4"}

    def __init__(self):
        super().__init__(convert_charrefs=True)
        self._skip = 0
        self._parts = []
        self._href = None
        self._anchor_text = []

    def handle_starttag(self, tag, attrs):
        if tag in self.SKIP:
            self._skip += 1
        elif tag == "a":
            href = dict(attrs).get("href")
            if href:
                self._href = href.strip()
                self._anchor_text = []
        elif tag in self.BREAK:
            self._parts.append("\n")

    def handle_endtag(self, tag):
        if tag in self.SKIP:
            if self._skip:
                self._skip -= 1
        elif tag == "a" and self._href is not None:
            text = "".join(self._anchor_text).strip()
            href = self._href
            self._parts.append(f"{text} <{href}>" if text and text != href else f"<{href}>")
            self._href = None
            self._anchor_text = []

    def handle_data(self, data):
        if self._skip:
            return
        if self._href is not None:
            self._anchor_text.append(data)
        else:
            self._parts.append(data)

    def get_text(self):
        text = "".join(self._parts)
        text = re.sub(r"[ \t]+\n", "\n", text)
        return re.sub(r"\n\s*\n+", "\n\n", text).strip()


def html_to_text(html):
    parser = _HTMLTextExtractor()
    try:
        parser.feed(html)
        return parser.get_text()
    except Exception:
        return re.sub(r"<[^>]+>", "", html).strip()


def _decode_payload(part):
    payload = part.get_payload(decode=True)
    if not payload:
        return ""
    charset = part.get_content_charset() or "utf-8"
    try:
        return payload.decode(charset, errors="replace")
    except LookupError:
        return payload.decode("utf-8", errors="replace")


def extract_parts(msg):
    if not msg.is_multipart():
        return _decode_payload(msg), []

    body_text, attachments = "", []
    html_part = None
    for part in msg.walk():
        ctype = part.get_content_type()
        cdisp = str(part.get("Content-Disposition") or "")
        filename = part.get_filename()
        if filename:
            filename = decode_mime_header(filename)

        if "attachment" in cdisp or (filename and ctype not in ("text/plain", "text/html")):
            data = part.get_payload(decode=True)
            if data:
                attachments.append((filename or "attachment.bin", data))
        elif ctype == "text/plain" and not body_text:
            body_text = _decode_payload(part)
        elif ctype == "text/html" and html_part is None:
            html_part = part

    if not body_text and html_part is not None:
        body_text = html_to_text(_decode_payload(html_part))
    return body_text, attachments


# ===================== IMAP 连接 =====================
def imap_login(email_addr, password):
    mail = imaplib.IMAP4_SSL(IMAP_HOST, IMAP_PORT, timeout=TIMEOUT)
    mail.login(email_addr, password)
    try:
        typ, dat = mail._simple_command(
            "ID", '("name" "163postboxGUI" "version" "1.0" "vendor" "EJIAOFEN")')
        mail._untagged_response(typ, dat, "ID")
    except Exception:
        pass
    return mail


@contextmanager
def imap_session(email_addr, password):
    mail = imap_login(email_addr, password)
    try:
        yield mail
    finally:
        try:
            mail.logout()
        except Exception:
            pass


def detect_special_folders(mail):
    result = {"inbox": "INBOX", "sent": None, "drafts": None, "trash": None, "junk": None}
    typ, lines = mail.list()
    if typ != "OK":
        return result
    for line in lines:
        if not isinstance(line, bytes):
            continue
        m = re.search(r'\(([^)]*)\)\s+"[^"]*"\s+(.+)$',
                      line.decode("utf-8", errors="replace"))
        if not m:
            continue
        attrs = m.group(1).upper()
        raw = m.group(2).strip().strip('"')
        decoded = imap_utf7_decode(raw)
        low = decoded.lower()

        if not result["sent"] and ("\\SENT" in attrs or "已发送" in decoded or low == "sent"):
            result["sent"] = raw
        elif not result["drafts"] and ("\\DRAFTS" in attrs or "草稿" in decoded or "draft" in low):
            result["drafts"] = raw
        elif not result["trash"] and ("\\TRASH" in attrs or "已删除" in decoded
                                      or "trash" in low or "deleted" in low):
            result["trash"] = raw
        elif not result["junk"] and ("\\JUNK" in attrs or "垃圾" in decoded
                                     or "junk" in low or "spam" in low):
            result["junk"] = raw
    return result


def list_folders(mail):
    typ, lines = mail.list()
    if typ != "OK":
        return []
    folders = []
    for line in lines:
        if not isinstance(line, bytes):
            continue
        m = re.search(r'\(([^)]*)\)\s+"[^"]*"\s+(.+)$',
                      line.decode("utf-8", errors="replace"))
        if m:
            folders.append(m.group(2).strip().strip('"'))
    return folders


# ===================== 主应用 =====================
class MailApp:
    def __init__(self, root):
        self.root = root
        self.root.title("163 PostBox GUI")
        self.root.geometry("1200x860")

        self.task_queue = queue.Queue()
        self.mail_cache = {}
        self.special_folders = {}
        self.current_folder = "INBOX"
        self.current_page = 0
        self.total_pages = 0
        self._loading = False
        self.pending_attachments = []
        self._busy_buttons = {}

        # 彩蛋缓冲
        self._key_buffer = []
        self._last_key_time = 0.0

        self.contacts_path = os.path.join(os.path.expanduser("~"), ".mail163_contacts.json")
        self.contacts = self._load_contacts()

        self._build_ui()
        self._load_cfg_to_ui()
        self._setup_easter_eggs()
        self._poll_queue()

        # 关闭窗口时保存凭据
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

    # ---------- 配置持久化 ----------
    def _cfg_path(self):
        """打包后 cfg 在 exe 同级；源码运行时在脚本同级；均无写权限则回退到用户目录"""
        if getattr(sys, "frozen", False):
            # PyInstaller 打包后，sys.executable 指向 exe 本体
            base = os.path.dirname(os.path.abspath(sys.executable))
        else:
            base = os.path.dirname(os.path.abspath(__file__))

        primary = os.path.join(base, CFG_NAME)

        # 放在 Program Files 等受保护目录时无写权限，回退到用户目录
        try:
            probe = primary + ".probe"
            with open(probe, "w") as f:
                f.write("")
            os.remove(probe)
            return primary
        except OSError:
            return os.path.join(os.path.expanduser("~"), "." + CFG_NAME)

    def _load_cfg_to_ui(self):
        """启动时把上次的邮箱和授权码填回输入框"""
        path = self._cfg_path()
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            self.email_var.set(data.get("email", ""))
            self.password_var.set(data.get("password", ""))
        except Exception:
            pass  # 首次运行或文件损坏，静默忽略

    def _save_cfg(self):
        """保存：两个字段都非空→写入并隐藏；都为空→删除文件；其余→不动"""
        path = self._cfg_path()
        email_addr = self.email_var.get().strip()
        password = self.password_var.get().strip()

        if not email_addr and not password:
            try:
                if os.path.exists(path):
                    os.remove(path)
            except Exception:
                pass
            return

        if not email_addr or not password:
            return

        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump({"email": email_addr, "password": password},
                          f, ensure_ascii=False, indent=2)
        except Exception:
            return

        if os.name == "nt":
            try:
                import ctypes
                ctypes.windll.kernel32.SetFileAttributesW(path, CFG_HIDDEN_ATTR)
            except Exception:
                pass

    def _on_close(self):
        self._save_cfg()
        self.root.destroy()

    # ---------- 联系人持久化 ----------
    def _load_contacts(self):
        try:
            with open(self.contacts_path, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return []

    def _save_contacts(self):
        try:
            with open(self.contacts_path, "w", encoding="utf-8") as f:
                json.dump(self.contacts, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    # ===================== 彩蛋 =====================
    def _setup_easter_eggs(self):
        self.root.bind_all("<Key>", self._on_global_key, add="+")

    def _on_global_key(self, event):
        now = time.time()
        if now - self._last_key_time > EASTER_KEY_TIMEOUT:
            self._key_buffer.clear()
        self._last_key_time = now

        keysym = event.keysym
        if keysym in ("Up", "Down", "Left", "Right"):
            self._key_buffer.append(f"<{keysym}>")
        elif event.char and len(event.char) == 1 and event.char.isprintable():
            self._key_buffer.append(event.char)
        else:
            return

        if len(self._key_buffer) > EASTER_KEY_BUFFER_MAX:
            del self._key_buffer[:len(self._key_buffer) - EASTER_KEY_BUFFER_MAX]

        seq = "".join(self._key_buffer)

        if seq.endswith("163163163"):
            self._key_buffer.clear()
            self._show_163_art()
            return

        if seq.upper().endswith(KONAMI_SEQ.upper()):
            self._key_buffer.clear()
            self._show_ejiaofen()

    def _show_163_art(self):
        self._show_popup("163", EASTER_EGG_163, font=("Courier New", 14, "bold"))

    def _show_ejiaofen(self):
        self._show_popup("By EJIAOFEN", "https://github.com/EJIAOFEN/163postboxGUI",
                         font=("", 18, "bold"))

    def _show_popup(self, title, text, font=None):
        win = tk.Toplevel(self.root)
        win.title(title)
        win.transient(self.root)
        win.resizable(False, False)

        frame = ttk.Frame(win, padding=24)
        frame.pack(fill="both", expand=True)
        tk.Label(frame, text=text, font=font or ("", 12),
                 justify="left").pack(pady=8)
        ttk.Button(frame, text="好", command=win.destroy).pack(pady=(12, 0))

        win.update_idletasks()
        w, h = win.winfo_width(), win.winfo_height()
        x = (win.winfo_screenwidth() - w) // 2
        y = (win.winfo_screenheight() - h) // 2
        win.geometry(f"+{x}+{y}")
        win.focus_force()

    # ===================== 通用辅助 =====================
    def _require_login(self):
        email_addr = self.email_var.get().strip()
        password = self.password_var.get().strip()
        if not email_addr or not password:
            messagebox.showwarning("提示", "请先填写邮箱地址和授权码。")
            return None
        return email_addr, password

    def _set_button_busy(self, btn, text=None):
        if btn is None:
            return
        if btn not in self._busy_buttons:
            self._busy_buttons[btn] = btn.cget("text")
        if text:
            btn.config(text=text)
        btn.config(state="disabled")

    def _restore_button(self, btn):
        if btn is None or btn not in self._busy_buttons:
            return
        try:
            btn.config(text=self._busy_buttons.pop(btn), state="normal")
        except Exception:
            self._busy_buttons.pop(btn, None)

    def _restore_all_buttons(self):
        for btn, text in list(self._busy_buttons.items()):
            try:
                btn.config(text=text, state="normal")
            except Exception:
                pass
        self._busy_buttons.clear()

    def _run_async(self, work, btn=None, busy_text=None, status=None, err_prefix="操作失败"):
        if btn is not None:
            self._set_button_busy(btn, busy_text)
        if status:
            self.status_var.set(status)

        def runner():
            try:
                work()
            except Exception as exc:
                self.task_queue.put(("error", f"{err_prefix}：\n{exc}"))

        threading.Thread(target=runner, daemon=True).start()

    # ===================== UI =====================
    def _build_ui(self):
        self._build_account_bar()
        self._build_notebook()

    def _build_account_bar(self):
        bar = ttk.Frame(self.root, padding=8)
        bar.pack(fill="x")

        ttk.Label(bar, text="邮箱：").pack(side="left")
        self.email_var = tk.StringVar()
        ttk.Entry(bar, textvariable=self.email_var, width=26).pack(side="left", padx=(0, 10))

        ttk.Label(bar, text="授权码：").pack(side="left")
        self.password_var = tk.StringVar()
        ttk.Entry(bar, textvariable=self.password_var, width=22, show="*").pack(side="left", padx=(0, 10))

        self.test_btn = ttk.Button(bar, text="测试连接", command=self.test_connection)
        self.test_btn.pack(side="left", padx=3)
        self.login_btn = ttk.Button(bar, text="登录 / 刷新文件夹", command=self.login_and_refresh)
        self.login_btn.pack(side="left", padx=3)

        self.status_var = tk.StringVar(value="就绪")
        ttk.Label(bar, textvariable=self.status_var, foreground="#666").pack(side="right", padx=8)

    def _build_notebook(self):
        self.notebook = ttk.Notebook(self.root)
        self.notebook.pack(fill="both", expand=True, padx=6, pady=(0, 6))

        self.mail_tab = ttk.Frame(self.notebook)
        self.compose_tab = ttk.Frame(self.notebook)
        self.contacts_tab = ttk.Frame(self.notebook)
        self.notebook.add(self.mail_tab, text="邮件")
        self.notebook.add(self.compose_tab, text="写邮件")
        self.notebook.add(self.contacts_tab, text="联系人")

        self._build_mail_tab()
        self._build_compose_tab()
        self._build_contacts_tab()

    # ---------- 邮件标签页 ----------
    def _build_mail_tab(self):
        paned = ttk.PanedWindow(self.mail_tab, orient="horizontal")
        paned.pack(fill="both", expand=True)

        left = ttk.Frame(paned, width=200)
        paned.add(left, weight=0)
        ttk.Label(left, text="文件夹", font=("", 10, "bold")).pack(anchor="w", padx=6, pady=(6, 2))
        self.folder_tree = ttk.Treeview(left, show="tree", selectmode="browse")
        self.folder_tree.pack(fill="both", expand=True, padx=4, pady=4)
        self.folder_tree.bind("<<TreeviewSelect>>", self._on_folder_select)

        for label, cmd in [
            ("新建文件夹", self.create_folder),
            ("重命名选中文件夹", self.rename_folder),
            ("删除选中文件夹", self.delete_folder),
        ]:
            ttk.Button(left, text=label, command=cmd).pack(fill="x", padx=4, pady=2)

        right = ttk.Frame(paned)
        paned.add(right, weight=1)

        toolbar = ttk.Frame(right)
        toolbar.pack(fill="x", padx=4, pady=4)

        self.refresh_btn = ttk.Button(toolbar, text="刷新",
                                      command=lambda: self.load_folder(self.current_folder))
        self.refresh_btn.pack(side="left", padx=2)
        self.prev_btn = ttk.Button(toolbar, text="上一页", command=self.prev_page)
        self.prev_btn.pack(side="left", padx=2)
        self.next_btn = ttk.Button(toolbar, text="下一页", command=self.next_page)
        self.next_btn.pack(side="left", padx=2)
        self.page_label = ttk.Label(toolbar, text="第 0 / 0 页")
        self.page_label.pack(side="left", padx=8)

        ttk.Label(toolbar, text="搜索：").pack(side="left", padx=(16, 2))
        self.search_var = tk.StringVar()
        search_entry = ttk.Entry(toolbar, textvariable=self.search_var, width=24)
        search_entry.pack(side="left")
        search_entry.bind("<Return>", lambda e: self.search_mail())

        ttk.Button(toolbar, text="搜索", command=self.search_mail).pack(side="left", padx=3)
        ttk.Button(toolbar, text="清除搜索",
                   command=lambda: self.load_folder(self.current_folder)).pack(side="left", padx=2)

        vpaned = ttk.PanedWindow(right, orient="vertical")
        vpaned.pack(fill="both", expand=True, padx=4, pady=(0, 4))

        top = ttk.Frame(vpaned)
        vpaned.add(top, weight=1)

        list_frame = ttk.Frame(top)
        list_frame.pack(fill="both", expand=True)

        self.mail_tree = ttk.Treeview(
            list_frame, show="headings", selectmode="extended", height=6,
            columns=("flag", "from", "subject", "date", "size"))
        for key, text, width, anchor in [
            ("flag", "", 28, "center"),
            ("from", "发件人", 220, "w"),
            ("subject", "主题", 420, "w"),
            ("date", "日期", 130, "center"),
            ("size", "大小", 70, "center"),
        ]:
            self.mail_tree.heading(key, text=text)
            self.mail_tree.column(key, width=width, anchor=anchor)

        vsb = ttk.Scrollbar(list_frame, orient="vertical", command=self.mail_tree.yview)
        self.mail_tree.configure(yscrollcommand=vsb.set)
        self.mail_tree.pack(side="left", fill="both", expand=True)
        vsb.pack(side="right", fill="y")
        self.mail_tree.bind("<<TreeviewSelect>>", self._on_select_mail)

        ops = ttk.Frame(top)
        ops.pack(fill="x", pady=(2, 0))
        for label, cmd in [
            ("回复", self.reply_mail),
            ("转发", self.forward_mail),
            ("标为已读", lambda: self.set_seen(True)),
            ("标为未读", lambda: self.set_seen(False)),
            ("星标 / 取消", self.toggle_flag),
            ("移动到…", self.move_selected),
            ("删除", self.delete_selected),
        ]:
            ttk.Button(ops, text=label, command=cmd).pack(side="left", padx=2)

        bottom = ttk.Frame(vpaned)
        vpaned.add(bottom, weight=3)

        preview_frame = ttk.LabelFrame(bottom, text="邮件内容（超链接单击打开）", padding=4)
        preview_frame.pack(fill="both", expand=True, pady=(0, 4))
        self.preview_text = scrolledtext.ScrolledText(preview_frame, height=16, wrap="word")
        self.preview_text.pack(fill="both", expand=True)
        self.preview_text.tag_config("link", foreground="#1a73e8", underline=True)
        self.preview_text.tag_bind("link", "<Button-1>", self._on_link_click)
        self.preview_text.tag_bind("link", "<Enter>", lambda e: self.preview_text.config(cursor="hand2"))
        self.preview_text.tag_bind("link", "<Leave>", lambda e: self.preview_text.config(cursor=""))

        att_frame = ttk.LabelFrame(bottom, text="附件（双击保存）", padding=4)
        att_frame.pack(fill="x")
        self.att_tree = ttk.Treeview(att_frame, columns=("name", "size"), show="headings", height=3)
        self.att_tree.heading("name", text="文件名")
        self.att_tree.heading("size", text="大小")
        self.att_tree.column("name", width=480, anchor="w")
        self.att_tree.column("size", width=100, anchor="center")
        self.att_tree.pack(side="left", fill="x", expand=True)
        self.att_tree.bind("<Double-1>", self.save_attachment)
        ttk.Button(att_frame, text="保存选中附件",
                   command=self.save_attachment).pack(side="right", padx=4)

    # ---------- 写邮件 ----------
    def _build_compose_tab(self):
        form = ttk.Frame(self.compose_tab, padding=12)
        form.pack(fill="both", expand=True)

        ttk.Label(form, text="收件人：").grid(row=0, column=0, sticky="w", pady=6)
        self.to_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.to_var, width=70).grid(row=0, column=1, sticky="ew", pady=6)
        ttk.Button(form, text="从联系人选择",
                   command=self.pick_contact).grid(row=0, column=2, padx=4)

        ttk.Label(form, text="主题：").grid(row=1, column=0, sticky="w", pady=6)
        self.subject_var = tk.StringVar()
        ttk.Entry(form, textvariable=self.subject_var, width=70).grid(
            row=1, column=1, columnspan=2, sticky="ew", pady=6)

        ttk.Label(form, text="正文：").grid(row=2, column=0, sticky="nw", pady=6)
        self.body_text = scrolledtext.ScrolledText(form, width=80, height=16, wrap="word")
        self.body_text.grid(row=2, column=1, columnspan=2, sticky="nsew", pady=6)

        att_row = ttk.Frame(form)
        att_row.grid(row=3, column=1, columnspan=2, sticky="ew", pady=4)
        ttk.Label(att_row, text="附件：").pack(side="left")
        ttk.Button(att_row, text="添加", command=self.add_attachment).pack(side="left", padx=2)
        ttk.Button(att_row, text="移除选中", command=self.remove_attachment).pack(side="left", padx=2)
        self.att_listbox = tk.Listbox(att_row, height=3)
        self.att_listbox.pack(side="left", fill="x", expand=True, padx=6)

        btn_row = ttk.Frame(form)
        btn_row.grid(row=4, column=1, columnspan=2, sticky="e", pady=8)
        self.draft_btn = ttk.Button(btn_row, text="保存到草稿箱", command=self.save_draft)
        self.draft_btn.pack(side="right", padx=6)
        self.send_btn = ttk.Button(btn_row, text="发送邮件", command=self.send_mail)
        self.send_btn.pack(side="right")

        form.columnconfigure(1, weight=1)
        form.rowconfigure(2, weight=1)

    # ---------- 联系人 ----------
    def _build_contacts_tab(self):
        frame = ttk.Frame(self.contacts_tab, padding=12)
        frame.pack(fill="both", expand=True)

        self.contact_tree = ttk.Treeview(frame, columns=("name", "email"), show="headings")
        self.contact_tree.heading("name", text="姓名")
        self.contact_tree.heading("email", text="邮箱")
        self.contact_tree.column("name", width=220, anchor="w")
        self.contact_tree.column("email", width=360, anchor="w")
        self.contact_tree.pack(fill="both", expand=True, pady=(0, 6))
        self._refresh_contact_tree()

        btn = ttk.Frame(frame)
        btn.pack(fill="x")
        ttk.Button(btn, text="添加联系人", command=self.add_contact).pack(side="left", padx=4)
        ttk.Button(btn, text="删除选中", command=self.delete_contact).pack(side="left", padx=4)

    def _refresh_contact_tree(self):
        for iid in self.contact_tree.get_children():
            self.contact_tree.delete(iid)
        for idx, c in enumerate(self.contacts):
            self.contact_tree.insert("", "end", iid=str(idx),
                                     values=(c.get("name", ""), c.get("email", "")))

    def add_contact(self):
        name = simpledialog.askstring("添加联系人", "姓名：")
        if not name:
            return
        mail_addr = simpledialog.askstring("添加联系人", "邮箱地址：")
        if not mail_addr:
            return
        self.contacts.append({"name": name.strip(), "email": mail_addr.strip()})
        self._save_contacts()
        self._refresh_contact_tree()

    def delete_contact(self):
        sel = self.contact_tree.selection()
        if not sel:
            return
        for idx in reversed([int(i) for i in sel]):
            del self.contacts[idx]
        self._save_contacts()
        self._refresh_contact_tree()

    def pick_contact(self):
        sel = self.contact_tree.selection()
        if not sel:
            messagebox.showinfo("提示", "请先在“联系人”标签页选择一个联系人。")
            return
        addr = self.contacts[int(sel[0])]["email"]
        current = self.to_var.get().strip()
        self.to_var.set(f"{current}, {addr}" if current else addr)
        self.notebook.select(self.compose_tab)

    # ===================== 登录与文件夹 =====================
    def login_and_refresh(self):
        creds = self._require_login()
        if not creds:
            return
        email_addr, password = creds

        def work():
            with imap_session(email_addr, password) as mail:
                self.special_folders = detect_special_folders(mail)
                folders = list_folders(mail)
            self.task_queue.put(("folders_ready", folders))

        self._run_async(work, btn=self.login_btn, busy_text="登录中…",
                        status="正在登录并获取文件夹列表…", err_prefix="登录失败")

    def _render_folder_tree(self, raw_folders):
        for iid in self.folder_tree.get_children():
            self.folder_tree.delete(iid)

        used = set()
        for role, label in ROLE_LABELS.items():
            raw = self.special_folders.get(role)
            if raw and raw in raw_folders:
                self.folder_tree.insert("", "end", iid=raw, text=label)
                used.add(raw)

        for raw in raw_folders:
            if raw in used or raw.upper() == "INBOX":
                continue
            self.folder_tree.insert("", "end", iid=raw, text=imap_utf7_decode(raw))

        if self.folder_tree.get_children():
            first = self.folder_tree.get_children()[0]
            self.folder_tree.selection_set(first)
            self.current_folder = first
            self.load_folder(first)

    def _on_folder_select(self, _event):
        sel = self.folder_tree.selection()
        if sel:
            self.current_folder = sel[0]
            self.current_page = 0
            self.load_folder(self.current_folder)

    def create_folder(self):
        name = simpledialog.askstring("新建文件夹", "文件夹名称（支持中文）：")
        if name:
            self._folder_op(lambda m: m.create(imap_utf7_encode(name.strip())),
                            f"文件夹「{name}」已创建")

    def rename_folder(self):
        sel = self.folder_tree.selection()
        if not sel:
            return
        old = sel[0]
        if old.upper() == "INBOX":
            messagebox.showwarning("提示", "不能重命名收件箱。")
            return
        new_name = simpledialog.askstring("重命名文件夹", "新名称：")
        if new_name:
            self._folder_op(lambda m: m.rename(old, imap_utf7_encode(new_name.strip())),
                            f"已重命名为「{new_name}」")

    def delete_folder(self):
        sel = self.folder_tree.selection()
        if not sel:
            return
        raw = sel[0]
        if raw == self.special_folders.get("inbox"):
            messagebox.showwarning("提示", "不能删除收件箱。")
            return
        if messagebox.askyesno("确认", f"确定删除文件夹「{imap_utf7_decode(raw)}」？"):
            self._folder_op(lambda m: m.delete(raw), "文件夹已删除")

    def _folder_op(self, op, success_msg):
        creds = self._require_login()
        if not creds:
            return
        email_addr, password = creds

        def work():
            with imap_session(email_addr, password) as mail:
                op(mail)
            self.task_queue.put(("info", success_msg))
            self.task_queue.put(("do_login_refresh", None))

        self._run_async(work, status="正在执行文件夹操作…", err_prefix="文件夹操作失败")

    # ===================== 加载列表 =====================
    def load_folder(self, raw_folder, search_criteria=None):
        if self._loading:
            return
        creds = self._require_login()
        if not creds:
            return
        email_addr, password = creds
        self._loading = True

        for iid in self.mail_tree.get_children():
            self.mail_tree.delete(iid)
        self.preview_text.delete("1.0", tk.END)
        for iid in self.att_tree.get_children():
            self.att_tree.delete(iid)
        self.page_label.config(text="正在加载邮件…")

        def work():
            with imap_session(email_addr, password) as mail:
                typ, _ = mail.select(raw_folder, readonly=False)
                if typ != "OK":
                    raise RuntimeError(f"无法打开文件夹：{imap_utf7_decode(raw_folder)}")
                typ, data = mail.uid("SEARCH", None, *(search_criteria or ["ALL"]))
                if typ != "OK":
                    raise RuntimeError("搜索失败")

                uids = data[0].split()
                total = len(uids)
                self.total_pages = max(1, (total + PAGE_SIZE - 1) // PAGE_SIZE)
                start = self.current_page * PAGE_SIZE

                page_info = []
                for uid in reversed(uids[start:start + PAGE_SIZE]):
                    typ, msg_data = mail.uid("FETCH", uid,
                                             "(BODY.PEEK[HEADER] FLAGS RFC822.SIZE)")
                    if typ != "OK" or not msg_data or not msg_data[0]:
                        continue
                    raw_header, flags, size = b"", b"", 0
                    for item in msg_data:
                        if not isinstance(item, tuple):
                            continue
                        meta = item[0].decode("utf-8", errors="replace")
                        raw_header = item[1]
                        fm = re.search(r"FLAGS \(([^)]*)\)", meta)
                        sm = re.search(r"RFC822\.SIZE (\d+)", meta)
                        if fm:
                            flags = fm.group(1).encode()
                        if sm:
                            size = int(sm.group(1))
                    if not raw_header:
                        continue
                    msg = email.message_from_bytes(raw_header)
                    from_name, from_addr = parseaddr(msg.get("From", ""))
                    flags_str = flags.decode("utf-8", errors="replace")
                    page_info.append({
                        "uid": uid.decode(),
                        "from_display": decode_mime_header(from_name) or from_addr,
                        "from_addr": from_addr,
                        "to_display": parse_people(msg.get("To", "")),
                        "subject": decode_mime_header(msg.get("Subject")),
                        "date": msg.get("Date", ""),
                        "size": size,
                        "seen": "\\Seen" in flags_str,
                        "flagged": "\\Flagged" in flags_str,
                    })
            self.task_queue.put(("page_ready", page_info, total, raw_folder))

        self._set_button_busy(self.refresh_btn, "加载中…")
        self._set_button_busy(self.prev_btn)
        self._set_button_busy(self.next_btn)
        self._run_async(
            work,
            status="正在搜索邮件…" if search_criteria else
                   f"正在加载「{imap_utf7_decode(raw_folder)}」…",
            err_prefix="加载邮件失败")

    def prev_page(self):
        if self.current_page > 0:
            self.current_page -= 1
            self.load_folder(self.current_folder)

    def next_page(self):
        if self.current_page < self.total_pages - 1:
            self.current_page += 1
            self.load_folder(self.current_folder)

    def search_mail(self):
        keyword = self.search_var.get().strip()
        if not keyword:
            self.load_folder(self.current_folder)
            return
        self.current_page = 0
        self.load_folder(self.current_folder,
                         search_criteria=["OR", "SUBJECT", f'"{keyword}"',
                                          "FROM", f'"{keyword}"'])

    # ===================== 预览 =====================
    def _on_select_mail(self, _event):
        sel = self.mail_tree.selection()
        if not sel:
            return
        uid = sel[0]
        info = self.mail_cache.get(uid)
        if info is not None:
            self._show_mail(info)
            return
        self.preview_text.delete("1.0", tk.END)
        self.preview_text.insert("1.0", "正在加载邮件正文……")
        self._fetch_mail_body(uid)

    def _fetch_mail_body(self, uid):
        creds = self._require_login()
        if not creds:
            return
        email_addr, password = creds
        folder = self.current_folder

        def work():
            with imap_session(email_addr, password) as mail:
                mail.select(folder, readonly=False)
                typ, msg_data = mail.uid("FETCH", uid.encode(), "(BODY.PEEK[])")
                if typ != "OK" or not msg_data or not msg_data[0]:
                    raise RuntimeError("拉取正文失败")
                raw = msg_data[0][1] if isinstance(msg_data[0], tuple) else b""
                msg = email.message_from_bytes(raw)
                body, attachments = extract_parts(msg)
                info = {
                    "body": body,
                    "attachments": attachments,
                    "from_addr": parseaddr(msg.get("From", ""))[1],
                    "subject": decode_mime_header(msg.get("Subject")),
                }
            self.task_queue.put(("mail_body_ready", uid, info))

        self._run_async(work, err_prefix="拉取正文失败")

    def _show_mail(self, info):
        self.preview_text.delete("1.0", tk.END)
        self.preview_text.insert("1.0", info.get("body") or "（无正文）")
        self._highlight_links()
        for iid in self.att_tree.get_children():
            self.att_tree.delete(iid)
        for idx, (fname, data) in enumerate(info.get("attachments", [])):
            self.att_tree.insert("", "end", iid=str(idx),
                                 values=(fname, human_size(len(data))))

    def _highlight_links(self):
        self.preview_text.tag_remove("link", "1.0", tk.END)
        text = self.preview_text.get("1.0", "end-1c")
        for m in URL_RE.finditer(text):
            clean = clean_url(m.group(0))
            if clean:
                self.preview_text.tag_add(
                    "link",
                    f"1.0 + {m.start()} chars",
                    f"1.0 + {m.start() + len(clean)} chars")

    def _on_link_click(self, event):
        idx = self.preview_text.index(f"@{event.x},{event.y}")
        ranges = self.preview_text.tag_ranges("link")
        for i in range(0, len(ranges), 2):
            start, end = ranges[i], ranges[i + 1]
            if (self.preview_text.compare(start, "<=", idx)
                    and self.preview_text.compare(idx, "<", end)):
                webbrowser.open(self.preview_text.get(start, end))
                return

    # ---------- 标记 ----------
    def set_seen(self, seen: bool):
        uids = self._selected_uids()
        if uids:
            self._uid_store(uids, "+FLAGS" if seen else "-FLAGS",
                            "\\Seen", "已更新标记")

    def toggle_flag(self):
        uids = self._selected_uids()
        if not uids:
            return
        any_flagged = any("★" in self.mail_tree.item(i, "values")[0]
                          for i in self.mail_tree.selection())
        self._uid_store(uids, "-FLAGS" if any_flagged else "+FLAGS",
                        "\\Flagged", "已更新星标")

    def _uid_store(self, uids, op, flag, success_msg):
        creds = self._require_login()
        if not creds:
            return
        email_addr, password = creds
        folder = self.current_folder

        def work():
            with imap_session(email_addr, password) as mail:
                mail.select(folder, readonly=False)
                for uid in uids:
                    mail.uid("STORE", uid.encode(), op, flag)
            self.task_queue.put(("info", success_msg))
            self.task_queue.put(("refresh_list", None))

        self._run_async(work, status="正在更新…", err_prefix="标记失败")

    # ---------- 移动与删除 ----------
    def move_selected(self):
        uids = self._selected_uids()
        if not uids:
            return
        targets = []
        for role in ("trash", "junk", "sent", "drafts"):
            raw = self.special_folders.get(role)
            if raw:
                targets.append((raw, imap_utf7_decode(raw)))
        for child in self.folder_tree.get_children():
            if child not in [t[0] for t in targets] and child != self.current_folder:
                targets.append((child, imap_utf7_decode(child)))

        if not targets:
            messagebox.showinfo("提示", "没有可移动的目标文件夹。")
            return
        choice = self._ask_choice("移动到文件夹", [label for _, label in targets])
        if choice is not None:
            self._move_uids(uids, targets[choice][0])

    def _move_uids(self, uids, target_raw):
        creds = self._require_login()
        if not creds:
            return
        email_addr, password = creds
        source = self.current_folder

        def work():
            with imap_session(email_addr, password) as mail:
                mail.select(source, readonly=False)
                for uid in uids:
                    mail.uid("COPY", uid.encode(), target_raw)
                    mail.uid("STORE", uid.encode(), "+FLAGS", "\\Deleted")
                mail.expunge()
            self.task_queue.put(("info", f"已移动 {len(uids)} 封邮件"))
            self.task_queue.put(("refresh_list", None))

        self._run_async(work, status="正在移动邮件…", err_prefix="移动失败")

    def delete_selected(self):
        uids = self._selected_uids()
        if not uids:
            return
        if not messagebox.askyesno("确认", f"确定删除选中的 {len(uids)} 封邮件？"):
            return
        trash_raw = self.special_folders.get("trash")
        if trash_raw and self.current_folder != trash_raw:
            self._move_uids(uids, trash_raw)
        else:
            self._permanent_delete(uids)

    def _permanent_delete(self, uids):
        creds = self._require_login()
        if not creds:
            return
        email_addr, password = creds
        folder = self.current_folder

        def work():
            with imap_session(email_addr, password) as mail:
                mail.select(folder, readonly=False)
                for uid in uids:
                    mail.uid("STORE", uid.encode(), "+FLAGS", "\\Deleted")
                mail.expunge()
            self.task_queue.put(("info", "已永久删除"))
            self.task_queue.put(("refresh_list", None))

        self._run_async(work, status="正在删除邮件…", err_prefix="删除失败")

    # ---------- 回复与转发 ----------
    def _current_mail_info(self, action_name="操作"):
        sel = self.mail_tree.selection()
        if not sel:
            messagebox.showwarning("提示", "请先选择一封邮件。")
            return None
        info = self.mail_cache.get(sel[0])
        if not info:
            messagebox.showwarning("提示", f"请先加载邮件正文后再{action_name}。")
            return None
        return info

    def _fill_quote(self, header, info):
        self.body_text.delete("1.0", tk.END)
        self.body_text.insert("1.0", header + (info.get("body") or ""))
        self.notebook.select(self.compose_tab)

    def reply_mail(self):
        info = self._current_mail_info("回复")
        if not info:
            return
        subj = info["subject"]
        if not subj.lower().startswith("re:"):
            subj = "Re: " + subj
        self.to_var.set(info["from_addr"])
        self.subject_var.set(subj)
        self._fill_quote("\n\n\n----- 原始邮件 -----\n", info)

    def forward_mail(self):
        info = self._current_mail_info("转发")
        if not info:
            return
        subj = info["subject"]
        if not subj.lower().startswith("fwd:"):
            subj = "Fwd: " + subj
        self.to_var.set("")
        self.subject_var.set(subj)
        header = (f"\n\n\n----- 转发邮件 -----\n"
                  f"发件人：{info['from_addr']}\n主题：{info['subject']}\n\n")
        self._fill_quote(header, info)

    def save_attachment(self, _event=None):
        info = self._current_mail_info("操作附件")
        if not info:
            return
        sel = self.att_tree.selection()
        if not sel:
            messagebox.showwarning("提示", "请选择一个附件。")
            return
        fname, data = info["attachments"][int(sel[0])]
        path = filedialog.asksaveasfilename(initialfile=fname)
        if not path:
            return
        try:
            with open(path, "wb") as f:
                f.write(data)
            messagebox.showinfo("成功", f"已保存到：\n{path}")
        except Exception as exc:
            messagebox.showerror("保存失败", str(exc))

    # ===================== 写信 =====================
    def add_attachment(self):
        for p in filedialog.askopenfilenames(title="选择附件"):
            if p and p not in self.pending_attachments:
                self.pending_attachments.append(p)
                self.att_listbox.insert(tk.END, p)

    def remove_attachment(self):
        for idx in reversed(self.att_listbox.curselection()):
            del self.pending_attachments[idx]
            self.att_listbox.delete(idx)

    def _build_message(self, to_list, subject, body, attachments):
        if attachments:
            msg = MIMEMultipart()
            msg.attach(MIMEText(body, "plain", "utf-8"))
            for fp in attachments:
                with open(fp, "rb") as f:
                    data = f.read()
                ctype, _ = mimetypes.guess_type(fp)
                maintype, subtype = (ctype or "application/octet-stream").split("/", 1)
                part = MIMEBase(maintype, subtype)
                part.set_payload(data)
                encoders.encode_base64(part)
                part.add_header("Content-Disposition", "attachment",
                                filename=os.path.basename(fp))
                msg.attach(part)
        else:
            msg = MIMEText(body, "plain", "utf-8")

        msg["From"] = formataddr(("", self.email_var.get().strip()))
        msg["To"] = ", ".join(to_list)
        msg["Subject"] = Header(subject or "(无主题)", "utf-8")
        return msg

    def _compose_fields(self):
        to_raw = self.to_var.get().strip()
        recipients = [x.strip() for x in re.split(r"[,;]", to_raw) if x.strip()]
        return (recipients,
                self.subject_var.get().strip(),
                self.body_text.get("1.0", tk.END).strip(),
                list(self.pending_attachments))

    def send_mail(self):
        creds = self._require_login()
        if not creds:
            return
        email_addr, password = creds
        recipients, subject, body, attachments = self._compose_fields()
        if not recipients:
            messagebox.showwarning("提示", "请填写收件人。")
            return

        def work():
            msg = self._build_message(recipients, subject, body, attachments)
            with smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, timeout=TIMEOUT) as server:
                server.login(email_addr, password)
                server.sendmail(email_addr, recipients, msg.as_string())
            self.task_queue.put(("send_ok", None))

        self._run_async(work, btn=self.send_btn, busy_text="发送中…",
                        status="正在发送邮件…", err_prefix="发送失败")

    def save_draft(self):
        creds = self._require_login()
        if not creds:
            return
        email_addr, password = creds
        recipients, subject, body, attachments = self._compose_fields()
        if not subject and not body:
            messagebox.showwarning("提示", "草稿内容为空。")
            return
        drafts_raw = self.special_folders.get("drafts") or imap_utf7_encode("草稿箱")

        def work():
            msg = self._build_message(recipients or [email_addr], subject, body, attachments)
            with imap_session(email_addr, password) as mail:
                mail.append(drafts_raw, "\\Draft",
                            imaplib.Time2Internaldate(datetime.now().timestamp()),
                            msg.as_bytes())
            self.task_queue.put(("draft_saved", None))

        self._run_async(work, btn=self.draft_btn, busy_text="保存中…",
                        status="正在保存草稿…", err_prefix="保存草稿失败")

    # ===================== 连接测试 =====================
    def test_connection(self):
        creds = self._require_login()
        if not creds:
            return
        email_addr, password = creds

        def work():
            imap_ok = smtp_ok = False
            imap_msg = smtp_msg = ""
            try:
                with imap_session(email_addr, password) as mail:
                    typ, _ = mail.select("INBOX", readonly=True)
                    imap_ok = typ == "OK"
                    imap_msg = "IMAP 连接成功" if imap_ok else "IMAP 无法打开 INBOX"
            except Exception as exc:
                imap_msg = f"IMAP 失败：{exc}"

            try:
                with smtplib.SMTP_SSL(SMTP_HOST, SMTP_PORT, timeout=TIMEOUT) as s:
                    s.login(email_addr, password)
                smtp_ok = True
                smtp_msg = "SMTP 连接成功"
            except Exception as exc:
                smtp_msg = f"SMTP 失败：{exc}"

            self.task_queue.put(("test_result", imap_ok and smtp_ok, imap_msg, smtp_msg))

        self._run_async(work, btn=self.test_btn, busy_text="测试中…",
                        status="正在测试 IMAP / SMTP 连接…")

    # ===================== 辅助 =====================
    def _is_sent_folder(self, folder):
        sent_raw = self.special_folders.get("sent")
        if sent_raw and folder == sent_raw:
            return True
        decoded = imap_utf7_decode(folder).lower()
        return "已发送" in decoded or decoded == "sent"

    def _selected_uids(self):
        sel = self.mail_tree.selection()
        if not sel:
            messagebox.showwarning("提示", "请先选择邮件。")
            return []
        return list(sel)

    def _ask_choice(self, title, options):
        win = tk.Toplevel(self.root)
        win.title(title)
        win.geometry("360x320")
        win.transient(self.root)
        win.grab_set()
        listbox = tk.Listbox(win)
        listbox.pack(fill="both", expand=True, padx=10, pady=10)
        for opt in options:
            listbox.insert(tk.END, opt)
        result = {"index": None}

        def ok(_event=None):
            sel = listbox.curselection()
            if sel:
                result["index"] = sel[0]
                win.destroy()

        ttk.Button(win, text="确定", command=ok).pack(pady=6)
        listbox.bind("<Double-1>", ok)
        self.root.wait_window(win)
        return result["index"]

    # ===================== 队列 =====================
    def _poll_queue(self):
        for _ in range(8):
            try:
                task = self.task_queue.get_nowait()
            except queue.Empty:
                break
            try:
                self._handle_task(task)
            except Exception as exc:
                messagebox.showerror("界面更新错误", str(exc))
        self.root.after(80, self._poll_queue)

    def _handle_task(self, task):
        action = task[0]

        if action == "folders_ready":
            self._restore_button(self.login_btn)
            self.status_var.set("就绪")
            self._save_cfg()          # 登录成功后立即把凭据存到 cfg
            self._render_folder_tree(task[1])

        elif action == "page_ready":
            page_info, total, folder = task[1], task[2], task[3]
            self._loading = False
            self._restore_button(self.refresh_btn)
            self._restore_button(self.prev_btn)
            self._restore_button(self.next_btn)

            if folder != self.current_folder:
                self.status_var.set("就绪")
                self.load_folder(self.current_folder)
                return

            self.status_var.set("就绪")
            is_sent = self._is_sent_folder(folder)
            self.mail_tree.heading("from", text="收件人" if is_sent else "发件人")
            self.page_label.config(
                text=f"第 {self.current_page + 1} / {self.total_pages} 页  ·  共 {total} 封")
            for info in page_info:
                flag = "★" if info["flagged"] else ("●" if not info["seen"] else "")
                person = info["to_display"] if is_sent else info["from_display"]
                if not person:
                    person = "(无收件人)" if is_sent else "(未知发件人)"
                self.mail_tree.insert(
                    "", "end", iid=info["uid"],
                    values=(flag, person,
                            info["subject"] or "(无主题)",
                            info["date"], human_size(info["size"])))

        elif action == "mail_body_ready":
            _, uid, info = task
            self.mail_cache[uid] = info
            if uid in self.mail_tree.selection():
                self._show_mail(info)

        elif action == "refresh_list":
            self.load_folder(self.current_folder)

        elif action == "do_login_refresh":
            self.login_and_refresh()

        elif action == "send_ok":
            self._restore_button(self.send_btn)
            self.status_var.set("就绪")
            messagebox.showinfo("成功", "邮件已发送。")
            self.to_var.set("")
            self.subject_var.set("")
            self.body_text.delete("1.0", tk.END)
            self.pending_attachments.clear()
            self.att_listbox.delete(0, tk.END)

        elif action == "draft_saved":
            self._restore_button(self.draft_btn)
            self.status_var.set("就绪")
            messagebox.showinfo("提示", "已保存到草稿箱。")

        elif action == "test_result":
            self._restore_button(self.test_btn)
            self.status_var.set("就绪")
            _, ok, imap_msg, smtp_msg = task
            (messagebox.showinfo if ok else messagebox.showerror)(
                "连接测试", f"{imap_msg}\n{smtp_msg}")

        elif action == "info":
            self.status_var.set("就绪")
            messagebox.showinfo("提示", task[1])

        elif action == "error":
            self._loading = False
            self._restore_all_buttons()
            self.status_var.set("就绪")
            self.page_label.config(text="加载失败")
            messagebox.showerror("错误", task[1])


if __name__ == "__main__":
    root = tk.Tk()
    MailApp(root)
    root.mainloop()