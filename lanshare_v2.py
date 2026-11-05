"""
LanShare v2 - AirShare-style LAN file sharing for Windows.
Pure standard library (Python 3.8+). No pip installs needed.

Run:  python lanshare_v2.py

Host     : asks for a name, shares chosen files, broadcasts itself on the LAN,
           receives uploads into its own folder.
Receiver : finds hosts by name, browses shared files, downloads them,
           or sends a file back to the host.
Several hosts can run on the same PC (each picks its own free port).
"""

import os
import sys
import json
import queue
import shutil
import socket
import threading
import time
import uuid
import ctypes
import http.client
import urllib.parse
import urllib.request
from http.server import ThreadingHTTPServer, BaseHTTPRequestHandler
import tkinter as tk
from tkinter import ttk, filedialog

# ----------------------------------------------------------------- config
APP = "LanShare"
DISCOVERY_PORT = 8766
BEACON_EVERY = 2
HOST_TIMEOUT = 7
CLIENT_TIMEOUT = 15
CHUNK = 256 * 1024
W, H = 800, 560

KEY = "#010101"
BG = "#0d1117"
PANEL = "#161b22"
PANEL_HI = "#21262d"
BORDER = "#30363d"
TEXT = "#e6edf3"
MUTED = "#8b949e"
ACCENT = "#58a6ff"
ACCENT_DIM = "#1f6feb"
GREEN = "#3fb950"
RED = "#f85149"
GLASS_OUTER = "#3d8bd9"
GLASS_MID = "#1a4d86"

FONT = ("Segoe UI", 10)
FONT_B = ("Segoe UI", 10, "bold")
FONT_H = ("Segoe UI Semibold", 16)
FONT_S = ("Segoe UI", 9)


# ----------------------------------------------------------------- helpers
def local_ip():
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ip = s.getsockname()[0]
        s.close()
        return ip
    except OSError:
        return "127.0.0.1"


def broadcast_targets():
    targets = {"255.255.255.255"}
    parts = local_ip().split(".")
    if len(parts) == 4:
        targets.add(".".join(parts[:3] + ["255"]))
    return list(targets)


def safe_name(name):
    name = os.path.basename(name.replace("\\", "/"))
    bad = '<>:"/\\|?*'
    name = "".join("_" if (c in bad or ord(c) < 32) else c for c in name)
    return name.strip(" .") or "file"


def unique_path(folder, name):
    base, ext = os.path.splitext(name)
    path = os.path.join(folder, name)
    n = 1
    while os.path.exists(path):
        path = os.path.join(folder, "%s (%d)%s" % (base, n, ext))
        n += 1
    return path


def human_size(n):
    for unit in ("B", "KB", "MB", "GB", "TB"):
        if n < 1024 or unit == "TB":
            return ("%d %s" % (n, unit)) if unit == "B" else ("%.1f %s" % (n, unit))
        n /= 1024.0


def round_rect(canvas, x1, y1, x2, y2, r, **kw):
    pts = [
        x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r,
        x2, y2 - r, x2, y2, x2 - r, y2, x1 + r, y2,
        x1, y2, x1, y2 - r, x1, y1 + r, x1, y1,
    ]
    kw.setdefault("outline", "")
    return canvas.create_polygon(pts, smooth=True, **kw)


# ----------------------------------------------------------------- HTTP
class HostServer(ThreadingHTTPServer):
    daemon_threads = True
    allow_reuse_address = True


class Handler(BaseHTTPRequestHandler):
    server_version = "LanShare/2.0"
    protocol_version = "HTTP/1.0"

    def log_message(self, *args):
        pass

    def _json(self, code, obj):
        body = json.dumps(obj).encode("utf-8")
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        app = self.server.app
        path = urllib.parse.urlparse(self.path).path
        app.touch_client(self.client_address[0])

        if path == "/api/info":
            self._json(200, {"name": app.host_name, "files": app.file_list()})
            return

        if path.startswith("/file/"):
            item = app.get_shared(path[len("/file/"):])
            if item is None:
                self.send_error(404, "Not shared")
                return
            try:
                f = open(item["path"], "rb")
            except OSError:
                self.send_error(404, "File missing")
                return
            with f:
                self.send_response(200)
                self.send_header("Content-Type", "application/octet-stream")
                self.send_header("Content-Length", str(item["size"]))
                self.send_header(
                    "Content-Disposition",
                    "attachment; filename*=UTF-8''" + urllib.parse.quote(item["name"]),
                )
                self.end_headers()
                shutil.copyfileobj(f, self.wfile, CHUNK)
            return

        self.send_error(404)

    def do_POST(self):
        app = self.server.app
        url = urllib.parse.urlparse(self.path)
        if url.path != "/upload":
            self.send_error(404)
            return

        qs = urllib.parse.parse_qs(url.query)
        name = safe_name(urllib.parse.unquote(qs.get("name", ["upload.bin"])[0]))
        length = int(self.headers.get("Content-Length", 0) or 0)
        dest = unique_path(app.inbox_dir, name)
        remaining = length
        try:
            with open(dest, "wb") as f:
                while remaining > 0:
                    chunk = self.rfile.read(min(CHUNK, remaining))
                    if not chunk:
                        break
                    f.write(chunk)
                    remaining -= len(chunk)
        except OSError:
            self._json(500, {"ok": False})
            return

        if remaining > 0:
            try:
                os.remove(dest)
            except OSError:
                pass
            self._json(400, {"ok": False})
            return

        app.on_received(os.path.basename(dest), self.client_address[0])
        self._json(200, {"ok": True})


# ----------------------------------------------------------------- App
class LanShare:
    def __init__(self):
        self.root = tk.Tk()
        self.root.title(APP)
        self.root.overrideredirect(True)
        self.root.configure(bg=KEY)
        self.root.wm_attributes("-transparentcolor", KEY)

        sw, sh = self.root.winfo_screenwidth(), self.root.winfo_screenheight()
        self.root.geometry("%dx%d+%d+%d" % (W, H, (sw - W) // 2, (sh - H) // 3))

        style = ttk.Style(self.root)
        style.theme_use("clam")
        style.configure("Dark.Treeview", background=PANEL, fieldbackground=PANEL,
                        foreground=TEXT, borderwidth=0, rowheight=26, font=FONT)
        style.configure("Dark.Treeview.Heading", background=PANEL_HI,
                        foreground=MUTED, relief="flat", font=FONT_B)
        style.map("Dark.Treeview", background=[("selected", ACCENT_DIM)],
                  foreground=[("selected", "#ffffff")])
        style.map("Dark.Treeview.Heading", background=[("active", BORDER)])
        style.configure("Dark.Horizontal.TProgressbar", troughcolor=PANEL_HI,
                        background=GREEN, bordercolor=PANEL_HI,
                        lightcolor=GREEN, darkcolor=GREEN)

        self.canvas = tk.Canvas(self.root, width=W, height=H, bg=KEY,
                                highlightthickness=0, bd=0)
        self.canvas.pack(fill="both", expand=True)
        round_rect(self.canvas, 0, 0, W, H, 26, fill=GLASS_OUTER)
        round_rect(self.canvas, 3, 3, W - 3, H - 3, 23, fill=GLASS_MID)
        round_rect(self.canvas, 7, 7, W - 7, H - 7, 20, fill=BG)

        self.body = tk.Frame(self.canvas, bg=BG)
        self.canvas.create_window(21, 21, window=self.body, anchor="nw",
                                  width=W - 42, height=H - 42)

        self.downloads_root = os.path.join(os.path.expanduser("~"), "Downloads", APP)
        self.receive_dir = os.path.join(os.path.expanduser("~"), "Desktop", APP)
        self.hosts_root = os.path.join(self.downloads_root, "Hosts")
        os.makedirs(self.receive_dir, exist_ok=True)
        os.makedirs(self.hosts_root, exist_ok=True)

        self.q = queue.Queue()
        self.lock = threading.Lock()
        self.shared = {}
        self.clients = {}
        self.server = None
        self.stop = threading.Event()
        self.mode = None
        self.status = None
        self.hosts = {}
        self.host_name = ""
        self.host_port = 0
        self.inbox_dir = self.hosts_root
        self.remote = None
        self.remote_files = {}
        self.host_keys = []

        self.show_home()
        self.root.after(120, self.poll)
        self.root.after(150, self.apply_taskbar)
        self.root.mainloop()

    # ---------- window helpers
    def apply_taskbar(self):
        if sys.platform != "win32":
            return
        try:
            hwnd = ctypes.windll.user32.GetParent(self.root.winfo_id())
            GWL_EXSTYLE, WS_EX_APPWINDOW, WS_EX_TOOLWINDOW = -20, 0x00040000, 0x00000080
            style = ctypes.windll.user32.GetWindowLongW(hwnd, GWL_EXSTYLE)
            style = (style & ~WS_EX_TOOLWINDOW) | WS_EX_APPWINDOW
            ctypes.windll.user32.SetWindowLongW(hwnd, GWL_EXSTYLE, style)
            self.root.withdraw()
            self.root.after(50, self.root.deiconify)
        except Exception:
            pass

    def drag_start(self, e):
        self._dx = e.x_root - self.root.winfo_x()
        self._dy = e.y_root - self.root.winfo_y()

    def drag_move(self, e):
        self.root.geometry("+%d+%d" % (e.x_root - self._dx, e.y_root - self._dy))

    def quit_app(self):
        self.leave_mode()
        self.root.after(200, self.root.destroy)

    def button(self, parent, text, cmd, primary=False, danger=False):
        bg, fg = PANEL_HI, TEXT
        if primary:
            bg, fg = ACCENT_DIM, "#ffffff"
        if danger:
            bg, fg = RED, "#ffffff"
        return tk.Button(parent, text=text, command=cmd, bg=bg, fg=fg,
                         activebackground=BORDER, activeforeground=TEXT,
                         relief="flat", bd=0, highlightthickness=0,
                         font=FONT_B, padx=14, pady=6, cursor="hand2")

    def titlebar(self, title, back=True):
        bar = tk.Frame(self.body, bg=BG)
        bar.pack(fill="x", padx=18, pady=(12, 0))
        if back:
            self.button(bar, "<  Back", self.show_home).pack(side="left")
        lbl = tk.Label(bar, text=title, bg=BG, fg=TEXT, font=FONT_H)
        lbl.pack(side="left", padx=14)
        close = tk.Label(bar, text="X", bg=BG, fg=MUTED, font=FONT_B, cursor="hand2")
        close.pack(side="right", padx=4)
        close.bind("<Button-1>", lambda e: self.quit_app())
        close.bind("<Enter>", lambda e: close.config(fg=RED))
        close.bind("<Leave>", lambda e: close.config(fg=MUTED))
        for w in (bar, lbl):
            w.bind("<ButtonPress-1>", self.drag_start)
            w.bind("<B1-Motion>", self.drag_move)
        return bar

    def statusbar(self):
        self.status = tk.Label(self.body, text="", bg=BG, fg=MUTED, font=FONT_S, anchor="w")
        self.status.pack(fill="x", padx=20, pady=(6, 10), side="bottom")

    def set_status(self, text, color=MUTED):
        try:
            self.status.config(text=text, fg=color)
        except (tk.TclError, AttributeError):
            pass

    def make_tree(self, parent, cols, heads, widths):
        frame = tk.Frame(parent, bg=PANEL, highlightthickness=1, highlightbackground=BORDER)
        frame.pack(fill="both", expand=True)
        tree = ttk.Treeview(frame, columns=cols, show="headings",
                            selectmode="extended", style="Dark.Treeview")
        for c, h, w in zip(cols, heads, widths):
            tree.heading(c, text=h, anchor="w")
            tree.column(c, anchor="w", width=w, stretch=(c == cols[0]))
        tree.pack(fill="both", expand=True, padx=1, pady=1)
        return tree

    # ---------- mode switching
    def leave_mode(self):
        self.stop.set()
        if self.server is not None:
            srv = self.server
            self.server = None
            threading.Thread(target=lambda: (srv.shutdown(), srv.server_close()),
                             daemon=True).start()
        with self.lock:
            self.shared.clear()
        self.clients.clear()
        for w in self.body.winfo_children():
            w.destroy()
        self.mode = None
        self.status = None

    def show_home(self):
        self.leave_mode()
        self.titlebar("LanShare", back=False)
        tk.Label(self.body, text="Share files across your local network",
                 bg=BG, fg=MUTED, font=FONT).pack(anchor="w", padx=20, pady=(2, 20))

        row = tk.Frame(self.body, bg=BG)
        row.pack(fill="both", expand=True, padx=20)
        self.card(row, "Host", "Share files from this PC with others on your network.",
                  self.show_host).pack(side="left", fill="both", expand=True, padx=(0, 10))
        self.card(row, "Receive", "Find a host by name and download its files.",
                  self.show_receive).pack(side="left", fill="both", expand=True, padx=(10, 0))

    def card(self, parent, title, desc, cmd):
        f = tk.Frame(parent, bg=PANEL, highlightthickness=1, highlightbackground=BORDER,
                     cursor="hand2")
        inner = tk.Frame(f, bg=PANEL)
        inner.pack(fill="both", expand=True, padx=22, pady=22)
        t = tk.Label(inner, text=title, bg=PANEL, fg=ACCENT, font=FONT_H, cursor="hand2")
        t.pack(anchor="w")
        d = tk.Label(inner, text=desc, bg=PANEL, fg=MUTED, font=FONT, wraplength=260,
                     justify="left", cursor="hand2")
        d.pack(anchor="w", pady=(8, 18))
        self.button(inner, "Open " + title.lower(), cmd, primary=True).pack(anchor="w")
        for w in (f, inner, t, d):
            w.bind("<Button-1>", lambda e: cmd())
        return f

    # ---------- HOST
    def show_host(self):
        self.leave_mode()
        self.mode = "host"
        self.stop = threading.Event()
        self.titlebar("Host")

        tk.Label(self.body, text="Name this host. Receivers will pick this name from their list.",
                 bg=BG, fg=MUTED, font=FONT).pack(anchor="w", padx=20, pady=(24, 8))
        self.name_var = tk.StringVar(value="")
        entry = tk.Entry(self.body, textvariable=self.name_var, bg=PANEL, fg=TEXT,
                         insertbackground=TEXT, relief="flat", font=FONT_H,
                         highlightthickness=1, highlightbackground=BORDER,
                         highlightcolor=ACCENT)
        entry.pack(fill="x", padx=20, ipady=6)
        entry.bind("<Return>", lambda e: self.start_host())
        entry.focus_set()
        self.button(self.body, "Start hosting", self.start_host,
                    primary=True).pack(anchor="w", padx=20, pady=14)

        self.statusbar()
        self.set_status("Example: Sir 1 - Lab PC 2", MUTED)

    def start_host(self):
        name = " ".join(self.name_var.get().split())[:30]
        if not name:
            self.set_status("Please type a name first.", RED)
            return
        try:
            server = HostServer(("0.0.0.0", 0), Handler)
        except OSError:
            self.set_status("Could not start host on this PC.", RED)
            return

        self.server = server
        server.app = self
        self.host_name = name
        self.host_port = server.server_address[1]
        self.inbox_dir = os.path.join(self.hosts_root, safe_name(name))
        os.makedirs(self.inbox_dir, exist_ok=True)

        for w in self.body.winfo_children():
            w.destroy()
        self.titlebar("Host")

        ip = local_ip()
        threading.Thread(target=server.serve_forever, daemon=True).start()
        threading.Thread(target=self.beacon, args=(self.stop, name, self.host_port),
                         daemon=True).start()

        top = tk.Frame(self.body, bg=BG)
        top.pack(fill="x", padx=20, pady=(10, 8))
        tk.Label(top, text="%s   %s:%d" % (name, ip, self.host_port),
                 bg=BG, fg=GREEN, font=FONT_B).pack(side="left")
        self.clients_lbl = tk.Label(top, text="0 receivers connected",
                                    bg=BG, fg=MUTED, font=FONT)
        self.clients_lbl.pack(side="right")

        main = tk.Frame(self.body, bg=BG)
        main.pack(fill="both", expand=True, padx=20)

        left = tk.Frame(main, bg=BG)
        left.pack(side="left", fill="both", expand=True)
        btns = tk.Frame(left, bg=BG)
        btns.pack(fill="x", pady=(0, 8))
        self.button(btns, "+ Add files", self.add_files, primary=True).pack(side="left")
        self.button(btns, "Remove", self.remove_files).pack(side="left", padx=8)
        self.button(btns, "Clear all", self.clear_files).pack(side="left")
        tk.Label(left, text="Shared files", bg=BG, fg=MUTED, font=FONT_S).pack(anchor="w", pady=(0, 4))
        self.share_tree = self.make_tree(left, ("name", "size"), ("Name", "Size"), (380, 110))

        right = tk.Frame(main, bg=BG, width=230)
        right.pack(side="left", fill="y", padx=(16, 0))
        right.pack_propagate(False)
        tk.Label(right, text="Received from receivers", bg=BG, fg=MUTED,
                 font=FONT_S).pack(anchor="w", pady=(0, 4))
        self.inbox_list = tk.Listbox(right, bg=PANEL, fg=TEXT, selectbackground=ACCENT_DIM,
                                     relief="flat", bd=0, highlightthickness=1,
                                     highlightbackground=BORDER, font=FONT_S)
        self.inbox_list.pack(fill="both", expand=True)
        self.button(right, "Open folder", lambda: self.open_folder(self.inbox_dir)).pack(
            fill="x", pady=(8, 0))

        self.statusbar()
        self.set_status("Hosting as '%s'. Add files to share them." % name, GREEN)
        self.refresh_share_tree()

    def beacon(self, stop, name, port):
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.setsockopt(socket.SOL_SOCKET, socket.SO_BROADCAST, 1)
        msg = json.dumps({"app": APP, "name": name, "port": port}).encode("utf-8")
        targets = broadcast_targets()
        while not stop.is_set():
            for t in targets:
                try:
                    s.sendto(msg, (t, DISCOVERY_PORT))
                except OSError:
                    pass
            stop.wait(BEACON_EVERY)
        s.close()

    def touch_client(self, ip):
        self.clients[ip] = time.time()

    def on_received(self, name, ip):
        self.q.put(lambda: self.add_inbox(name, ip))

    def add_inbox(self, name, ip):
        self.inbox_list.insert(0, "%s  (from %s)" % (name, ip))
        self.set_status("Received %s" % name, GREEN)

    def file_list(self):
        with self.lock:
            return [{"id": fid, "name": it["name"], "size": it["size"]}
                    for fid, it in self.shared.items()]

    def get_shared(self, fid):
        with self.lock:
            it = self.shared.get(fid)
            return dict(it) if it else None

    def add_files(self):
        paths = filedialog.askopenfilenames(parent=self.root, title="Select files to share")
        for p in paths:
            try:
                size = os.path.getsize(p)
            except OSError:
                continue
            fid = uuid.uuid4().hex[:12]
            with self.lock:
                self.shared[fid] = {"name": os.path.basename(p), "path": p, "size": size}
        self.refresh_share_tree()

    def remove_files(self):
        with self.lock:
            for fid in self.share_tree.selection():
                self.shared.pop(fid, None)
        self.refresh_share_tree()

    def clear_files(self):
        with self.lock:
            self.shared.clear()
        self.refresh_share_tree()

    def refresh_share_tree(self):
        self.share_tree.delete(*self.share_tree.get_children())
        for f in self.file_list():
            self.share_tree.insert("", "end", iid=f["id"],
                                   values=(f["name"], human_size(f["size"])))
        count = len(self.file_list())
        self.set_status("%d file(s) shared" % count, GREEN if count else MUTED)

    def open_folder(self, path):
        try:
            os.startfile(path)
        except Exception:
            pass

    # ---------- RECEIVER
    def show_receive(self):
        self.leave_mode()
        self.mode = "receive"
        self.stop = threading.Event()
        self.hosts = {}
        self.remote = None
        self.remote_files = {}
        self.host_keys = []
        self.titlebar("Receive")

        top = tk.Frame(self.body, bg=BG)
        top.pack(fill="x", padx=20, pady=(10, 8))
        self.scan_lbl = tk.Label(top, text="Scanning...", bg=BG, fg=MUTED, font=FONT)
        self.scan_lbl.pack(side="left")
        self.save_lbl = tk.Label(top, text="Save to: " + self.receive_dir, bg=BG, fg=MUTED, font=FONT_S)
        self.save_lbl.pack(side="right")

        main = tk.Frame(self.body, bg=BG)
        main.pack(fill="both", expand=True, padx=20)

        left = tk.Frame(main, bg=BG, width=250)
        left.pack(side="left", fill="y")
        left.pack_propagate(False)
        tk.Label(left, text="Hosts on network", bg=BG, fg=MUTED, font=FONT_S).pack(anchor="w", pady=(0, 4))
        self.host_list = tk.Listbox(left, bg=PANEL, fg=TEXT, selectbackground=ACCENT_DIM,
                                    relief="flat", bd=0, highlightthickness=1,
                                    highlightbackground=BORDER, font=FONT)
        self.host_list.pack(fill="both", expand=True)
        self.host_list.bind("<Double-Button-1>", lambda e: self.connect_selected_host())
        self.button(left, "Connect", self.connect_selected_host, primary=True).pack(fill="x", pady=(8, 0))

        right = tk.Frame(main, bg=BG)
        right.pack(side="left", fill="both", expand=True, padx=(16, 0))
        rbtns = tk.Frame(right, bg=BG)
        rbtns.pack(fill="x", pady=(0, 8))
        self.button(rbtns, "Download", self.download_selected, primary=True).pack(side="left")
        self.button(rbtns, "Refresh", self.refresh_remote).pack(side="left", padx=8)
        self.button(rbtns, "Send to host", self.send_to_host).pack(side="left")
        self.button(rbtns, "Open folder", lambda: self.open_folder(self.receive_dir)).pack(side="right")
        self.button(rbtns, "Save to...", self.choose_save_dir).pack(side="right", padx=8)
        tk.Label(right, text="Files on host (Ctrl-click for several)", bg=BG, fg=MUTED,
                 font=FONT_S).pack(anchor="w", pady=(0, 4))
        self.remote_tree = self.make_tree(right, ("name", "size"), ("Name", "Size"), (330, 100))

        bottom = tk.Frame(self.body, bg=BG)
        bottom.pack(side="bottom", fill="x", padx=20, pady=(0, 2))
        self.progress = ttk.Progressbar(bottom, style="Dark.Horizontal.TProgressbar",
                                        maximum=100, value=0)
        self.progress.pack(fill="x")
        self.statusbar()

        threading.Thread(target=self.listen_hosts, args=(self.stop, self.hosts),
                         daemon=True).start()
        self.set_status("Looking for hosts...")

    def choose_save_dir(self):
        path = filedialog.askdirectory(parent=self.root, title="Choose save folder",
                                       initialdir=self.receive_dir)
        if path:
            self.receive_dir = path
            self.save_lbl.config(text="Save to: " + path)
            self.set_status("Save folder set.", GREEN)

    def listen_hosts(self, stop, hosts):
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        try:
            s.bind(("", DISCOVERY_PORT))
        except OSError:
            self.q.put(lambda: self.set_status("Discovery port busy. Close other LanShare windows.", RED))
            s.close()
            return
        s.settimeout(1.0)
        while not stop.is_set():
            try:
                data, addr = s.recvfrom(2048)
                info = json.loads(data.decode("utf-8"))
                if info.get("app") == APP:
                    port = int(info.get("port", 0))
                    key = "%s:%d" % (addr[0], port)
                    hosts[key] = {
                        "name": str(info.get("name", "Host")),
                        "ip": addr[0],
                        "port": port,
                        "seen": time.time(),
                    }
                    self.q.put(self.refresh_hosts)
            except socket.timeout:
                pass
            except (ValueError, OSError):
                time.sleep(0.2)
            now = time.time()
            stale = [k for k, h in list(hosts.items()) if now - h["seen"] > HOST_TIMEOUT]
            if stale:
                for k in stale:
                    hosts.pop(k, None)
                self.q.put(self.refresh_hosts)
        s.close()

    def refresh_hosts(self):
        if self.mode != "receive":
            return
        items = list(self.hosts.values())
        self.host_list.delete(0, "end")
        self.host_keys = []
        for h in sorted(items, key=lambda x: (x["name"].lower(), x["ip"], x["port"])):
            self.host_list.insert("end", "  %s   (%s:%d)" % (h["name"], h["ip"], h["port"]))
            self.host_keys.append("%s:%d" % (h["ip"], h["port"]))
        self.scan_lbl.config(text=("%d host(s) found" % len(items)) if items else "Scanning...")

    def connect_selected_host(self):
        sel = self.host_list.curselection()
        if not sel:
            return
        key = self.host_keys[sel[0]]
        h = self.hosts.get(key)
        if h:
            self.connect_host(h["ip"], h["port"], h["name"])

    def connect_host(self, ip, port, name=""):
        self.set_status("Connecting to %s..." % (name or ip))
        url = "http://%s:%d/api/info" % (ip, port)

        def work():
            try:
                with urllib.request.urlopen(url, timeout=5) as r:
                    data = json.loads(r.read().decode("utf-8"))
                self.q.put(lambda: self.show_remote(ip, port, data))
            except Exception as ex:
                msg = str(ex)
                self.q.put(lambda: self.set_status("Connect failed: " + msg, RED))

        threading.Thread(target=work, daemon=True).start()

    def show_remote(self, ip, port, data):
        name = data.get("name", ip)
        self.remote = (ip, port, name)
        files = data.get("files", [])
        self.remote_files = {f["id"]: f for f in files}
        self.remote_tree.delete(*self.remote_tree.get_children())
        for f in files:
            self.remote_tree.insert("", "end", iid=f["id"],
                                    values=(f["name"], human_size(f["size"])))
        self.set_status("Connected to '%s'. %d file(s)." % (name, len(files)), GREEN)

    def refresh_remote(self):
        if self.remote:
            ip, port, name = self.remote
            self.connect_host(ip, port, name)
        else:
            self.set_status("Connect to a host first.", RED)

    def download_selected(self):
        if not self.remote:
            self.set_status("Connect to a host first.", RED)
            return
        fids = list(self.remote_tree.selection())
        if not fids:
            self.set_status("Select file(s) to download.", RED)
            return
        ip, port, _ = self.remote
        jobs = [(fid, dict(self.remote_files[fid])) for fid in fids if fid in self.remote_files]

        def work():
            total = len(jobs)
            for i, (fid, item) in enumerate(jobs, 1):
                url = "http://%s:%d/file/%s" % (ip, port, fid)
                dest = unique_path(self.receive_dir, safe_name(item["name"]))
                self.q.put(lambda t=i, n=total, nm=item["name"]:
                           self.set_status("Downloading %d/%d: %s" % (t, n, nm), ACCENT))
                try:
                    with urllib.request.urlopen(url, timeout=30) as r:
                        length = int(r.headers.get("Content-Length", 0) or item["size"] or 0)
                        done = 0
                        with open(dest, "wb") as f:
                            while True:
                                chunk = r.read(CHUNK)
                                if not chunk:
                                    break
                                f.write(chunk)
                                done += len(chunk)
                                if length:
                                    pct = done * 100.0 / length
                                    self.q.put(lambda p=pct: self.progress.config(value=p))
                    self.q.put(lambda p=dest: self.set_status("Saved " + os.path.basename(p), GREEN))
                except Exception as ex:
                    msg = str(ex)
                    self.q.put(lambda m=msg: self.set_status("Download failed: " + m, RED))
                    return
            self.q.put(lambda: self.progress.config(value=0))
            self.q.put(lambda: self.set_status("Saved to " + self.receive_dir, GREEN))

        threading.Thread(target=work, daemon=True).start()

    def send_to_host(self):
        if not self.remote:
            self.set_status("Connect to a host first.", RED)
            return
        path = filedialog.askopenfilename(parent=self.root, title="Select file to send")
        if not path:
            return
        ip, port, _ = self.remote
        name = os.path.basename(path)

        def work():
            self.q.put(lambda: self.set_status("Sending " + name + "...", ACCENT))
            try:
                size = os.path.getsize(path)
                conn = http.client.HTTPConnection(ip, port, timeout=60)
                with open(path, "rb") as f:
                    conn.request("POST", "/upload?name=" + urllib.parse.quote(name), body=f,
                                 headers={"Content-Length": str(size)})
                resp = conn.getresponse()
                resp.read()
                conn.close()
                if resp.status == 200:
                    self.q.put(lambda: self.set_status("Sent " + name, GREEN))
                else:
                    self.q.put(lambda: self.set_status("Send failed (%d)" % resp.status, RED))
            except Exception as ex:
                msg = str(ex)
                self.q.put(lambda m=msg: self.set_status("Send failed: " + m, RED))

        threading.Thread(target=work, daemon=True).start()

    # ---------- event loop
    def poll(self):
        try:
            while True:
                fn = self.q.get_nowait()
                try:
                    fn()
                except Exception:
                    pass
        except queue.Empty:
            pass

        if self.mode == "host" and hasattr(self, "clients_lbl"):
            try:
                now = time.time()
                active = [ip for ip, t in list(self.clients.items()) if now - t < CLIENT_TIMEOUT]
                n = len(active)
                self.clients_lbl.config(text="%d receiver%s connected" % (n, "" if n == 1 else "s"))
            except tk.TclError:
                pass

        self.root.after(120, self.poll)


if __name__ == "__main__":
    LanShare()
