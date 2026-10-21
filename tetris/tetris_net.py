"""
Сетевая часть тетриса: прямое соединение двух компьютеров без сервера.

Работает в одной локальной сети (Wi-Fi / роутер) и через интернет, если оба игрока
в одной виртуальной сети — Radmin VPN, ZeroTier, Tailscale и т. п.

Сообщения — JSON, по одному в строке. Сокеты неблокирующие: игра раз в кадр
вызывает pump() и получает пришедшие сообщения, поэтому отдельные потоки не нужны.
"""
import ipaddress
import json
import re
import select
import socket
import subprocess
import sys
import time

DEFAULT_PORT = 47474
PROTOCOL_VERSION = 1
CONNECT_TIMEOUT = 7.0
MAX_BUFFER = 1 << 20


class Connection:
    def __init__(self, sock):
        sock.setblocking(False)
        try:
            sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        except OSError:
            pass
        self.sock = sock
        self.inbox = b""
        self.outbox = b""
        self.closed = False
        self.last_recv = time.time()

    def send(self, msg):
        if not self.closed:
            self.outbox += (json.dumps(msg, ensure_ascii=False, separators=(",", ":")) + "\n").encode("utf-8")
            if len(self.outbox) > MAX_BUFFER:     # соперник не читает — связь фактически потеряна
                self.close()

    def pump(self):
        """Отправить накопленное и забрать пришедшее. Возвращает список сообщений (dict)."""
        if self.closed:
            return []
        try:
            while self.outbox:
                sent = self.sock.send(self.outbox)
                if not sent:
                    break
                self.outbox = self.outbox[sent:]
        except (BlockingIOError, InterruptedError):
            pass
        except OSError:
            self.close()
            return []
        while True:
            try:
                data = self.sock.recv(65536)
            except (BlockingIOError, InterruptedError):
                break
            except OSError:
                self.close()
                break
            if not data:
                self.close()
                break
            self.inbox += data
            self.last_recv = time.time()
        messages = []
        while b"\n" in self.inbox:
            line, self.inbox = self.inbox.split(b"\n", 1)
            try:
                msg = json.loads(line.decode("utf-8"))
            except ValueError:
                continue
            if isinstance(msg, dict):
                messages.append(msg)
        if len(self.inbox) > MAX_BUFFER:
            self.close()
        return messages

    def flush(self, timeout=0.3):
        """Дослать остаток перед закрытием (например, прощальное сообщение)."""
        end = time.time() + timeout
        while self.outbox and not self.closed and time.time() < end:
            self.pump()
            time.sleep(0.01)

    def close(self):
        if not self.closed:
            self.closed = True
            try:
                self.sock.close()
            except OSError:
                pass


class Listener:
    """Ожидание входящего подключения (тот, кто «создал игру»)."""

    def __init__(self, port=DEFAULT_PORT):
        self.port = port
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        try:
            self.sock.bind(("", port))
            self.sock.listen(1)
            self.sock.setblocking(False)
        except OSError:
            self.sock.close()
            raise

    def accept(self):
        try:
            sock, addr = self.sock.accept()
        except (BlockingIOError, InterruptedError):
            return None
        except OSError:
            return None
        return Connection(sock), addr[0]

    def close(self):
        try:
            self.sock.close()
        except OSError:
            pass


class Connector:
    """Неблокирующее подключение к сопернику: poll() раз в кадр, пока не вернёт результат."""

    def __init__(self, address):
        self.error = None
        self.sock = None
        self.started = time.time()
        host, port = parse_address(address)
        try:
            ip = socket.getaddrinfo(host, port, socket.AF_INET, socket.SOCK_STREAM)[0][4][0]
        except (OSError, IndexError):
            self.error = "Адрес не найден: {}".format(host)
            return
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.setblocking(False)
        code = self.sock.connect_ex((ip, port))
        if code not in (0, 10035, 115, 36, 114):  # 0, WSAEWOULDBLOCK, EINPROGRESS (Linux/macOS), EALREADY
            self.fail("Не удалось подключиться (код {})".format(code))

    def fail(self, text):
        self.error = text
        if self.sock:
            self.sock.close()
            self.sock = None

    def poll(self):
        """None — ещё подключаемся; Connection — готово; "error" — см. self.error."""
        if self.error:
            return "error"
        try:
            _, writable, failed = select.select([], [self.sock], [self.sock], 0)
        except OSError:
            self.fail("Ошибка сети")
            return "error"
        if failed or writable:
            err = self.sock.getsockopt(socket.SOL_SOCKET, socket.SO_ERROR)
            if failed or err:
                self.fail("Соперник не отвечает. Проверьте адрес и что он нажал «Создать игру»")
                return "error"
            sock, self.sock = self.sock, None
            return Connection(sock)
        if time.time() - self.started > CONNECT_TIMEOUT:
            self.fail("Время ожидания вышло. Проверьте адрес, сеть и брандмауэр")
            return "error"
        return None

    def cancel(self):
        if self.sock:
            self.sock.close()
            self.sock = None


def parse_address(text):
    text = text.strip()
    host, port = text, DEFAULT_PORT
    if text.count(":") == 1:
        host, _, p = text.partition(":")
        if p.isdigit() and 0 < int(p) < 65536:
            port = int(p)
    return host.strip(), port


def describe(ip):
    """Подсказка, что это за адрес."""
    a = ipaddress.ip_address(ip)
    if ip.startswith("26."):
        return "Radmin VPN"
    if ip.startswith("25."):
        return "Hamachi"
    if a in ipaddress.ip_network("100.64.0.0/10"):
        return "Tailscale"
    if a.is_private:
        return "локальная сеть или ZeroTier"
    return "интернет"


def _windows_adapters():
    """[(ip, заголовок адаптера)] из ipconfig — по названию адаптера видно, где VPN, а где Wi-Fi."""
    flags = getattr(subprocess, "CREATE_NO_WINDOW", 0x08000000)   # без мелькающего окна консоли
    out = subprocess.run(["ipconfig"], capture_output=True, timeout=3, creationflags=flags).stdout
    text = out.decode("oem", "replace")
    result, header = [], ""
    for line in text.splitlines():
        if line and not line[0].isspace() and line.rstrip().endswith(":"):
            header = line.rstrip()[:-1]
            continue
        m = re.search(r"IPv4[^:]*:\s*(\d+\.\d+\.\d+\.\d+)", line)
        if m:
            result.append((m.group(1), header))
    return result


VIRTUAL_WORDS = ("vethernet", "wsl", "hyper-v", "virtualbox", "vmware", "docker", "loopback")


def classify(ip, header=""):
    """(подпись, порядок): сначала VPN для игры через интернет, потом домашняя сеть, в конце прочее."""
    h = header.lower()
    if "radmin" in h or ip.startswith("26."):
        return "Radmin VPN", 0
    if "zerotier" in h:
        return "ZeroTier", 0
    if "tailscale" in h or ipaddress.ip_address(ip) in ipaddress.ip_network("100.64.0.0/10"):
        return "Tailscale", 0
    if "hamachi" in h or ip.startswith("25."):
        return "Hamachi", 0
    if not header:
        return describe(ip), 1
    if any(word in h for word in VIRTUAL_WORDS):
        return "виртуальный адаптер", 3
    if any(word in h for word in ("беспровод", "wireless", "wi-fi", "wlan")):
        return "Wi-Fi", 1
    if "ethernet" in h:
        return "кабель / роутер", 1
    return "другой адаптер (VPN или прокси?)", 2


def local_addresses():
    """IPv4-адреса этого компьютера во всех сетях (Wi-Fi, кабель, VPN) с подписями."""
    found = []
    if sys.platform == "win32":
        try:
            found = _windows_adapters()
        except (OSError, subprocess.SubprocessError, ValueError):
            found = []
    if not found:
        try:
            found = [(info[4][0], "") for info in socket.getaddrinfo(socket.gethostname(), None, socket.AF_INET)]
        except OSError:
            pass
        try:
            # адрес, через который идёт выход в сеть (пакет при этом не отправляется)
            probe = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            probe.connect(("8.8.8.8", 80))
            found.insert(0, (probe.getsockname()[0], ""))
            probe.close()
        except OSError:
            pass
    result, seen = [], set()
    for ip, header in found:
        if ip in seen or ip.startswith("127.") or ip.startswith("169.254.") or ip == "0.0.0.0":
            continue
        seen.add(ip)
        result.append((ip,) + classify(ip, header))
    result.sort(key=lambda item: item[2])
    return [(ip, label) for ip, label, _ in result]
