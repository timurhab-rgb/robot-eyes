import time
import random
import framebuf
import socket
import network
import gc
import machine
from machine import I2C, Pin

try:
    from math import isqrt
except ImportError:
    def isqrt(n):
        return int(n ** 0.5)

try:
    from machine import ADC
except ImportError:
    ADC = None


# ================================
# Wi-Fi
# ================================
WIFI_NETWORKS = (
    ("Knokey_WiFi", "Qwerty12345"),
    ("Beeline_2G_F26159", "sGRpKQqQ"),
    ("iPhone (Диана)", "diana188"),
    ("Vertikal463_2.4G", "18071712"),
)

last_good_ssid = None


# ================================
# MQTT
# ================================
MQTT_BROKER = "broker.emqx.io"
MQTT_PORT = 1883

# SECRET должен быть одинаковым в main.py и index.html.
SECRET = "r3b0t-3y3s-7f2a91c4d8e6b0a35c7d9e1f2a4b6c8d"

MQTT_CMD_TOPIC = ("robot-eyes/" + SECRET + "/cmd").encode()
MQTT_IMAGE_TOPIC = ("robot-eyes/" + SECRET + "/image").encode()
MQTT_STATUS_TOPIC = ("robot-eyes/" + SECRET + "/status").encode()

MQTT_KEEPALIVE = 60
HEARTBEAT_INTERVAL = 8000


# ================================
# Батарея
# ================================
BATTERY_ENABLED = True
BATTERY_ADC_PIN = 2
BATTERY_DIVIDER = 2.0
BATTERY_EMPTY_MV = 3300
BATTERY_FULL_MV = 3800
BATTERY_SAMPLE_INTERVAL = 5000


# ================================
# Поведение робота
# ================================
EMOTION_DURATION = 3000
SURPRISE_BEFORE_IMAGE_DURATION = 2000
CUSTOM_IMAGE_DURATION = 60000

# Если нет контакта 3 часа, робот начинает грустить.
IDLE_SAD_AFTER = 3 * 60 * 60 * 1000

# После начала авто-грусти повторять её каждые 30 секунд.
AUTO_SAD_INTERVAL = 30000

# Контактные эмоции. laughter/anger оставлены для совместимости со старым сайтом.
CONTACT_EMOTIONS = (
    "hug",
    "tickle",
    "laughter",
    "anger"
)

ALLOWED_EMOTIONS = (
    "hug",
    "tickle",
    "sadness",
    "surprise",
    "laughter",
    "anger"
)


# ================================
# Железо
# ================================
SDA_PIN = 7
SCL_PIN = 6
I2C_ADDR = 0x3C

BOOT_PIN = 9
BOOT_ACTIVE_LOW = True

WIDTH = 128
HEIGHT = 64


# ================================
# Глобальные состояния
# ================================
wlan = None
mqtt_client = None
next_mqtt_try = 0
last_heartbeat = 0
last_mqtt_lost = 0

battery_adc = None
last_battery_sample = 0
battery_percent = -1

last_interaction = 0
last_auto_sad = 0

pending_emotion = None
current_emotion = None
emotion_start = 0
emotion_duration = EMOTION_DURATION

custom_image_buffer = bytearray(1024)
custom_image_until = 0
custom_image_pending = False
pending_image_after = False
custom_image_shown = False

left_eye = None
right_eye = None
gaze = None
next_blink = None


# ================================
# Base64 decode directly into buffer
# ================================
_B64_CHARS = b"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
B64_INV = [255] * 256
for _i, _c in enumerate(_B64_CHARS):
    B64_INV[_c] = _i


def b64_decode_into(src, start, length, dst, dst_size):
    out = 0
    acc = 0
    bits = 0

    end = start + length
    i = start

    while i < end:
        c = src[i]
        i += 1

        if c == 61:  # '='
            break

        if c <= 32:  # whitespace
            continue

        v = B64_INV[c]
        if v == 255:
            return -1

        acc = (acc << 6) | v
        bits += 6

        if bits >= 8:
            bits -= 8
            if out >= dst_size:
                return -1

            dst[out] = (acc >> bits) & 0xFF
            out += 1

            if bits:
                acc &= (1 << bits) - 1
            else:
                acc = 0

    if out != dst_size:
        return -1

    return out


EMOTION_BYTES = (
    (b"hug", "hug"),
    (b"tickle", "tickle"),
    (b"sadness", "sadness"),
    (b"surprise", "surprise"),
    (b"laughter", "laughter"),
    (b"anger", "anger"),
)


# ================================
# Взаимодействие / рисунок
# ================================
def touch_interaction():
    global last_interaction, last_auto_sad
    now = time.ticks_ms()
    last_interaction = now
    last_auto_sad = now


def cancel_custom_image():
    global custom_image_until, custom_image_pending
    global pending_image_after, custom_image_shown

    custom_image_until = 0
    custom_image_pending = False
    pending_image_after = False
    custom_image_shown = False


# ================================
# Минимальный MQTT-клиент с фиксированным буфером
# ================================
class MinimalMQTT:
    RX_SIZE = 4096

    def __init__(self, client_id, host, port=1883, keepalive=60):
        self.client_id = client_id
        self.host = host
        self.port = port
        self.keepalive = keepalive

        self.sock = None
        self.connected = False

        self.rx = bytearray(self.RX_SIZE)
        self.rx_len = 0
        self.parse_pos = 0

        self.pid = 1
        self.last_ping = 0
        self.last_rx = 0

        self.awaiting_ping = False
        self.ping_sent_at = 0
        self.ping_timeout_ms = 20000
        self.missed_pings = 0

    @staticmethod
    def _enc_str(data):
        if isinstance(data, str):
            data = data.encode()
        length = len(data)
        return bytes((length >> 8, length & 0xFF)) + data

    @staticmethod
    def _rem_len(length):
        out = bytearray()
        while True:
            digit = length % 128
            length //= 128
            if length > 0:
                digit |= 0x80
            out.append(digit)
            if length == 0:
                break
        return bytes(out)

    @classmethod
    def _build_packet(cls, cmd, payload):
        return bytes((cmd,)) + cls._rem_len(len(payload)) + payload

    def _reset_rx(self):
        self.rx_len = 0
        self.parse_pos = 0

    def _compact_rx(self):
        remaining = self.rx_len - self.parse_pos

        if remaining <= 0:
            self.rx_len = 0
            self.parse_pos = 0
            return

        if self.parse_pos == 0:
            return

        for i in range(remaining - 1, -1, -1):
            self.rx[i] = self.rx[self.parse_pos + i]

        self.rx_len = remaining
        self.parse_pos = 0

    def _feed(self, data):
        ln = len(data)
        if ln == 0:
            return

        if self.rx_len + ln > self.RX_SIZE:
            self._compact_rx()

        if self.rx_len + ln > self.RX_SIZE:
            self._reset_rx()
            raise OSError("MQTT rx overflow")

        for i in range(ln):
            self.rx[self.rx_len + i] = data[i]

        self.rx_len += ln

    def _decode_remaining_length_at(self, pos):
        multiplier = 1
        value = 0

        while True:
            if pos >= self.rx_len:
                raise IndexError("incomplete remaining length")

            encoded_byte = self.rx[pos]
            pos += 1

            value += (encoded_byte & 0x7F) * multiplier

            if (encoded_byte & 0x80) == 0:
                break

            multiplier *= 128
            if multiplier > 128 * 128 * 128:
                raise ValueError("malformed remaining length")

        return value, pos

    def _next_pid(self):
        self.pid += 1
        if self.pid > 65535:
            self.pid = 1
        return self.pid

    def _recv_exact(self, n):
        if self.sock is None:
            raise OSError("MQTT socket is None")

        buf = bytearray()
        self.sock.settimeout(8)

        while len(buf) < n:
            chunk = self.sock.recv(n - len(buf))
            if not chunk:
                raise OSError("MQTT connection closed")
            buf.extend(chunk)

        return bytes(buf)

    def _is_timeout(self, exc):
        try:
            code = exc.args[0]
            if code in (11, 10035, 110, 116):
                return True
        except Exception:
            pass

        text = str(exc).lower()
        return "timed out" in text or "timeout" in text

    def _send(self, packet):
        if self.sock is None:
            raise OSError("MQTT socket is None")

        try:
            self.sock.settimeout(2)
        except Exception:
            pass

        self.sock.sendall(packet)

        try:
            self.sock.settimeout(0.02)
        except Exception:
            pass

    def _topic_is(self, start, length, expected):
        if length != len(expected):
            return False

        rx = self.rx
        for i in range(length):
            if rx[start + i] != expected[i]:
                return False

        return True

    def _match_emotion(self, start, length):
        rx = self.rx

        for eb, name in EMOTION_BYTES:
            if length != len(eb):
                continue

            ok = True
            for i in range(length):
                if rx[start + i] != eb[i]:
                    ok = False
                    break

            if ok:
                return name

        return None

    def _handle_publish_at(self, hdr_end, rem_len, qos):
        global pending_emotion
        global custom_image_pending, pending_image_after

        rx = self.rx

        if rem_len < 2:
            return

        topic_len = (rx[hdr_end] << 8) | rx[hdr_end + 1]
        topic_start = hdr_end + 2
        pos = topic_start + topic_len

        pid = None
        if qos > 0:
            if pos + 2 > hdr_end + rem_len:
                return
            pid = (rx[pos] << 8) | rx[pos + 1]
            pos += 2

        payload_start = pos
        payload_end = hdr_end + rem_len
        payload_len = payload_end - payload_start

        if payload_len < 0:
            return

        if self._topic_is(topic_start, topic_len, MQTT_CMD_TOPIC):
            emotion = self._match_emotion(payload_start, payload_len)
            if emotion is not None:
                touch_interaction()

                # Любая команда, кроме специально запланированного surprise перед рисунком,
                # отменяет текущий/ожидающий рисунок.
                if not (emotion == "surprise" and custom_image_pending and pending_image_after):
                    cancel_custom_image()

                pending_emotion = emotion
                print("MQTT emotion received:", emotion)

        elif self._topic_is(topic_start, topic_len, MQTT_IMAGE_TOPIC):
            decoded = b64_decode_into(
                rx,
                payload_start,
                payload_len,
                custom_image_buffer,
                1024
            )

            if decoded == 1024:
                touch_interaction()
                cancel_custom_image()

                custom_image_pending = True
                pending_image_after = True
                pending_emotion = "surprise"
                print("Custom image queued, surprise first")
            else:
                print("Image decode error, decoded:", decoded)

        # Подтверждаем QoS 1, чтобы брокер не переотправлял сообщение бесконечно.
        if qos == 1 and pid is not None:
            try:
                puback = self._build_packet(0x40, bytes((pid >> 8, pid & 0xFF)))
                self._send(puback)
            except Exception as exc:
                print("MQTT PUBACK error:", exc)

    def _process_rx(self):
        while True:
            if self.parse_pos >= self.rx_len:
                self._compact_rx()
                return

            if self.rx_len - self.parse_pos < 2:
                return

            fixed = self.rx[self.parse_pos]
            pkt_type = fixed >> 4
            qos = (fixed >> 1) & 0x03

            try:
                rem_len, hdr_end = self._decode_remaining_length_at(self.parse_pos + 1)
            except IndexError:
                return
            except ValueError:
                self._reset_rx()
                raise OSError("MQTT malformed packet")

            end = hdr_end + rem_len

            if self.rx_len < end:
                return

            if pkt_type == 3:
                self._handle_publish_at(hdr_end, rem_len, qos)
            elif pkt_type == 13:
                # PINGRESP
                self.awaiting_ping = False
                self.missed_pings = 0
            elif pkt_type == 9:
                # SUBACK
                pass

            self.parse_pos = end

            if self.parse_pos > 1024:
                self._compact_rx()

    def connect(self):
        self.disconnect()

        info = socket.getaddrinfo(
            self.host,
            self.port,
            socket.AF_INET,
            socket.SOCK_STREAM
        )[0][-1]

        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.settimeout(8)
        self.sock.connect(info)

        keepalive = bytes((
            (self.keepalive >> 8) & 0xFF,
            self.keepalive & 0xFF
        ))

        # MQTT 3.1.1, clean session = true
        variable_header = (
            b"\x00\x04MQTT" +
            b"\x04" +
            b"\x02" +
            keepalive
        )

        payload = self._enc_str(self.client_id)
        packet = self._build_packet(0x10, variable_header + payload)

        self.sock.sendall(packet)

        ack = self._recv_exact(4)

        if ack[0] != 0x20:
            raise OSError("MQTT bad CONNACK type")

        if ack[1] != 0x02:
            raise OSError("MQTT bad CONNACK length")

        if ack[3] != 0x00:
            raise OSError("MQTT CONNACK refused, code=%d" % ack[3])

        now = time.ticks_ms()

        self.connected = True
        self._reset_rx()
        self.last_rx = now
        self.last_ping = now
        self.awaiting_ping = False
        self.ping_sent_at = 0
        self.missed_pings = 0

        try:
            self.sock.settimeout(0.02)
        except Exception:
            pass

    def subscribe(self, topic):
        if not self.connected:
            raise OSError("MQTT not connected")

        pid = self._next_pid()

        variable_header = (
            bytes((pid >> 8, pid & 0xFF)) +
            self._enc_str(topic) +
            b"\x00"
        )

        packet = self._build_packet(0x82, variable_header)
        self._send(packet)

    def publish(self, topic, msg):
        if not self.connected:
            raise OSError("MQTT not connected")

        if isinstance(msg, str):
            msg = msg.encode()

        variable_header = self._enc_str(topic)
        packet = self._build_packet(0x30, variable_header + msg)
        self._send(packet)

    def ping(self):
        if not self.connected:
            raise OSError("MQTT not connected")

        packet = self._build_packet(0xC0, b"")
        self._send(packet)

    def check_msg(self):
        if not self.connected:
            raise OSError("MQTT not connected")

        if self.sock is None:
            self.connected = False
            raise OSError("MQTT socket is None")

        now = time.ticks_ms()

        # Если ждём PINGRESP и он не пришёл — не рвём соединение сразу,
        # а позволяем брокеру немного тормозить.
        if self.awaiting_ping:
            if time.ticks_diff(now, self.ping_sent_at) > self.ping_timeout_ms:
                self.awaiting_ping = False
                self.missed_pings += 1
                print("MQTT missed ping:", self.missed_pings)

                # Два пропущенных пинга подряд — reconnect.
                if self.missed_pings >= 2:
                    self.connected = False
                    raise OSError("MQTT ping timeout")

        # Общий timeout по входящим данным.
        rx_timeout = self.keepalive * 1000 + self.ping_timeout_ms + 20000
        if time.ticks_diff(now, self.last_rx) > rx_timeout:
            self.connected = False
            raise OSError("MQTT rx timeout")

        try:
            self.sock.settimeout(0.02)
        except Exception:
            self.connected = False
            raise OSError("MQTT socket timeout set failed")

        try:
            data = self.sock.recv(256)
        except OSError as exc:
            if self._is_timeout(exc):
                data = None
            else:
                self.connected = False
                raise

        if data:
            self.last_rx = time.ticks_ms()
            self.awaiting_ping = False
            self.missed_pings = 0
            self._feed(data)
            self._process_rx()
        elif data == b"":
            self.connected = False
            raise OSError("MQTT connection closed by broker")

        now = time.ticks_ms()

        # Пингуемся реже: при keepalive=60 это примерно раз в 30 секунд.
        ping_interval = max(15000, self.keepalive * 1000 // 2)

        if time.ticks_diff(now, self.last_ping) > ping_interval:
            self.ping()
            self.last_ping = now
            self.awaiting_ping = True
            self.ping_sent_at = now

    def disconnect(self):
        try:
            if self.connected and self.sock is not None:
                self.sock.settimeout(1)
                self.sock.sendall(self._build_packet(0xE0, b""))
        except Exception:
            pass

        try:
            if self.sock is not None:
                self.sock.close()
        except Exception:
            pass

        self.connected = False
        self.sock = None
        self._reset_rx()
        self.awaiting_ping = False
        self.missed_pings = 0

        try:
            gc.collect()
        except Exception:
            pass


# ================================
# Wi-Fi
# ================================
def _decode_ssid(raw):
    if isinstance(raw, bytes):
        try:
            return raw.decode()
        except Exception:
            try:
                return raw.decode("latin1")
            except Exception:
                return str(raw)

    return str(raw)


def _ssid_to_bytes(ssid):
    if isinstance(ssid, bytes):
        return ssid

    try:
        return ssid.encode()
    except Exception:
        return ssid.encode("utf-8")


def configure_wifi_power(wlan_obj):
    values = []

    for obj in (wlan_obj, network):
        for name in ("POWER_NONE", "PM_NONE", "POWER_MODEM_NONE"):
            val = getattr(obj, name, None)
            if val is not None:
                values.append(val)

    values.append(0)

    for val in values:
        for key in ("pm", "power_save"):
            try:
                wlan_obj.config(**{key: val})
                print("WiFi power save disabled:", key, val)
                return
            except Exception:
                pass


def _configured_network_candidates():
    known = {}

    for ssid, password in WIFI_NETWORKS:
        known[ssid] = (password, _ssid_to_bytes(ssid))

    best = {}

    try:
        scans = wlan.scan()
    except Exception as exc:
        print("WiFi scan error:", exc)
        scans = []

    if scans:
        for net in scans:
            try:
                raw_ssid = net[0]
                rssi = net[3]
            except Exception:
                continue

            ssid = _decode_ssid(raw_ssid)

            if ssid not in known:
                continue

            password, _ = known[ssid]
            prev = best.get(ssid)

            if prev is None or rssi > prev[0]:
                best[ssid] = (rssi, raw_ssid, password)

    candidates = []

    for ssid, item in best.items():
        rssi, raw_ssid, password = item
        candidates.append((rssi, raw_ssid, ssid, password))

    # Сортируем по уровню сигнала: сначала самые сильные сети.
    candidates.sort(key=lambda item: item[0], reverse=True)

    # Если ранее успешно подключались к какой-то сети, пробуем её первой.
    if last_good_ssid is not None:
        for idx, item in enumerate(candidates):
            if item[2] == last_good_ssid:
                candidates.insert(0, candidates.pop(idx))
                break

    # Если сканирование ничего не нашло, всё равно пробуем все известные сети.
    if not candidates:
        for ssid, password in WIFI_NETWORKS:
            candidates.append((-999, _ssid_to_bytes(ssid), ssid, password))

    return candidates


def connect_wifi():
    global wlan, last_good_ssid

    if wlan is None:
        wlan = network.WLAN(network.STA_IF)

    wlan.active(True)
    configure_wifi_power(wlan)

    time.sleep_ms(200)

    if wlan.isconnected():
        ip = wlan.ifconfig()[0]
        print("WiFi already connected:", ip)
        return ip

    candidates = _configured_network_candidates()

    for rssi, connect_ssid, display_ssid, password in candidates:
        print("Trying WiFi:", display_ssid, "RSSI:", rssi)

        try:
            wlan.disconnect()
        except Exception:
            pass

        time.sleep_ms(200)

        try:
            wlan.connect(connect_ssid, password)
        except Exception as exc:
            print("Connect start error:", display_ssid, exc)
            continue

        # Ждём подключения до 12 секунд.
        for _ in range(24):
            if wlan.isconnected():
                break
            time.sleep_ms(500)

        if wlan.isconnected():
            configure_wifi_power(wlan)
            last_good_ssid = display_ssid
            ip = wlan.ifconfig()[0]
            print("WiFi OK:", display_ssid, "IP:", ip)
            return ip

        print("WiFi failed:", display_ssid)

    raise OSError("No configured WiFi network connected")


def ensure_wifi():
    global wlan

    if wlan is None:
        return connect_wifi()

    if not wlan.isconnected():
        print("WiFi lost, reconnecting...")

        try:
            wlan.disconnect()
        except Exception:
            pass

        time.sleep_ms(500)
        return connect_wifi()

    return wlan.ifconfig()[0]


# ================================
# Батарея
# ================================
def init_battery_adc():
    global battery_adc

    if not BATTERY_ENABLED or ADC is None:
        battery_adc = None
        return

    try:
        battery_adc = ADC(Pin(BATTERY_ADC_PIN))

        try:
            battery_adc.atten(ADC.ATTN_11DB)
        except Exception:
            try:
                battery_adc.atten(3)
            except Exception:
                pass

        try:
            battery_adc.width(ADC.BITS_12)
        except Exception:
            try:
                battery_adc.width(12)
            except Exception:
                pass

        print("Battery ADC initialized on GPIO", BATTERY_ADC_PIN)
    except Exception as exc:
        print("Battery ADC init error:", exc)
        battery_adc = None


def read_battery_percent():
    global battery_percent

    if not BATTERY_ENABLED or battery_adc is None:
        battery_percent = -1
        return battery_percent

    try:
        raw = battery_adc.read()

        if raw > 4095:
            raw = 4095

        mv = (raw * 3300) // 4095
        batt_mv = int(mv * BATTERY_DIVIDER)

        span = BATTERY_FULL_MV - BATTERY_EMPTY_MV
        if span <= 0:
            pct = 0
        else:
            pct = ((batt_mv - BATTERY_EMPTY_MV) * 100) // span

        if pct < 0:
            pct = 0
        if pct > 100:
            pct = 100

        if battery_percent < 0:
            battery_percent = pct
        else:
            battery_percent = (battery_percent * 3 + pct) // 4

    except Exception as exc:
        print("Battery read error:", exc)
        battery_percent = -1

    return battery_percent


# ================================
# MQTT status / connect / poll
# ================================
def publish_status():
    if mqtt_client is None or not mqtt_client.connected:
        return

    try:
        now = time.ticks_ms()
        idle_ms = time.ticks_diff(now, last_interaction)
        if idle_ms < 0:
            idle_ms = 0
        idle_s = idle_ms // 1000

        payload = "online;battery=%d;idle=%d" % (battery_percent, idle_s)
        mqtt_client.publish(MQTT_STATUS_TOPIC, payload.encode())
    except Exception as exc:
        print("Status publish error:", exc)


def try_connect_mqtt():
    global mqtt_client, last_heartbeat, last_mqtt_lost

    if mqtt_client is not None:
        if mqtt_client.connected:
            last_mqtt_lost = 0
            return True

        try:
            mqtt_client.disconnect()
        except Exception:
            pass

        mqtt_client = None

    try:
        ensure_wifi()

        client_id = ("esp32c3-eyes-%08x" % random.getrandbits(32)).encode()

        client = MinimalMQTT(
            client_id,
            MQTT_BROKER,
            port=MQTT_PORT,
            keepalive=MQTT_KEEPALIVE
        )

        try:
            client.connect()
            client.subscribe(MQTT_CMD_TOPIC)
            client.subscribe(MQTT_IMAGE_TOPIC)

            try:
                publish_status()
            except Exception as exc:
                print("Initial status publish error:", exc)

        except Exception:
            try:
                client.disconnect()
            except Exception:
                pass
            raise

        mqtt_client = client
        last_heartbeat = time.ticks_ms()
        last_mqtt_lost = 0

        print("MQTT connected")
        print("Command topic:", MQTT_CMD_TOPIC.decode())
        print("Image topic:", MQTT_IMAGE_TOPIC.decode())
        print("Status topic:", MQTT_STATUS_TOPIC.decode())
        return True

    except Exception as exc:
        print("MQTT connect error:", exc)

        if mqtt_client is not None:
            try:
                mqtt_client.disconnect()
            except Exception:
                pass

        mqtt_client = None
        last_heartbeat = 0

        if last_mqtt_lost == 0:
            last_mqtt_lost = time.ticks_ms()

        return False


def mqtt_poll(now):
    global mqtt_client, next_mqtt_try, last_heartbeat, last_mqtt_lost

    if mqtt_client is None:
        if last_mqtt_lost == 0:
            last_mqtt_lost = now

        if time.ticks_diff(now, next_mqtt_try) >= 0:
            if try_connect_mqtt():
                next_mqtt_try = 0
            else:
                next_mqtt_try = time.ticks_add(now, 1500)
        return

    last_mqtt_lost = 0

    try:
        mqtt_client.check_msg()
    except Exception as exc:
        print("MQTT poll error:", exc)

        try:
            mqtt_client.disconnect()
        except Exception:
            pass

        mqtt_client = None
        last_heartbeat = 0
        last_mqtt_lost = now
        next_mqtt_try = time.ticks_add(now, 1500)


# ================================
# Минимальный драйвер SSD1306
# ================================
class SSD1306(framebuf.FrameBuffer):
    def __init__(self, width, height, i2c, addr=0x3C):
        self.width = width
        self.height = height
        self.i2c = i2c
        self.addr = addr

        self.buffer = bytearray(width * height // 8)

        self._cmd_buf = bytearray(2)
        self._data_buf = bytearray(1 + width)
        self._data_buf[0] = 0x40

        super().__init__(self.buffer, width, height, framebuf.MONO_VLSB)
        self._init_display()

    def _cmd(self, c):
        self._cmd_buf[0] = 0x00
        self._cmd_buf[1] = c
        self.i2c.writeto(self.addr, self._cmd_buf)

    def _init_display(self):
        for c in (
            0xAE,               # display off
            0xD5, 0x80,         # clock divide / oscillator
            0xA8, self.height - 1,
            0xD3, 0x00,         # display offset
            0x40,               # start line
            0x8D, 0x14,         # charge pump
            0x20, 0x02,         # page addressing mode
            0xA1,               # segment remap
            0xC8,               # COM scan direction
            0xDA, 0x12,         # COM pins
            0x81, 0xFF,         # contrast
            0xD9, 0xF1,         # precharge
            0xDB, 0x40,         # VCOMH
            0xA4,               # output follows RAM
            0xA6,               # normal display
            0xAF,               # display on
        ):
            self._cmd(c)

        self.fill(0)
        self.show()

    def show(self):
        self._cmd(0x20)
        self._cmd(0x02)

        page_len = self.width

        for page in range(self.height // 8):
            self._cmd(0xB0 | page)
            self._cmd(0x00)
            self._cmd(0x10)

            start = page * page_len
            self._data_buf[1:] = self.buffer[start:start + page_len]
            self.i2c.writeto(self.addr, self._data_buf)


# ================================
# Обычный скруглённый прямоугольник
# ================================
def fill_round_rect(fb, x, y, w, h, r, c=1):
    if w <= 0 or h <= 0:
        return

    if r < 0:
        r = 0

    max_r = min(w, h) // 2
    if r > max_r:
        r = max_r

    rr = r * r

    for j in range(h):
        if j < r:
            dy = r - j
            half = isqrt(rr - dy * dy)
            inset = r - half
        elif j >= h - r:
            dy = r - (h - 1 - j)
            half = isqrt(rr - dy * dy)
            inset = r - half
        else:
            inset = 0

        x1 = x + inset
        x2 = x + w - 1 - inset

        if x1 <= x2:
            fb.hline(x1, y + j, x2 - x1 + 1, c)


# ================================
# Деформированный глаз для эмоций
# ================================
def draw_deformed_round_eye(
    fb,
    cx,
    cy,
    w,
    h,
    r,
    top_a=0,
    top_b=0,
    top_c=0,
    bottom_a=0,
    bottom_b=0,
    bottom_c=0
):
    if w <= 0 or h <= 0:
        return

    half_w = w // 2
    half_h = h // 2

    if half_w <= 0:
        half_w = 1
    if half_h <= 0:
        half_h = 1

    max_r = min(half_w, half_h, r)
    if max_r < 0:
        max_r = 0

    straight = half_w - max_r
    rr = max_r * max_r

    for xi in range(-half_w, half_w + 1):
        x = cx + xi
        if x < 0 or x >= WIDTH:
            continue

        axi = -xi if xi < 0 else xi

        if axi <= straight:
            yy = half_h
        else:
            dx = axi - straight
            if dx > max_r:
                continue
            v = rr - dx * dx
            yy = isqrt(v) if v > 0 else 0

        if half_w > 0:
            raw_top = (
                top_a
                + ((top_b * xi) // half_w)
                + ((top_c * (half_w - axi)) // half_w)
            )
            raw_bottom = (
                bottom_a
                + ((bottom_b * xi) // half_w)
                + ((bottom_c * (half_w - axi)) // half_w)
            )
        else:
            raw_top = top_a
            raw_bottom = bottom_a

        if half_h > 0:
            top_shift = (raw_top * yy) // half_h
            bottom_shift = (raw_bottom * yy) // half_h
        else:
            top_shift = raw_top
            bottom_shift = raw_bottom

        y1 = cy - yy + top_shift
        y2 = cy + yy - 1 - bottom_shift

        if y1 < 0:
            y1 = 0
        if y2 >= HEIGHT:
            y2 = HEIGHT - 1

        if y1 <= y2:
            fb.vline(x, y1, y2 - y1 + 1, 1)


# ================================
# Толстая линия для бровей
# ================================
def draw_thick_line(fb, x1, y1, x2, y2, t, c=1):
    if t < 1:
        t = 1

    dx = abs(x2 - x1)
    dy = abs(y2 - y1)

    sx = 1 if x1 < x2 else -1
    sy = 1 if y1 < y2 else -1

    err = dx - dy
    off = -((t - 1) // 2)

    steps = dx + dy + 8

    for _ in range(steps):
        if 0 <= x1 < WIDTH:
            for oy in range(t):
                y = y1 + off + oy
                if 0 <= y < HEIGHT:
                    fb.pixel(x1, y, c)

        if x1 == x2 and y1 == y2:
            break

        e2 = 2 * err

        if e2 > -dy:
            err -= dy
            x1 += sx

        if e2 < dx:
            err += dy
            y1 += sy


# ================================
# Плавность
# ================================
def env_in_out(ms, attack, release):
    total = emotion_duration if emotion_duration > 0 else EMOTION_DURATION

    if ms <= 0 or ms >= total:
        return 0.0

    if attack > 0 and ms < attack:
        v = ms / attack
    elif release > 0 and ms > total - release:
        v = (total - ms) / release
    else:
        v = 1.0

    if v < 0.0:
        v = 0.0
    if v > 1.0:
        v = 1.0

    return v


def tri_wave(t):
    return 1.0 - abs(2.0 * t - 1.0)


# ================================
# Параметры глаз
# ================================
EYE_W = 44
EYE_H = 30
EYE_R = 13

CLOSED_H = 5

LEFT_CX = 32
RIGHT_CX = 96
EYE_CY = 32

MAX_GAZE_X = max(
    0,
    min(
        LEFT_CX - EYE_W // 2,
        WIDTH - EYE_W // 2 - RIGHT_CX
    )
)

MAX_GAZE_Y = max(
    0,
    min(
        EYE_CY - EYE_H // 2,
        HEIGHT - EYE_H // 2 - EYE_CY
    )
)

LOOK_SPEED = 3
BLINK_SPEED = 10
BLINK_HOLD = 20

LOOK_MIN = 450
LOOK_MAX = 1200

# Моргание примерно раз в 30 секунд
BLINK_MIN = 30000
BLINK_MAX = 30000


# ================================
# Сердечки для обнимашек
# ================================
HEART_PATTERN = (
    0b0110110,
    0b1111111,
    0b1111111,
    0b0111110,
    0b0011100,
    0b0001000,
)


def draw_heart(fb, x, y, c=1):
    for row, bits in enumerate(HEART_PATTERN):
        yy = y + row
        if yy < 0 or yy >= HEIGHT:
            continue

        for col in range(7):
            if (bits >> (6 - col)) & 1:
                xx = x + col
                if 0 <= xx < WIDTH:
                    fb.pixel(xx, yy, c)


# ================================
# Общий взгляд
# ================================
class Gaze:
    def __init__(self):
        self.x = 0
        self.y = 0

        self.tx = 0
        self.ty = 0

        self.next_look = 0

    def update(self, now):
        if time.ticks_diff(now, self.next_look) >= 0:
            self.tx = random.randint(-MAX_GAZE_X, MAX_GAZE_X)
            self.ty = random.randint(-MAX_GAZE_Y, MAX_GAZE_Y)
            self.next_look = time.ticks_add(
                now,
                random.randint(LOOK_MIN, LOOK_MAX)
            )

        dx = self.tx - self.x
        if dx > LOOK_SPEED:
            self.x += LOOK_SPEED
        elif dx < -LOOK_SPEED:
            self.x -= LOOK_SPEED
        else:
            self.x = self.tx

        dy = self.ty - self.y
        if dy > LOOK_SPEED:
            self.y += LOOK_SPEED
        elif dy < -LOOK_SPEED:
            self.y -= LOOK_SPEED
        else:
            self.y = self.ty


# ================================
# Глаз для idle-моргания
# ================================
class Eye:
    def __init__(self, base_cx, base_cy):
        self.base_cx = base_cx
        self.base_cy = base_cy

        self.h = EYE_H

        # 0 = открыт
        # 1 = закрывается
        # 2 = закрыт
        # 3 = открывается
        self.state = 0
        self.timer = 0


def start_blink(eye):
    if eye.state == 0:
        eye.state = 1


def update_blink(eye, now):
    if eye.state == 1:
        eye.h -= BLINK_SPEED
        if eye.h <= CLOSED_H:
            eye.h = CLOSED_H
            eye.state = 2
            eye.timer = time.ticks_add(now, BLINK_HOLD)

    elif eye.state == 2:
        if time.ticks_diff(now, eye.timer) >= 0:
            eye.state = 3

    elif eye.state == 3:
        eye.h += BLINK_SPEED
        if eye.h >= EYE_H:
            eye.h = EYE_H
            eye.state = 0


def draw_eye(fb, eye, gaze):
    x = eye.base_cx + gaze.x - EYE_W // 2
    y = eye.base_cy + gaze.y - eye.h // 2

    fill_round_rect(
        fb,
        x,
        y,
        EYE_W,
        eye.h,
        EYE_R,
        1
    )


def pick_contact_emotion():
    return CONTACT_EMOTIONS[random.randint(0, len(CONTACT_EMOTIONS) - 1)]


def start_emotion(name, now, duration):
    global current_emotion, emotion_start, emotion_duration, next_blink
    global left_eye, right_eye, gaze

    current_emotion = name
    emotion_start = now
    emotion_duration = duration
    next_blink = None

    if left_eye is not None:
        left_eye.state = 0
        left_eye.h = EYE_H

    if right_eye is not None:
        right_eye.state = 0
        right_eye.h = EYE_H

    if gaze is not None:
        gaze.x = 0
        gaze.y = 0
        gaze.tx = 0
        gaze.ty = 0
        gaze.next_look = time.ticks_add(now, duration + 300)


def reset_to_idle(now):
    global current_emotion, emotion_start, emotion_duration, next_blink
    global left_eye, right_eye, gaze

    current_emotion = None
    emotion_start = 0
    emotion_duration = EMOTION_DURATION

    if left_eye is not None:
        left_eye.state = 0
        left_eye.h = EYE_H

    if right_eye is not None:
        right_eye.state = 0
        right_eye.h = EYE_H

    if gaze is not None:
        gaze.x = 0
        gaze.y = 0
        gaze.tx = 0
        gaze.ty = 0
        gaze.next_look = time.ticks_add(now, random.randint(300, 900))

    next_blink = time.ticks_add(now, random.randint(BLINK_MIN, BLINK_MAX))


# ================================
# Эмоция: обнимашки
# ================================
def draw_hug(fb, ms):
    env = env_in_out(ms, 180, 300)

    phase = (ms % 500) / 500.0
    bounce = tri_wave(phase)
    amp = bounce * env

    w = int(EYE_W - 2.0 * amp)
    h = int(EYE_H - 8.0 * amp)
    r = int(EYE_R - 2.0 * amp)
    if r < 4:
        r = 4

    cy = EYE_CY - int(4.0 * amp)

    ta = int(1.0 * amp)
    tc = int(2.0 * amp)

    ba = int(4.0 * amp)
    bc = int(6.0 * amp)

    dx = int(2.0 * amp)

    draw_deformed_round_eye(
        fb,
        LEFT_CX - dx,
        cy,
        w,
        h,
        r,
        ta,
        0,
        tc,
        ba,
        0,
        bc
    )

    draw_deformed_round_eye(
        fb,
        RIGHT_CX + dx,
        cy,
        w,
        h,
        r,
        ta,
        0,
        tc,
        ba,
        0,
        bc
    )

    y_base = cy - h // 2 - 7 - int(3.0 * amp)
    if y_base < 1:
        y_base = 1

    lift = int(2.0 * amp)

    lx1 = LEFT_CX - dx - w // 2 + 4
    lx2 = LEFT_CX - dx + w // 2 - 4

    rx1 = RIGHT_CX + dx - w // 2 + 4
    rx2 = RIGHT_CX + dx + w // 2 - 4

    draw_thick_line(fb, lx1, y_base + lift, lx2, y_base - lift, 2)
    draw_thick_line(fb, rx2, y_base + lift, rx1, y_base - lift, 2)

    if env > 0.2:
        xs = (8, WIDTH // 2 - 3, WIDTH - 16)
        for i, hx in enumerate(xs):
            hy = HEIGHT - 9 - ((ms // 40 + i * 29) % 28)
            if hy >= 0:
                draw_heart(fb, hx, hy, 1)


# ================================
# Эмоция: щекотка
# ================================
def draw_tickle(fb, ms):
    env = env_in_out(ms, 120, 250)

    seq = (0, 1, 0, -1)
    shake = seq[(ms // 70) % 4]

    sx = int(4.0 * shake * env)

    w = int(EYE_W - 8.0 * env)
    h = int(EYE_H - 14.0 * env)
    r = int(EYE_R - 6.0 * env)
    if r < 2:
        r = 2

    cy = EYE_CY + int(2.0 * env)

    ta = int(4.0 * env)
    tc = int(3.0 * env)

    ba = int(6.0 * env)
    bc = int(8.0 * env)

    draw_deformed_round_eye(
        fb,
        LEFT_CX + sx,
        cy,
        w,
        h,
        r,
        ta,
        0,
        tc,
        ba,
        0,
        bc
    )

    draw_deformed_round_eye(
        fb,
        RIGHT_CX - sx,
        cy,
        w,
        h,
        r,
        ta,
        0,
        tc,
        ba,
        0,
        bc
    )

    y_base = cy - h // 2 - 6
    if y_base < 1:
        y_base = 1

    wig = int(2.0 * shake * env)

    lx1 = LEFT_CX + sx - w // 2 + 3
    lx2 = LEFT_CX + sx + w // 2 - 3

    rx1 = RIGHT_CX - sx - w // 2 + 3
    rx2 = RIGHT_CX - sx + w // 2 - 3

    draw_thick_line(fb, lx1, y_base + wig, lx2, y_base - wig, 2)
    draw_thick_line(fb, rx2, y_base + wig, rx1, y_base - wig, 2)

    if env > 0.35:
        for i in range(3):
            phase = ((ms // 65) + i) % 4
            ox = (0, 1, 2, 1)[phase]

            xL = LEFT_CX + sx - w // 2 - 3 - ox
            xR = RIGHT_CX - sx + w // 2 + 3 + ox
            y = cy - 5 + i * 4

            if 0 <= xL < WIDTH and 0 <= y < HEIGHT:
                fb.pixel(xL, y, 1)

            if 0 <= xR < WIDTH and 0 <= y < HEIGHT:
                fb.pixel(xR, y, 1)


# ================================
# Эмоция: злость / старая команда anger -> щекотка
# ================================
def draw_anger(fb, ms):
    env = env_in_out(ms, 180, 260)

    shake = 1 if ((ms // 55) % 2 == 0) else -1
    sx = int(2.0 * shake * env)
    sy = int(1.0 * shake * env)

    w = int(EYE_W - 6.0 * env)
    h = int(EYE_H - 12.0 * env)
    r = int(EYE_R - 6.0 * env)

    cy = EYE_CY + int(3.0 * env) + sy

    cx_l = LEFT_CX + sx
    cx_r = RIGHT_CX - sx

    ta = int(2.0 * env)
    tb_l = int(7.0 * env)
    tb_r = int(-7.0 * env)

    ba = int(2.0 * env)
    bb_l = int(4.0 * env)
    bb_r = int(-4.0 * env)

    draw_deformed_round_eye(
        fb,
        cx_l,
        cy,
        w,
        h,
        r,
        ta,
        tb_l,
        0,
        ba,
        bb_l,
        0
    )

    draw_deformed_round_eye(
        fb,
        cx_r,
        cy,
        w,
        h,
        r,
        ta,
        tb_r,
        0,
        ba,
        bb_r,
        0
    )

    y_base = cy - h // 2 - 5
    if y_base < 1:
        y_base = 1

    drop = int(7.0 * env)
    lift = int(4.0 * env)

    lx1 = cx_l - w // 2 + 3
    lx2 = cx_l + w // 2 - 3

    rx1 = cx_r - w // 2 + 3
    rx2 = cx_r + w // 2 - 3

    draw_thick_line(fb, lx1, y_base - lift, lx2, y_base + drop, 3)
    draw_thick_line(fb, rx2, y_base - lift, rx1, y_base + drop, 3)


# ================================
# Эмоция: смех / старая команда laughter -> обнимашки
# ================================
def draw_laughter(fb, ms):
    draw_hug(fb, ms)


# ================================
# Эмоция: грусть
# ================================
def draw_sadness(fb, ms):
    env = env_in_out(ms, 400, 400)

    tremble = 1 if ((ms // 130) % 2 == 0) else -1
    dy = int(2 * tremble * env)

    w = int(EYE_W - 4.0 * env)
    h = int(EYE_H - 8.0 * env)
    r = int(EYE_R - 3.0 * env)

    cy = EYE_CY + int(7.0 * env) + dy

    ta = int(2.0 * env)
    tc = int(1.0 * env)

    ba = int(1.0 * env)

    tb_l = int(-5.0 * env)
    bb_l = int(2.0 * env)

    tb_r = int(5.0 * env)
    bb_r = int(-2.0 * env)

    draw_deformed_round_eye(
        fb,
        LEFT_CX,
        cy,
        w,
        h,
        r,
        ta,
        tb_l,
        tc,
        ba,
        bb_l,
        0
    )

    draw_deformed_round_eye(
        fb,
        RIGHT_CX,
        cy,
        w,
        h,
        r,
        ta,
        tb_r,
        tc,
        ba,
        bb_r,
        0
    )

    y_base = cy - h // 2 - 6
    if y_base < 1:
        y_base = 1

    lift = int(6.0 * env)
    drop = int(4.0 * env)

    lx1 = LEFT_CX - w // 2 + 3
    lx2 = LEFT_CX + w // 2 - 3

    rx1 = RIGHT_CX - w // 2 + 3
    rx2 = RIGHT_CX + w // 2 - 3

    draw_thick_line(fb, lx1, y_base + drop, lx2, y_base - lift, 2)
    draw_thick_line(fb, rx2, y_base + drop, rx1, y_base - lift, 2)

    if env > 0.45:
        phase_l = (ms % 1000) / 1000.0
        phase_r = ((ms + 430) % 1000) / 1000.0

        tear_y_l = int(cy + h // 2 + 2 + phase_l * 13)
        tear_y_r = int(cy + h // 2 + 2 + phase_r * 13)

        tear_x_l = LEFT_CX + w // 2 - 7
        tear_x_r = RIGHT_CX - w // 2 + 7

        if 0 <= tear_x_l < WIDTH and tear_y_l < HEIGHT - 2:
            fb.vline(tear_x_l, tear_y_l, 2, 1)

        if 0 <= tear_x_r < WIDTH and tear_y_r < HEIGHT - 2:
            fb.vline(tear_x_r, tear_y_r, 2, 1)


# ================================
# Эмоция: удивление
# ================================
def draw_surprise(fb, ms):
    env = env_in_out(ms, 120, 500)

    extra = 0.0
    if ms < 350:
        extra = 0.25 * (1.0 - ms / 350.0)

    e = env + extra
    if e > 1.2:
        e = 1.2

    w = int(EYE_W + 12.0 * e)
    h = int(EYE_H + 14.0 * e)
    r = min(w, h) // 2

    cy = EYE_CY - int(3.0 * env)

    wob = int(1.0 * ((ms // 90) % 2) * env)

    draw_deformed_round_eye(
        fb,
        LEFT_CX - wob,
        cy,
        w,
        h,
        r,
        0,
        0,
        0,
        0,
        0,
        0
    )

    draw_deformed_round_eye(
        fb,
        RIGHT_CX + wob,
        cy,
        w,
        h,
        r,
        0,
        0,
        0,
        0,
        0,
        0
    )

    y_base = cy - h // 2 - 8 - int(7.0 * env)
    if y_base < 1:
        y_base = 1

    lift = int(2.0 * env)

    lx1 = LEFT_CX - w // 2 + 5
    lx2 = LEFT_CX + w // 2 - 5

    rx1 = RIGHT_CX - w // 2 + 5
    rx2 = RIGHT_CX + w // 2 - 5

    draw_thick_line(fb, lx1, y_base + lift, lx2, y_base - lift, 2)
    draw_thick_line(fb, rx2, y_base + lift, rx1, y_base - lift, 2)


# ================================
# Диспетчер эмоций
# ================================
def draw_expression(fb, name, ms):
    # Совместимость со старой страницей:
    # laughter -> обнимашки
    # anger -> щекотка
    if name == "hug" or name == "laughter":
        draw_hug(fb, ms)
    elif name == "tickle" or name == "anger":
        draw_tickle(fb, ms)
    elif name == "sadness":
        draw_sadness(fb, ms)
    elif name == "surprise":
        draw_surprise(fb, ms)


# ================================
# Главная программа
# ================================
def main():
    global pending_emotion, current_emotion, emotion_start, emotion_duration
    global mqtt_client, next_mqtt_try, wlan, last_heartbeat, last_mqtt_lost
    global last_interaction, last_auto_sad
    global custom_image_until, custom_image_pending, pending_image_after, custom_image_shown
    global last_battery_sample, battery_percent, battery_adc
    global left_eye, right_eye, gaze, next_blink

    random.seed(time.ticks_ms())

    try:
        gc.collect()
        gc.threshold(gc.mem_alloc() + 65536)
    except Exception:
        pass

    now0 = time.ticks_ms()
    last_interaction = now0
    last_auto_sad = now0
    last_battery_sample = 0
    last_mqtt_lost = 0

    # Подбираем рабочую частоту I2C.
    oled = None

    for freq in (400000, 200000, 100000):
        i2c = None

        try:
            i2c = I2C(
                0,
                sda=Pin(SDA_PIN),
                scl=Pin(SCL_PIN),
                freq=freq
            )

            time.sleep_ms(50)

            addrs = i2c.scan()
            print("I2C scan at", freq, "Hz:", addrs, [hex(a) for a in addrs])

            if not addrs:
                raise OSError("no devices")

            addr = I2C_ADDR

            if addr not in addrs:
                if 0x3C in addrs:
                    addr = 0x3C
                elif 0x3D in addrs:
                    addr = 0x3D
                else:
                    addr = addrs[0]

                print("OLED address auto-selected:", hex(addr))

            oled = SSD1306(WIDTH, HEIGHT, i2c, addr)
            print("OLED OK, I2C freq:", freq, "Hz, addr:", hex(addr))
            break

        except Exception as exc:
            print("OLED init failed at", freq, "Hz:", exc)

            if i2c is not None:
                try:
                    i2c.deinit()
                except Exception:
                    pass

            oled = None

    if oled is None:
        raise OSError(
            "OLED not found. Check SDA=7, SCL=6, 3.3V, GND."
        )

    try:
        boot = Pin(BOOT_PIN, Pin.IN, Pin.PULL_UP)
    except Exception as exc:
        print("BOOT pin init error:", exc)
        boot = None

    init_battery_adc()
    read_battery_percent()

    left_eye = Eye(LEFT_CX, EYE_CY)
    right_eye = Eye(RIGHT_CX, EYE_CY)
    gaze = Gaze()

    next_blink = None

    boot_prev = False
    boot_last_change = 0

    last_mem_check = 0
    low_memory_strikes = 0

    CRITICAL_FREE = 6000
    LOW_FREE = 15000
    MQTT_DOWN_RESET_MS = 300000

    print("System started. Waiting for WiFi/MQTT...")

    while True:
        now = time.ticks_ms()

        # ----------------------------
        # MQTT poll
        # ----------------------------
        mqtt_poll(now)

        # ----------------------------
        # Если пришла новая команда, запускаем её сразу,
        # прерывая рисунок или текущую анимацию.
        # ----------------------------
        if pending_emotion is not None:
            name = pending_emotion
            pending_emotion = None

            if name == "surprise" and custom_image_pending and pending_image_after:
                duration = SURPRISE_BEFORE_IMAGE_DURATION
            else:
                cancel_custom_image()
                duration = EMOTION_DURATION

            start_emotion(name, now, duration)

        # ----------------------------
        # Батарея
        # ----------------------------
        if BATTERY_ENABLED and time.ticks_diff(now, last_battery_sample) >= BATTERY_SAMPLE_INTERVAL:
            read_battery_percent()
            last_battery_sample = now

        # ----------------------------
        # MQTT heartbeat / статус
        # ----------------------------
        if mqtt_client is not None and mqtt_client.connected:
            if last_heartbeat == 0 or time.ticks_diff(now, last_heartbeat) >= HEARTBEAT_INTERVAL:
                try:
                    publish_status()
                    last_heartbeat = now
                except Exception as exc:
                    print("MQTT heartbeat error:", exc)

                    try:
                        mqtt_client.disconnect()
                    except Exception:
                        pass

                    mqtt_client = None
                    last_heartbeat = 0
                    last_mqtt_lost = now
                    next_mqtt_try = time.ticks_add(now, 1500)
        else:
            if last_mqtt_lost == 0:
                last_mqtt_lost = now

        # ----------------------------
        # Memory / watchdog
        # ----------------------------
        if time.ticks_diff(now, last_mem_check) >= 10000:
            last_mem_check = now

            try:
                alloc = gc.mem_alloc()
                free = gc.mem_free()
                print("MEM alloc:", alloc, "free:", free)

                if free < LOW_FREE:
                    gc.collect()
                    free = gc.mem_free()
                    print("GC done, free:", free)

                if free < CRITICAL_FREE:
                    low_memory_strikes += 1
                    print("Low memory strike:", low_memory_strikes)

                    if low_memory_strikes >= 6:
                        print("Critical memory, resetting ESP32")
                        machine.reset()
                else:
                    low_memory_strikes = 0

                if mqtt_client is None and last_mqtt_lost != 0:
                    if time.ticks_diff(now, last_mqtt_lost) > MQTT_DOWN_RESET_MS:
                        print("MQTT down too long, resetting ESP32")
                        machine.reset()

            except Exception as exc:
                print("Memory watchdog error:", exc)

        # ----------------------------
        # Кнопка BOOT:
        # - отменяет рисунок
        # - запускает случайную контактную эмоцию
        # ----------------------------
        if boot is not None:
            raw = boot.value()
            pressed = (raw == 0) if BOOT_ACTIVE_LOW else (raw == 1)

            if pressed != boot_prev:
                if time.ticks_diff(now, boot_last_change) > 80:
                    boot_prev = pressed
                    boot_last_change = now

                    if pressed:
                        touch_interaction()
                        cancel_custom_image()
                        start_emotion(pick_contact_emotion(), now, EMOTION_DURATION)

        # ----------------------------
        # Авто-грусть, если долго нет контакта
        # ----------------------------
        if (
            current_emotion is None and
            pending_emotion is None and
            custom_image_until == 0 and
            not custom_image_pending
        ):
            if (
                time.ticks_diff(now, last_interaction) >= IDLE_SAD_AFTER and
                time.ticks_diff(now, last_auto_sad) >= AUTO_SAD_INTERVAL
            ):
                start_emotion("sadness", now, EMOTION_DURATION)
                last_auto_sad = now

        # ----------------------------
        # Если активен пользовательский рисунок, показываем его.
        # Рисунок грузится на OLED один раз, чтобы не тормозить реакцию.
        # ----------------------------
        if custom_image_until != 0:
            if time.ticks_diff(now, custom_image_until) >= 0:
                cancel_custom_image()
                reset_to_idle(now)
            else:
                if not custom_image_shown:
                    oled.buffer[:] = custom_image_buffer
                    oled.show()
                    custom_image_shown = True

                time.sleep_ms(20)
                continue

        # ----------------------------
        # Отрисовка эмоции
        # ----------------------------
        if current_emotion is not None:
            elapsed = time.ticks_diff(now, emotion_start)

            if elapsed >= emotion_duration:
                current_emotion = None

                if pending_image_after and custom_image_pending:
                    custom_image_until = time.ticks_add(now, CUSTOM_IMAGE_DURATION)
                    custom_image_pending = False
                    pending_image_after = False
                    custom_image_shown = False
                else:
                    reset_to_idle(now)

            else:
                oled.fill(0)

                try:
                    draw_expression(oled, current_emotion, elapsed)
                except Exception as exc:
                    print("Emotion draw error:", exc)

                    current_emotion = None
                    cancel_custom_image()
                    reset_to_idle(now)

                oled.show()
                time.sleep_ms(15)
                continue

        # ----------------------------
        # Idle-режим
        # ----------------------------
        update_blink(left_eye, now)
        update_blink(right_eye, now)

        gaze.update(now)

        if left_eye.state == 0 and right_eye.state == 0:
            if next_blink is None:
                next_blink = time.ticks_add(
                    now,
                    random.randint(BLINK_MIN, BLINK_MAX)
                )
            elif time.ticks_diff(now, next_blink) >= 0:
                choice = random.randint(0, 9)

                if choice < 4:
                    start_blink(left_eye)
                    start_blink(right_eye)
                elif choice < 7:
                    start_blink(left_eye)
                else:
                    start_blink(right_eye)

                next_blink = None

        oled.fill(0)

        draw_eye(oled, left_eye, gaze)
        draw_eye(oled, right_eye, gaze)

        oled.show()

        time.sleep_ms(12)


if __name__ == "__main__":
    main()
