import sys
import math
import random
import os
import threading
import time

import numpy as np
import mss
from PIL import Image, ImageOps
import pytesseract

from PyQt5.QtCore import Qt, QTimer, QPointF
from PyQt5.QtGui import (
    QPainter,
    QPen,
    QColor,
    QFont,
    QPixmap,
    QCursor,
)
from PyQt5.QtWidgets import QApplication, QWidget


ASSETS_DIR = "assets"
HOTKEY_KEY = "f9"


def load_pixmap(filename):
    path = os.path.join(ASSETS_DIR, filename)
    if not os.path.isfile(path):
        print(f"[overlay] missing asset: {path}")
        return None
    pm = QPixmap(path)
    if pm.isNull():
        print(f"[overlay] failed to load: {path}")
        return None
    return pm


class CrosshairOverlay(QWidget):
    def __init__(self, screen_width=1920, screen_height=1080):
        super().__init__()

        self.screen_width = screen_width
        self.screen_height = screen_height
        self.center_x = screen_width // 2
        self.center_y = screen_height // 2

    
        self.setWindowFlags(
            Qt.FramelessWindowHint |
            Qt.WindowStaysOnTopHint |
            Qt.Tool
        )
        self.setAttribute(Qt.WA_TranslucentBackground, True)
        self.setAttribute(Qt.WA_TransparentForMouseEvents, True)
        self.setGeometry(0, 0, self.screen_width, self.screen_height)

        
        self.modes = [
            "static",
            "shaky",
            "orbit_ball",
            "cute_quotes",
            "angel_devil",
            "duck",
            "sleepy",
            "pointer",
            "blackhole",
            "panic",
            "jelly",
            "broken",
            "lag_echo",
            "focus_window",
            "overheated",
            "metronome",
            "mega_cross",   
        ]
        self.mode_index = 0
        self.current_mode = self.modes[0]

        
        self.pending_name_hit = False
        self.last_killfeed_snippet = ""
        self.last_killfeed_time = 0.0

        
        self.dt = 1.0 / 60.0
        self.orbit_angle = 0.0
        self.blackhole_phase = 0.0
        self.panic_phase = 0.0
        self.duck_phase = 0.0
        self.metronome_time = 0.0

        self.jelly_scale = 1.0
        self.jelly_vel = 0.0

        self.broken_time = 0.0
        self.broken_period = 4.0
        self.broken_drift_time = 3.2

        
        self.lag_trail = []          
        self.lag_trail_len = 6
        self.lag_offset = (0.0, 0.0)

        
        self.heat = 0.0              

   
        self.mega_scale = 0.0        

    
        self.quotes = [
            "u can do it man!",
            "dont whiff this one",
            "trust the crosshair fr",
            "they're scared of u",
            "one good round changes everything",
        ]
        self.current_quote = random.choice(self.quotes)
        self.quote_timer = 0.0
        self.quote_interval = random.uniform(4.0, 7.0)

        
        self.cute_pix = load_pixmap("cute_guy.png")
        self.cute_pix_scaled = None
        if self.cute_pix:
            max_size = 260  
            w = self.cute_pix.width()
            h = self.cute_pix.height()
            scale = min(max_size / float(max(w, h)), 1.0)
            self.cute_pix_scaled = self.cute_pix.scaled(
                int(w * scale),
                int(h * scale),
                Qt.KeepAspectRatio,
                Qt.SmoothTransformation,
            )

        
        self.angel_pix = load_pixmap("angel_guy.png")
        self.devil_pix = load_pixmap("devil_guy.png")
        self.angel_pix_scaled = None
        self.devil_pix_scaled = None
        max_ad_size = 200  
        if self.angel_pix:
            w = self.angel_pix.width()
            h = self.angel_pix.height()
            scale = min(max_ad_size / float(max(w, h)), 1.0)
            self.angel_pix_scaled = self.angel_pix.scaled(
                int(w * scale),
                int(h * scale),
                Qt.KeepAspectRatio,
                Qt.SmoothTransformation,
            )
        if self.devil_pix:
            w = self.devil_pix.width()
            h = self.devil_pix.height()
            scale = min(max_ad_size / float(max(w, h)), 1.0)
            self.devil_pix_scaled = self.devil_pix.scaled(
                int(w * scale),
                int(h * scale),
                Qt.KeepAspectRatio,
                Qt.SmoothTransformation,
            )

        self.ad_is_angel = True
        self.ad_timer = 0.0
        self.ad_interval = random.uniform(4.0, 8.0)
        self.angel_quotes = [
            "play smart :)",
            "just breathe and hold",
            "you got this, king",
            "trust your crosshair",
        ]
        self.devil_quotes = [
            "swing this dude.",
            "full W, no brakes.",
            "knife him. do it.",
            "peek again. they won't expect it.",
        ]
        self.ad_current_quote = random.choice(self.angel_quotes)

        
        self.duck_pix = load_pixmap("duck_guy.png")
        self.duck_pix_scaled = None
        if self.duck_pix:
            max_duck = 200  
            w = self.duck_pix.width()
            h = self.duck_pix.height()
            scale = min(max_duck / float(max(w, h)), 1.0)
            self.duck_pix_scaled = self.duck_pix.scaled(
                int(w * scale),
                int(h * scale),
                Qt.KeepAspectRatio,
                Qt.SmoothTransformation,
            )

        
        self.sleep_progress = 0.0
        self.idle_time = 0.0
        self.windows_pointer_timer = 0.0
        self.windows_pointer_duration = 1.5

        
        self.cursor_speed = 0.0
        self.last_cursor_pos = None

        
        self.timer = QTimer()
        self.timer.timeout.connect(self.on_tick)
        self.timer.start(int(self.dt * 1000))

        print("[overlay] started. Modes:", self.modes)

        self._start_ocr_watcher()
        self._start_hotkey_listener()
        self._start_mouse_listener()

   
    def _start_hotkey_listener(self):
        def worker():
            try:
                import keyboard
            except Exception as e:
                print("[overlay] keyboard import failed, hotkey disabled:", e)
                return
            try:
                keyboard.add_hotkey(HOTKEY_KEY, lambda: self._cycle_mode("hotkey"))
                keyboard.wait()
            except Exception as e:
                print("[overlay] keyboard listener error:", e)

        t = threading.Thread(target=worker, daemon=True)
        t.start()

    
    def _start_mouse_listener(self):
        def worker():
            try:
                import mouse
            except Exception as e:
                print("[overlay] mouse import failed, sleepy wake disabled:", e)
                return
            try:
                mouse.on_right_click(lambda: self._on_right_click())
                mouse.wait()
            except Exception as e:
                print("[overlay] mouse listener error:", e)

        t = threading.Thread(target=worker, daemon=True)
        t.start()

    def _on_right_click(self):
        if self.current_mode == "sleepy":
            
            self.sleep_progress = 0.0
            self.idle_time = 0.0
            self.windows_pointer_timer = self.windows_pointer_duration
            print("[overlay] sleepy wake: right-click")

    
    def _start_ocr_watcher(self):
        def worker():
            print("[overlay] OCR watching...")

            monitor = {
                "left": int(self.screen_width - 700),
                "top": 30,
                "width": 700,
                "height": 320,
            }
            print("[overlay] OCR region:", monitor)

            while True:
                try:
                    with mss.mss() as sct:
                        while True:
                            try:
                                img = sct.grab(monitor)
                                arr = np.array(img)[..., :3]

                                pil_img = Image.fromarray(arr)
                                proc = self._preprocess_for_ocr(pil_img)

                                text = pytesseract.image_to_string(
                                    proc,
                                    config="--psm 6 --oem 3",
                                ).lower()

                                if any(k in text for k in [
                                    "dieselderek",
                                    "diesel",
                                    "derek",
                                    "derke",
                                ]):
                                    snippet = text.replace("\n", " ").strip()
                                    now = time.time()

                                    
                                    if snippet and (
                                        snippet != self.last_killfeed_snippet
                                        or now - self.last_killfeed_time > 2.5
                                    ):
                                        self.last_killfeed_snippet = snippet
                                        self.last_killfeed_time = now
                                        print("[overlay] killfeed match →", snippet[:80])
                                        self.pending_name_hit = True

                                time.sleep(0.25)

                            except Exception as frame_err:
                                print("[OCR] frame error:", frame_err)
                                time.sleep(0.5)
                                break
                except Exception as outer_err:
                    print("[OCR] outer error, retrying:", outer_err)
                    time.sleep(1.0)

        t = threading.Thread(target=worker, daemon=True)
        t.start()

    def _preprocess_for_ocr(self, pil_img):
        w, h = pil_img.size
        pil_img = pil_img.crop((0, int(h * 0.15), w, int(h * 0.85)))
        img = pil_img.convert("L")
        img = ImageOps.autocontrast(img)

        def thresh(x):
            return 255 if x > 160 else 0

        img = img.point(thresh, mode="L")
        img = img.resize((img.width * 2, img.height * 2), Image.BICUBIC)
        return img

    
    def _cycle_mode(self, reason=""):
        prev = self.current_mode
        self.mode_index = (self.mode_index + 1) % len(self.modes)
        self.current_mode = self.modes[self.mode_index]
        print(f"[overlay] mode: {prev} → {self.current_mode} ({reason})")

        
        if self.current_mode != "sleepy":
            self.sleep_progress = 0.0
            self.idle_time = 0.0
            self.windows_pointer_timer = 0.0

        if self.current_mode != "jelly":
            self.jelly_scale = 1.0
            self.jelly_vel = 0.0

        if self.current_mode != "broken":
            self.broken_time = 0.0

        if self.current_mode != "mega_cross":
            self.mega_scale = 0.0  

   
    def on_tick(self):
        dt = self.dt

        
        if self.pending_name_hit:
            self.pending_name_hit = False
            self._cycle_mode("killfeed")

        
        self.orbit_angle = (self.orbit_angle + 90.0 * dt) % 360.0
        self.blackhole_phase = (self.blackhole_phase + 1.5 * dt) % (2 * math.pi)
        self.panic_phase = (self.panic_phase + dt) % 1.0
        self.duck_phase = (self.duck_phase + 2.0 * dt) % (2 * math.pi)
        self.metronome_time += dt

        
        dx = dy = 0.0
        try:
            pos = QCursor.pos()
            if self.last_cursor_pos is not None:
                dx = pos.x() - self.last_cursor_pos.x()
                dy = pos.y() - self.last_cursor_pos.y()
                dist = math.hypot(dx, dy)
                self.cursor_speed = self.cursor_speed * 0.8 + dist * 0.2
            self.last_cursor_pos = pos
        except Exception:
            pass

        
        ox, oy = self.lag_offset
        if dx != 0.0 or dy != 0.0:
            factor = 0.4
            ox = ox * 0.8 - dx * factor
            oy = oy * 0.8 - dy * factor
        else:
            ox = ox * 0.85
            oy = oy * 0.85
        self.lag_offset = (ox, oy)
        self.lag_trail.insert(0, (ox, oy))
        self.lag_trail = self.lag_trail[:self.lag_trail_len]

        
        self.heat += (self.cursor_speed / 800.0) * dt   
        self.heat -= 0.3 * dt                           
        self.heat = max(0.0, min(self.heat, 1.0))

        
        if self.current_mode == "mega_cross":
            self.mega_scale += dt * 0.02  
        

        
        if self.current_mode == "sleepy":
            if self.windows_pointer_timer > 0.0:
                self.windows_pointer_timer = max(
                    0.0, self.windows_pointer_timer - dt
                )
            else:
                if self.cursor_speed < 2.0:
                    self.idle_time += dt
                else:
                    self.idle_time = 0.0
                    self.sleep_progress = max(0.0, self.sleep_progress - dt * 0.4)

                if self.idle_time > 2.0:
                    self.sleep_progress = min(
                        1.0, self.sleep_progress + dt / 2.5
                    )
        else:
            self.idle_time = 0.0
            self.sleep_progress = 0.0
            self.windows_pointer_timer = 0.0

        
        target = 1.0 + min(self.cursor_speed / 40.0, 1.0) * 0.6
        k = 10.0
        d = 8.0
        self.jelly_vel += (target - self.jelly_scale) * k * dt
        self.jelly_vel -= self.jelly_vel * d * dt
        self.jelly_scale += self.jelly_vel * dt
        self.jelly_scale = max(0.6, min(self.jelly_scale, 1.8))

        
        self.broken_time += dt
        if self.broken_time > self.broken_period:
            self.broken_time = 0.0

        
        self.quote_timer += dt
        if self.quote_timer >= self.quote_interval:
            self.quote_timer = 0.0
            self.current_quote = random.choice(self.quotes)
            self.quote_interval = random.uniform(4.0, 7.0)

        
        self.ad_timer += dt
        if self.ad_timer >= self.ad_interval:
            self.ad_timer = 0.0
            self.ad_interval = random.uniform(4.0, 8.0)
            self.ad_is_angel = random.choice([True, False])
            if self.ad_is_angel:
                self.ad_current_quote = random.choice(self.angel_quotes)
            else:
                self.ad_current_quote = random.choice(self.devil_quotes)

        self.update()

    
    def paintEvent(self, e):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)

        mode = self.current_mode
        try:
            if mode == "static":
                self.draw_static(p)
            elif mode == "shaky":
                self.draw_shaky(p)
            elif mode == "orbit_ball":
                self.draw_orbit_ball(p)
            elif mode == "cute_quotes":
                self.draw_cute(p)
            elif mode == "angel_devil":
                self.draw_angel_devil(p)
            elif mode == "duck":
                self.draw_duck(p)
            elif mode == "sleepy":
                self.draw_sleepy(p)
            elif mode == "pointer":
                self.draw_pointer(p)
            elif mode == "blackhole":
                self.draw_blackhole(p)
            elif mode == "panic":
                self.draw_panic(p)
            elif mode == "jelly":
                self.draw_jelly(p)
            elif mode == "broken":
                self.draw_broken(p)
            elif mode == "lag_echo":
                self.draw_lag_echo(p)
            elif mode == "focus_window":
                self.draw_focus_window(p)
            elif mode == "overheated":
                self.draw_overheated(p)
            elif mode == "metronome":
                self.draw_metronome(p)
            elif mode == "mega_cross":
                self.draw_mega_cross(p)
        except Exception as err:
            print("[overlay] draw error:", err)
            self.draw_static(p)

        
        p.setPen(QPen(QColor(0, 0, 0, 180)))
        p.setFont(QFont("Consolas", 10))
        p.drawText(10, 20, self.current_mode)

        p.end()
    
    def draw_cross(self, p: QPainter, cx: int, cy: int,
                   scale: float = 1.0,
                   length: int = 12,
                   gap: int = 4,
                   thickness: int = 2):
        p.save()
        p.translate(cx, cy)
        p.scale(scale, scale)
        p.setPen(QPen(QColor(255, 255, 255), thickness))

        
        p.drawLine(-gap - length, 0, -gap, 0)
        p.drawLine(gap, 0, gap + length, 0)
        
        p.drawLine(0, -gap - length, 0, -gap)
        p.drawLine(0, gap, 0, gap + length)

        p.drawEllipse(QPointF(0, 0), 2, 2)
        p.restore()

    def draw_circle_shape(self, p: QPainter, cx: int, cy: int,
                          radius: float = 10.0,
                          thickness: int = 2):
        p.save()
        p.setPen(QPen(QColor(255, 255, 255), thickness))
        p.setBrush(Qt.NoBrush)
        p.drawEllipse(QPointF(cx, cy), radius, radius)
        p.restore()

    def draw_dot_shape(self, p: QPainter, cx: int, cy: int,
                       radius: float = 3.0):
        p.save()
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(255, 255, 255))
        p.drawEllipse(QPointF(cx, cy), radius, radius)
        p.restore()

    
    def draw_static(self, p: QPainter):
        
        self.draw_cross(p, self.center_x, self.center_y)

    def draw_shaky(self, p: QPainter):
        
        jitter = 3
        cx = self.center_x + random.randint(-jitter, jitter)
        cy = self.center_y + random.randint(-jitter, jitter)
        self.draw_circle_shape(p, cx, cy, radius=6, thickness=2)

    def draw_orbit_ball(self, p: QPainter):
        cx, cy = self.center_x, self.center_y

        p.setPen(QPen(QColor(255, 255, 255, 60), 1))
        radius = 35
        p.drawEllipse(QPointF(cx, cy), radius, radius)

        a = math.radians(self.orbit_angle)
        x = cx + math.cos(a) * radius
        y = cy + math.sin(a) * radius

        p.setPen(Qt.NoPen)
        p.setBrush(QColor(255, 255, 255))
        p.drawEllipse(QPointF(x, y), 7, 7)

        p.setBrush(QColor(0, 0, 0))
        p.drawEllipse(QPointF(x + 2, y - 1), 2, 2)

    def draw_cute(self, p: QPainter):
        cx, cy = self.center_x, self.center_y

        if self.cute_pix_scaled:
            w = self.cute_pix_scaled.width()
            h = self.cute_pix_scaled.height()
            p.drawPixmap(cx - w // 2, cy - h // 2, self.cute_pix_scaled)
        else:
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(255, 255, 255))
            p.drawEllipse(QPointF(cx, cy), 20, 20)

        text = self.current_quote
        p.setFont(QFont("Segoe UI", 20, QFont.Bold))

        tx = cx + 100
        ty = cy + 8

        p.setPen(QPen(QColor(0, 0, 0, 220), 3))
        p.drawText(tx + 2, ty + 2, text)

        p.setPen(QPen(QColor(255, 255, 255, 255), 1))
        p.drawText(tx, ty, text)

    def draw_angel_devil(self, p: QPainter):
        cx, cy = self.center_x, self.center_y

        pm = self.angel_pix_scaled if self.ad_is_angel else self.devil_pix_scaled
        if pm:
            w = pm.width()
            h = pm.height()
            p.drawPixmap(cx - w // 2, cy - h // 2, pm)
        else:
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(255, 255, 255))
            p.drawEllipse(QPointF(cx, cy), 20, 20)

        text = self.ad_current_quote
        p.setFont(QFont("Segoe UI", 20, QFont.Bold))

        tx = cx + 100
        ty = cy + 8

        p.setPen(QPen(QColor(0, 0, 0, 220), 3))
        p.drawText(tx + 2, ty + 2, text)

        p.setPen(QPen(QColor(255, 255, 255, 255), 1))
        p.drawText(tx, ty, text)

    def draw_duck(self, p: QPainter):
        """
        Duck crosshair:
        - Little duck PNG bobbing up/down
        - Slight squish based on mouse speed
        """
        cx, cy = self.center_x, self.center_y

        if self.duck_pix_scaled:
            w = self.duck_pix_scaled.width()
            h = self.duck_pix_scaled.height()

            
            bob_amp = 10
            bob = int(math.sin(self.duck_phase) * bob_amp)

            
            speed_factor = min(self.cursor_speed / 50.0, 1.0)
            scale = 1.0 + 0.1 * speed_factor

            p.save()
            p.translate(cx, cy + bob)
            p.scale(scale, scale)
            p.drawPixmap(-w // 2, -h // 2, self.duck_pix_scaled)
            p.restore()
        else:
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(255, 255, 0))
            p.drawEllipse(QPointF(cx, cy), 20, 20)

    def draw_sleepy(self, p: QPainter):
        """
        Sleepy: drooping cross + Zzz
        (we can convert this to a pillow icon later if you want)
        """
        cx, cy = self.center_x, self.center_y

        if self.windows_pointer_timer > 0.0:
            self.draw_pointer(p)
            return

        droop = int(self.sleep_progress * 45.0)
        self.draw_cross(p, cx, cy + droop)

        if self.sleep_progress > 0.95:
            p.setPen(QPen(QColor(255, 255, 255, 200)))
            p.setFont(QFont("Segoe UI", 16, QFont.Bold))
            p.drawText(cx + 20, cy - 30, "Zzz")

    def draw_pointer(self, p: QPainter):
        cx, cy = self.center_x, self.center_y
        size = 26

        p.setPen(QPen(QColor(0, 0, 0), 2))
        p.setBrush(QColor(255, 255, 255))

        tip = QPointF(cx, cy)
        bottom = QPointF(cx, cy + size)
        right = QPointF(cx + size * 0.5, cy + size * 0.6)
        p.drawPolygon(tip, bottom, right)

    def draw_blackhole(self, p: QPainter):
        cx, cy = self.center_x, self.center_y

        
        self.draw_cross(p, cx, cy)

        max_r = 55
        p.setPen(Qt.NoPen)

        for i in range(4):
            t = i / 4.0
            r = max_r * (1.0 - 0.18 * i)
            alpha = int(150 * (1.0 - t))
            p.setBrush(QColor(10, 10, 15, alpha))
            p.drawEllipse(QPointF(cx, cy), r, r)

        p.setBrush(QColor(0, 0, 0, 230))
        p.drawEllipse(QPointF(cx, cy), 9, 9)

        p.setPen(QPen(QColor(255, 255, 255, 210), 2))
        inner_r = 14
        spokes = 6

        for j in range(spokes):
            ang = self.blackhole_phase + j * (2 * math.pi / spokes)
            x1 = int(cx + math.cos(ang) * inner_r)
            y1 = int(cy + math.sin(ang) * inner_r)
            x2 = int(cx + math.cos(ang) * max_r)
            y2 = int(cy + math.sin(ang) * max_r)
            p.drawLine(x1, y1, x2, y2)

    def draw_panic(self, p: QPainter):
        """
        Panic: big heartbeat crosshair
        """
        cx, cy = self.center_x, self.center_y
        speed_factor = 1.0 + min(self.cursor_speed / 40.0, 1.0) * 2.0
        phase = (self.panic_phase * speed_factor) % 1.0
        pulse = math.sin(phase * 2 * math.pi)
        scale = 1.0 + 0.25 * pulse  
        self.draw_cross(p, cx, cy, scale=scale * 1.4, length=18, gap=6, thickness=3)

    def draw_jelly(self, p: QPainter):
        """
        Jelly: breathing ring instead of cross
        """
        cx, cy = self.center_x, self.center_y
        radius = 10.0 * self.jelly_scale
        self.draw_circle_shape(p, cx, cy, radius=radius, thickness=3)

    def draw_broken(self, p: QPainter):
        cx, cy = self.center_x, self.center_y

        t = self.broken_time
        max_offset = 10

        if t <= self.broken_drift_time:
            offset = int(max_offset * (t / self.broken_drift_time))
        else:
            offset = max_offset

        gap = 4 + offset
        length = 12

        p.save()
        p.translate(cx, cy)
        p.setPen(QPen(QColor(255, 255, 255), 2))

        p.drawLine(-(gap + length), 0, -gap, 0)
        p.drawLine(gap, 0, gap + length, 0)
        p.drawLine(0, -(gap + length), 0, -gap)
        p.drawLine(0, gap, 0, gap + length)
        p.drawEllipse(QPointF(0, 0), 2, 2)

        p.restore()

    
    def draw_lag_echo(self, p: QPainter):
        """
        Lagging crosshair:
        - main dot at center
        - trailing faint ghosts based on mouse movement
        """
        cx, cy = self.center_x, self.center_y

       
        self.draw_dot_shape(p, cx, cy, radius=4)

        if not self.lag_trail:
            return

        n = len(self.lag_trail)
        for i, (ox, oy) in enumerate(self.lag_trail):
            alpha = int(160 * (1.0 - i / max(1, n)))
            radius = max(2, 4 - i)
            p.save()
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(255, 255, 255, max(0, alpha)))
            p.drawEllipse(QPointF(cx + ox, cy + oy), radius, radius)
            p.restore()

    def draw_focus_window(self, p: QPainter):
        """
        Focus window: camera viewfinder corners + blinking REC dot
        """
        cx, cy = self.center_x, self.center_y

        half_size = 20
        corner_len = 10

        p.setPen(QPen(QColor(255, 255, 255), 2))
        p.setBrush(Qt.NoBrush)

        
        p.drawLine(cx - half_size, cy - half_size, cx - half_size + corner_len, cy - half_size)
        p.drawLine(cx - half_size, cy - half_size, cx - half_size, cy - half_size + corner_len)

       
        p.drawLine(cx + half_size, cy - half_size, cx + half_size - corner_len, cy - half_size)
        p.drawLine(cx + half_size, cy - half_size, cx + half_size, cy - half_size + corner_len)

        
        p.drawLine(cx - half_size, cy + half_size, cx - half_size + corner_len, cy + half_size)
        p.drawLine(cx - half_size, cy + half_size, cx - half_size, cy + half_size - corner_len)

        
        p.drawLine(cx + half_size, cy + half_size, cx + half_size - corner_len, cy + half_size)
        p.drawLine(cx + half_size, cy + half_size, cx + half_size, cy + half_size - corner_len)

        
        blink_on = (self.panic_phase % 1.0) < 0.5
        if blink_on:
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(255, 80, 80, 220))
            rec_x = cx + half_size + 18
            rec_y = cy - half_size - 2
            p.drawEllipse(QPointF(rec_x, rec_y), 4, 4)

            p.setPen(QPen(QColor(255, 255, 255, 220), 1))
            p.setFont(QFont("Consolas", 9))
            p.drawText(rec_x + 8, rec_y + 3, "REC")

    def draw_overheated(self, p: QPainter):
        """
        Overheated crosshair:
        - color + shake + size based on heat value (0..1)
        """
        cx, cy = self.center_x, self.center_y

        heat = self.heat
        
        r = 255
        g = int(255 * (1.0 - 0.7 * heat))
        b = int(255 * (1.0 - 0.9 * heat))

        
        shake = 1.0 + 4.0 * heat
        jitter_x = random.uniform(-shake, shake)
        jitter_y = random.uniform(-shake, shake)

        
        scale = 1.0 + 0.6 * heat

        p.save()
        p.translate(cx + jitter_x, cy + jitter_y)
        p.scale(scale, scale)
        p.setPen(QPen(QColor(r, g, b), 3))

        length = 14
        gap = 5

        p.drawLine(-gap - length, 0, -gap, 0)
        p.drawLine(gap, 0, gap + length, 0)
        p.drawLine(0, -gap - length, 0, -gap)
        p.drawLine(0, gap, 0, gap + length)
        p.drawEllipse(QPointF(0, 0), 2, 2)

        p.restore()

        
        if heat > 0.75:
            p.setPen(QPen(QColor(255, 80, 80, 220)))
            p.setFont(QFont("Consolas", 10, QFont.Bold))
            p.drawText(cx + 20, cy - 25, "HEAT")

    def draw_metronome(self, p: QPainter):
        """
        Metronome: swinging arm line pivoting at center
        """
        cx, cy = self.center_x, self.center_y

        max_angle_deg = 35.0
        
        ang = math.sin(self.metronome_time * 2 * math.pi * 0.5)
        angle_rad = math.radians(max_angle_deg) * ang

        length = 40

        x2 = cx + math.sin(angle_rad) * length
        y2 = cy - math.cos(angle_rad) * length  

        p.setPen(QPen(QColor(255, 255, 255), 2))
        p.drawLine(cx, cy, int(x2), int(y2))

        
        self.draw_dot_shape(p, cx, cy, radius=3)

    def draw_mega_cross(self, p: QPainter):
        """
        Mega cross:
        - huge connected cross across the whole screen
        - very thick, bright colors
        - slowly grows thicker over time (mega_scale)
        """
        cx, cy = self.center_x, self.center_y

        
        base_thickness = 8
        extra = int(self.mega_scale * 12)   
        thickness = base_thickness + extra

        
        t = self.mega_scale * 3.0
        r = int(180 + 75 * (math.sin(t) * 0.5 + 0.5))
        g = int(80 + 120 * (math.sin(t + 2.1) * 0.5 + 0.5))
        b = int(200 + 55 * (math.sin(t + 4.2) * 0.5 + 0.5))
        color = QColor(r, g, b, 230)

        p.setPen(QPen(color, thickness))

        
        p.drawLine(0, cy, self.screen_width, cy)
        
        p.drawLine(cx, 0, cx, self.screen_height)

        
        p.setPen(Qt.NoPen)
        p.setBrush(QColor(255, 255, 255, 220))
        glow_radius = 6 + extra * 0.5
        p.drawEllipse(QPointF(cx, cy), glow_radius, glow_radius)



def main():
    app = QApplication(sys.argv)
    overlay = CrosshairOverlay(1920, 1080)
    overlay.show()
    sys.exit(app.exec_())


if __name__ == "__main__":
    main()
