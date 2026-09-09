from __future__ import annotations

import json
import re
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Tuple, Any

import requests
from PySide6.QtCore import (
    Qt,
    QThread,
    Signal,
    QTimer,
    QPropertyAnimation,
    QEasingCurve,
    QSize,
    QPoint,
    QEvent,
    QDateTime,
)
from PySide6.QtGui import (
    QAction,
    QPixmap,
    QKeyEvent,
    QFont,
    QPalette,
    QColor,
    QIcon,
    QPainter,
    QCursor,
)
from PySide6.QtWidgets import (
    QFrame,
    QHBoxLayout,
    QLabel,
    QProgressBar,
    QLineEdit,
    QListWidget,
    QAbstractItemView,
    QListWidgetItem,
    QMainWindow,
    QMessageBox,
    QPushButton,
    QSizePolicy,
    QSplitter,
    QStackedWidget,
    QToolBar,
    QVBoxLayout,
    QWidget,
    QDialog,
    QGraphicsOpacityEffect,
    QGraphicsDropShadowEffect,
    QScrollArea,
    QSpacerItem,
    QScrollBar,
    QApplication,
    QDialogButtonBox,
)

from iptvgui.player import Player
from iptvgui.providers import load_stalker_portals
from iptvgui.stalker_api import StalkerSession

# EPG (z Twojego projektu)
from iptvgui.epg import (
    EpgNowNext,
    fetch_xmltv_bytes,
    parse_xmltv_index_and_now_next,
    normalize_name,
)


# ----------------------------
# Models
# ----------------------------

@dataclass
class MediaItem:
    name: str
    url: str
    group: str = ""
    tvg_id: str = ""
    tvg_logo: str = ""
    kind: str = "live"  # live | vod | series

    host: str = ""
    stream_id: Optional[int] = None
    xt_type: str = ""  # "vod" | "series" | ""


# ----------------------------
# Xtream helper (player_api.php)
# ----------------------------

class XtreamClient:
    def __init__(self, base: str, username: str, password: str) -> None:
        self.base = (base or "").strip().rstrip("/")
        self.username = (username or "").strip()
        self.password = (password or "").strip()

    def _get(self, params: dict, timeout: int = 20) -> Optional[dict]:
        if not self.base or not self.username or not self.password:
            return None
        try:
            url = f"{self.base}/player_api.php"
            p = {"username": self.username, "password": self.password}
            p.update(params or {})
            r = requests.get(
                url,
                params=p,
                timeout=timeout,
                headers={"User-Agent": "Mozilla/5.0 IPTV_on_the_GO/1.1"},
                allow_redirects=True,
            )
            if r.status_code != 200:
                return {"_http_status": r.status_code, "_text_head": (r.text or "")[:300]}
            try:
                js = r.json()
            except Exception:
                return {"_http_status": r.status_code, "_text_head": (r.text or "")[:600]}
            if isinstance(js, dict):
                js["_http_status"] = r.status_code
            return js if isinstance(js, dict) else {"_http_status": r.status_code, "_not_dict": True}
        except Exception as e:
            return {"_error": str(e)}

    def get_vod_info(self, vod_id: int) -> Optional[dict]:
        return self._get({"action": "get_vod_info", "vod_id": int(vod_id)}, timeout=25)

    def get_series_info(self, series_id: int) -> Optional[dict]:
        return self._get({"action": "get_series_info", "series_id": int(series_id)}, timeout=25)


def _infer_host(url: str) -> str:
    u = (url or "").strip()
    m = re.match(r"^https?://([^/]+)/", u, flags=re.IGNORECASE)
    return (m.group(1) or "").strip().lower() if m else ""


# ----------------------------
# M3U parsing
# ----------------------------

_RE_EXTINF = re.compile(r"#EXTINF:(?P<attrs>[^,]*),(?P<name>.*)$", flags=re.IGNORECASE)


def _parse_extinf_attrs(attrs: str) -> Dict[str, str]:
    out: Dict[str, str] = {}
    for m in re.finditer(r'(\w[\w\-]*)="([^"]*)"', attrs or ""):
        out[m.group(1).strip()] = (m.group(2) or "").strip()
    return out


def _extract_tvg_url_from_m3u(text: str) -> List[str]:
    if not text:
        return []
    lines = text.splitlines()
    head = lines[0] if lines else ""
    urls: List[str] = []
    for key in ("url-tvg", "tvg-url"):
        m = re.search(rf'{key}="([^"]+)"', head, flags=re.IGNORECASE)
        if m:
            u = (m.group(1) or "").strip()
            if u:
                urls.append(u)
    return urls


def _detect_kind_from_url(url: str) -> str:
    u = (url or "").lower()
    if "/movie/" in u or "type=movie" in u or "/vod/" in u:
        return "vod"
    if "/series/" in u or "type=series" in u:
        return "series"
    if "/live/" in u or "type=itv" in u:
        return "live"
    return "live"


def _detect_kind_from_attrs(attrs: Dict[str, str], url: str) -> str:
    tt = (attrs.get("tvg-type", "") or attrs.get("type", "") or "").strip().lower()
    if tt in ("movie", "vod", "video"):
        return "vod"
    if tt in ("series", "tvshow", "show"):
        return "series"
    gt = (attrs.get("group-title", "") or "").strip().lower()
    if any(x in gt for x in ("vod", "film", "movie", "movies")):
        return "vod"
    if any(x in gt for x in ("series", "serial", "tv shows", "shows")):
        return "series"
    return _detect_kind_from_url(url)


def _xtream_type_and_id_from_stream_url(url: str) -> Tuple[str, Optional[int]]:
    u = (url or "").strip()
    # Nowa REGEX: obsługuje różne formaty Xtream
    m = re.match(r"^https?://[^/]+/(movie|series|live)/[^/]+/[^/]+/(\d+)", u, flags=re.IGNORECASE)
    if not m:
        # Spróbuj inny format: /series.php?seriesid=...
        m2 = re.search(r"seriesid[=:](\d+)", u, flags=re.IGNORECASE)
        if m2:
            return "series", int(m2.group(1))
        m3 = re.search(r"id[=:](\d+)", u, flags=re.IGNORECASE)
        if m3:
            # Nie wiemy czy to vod czy series, sprawdźmy URL
            if "series" in u.lower():
                return "series", int(m3.group(1))
            elif "movie" in u.lower():
                return "vod", int(m3.group(1))
        return "", None
    
    kind = m.group(1).lower()
    sid = int(m.group(2))
    if kind == "movie":
        return "vod", sid
    if kind == "series":
        return "series", sid
    return "", sid


def parse_m3u(text: str) -> Tuple[List[MediaItem], List[str]]:
    items: List[MediaItem] = []
    epg_urls = _extract_tvg_url_from_m3u(text)

    lines = [ln.strip() for ln in (text or "").splitlines() if ln.strip()]
    pending: Optional[Tuple[Dict[str, str], str]] = None

    for ln in lines:
        if ln.startswith("#EXTINF:"):
            m = _RE_EXTINF.match(ln)
            if m:
                attrs = _parse_extinf_attrs(m.group("attrs") or "")
                name = (m.group("name") or "").strip()
                pending = (attrs, name)
            continue

        if not ln.startswith("#") and pending:
            attrs, name = pending
            tvg_id = (attrs.get("tvg-id", "") or attrs.get("xmltv_id", "") or "").strip()
            logo = (attrs.get("tvg-logo", "") or "").strip()
            group = (attrs.get("group-title", "") or "").strip()
            kind = _detect_kind_from_attrs(attrs, ln)

            host = _infer_host(ln)
            xt_type, stream_id = _xtream_type_and_id_from_stream_url(ln)

            items.append(
                MediaItem(
                    name=name or "Unknown",
                    url=ln,
                    group=group,
                    tvg_id=tvg_id,
                    tvg_logo=logo,
                    kind=kind,
                    host=host,
                    stream_id=stream_id,
                    xt_type=xt_type,
                )
            )
            pending = None

    return items, epg_urls


def _dedup_keep_order(urls: List[str]) -> List[str]:
    seen = set()
    out: List[str] = []
    for u in urls:
        u = (u or "").strip()
        if not u or u in seen:
            continue
        seen.add(u)
        out.append(u)
    return out


# ----------------------------
# FULLSCREEN host (ten sam widget video)
# ----------------------------


class LiveInfoBarOverlay(QWidget):
    """
    Prosty infobar do FullScreen dla LIVE TV.
    - pokazuje się na starcie oraz po wciśnięciu OK/Enter
    - auto-ukrywanie po kilku sekundach (fade in/out)
    Dane dostarcza callback: fn() -> dict
    """
    def __init__(self, parent: QWidget):
        super().__init__(parent)
        self.setObjectName("liveInfoBar")
        self.setAttribute(Qt.WA_TransparentForMouseEvents, True)
        self.setStyleSheet("""
            QWidget#liveInfoBar {
                background: rgba(10,10,10,170);
                border: 1px solid rgba(255,255,255,35);
                border-radius: 14px;
            }
            QLabel { color: #fff; }
        """)
        self._cb = None
        self._hide_timer = QTimer(self)
        self._hide_timer.setSingleShot(True)
        self._hide_timer.timeout.connect(self.hide_fade)

        # layout
        root = QHBoxLayout(self)
        root.setContentsMargins(14, 10, 14, 10)
        root.setSpacing(12)

        self.lbl_picon = QLabel()
        self.lbl_picon.setFixedSize(56, 56)
        self.lbl_picon.setScaledContents(True)
        self.lbl_picon.setStyleSheet("background: rgba(0,0,0,60); border-radius:10px;")
        root.addWidget(self.lbl_picon, 0, Qt.AlignVCenter)

        mid = QVBoxLayout()
        mid.setSpacing(6)
        self.lbl_now = QLabel("—")
        self.lbl_now.setStyleSheet("font-weight:600; font-size:16px;")
        self.lbl_now_time = QLabel("")
        self.lbl_now_time.setStyleSheet("color: rgba(255,255,255,180); font-size:12px;")
        mid.addWidget(self.lbl_now)
        mid.addWidget(self.lbl_now_time)

        self.bar = QProgressBar()
        self.bar.setTextVisible(False)
        self.bar.setFixedHeight(6)
        self.bar.setRange(0, 1000)
        self.bar.setValue(0)
        self.bar.setStyleSheet("""
            QProgressBar { background: rgba(255,255,255,35); border-radius:3px; }
            QProgressBar::chunk { background: rgba(255,255,255,220); border-radius:3px; }
        """)
        mid.addWidget(self.bar)

        self.lbl_next = QLabel("—")
        self.lbl_next.setStyleSheet("font-size:13px; color: rgba(255,255,255,210);")
        self.lbl_next_time = QLabel("")
        self.lbl_next_time.setStyleSheet("color: rgba(255,255,255,160); font-size:11px;")
        mid.addWidget(self.lbl_next)
        mid.addWidget(self.lbl_next_time)

        root.addLayout(mid, 1)

        right = QVBoxLayout()
        right.setSpacing(4)
        right.setAlignment(Qt.AlignRight | Qt.AlignVCenter)
        self.lbl_quality = QLabel("—")
        self.lbl_quality.setStyleSheet("font-weight:600;")
        self.lbl_fps = QLabel("")
        self.lbl_fps.setStyleSheet("color: rgba(255,255,255,160); font-size:11px;")
        self.lbl_clock = QLabel("")
        self.lbl_clock.setStyleSheet("color: rgba(255,255,255,200); font-size:12px;")
        right.addWidget(self.lbl_quality, 0, Qt.AlignRight)
        right.addWidget(self.lbl_fps, 0, Qt.AlignRight)
        right.addWidget(self.lbl_clock, 0, Qt.AlignRight)
        root.addLayout(right)

        # fade
        self._fx = QGraphicsOpacityEffect(self)
        self.setGraphicsEffect(self._fx)
        self._anim = QPropertyAnimation(self._fx, b"opacity", self)
        self._anim.setDuration(220)
        self._anim.setEasingCurve(QEasingCurve.OutCubic)
        self._want_hide = False
        self._anim.finished.connect(self._on_anim_finished)

        self.hide()


    def _on_anim_finished(self):
        # Hide only after fade-out.
        if getattr(self, '_want_hide', False):
            try:
                self.hide()
            except Exception:
                pass

    def set_callback(self, cb):
        self._cb = cb

    def refresh(self):
        if not self._cb:
            return
        try:
            d = self._cb() or {}
        except Exception:
            d = {}
        self.lbl_now.setText(d.get("now_title") or "—")
        self.lbl_now_time.setText(d.get("now_time") or "")
        self.lbl_next.setText(d.get("next_title") or "—")
        self.lbl_next_time.setText(d.get("next_time") or "")
        self.lbl_quality.setText(d.get("quality") or "—")
        self.lbl_fps.setText(d.get("fps") or "")
        self.lbl_clock.setText(d.get("clock") or "")

        prog = d.get("progress")
        if isinstance(prog, (int, float)):
            v = int(max(0.0, min(1.0, float(prog))) * 1000)
            self.bar.setValue(v)
        else:
            self.bar.setValue(0)

        px = d.get("picon_pixmap")
        if px is not None:
            self.lbl_picon.setPixmap(px)
        else:
            self.lbl_picon.clear()

    def show_fade(self, timeout_ms: int = 4500):
        self.refresh()
        self._hide_timer.stop()
        self._want_hide = False
        self.show()
        self.raise_()
        self._anim.stop()
        self._anim.setStartValue(self._fx.opacity())
        self._anim.setEndValue(1.0)
        self._anim.start()
        if timeout_ms > 0:
            self._hide_timer.start(timeout_ms)

    def hide_fade(self):
        if not self.isVisible():
            return
    def hide_fade(self):
        if not self.isVisible():
            return
        self._want_hide = True
        self._anim.stop()
        self._anim.setStartValue(self._fx.opacity())
        self._anim.setEndValue(0.0)
        self._anim.start()

    def __init__(self, video_widget: QWidget):
        super().__init__(None, Qt.Window | Qt.FramelessWindowHint)
        self.setAttribute(Qt.WA_DeleteOnClose, True)
        self.setFocusPolicy(Qt.StrongFocus)
        self._video = video_widget

        lay = QVBoxLayout(self)
        lay.setContentsMargins(0, 0, 0, 0)
        lay.setSpacing(0)
        lay.addWidget(self._video)

        # --- LIVE fullscreen infobar overlay ---
        self._info_cb = None
        self._info_overlay = LiveInfoBarOverlay(self)
        self._info_overlay.set_callback(lambda: self._info_cb() if self._info_cb else {})
        self._info_overlay.hide()

        self._info_enabled = False



    def set_info_callback(self, cb):
        self._info_cb = cb

    def set_infobar_enabled(self, enabled: bool) -> None:
        self._info_enabled = bool(enabled)
        if not self._info_enabled:
            try:
                self._info_overlay.hide()
            except Exception:
                pass

    def show_info_bar(self, timeout_ms: int = 4500):
        try:
            self._info_overlay.show_fade(timeout_ms=timeout_ms)
        except Exception:
            pass

    def resizeEvent(self, e):
        super().resizeEvent(e)
        try:
            m = 24
            h = 150
            w = max(400, int(self.width() * 0.78))
            x = int((self.width() - w) / 2)
            y = self.height() - h - m
            self._info_overlay.setGeometry(x, y, w, h)
        except Exception:
            pass


    def open_fullscreen(self) -> None:
        self.showFullScreen()
        self.raise_()
        self.activateWindow()
        self.grabKeyboard()
        self.setFocus()

    def keyPressEvent(self, e: QKeyEvent) -> None:
        k = e.key()

        # WSTECZ zawsze działa
        if k in (Qt.Key_Escape, Qt.Key_Back, Qt.Key_Backspace):
            self.close()
            return

        # Infobar tylko jeśli włączony (LIVE)
        if self._info_enabled and k in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Select, Qt.Key_Space):
            self.show_info_bar(timeout_ms=4500)
            e.accept()
            return

        super().keyPressEvent(e)


    def mouseDoubleClickEvent(self, _e) -> None:
        self.close()

    def closeEvent(self, e) -> None:
        try:
            self.releaseKeyboard()
        except Exception:
            pass
        self.closed.emit()
        super().closeEvent(e)


# ----------------------------
# Nowe okno detalu filmu/serialu
# ----------------------------

class MediaDetailDialog(QDialog):
    """Nowe okno detalu filmu/serialu z posterem, opisem i przyciskiem OGLĄDAJ"""

    def __init__(self, media_item: MediaItem, meta_data: dict, parent=None):
        super().__init__(parent)
        self.media_item = media_item
        # IMPORTANT FIX: nie mutuj oryginalnego słownika z cache
        self.meta_data = dict(meta_data or {})

        self.setWindowTitle("Szczegóły")
        self.setWindowFlags(self.windowFlags() | Qt.WindowStaysOnTopHint)
        self.resize(900, 600)
        self.setFocusPolicy(Qt.StrongFocus)

        # Ustawiamy style dla dialogu
        self._setup_styles()

        self._build_ui()
        self._load_data()

        # Ustawiamy focus na opisie (dla uproszczonej nawigacji)
        self.plot_label.setFocus()
        self._is_watch_button_focused = False

    def _setup_styles(self):
        """Ustawia style CSS dla dialogu"""
        self.setStyleSheet(
            """
            QDialog {
                background: #0a0a0a;
                border: 2px solid #2a2a2a;
                border-radius: 15px;
            }
            QLabel {
                color: #e6e6e6;
            }
            QPushButton#watchButtonNormal {
                background: linear-gradient(to bottom, #1a3a1a, #0a2a0a);
                border: 2px solid #3a8c3a;
                border-radius: 10px;
                color: white;
                font-size: 18px;
                font-weight: bold;
                padding: 15px 30px;
            }
            QPushButton#watchButtonNormal:hover {
                background: linear-gradient(to bottom, #2a5c2a, #1a4a1a);
                border: 2px solid #4aac4a;
            }
            QPushButton#watchButtonNormal:pressed {
                background: linear-gradient(to bottom, #0a2a0a, #001a00);
            }
            QPushButton#watchButtonFocused {
                background: linear-gradient(to bottom, #3a8c3a, #2a5c2a);
                border: 3px solid #5acc5a;
                border-radius: 10px;
                color: white;
                font-size: 18px;
                font-weight: bold;
                padding: 15px 30px;
            }
            QPushButton#watchButtonFocused:hover {
                background: linear-gradient(to bottom, #4aac4a, #3a8c3a);
                border: 3px solid #6aec6a;
            }
            QPushButton#watchButtonFocused:pressed {
                background: linear-gradient(to bottom, #2a5c2a, #1a4a1a);
            }
        """
        )

    def _build_ui(self):
        layout = QVBoxLayout(self)
        layout.setContentsMargins(20, 20, 20, 20)
        layout.setSpacing(15)

        # Główny kontener
        main_widget = QWidget()
        main_layout = QHBoxLayout(main_widget)
        main_layout.setContentsMargins(0, 0, 0, 0)
        main_layout.setSpacing(25)

        # Lewa strona - poster
        poster_container = QFrame()
        poster_container.setFixedWidth(300)
        poster_layout = QVBoxLayout(poster_container)
        poster_layout.setContentsMargins(0, 0, 0, 0)

        self.poster_label = QLabel()
        self.poster_label.setFixedSize(280, 420)
        self.poster_label.setScaledContents(True)
        self.poster_label.setStyleSheet(
            """
            QLabel {
                background: #111;
                border: 2px solid #333;
                border-radius: 10px;
                padding: 5px;
            }
        """
        )
        poster_layout.addWidget(self.poster_label, 0, Qt.AlignCenter)

        # Prawa strona - szczegóły
        details_container = QWidget()
        details_layout = QVBoxLayout(details_container)
        details_layout.setContentsMargins(0, 0, 0, 0)
        details_layout.setSpacing(12)

        # Tytuł
        self.title_label = QLabel()
        self.title_label.setWordWrap(True)
        title_font = QFont()
        title_font.setPointSize(22)
        title_font.setBold(True)
        self.title_label.setFont(title_font)
        self.title_label.setStyleSheet("color: #ffffff; padding: 5px;")

        # Informacje liniowe
        self.info_label = QLabel()
        self.info_label.setWordWrap(True)
        info_font = QFont()
        info_font.setPointSize(14)
        self.info_label.setFont(info_font)
        self.info_label.setStyleSheet("color: #aaaaaa; padding: 5px;")

        # Opis (scrollable)
        scroll_area = QScrollArea()
        scroll_area.setWidgetResizable(True)
        scroll_area.setStyleSheet(
            """
            QScrollArea {
                background: transparent;
                border: 1px solid #333;
                border-radius: 8px;
            }
            QScrollBar:vertical {
                background: #1a1a1a;
                width: 12px;
                border-radius: 6px;
            }
            QScrollBar::handle:vertical {
                background: #3a3a3a;
                border-radius: 6px;
                min-height: 20px;
            }
            QScrollBar::handle:vertical:hover {
                background: #4a4a4a;
            }
        """
        )

        plot_container = QWidget()
        plot_layout = QVBoxLayout(plot_container)
        plot_layout.setContentsMargins(15, 15, 15, 15)

        self.plot_label = QLabel()
        self.plot_label.setWordWrap(True)
        self.plot_label.setTextFormat(Qt.RichText)
        self.plot_label.setFocusPolicy(Qt.StrongFocus)
        plot_font = QFont()
        plot_font.setPointSize(13)
        self.plot_label.setFont(plot_font)
        self.plot_label.setStyleSheet("color: #cccccc;")
        self.plot_label.setAlignment(Qt.AlignTop | Qt.AlignLeft)
        self.plot_label.setFocusPolicy(Qt.StrongFocus)

        plot_layout.addWidget(self.plot_label)
        scroll_area.setWidget(plot_container)

        # Dodaj do layoutu szczegółów
        details_layout.addWidget(self.title_label)
        details_layout.addWidget(self.info_label)
        details_layout.addWidget(scroll_area, 1)  # 1 = rozciągnij

        # Dodaj lewą i prawą stronę do głównego layoutu
        main_layout.addWidget(poster_container)
        main_layout.addWidget(details_container, 1)  # 1 = rozciągnij

        # Przycisk OGLĄDAJ
        self.watch_button = QPushButton("▶ OGLĄDAJ")
        self.watch_button.setFocusPolicy(Qt.StrongFocus)
        self.watch_button.setMinimumHeight(60)
        self.watch_button.setObjectName("watchButtonNormal")  # Domyślnie normalny styl
        self.watch_button.setIcon(QIcon.fromTheme("media-playback-start"))
        self.watch_button.clicked.connect(self._on_watch_clicked)

        # Klawisze z pilota/klawiatury czasem trafiają do dzieci (scroll/viewport/przycisk),
        # więc przechwytujemy je przez eventFilter.
        for wdg in (self, self.plot_label, self.watch_button, scroll_area, scroll_area.viewport()):
            wdg.installEventFilter(self)

        # Dodaj wszystko do głównego layoutu
        layout.addWidget(main_widget, 1)  # 1 = rozciągnij
        layout.addWidget(self.watch_button, 0, Qt.AlignCenter)

    def _load_data(self):
        # Tytuł
        title = self.meta_data.get("title") or self.media_item.name or "—"
        self.title_label.setText(title)

        # Informacje liniowe
        info_parts = []

        year = (self.meta_data.get("year") or "").strip()
        if year:
            info_parts.append(f"<b>Rok:</b> {year}")

        duration = (self.meta_data.get("duration") or "").strip()
        if duration:
            info_parts.append(f"<b>Czas:</b> {duration}")

        genre = (self.meta_data.get("genre") or "").strip()
        if genre:
            info_parts.append(f"<b>Gatunek:</b> {genre}")

        rating = (self.meta_data.get("rating") or "").strip()
        if rating:
            info_parts.append(f"<b>Ocena:</b> {rating}")

        source = (self.meta_data.get("source") or "").strip()
        if source:
            info_parts.append(f"<b>Źródło:</b> {source}")

        self.info_label.setText("  •  ".join(info_parts) if info_parts else "")

        # Opis
        plot = (self.meta_data.get("plot") or "").strip()
        if not plot:
            plot = "Brak opisu."

        # Formatowanie opisu
        formatted_plot = f"<p style='line-height: 140%;'>{plot}</p>"

        # Obsada
        cast = (self.meta_data.get("cast") or "").strip()
        if cast:
            formatted_plot += f"<br><br><b>Obsada:</b><br>{cast}"

        self.plot_label.setText(formatted_plot)

        # Poster
        poster_url = (self.meta_data.get("poster") or self.media_item.tvg_logo or "").strip()
        if poster_url.lower().startswith(("http://", "https://")):
            self._load_poster(poster_url)

    def _load_poster(self, url: str):
        try:
            r = requests.get(url, timeout=10, headers={"User-Agent": "Mozilla/5.0 IPTV_on_the_GO/1.1"})
            if r.status_code == 200:
                pixmap = QPixmap()
                if pixmap.loadFromData(r.content):
                    self.poster_label.setPixmap(
                        pixmap.scaled(self.poster_label.size(), Qt.KeepAspectRatio, Qt.SmoothTransformation)
                    )
        except Exception:
            pass

    def _on_watch_clicked(self):
        # Kliknięcie / Enter / OK -> uruchom
        self.accept()

    def _set_watch_button_focused(self, focused: bool):
        """Ustawia stan focusu przycisku OGLĄDAJ"""
        self._is_watch_button_focused = focused

        if focused:
            # zielone podświetlenie + grubsza ramka
            try:
                eff = QGraphicsDropShadowEffect(self.watch_button)
                eff.setBlurRadius(35)
                eff.setOffset(0, 0)
                eff.setColor(QColor(90, 204, 90))
                self.watch_button.setGraphicsEffect(eff)
            except Exception:
                pass

            self.watch_button.setObjectName("watchButtonFocused")
            self.watch_button.setStyleSheet(
                """
                QPushButton#watchButtonFocused {
                    background: linear-gradient(to bottom, #3a8c3a, #2a5c2a);
                    border: 3px solid #5acc5a;
                    border-radius: 10px;
                    color: white;
                    font-size: 18px;
                    font-weight: bold;
                    padding: 15px 30px;
                }
                QPushButton#watchButtonFocused:hover {
                    background: linear-gradient(to bottom, #4aac4a, #3a8c3a);
                    border: 3px solid #6aec6a;
                }
                QPushButton#watchButtonFocused:pressed {
                    background: linear-gradient(to bottom, #2a5c2a, #1a4a1a);
                }
            """
            )
        else:
            try:
                self.watch_button.setGraphicsEffect(None)
            except Exception:
                pass

            self.watch_button.setObjectName("watchButtonNormal")
            self.watch_button.setStyleSheet(
                """
                QPushButton#watchButtonNormal {
                    background: linear-gradient(to bottom, #1a3a1a, #0a2a0a);
                    border: 2px solid #3a8c3a;
                    border-radius: 10px;
                    color: white;
                    font-size: 18px;
                    font-weight: bold;
                    padding: 15px 30px;
                }
                QPushButton#watchButtonNormal:hover {
                    background: linear-gradient(to bottom, #2a5c2a, #1a4a1a);
                    border: 2px solid #4aac4a;
                }
                QPushButton#watchButtonNormal:pressed {
                    background: linear-gradient(to bottom, #0a2a0a, #001a00);
                }
            """
            )

        self.watch_button.update()

    def _handle_detail_key(self, e: QKeyEvent) -> bool:
        # UPROSZCZONA LOGIKA: opis → strzałka w prawo → przycisk → Enter → odtwarzaj
        if e.key() in (Qt.Key_Escape, Qt.Key_Back, Qt.Key_Backspace):
            self.reject()
            e.accept()
            return True
        if e.key() == Qt.Key_Right:
            self.watch_button.setFocus()
            self._set_watch_button_focused(True)
            e.accept()
            return True
        if e.key() == Qt.Key_Left:
            self.plot_label.setFocus()
            self._set_watch_button_focused(False)
            e.accept()
            return True
        if e.key() in (Qt.Key_Return, Qt.Key_Enter):
            if self._is_watch_button_focused:
                self.accept()
                e.accept()
                return True
            # Enter na opisie nic nie robi
            e.ignore()
            return True
        return False

    def eventFilter(self, obj, event):
        if event.type() == QEvent.Type.KeyPress:
            if self._handle_detail_key(event):
                return True
        return super().eventFilter(obj, event)

    def keyPressEvent(self, e: QKeyEvent):
        if self._handle_detail_key(e):
            return
        super().keyPressEvent(e)

    def focusInEvent(self, e):
        super().focusInEvent(e)
        # Domyślnie focus na opisie
        if not self._is_watch_button_focused:
            self.plot_label.setFocus()


# ----------------------------
# Dialog potwierdzenia wyjścia
# ----------------------------

class ExitConfirmationDialog(QDialog):
    """Dialog potwierdzenia wyjścia z aplikacji"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Potwierdzenie wyjścia")
        self.setWindowFlags(self.windowFlags() | Qt.WindowStaysOnTopHint)
        self.resize(500, 200)
        self.setStyleSheet(
            """
            QDialog {
                background: #0a0a0a;
                border: 2px solid #2a2a2a;
                border-radius: 15px;
            }
            QLabel {
                color: #e6e6e6;
                font-size: 16px;
                padding: 10px;
            }
            QPushButton {
                background: #222;
                border: 2px solid #333;
                border-radius: 8px;
                color: white;
                font-size: 16px;
                font-weight: bold;
                padding: 12px 24px;
                min-width: 100px;
            }
            QPushButton:hover {
                background: #2a2a2a;
            }
            QPushButton:focus {
                border: 3px solid #5acc5a;
            }
        """
        )

        self._build_ui()

    def _build_ui(self):
        layout = QVBoxLayout(self)
        layout.setContentsMargins(30, 30, 30, 30)
        layout.setSpacing(20)

        # Tekst pytania
        self.label = QLabel("Czy na pewno chcesz wyjść z aplikacji?")
        self.label.setAlignment(Qt.AlignCenter)

        # Przyciski
        buttons_layout = QHBoxLayout()
        buttons_layout.setSpacing(30)

        self.btn_no = QPushButton("NIE")
        self.btn_no.setStyleSheet(
            """
            QPushButton {
                background: linear-gradient(to bottom, #1a3a1a, #0a2a0a);
                border: 2px solid #3a8c3a;
            }
            QPushButton:hover {
                background: linear-gradient(to bottom, #2a5c2a, #1a4a1a);
                border: 2px solid #4aac4a;
            }
            QPushButton:focus {
                background: linear-gradient(to bottom, #3a8c3a, #2a5c2a);
                border: 3px solid #5acc5a;
            }
        """
        )
        self.btn_no.clicked.connect(self.reject)

        self.btn_yes = QPushButton("TAK")
        self.btn_yes.setStyleSheet(
            """
            QPushButton {
                background: linear-gradient(to bottom, #5a1a1a, #3a0a0a);
                border: 2px solid #cc3a3a;
            }
            QPushButton:hover {
                background: linear-gradient(to bottom, #6a2a2a, #4a1a1a);
                border: 2px solid #dd4a4a;
            }
            QPushButton:focus {
                background: linear-gradient(to bottom, #7a3a3a, #5a2a2a);
                border: 3px solid #ee5a5a;
            }
        """
        )
        self.btn_yes.clicked.connect(self.accept)

        buttons_layout.addStretch()
        buttons_layout.addWidget(self.btn_no)
        buttons_layout.addWidget(self.btn_yes)
        buttons_layout.addStretch()

        layout.addWidget(self.label)
        layout.addLayout(buttons_layout)

        # Ustaw focus na przycisku NIE domyślnie
        self.btn_no.setFocus()

    def keyPressEvent(self, e: QKeyEvent):
        # Obsługa strzałek lewo/prawo
        if e.key() == Qt.Key_Left:
            if self.btn_yes.hasFocus():
                self.btn_no.setFocus()
            e.accept()
        elif e.key() == Qt.Key_Right:
            if self.btn_no.hasFocus():
                self.btn_yes.setFocus()
            e.accept()
        elif e.key() in (Qt.Key_Escape, Qt.Key_Back, Qt.Key_Backspace):
            self.reject()
            e.accept()
        elif e.key() in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Select, Qt.Key_Execute, Qt.Key_Space):
            # Enter - kliknij aktualnie zaznaczony przycisk
            if self.btn_yes.hasFocus():
                self.accept()
            elif self.btn_no.hasFocus():
                self.reject()
            else:
                super().keyPressEvent(e)
        else:
            super().keyPressEvent(e)


# ----------------------------
# Background loader thread
# ----------------------------

class RefreshThread(QThread):
    done = Signal(list, dict, dict, dict)  # items, epg_by_id, name_index, xtream_profiles
    error = Signal(str)

    def __init__(self, data_dir: Path, use_m3u: bool, use_stalker: bool, use_xc: bool) -> None:
        super().__init__()
        self.data_dir = data_dir
        self.use_m3u = use_m3u
        self.use_stalker = use_stalker
        self.use_xc = use_xc

    @staticmethod
    def _extract_xtream_profile_from_getphp(m3u_url: str) -> Optional[dict]:
        u = (m3u_url or "").strip()
        m_host = re.match(r"^(https?://[^/]+)/", u, flags=re.IGNORECASE)
        if not m_host:
            return None
        base = m_host.group(1)
        mu = re.search(r"[?&]username=([^&]+)", u, flags=re.IGNORECASE)
        mp = re.search(r"[?&]password=([^&]+)", u, flags=re.IGNORECASE)
        if not (mu and mp):
            return None
        username = mu.group(1)
        password = mp.group(1)
        host = re.sub(r"^https?://", "", base, flags=re.IGNORECASE).strip().lower()

        # Normalizuj host (usuń port 80 jeśli jest)
        if host.endswith(":80"):
            host = host[:-3]

        return {"host": host, "base": base, "username": username, "password": password}

    def run(self) -> None:
        try:
            items: List[MediaItem] = []
            epg_urls: List[str] = []
            xtream_profiles: Dict[str, dict] = {}

            # M3U list
            if self.use_m3u:
                m3u_file = self.data_dir / "m3ulist.txt"
                if m3u_file.exists():
                    for raw in m3u_file.read_text(encoding="utf-8", errors="ignore").splitlines():
                        line = raw.strip()
                        if not line or line.startswith("#"):
                            continue

                        parts = [p.strip() for p in line.split("|", 1)]
                        m3u_url = parts[0]
                        if len(parts) == 2 and parts[1]:
                            epg_urls.extend([u.strip() for u in parts[1].split(",") if u.strip()])

                        prof = self._extract_xtream_profile_from_getphp(m3u_url)
                        if prof:
                            xtream_profiles[prof["host"]] = prof

                        if m3u_url.lower().startswith(("http://", "https://")):
                            r = requests.get(
                                m3u_url,
                                timeout=180,
                                headers={"User-Agent": "Mozilla/5.0 IPTV_on_the_GO/1.1"},
                                allow_redirects=True,
                            )
                            r.raise_for_status()
                            got, header_epg = parse_m3u(r.text)
                            items.extend(got)
                            epg_urls.extend(header_epg)

            # XC
            if self.use_xc:
                xc_file = self.data_dir / "xccodes.txt"
                if xc_file.exists():
                    for raw in xc_file.read_text(encoding="utf-8", errors="ignore").splitlines():
                        line = raw.strip()
                        if not line or line.startswith("#"):
                            continue

                        parts = [p.strip() for p in line.split("|", 1)]
                        m3u_url = parts[0]
                        if len(parts) == 2 and parts[1]:
                            epg_urls.extend([u.strip() for u in parts[1].split(",") if u.strip()])

                        prof = self._extract_xtream_profile_from_getphp(m3u_url)
                        if prof:
                            xtream_profiles[prof["host"]] = prof

                        if m3u_url.lower().startswith(("http://", "https://")):
                            r = requests.get(
                                m3u_url,
                                timeout=180,
                                headers={"User-Agent": "Mozilla/5.0 IPTV_on_the_GO/1.1"},
                                allow_redirects=True,
                            )
                            r.raise_for_status()
                            got, header_epg = parse_m3u(r.text)
                            items.extend(got)
                            epg_urls.extend(header_epg)

            # STALKER (LIVE)
            if self.use_stalker:
                stalker_txt = self.data_dir / "stalker.txt"
                if stalker_txt.exists():
                    for raw in stalker_txt.read_text(encoding="utf-8", errors="ignore").splitlines():
                        line = raw.strip()
                        if not line or line.startswith("#"):
                            continue
                        parts = [p.strip() for p in line.split("|", 1)]
                        if len(parts) == 2 and parts[1]:
                            epg_urls.extend([u.strip() for u in parts[1].split(",") if u.strip()])

                try:
                    stalkers = load_stalker_portals(self.data_dir)
                except Exception:
                    stalkers = []

                for sp in stalkers:
                    sess = StalkerSession(
                        sp.portal_url,
                        sp.mac,
                        sp.serial or "",
                        sp.device1 or "",
                        sp.device2 or "",
                        timeout_s=25,
                    )
                    sch = sess.get_all_channels()
                    for it in sch:
                        items.append(
                            MediaItem(
                                name=it.name,
                                url=f"stalker://{sp.name}::{it.id}::{it.cmd}",
                                group=(it.group or "STALKER") if hasattr(it, "group") else "STALKER",
                                tvg_id=(it.tvg_id or "").strip(),
                                tvg_logo=(it.tvg_logo or "").strip(),
                                kind="live",
                            )
                        )

            epg_urls = _dedup_keep_order([u for u in epg_urls if u])

            try:
                (self.data_dir / "epg_urls_used.txt").write_text("\n".join(epg_urls), encoding="utf-8")
            except Exception:
                pass

            epg_by_id: Dict[str, EpgNowNext] = {}
            epg_by_name: Dict[str, EpgNowNext] = {}
            icon_by_id: Dict[str, str] = {}
            icon_by_name: Dict[str, str] = {}

            fetch_logs: List[str] = []
            for url in epg_urls[:40]:
                xml_bytes, log_line = fetch_xmltv_bytes(url, timeout_s=120, retries=2)
                fetch_logs.append(log_line)
                if not xml_bytes:
                    continue

                by_id, _id_to_name, id_to_icon, by_name, name_to_icon = parse_xmltv_index_and_now_next(xml_bytes)

                for k, v in by_id.items():
                    if k not in epg_by_id:
                        epg_by_id[k] = v
                for k, v in by_name.items():
                    if k not in epg_by_name:
                        epg_by_name[k] = v
                for k, v in id_to_icon.items():
                    if k not in icon_by_id and v:
                        icon_by_id[k] = v
                for k, v in name_to_icon.items():
                    if k not in icon_by_name and v:
                        icon_by_name[k] = v

            try:
                (self.data_dir / "epg_fetch_log.txt").write_text("\n".join(fetch_logs), encoding="utf-8")
            except Exception:
                pass

            name_index = {
                "epg_by_name": epg_by_name,
                "icon_by_id": icon_by_id,
                "icon_by_name": icon_by_name,
            }

            self.done.emit(items, epg_by_id, name_index, xtream_profiles)

        except Exception as e:
            self.error.emit(str(e))


# ----------------------------
# Helpers: title/year parsing for TMDB/OMDb
# ----------------------------

_RE_YEAR = re.compile(r"(19\d{2}|20\d{2})")
_RE_BRACKETS = re.compile(r"[\[\]\(\)\{\}]")
_RE_TAGS = re.compile(
    r"\b(uhd|fhd|hd|sd|4k|8k|hevc|h\.?265|h\.?264|aac|ddp|dolby|multi|pl|pol|uk|de|fr|it|es)\b",
    re.IGNORECASE,
)


def _clean_title_for_search(name: str) -> Tuple[str, Optional[str]]:
    n = (name or "").strip()

    # usuń gwiazdki/ikonki ulubionych i wiodące znaki
    n = n.lstrip("★☆ ").strip()

    # często kanały/pozycje mają prefiks językowy typu "EN -", "FR ★" itp.
    n = re.sub(r"^(?:[A-Z]{2,3}\s*[-|:]\s*)", "", n).strip()
    n = n.lstrip("★☆ ").strip()

    # czasem nazwa jest w formacie "PL|Tytuł"
    if "|" in n:
        n = n.split("|", 1)[1].strip()

    n2 = _RE_BRACKETS.sub(" ", n)
    n2 = re.sub(r"\s+", " ", n2).strip()

    # usuń typowe tagi jakości/językowe
    n3 = _RE_TAGS.sub(" ", n2)
    n3 = re.sub(r"\s+", " ", n3).strip()

    # usuń oznaczenia odcinków: S01 E03 / 1x03
    n3 = re.sub(r"\bS\d{1,2}\s*E\d{1,3}\b", " ", n3, flags=re.IGNORECASE)
    n3 = re.sub(r"\b\d{1,2}x\d{1,3}\b", " ", n3, flags=re.IGNORECASE)
    n3 = re.sub(r"\s+", " ", n3).strip()

    year = None
    m = _RE_YEAR.search(n3)
    if m:
        year = m.group(1)
        n3 = re.sub(rf"\b{re.escape(year)}\b", " ", n3)
        n3 = re.sub(r"\s+[-–]\s*$", "", n3).strip()
        n3 = re.sub(r"\s+", " ", n3).strip()

    n3 = re.sub(r"\s*[-–]\s*\Z", "", n3).strip()

    return (n3 if n3 else (name or "Unknown").strip(), year)



# ----------------------------
# Metadata thread: SERWER (Xtream) -> potem TMDB/OMDb
# ----------------------------

class MetaThread(QThread):
    done = Signal(str, dict)   # url, meta
    error = Signal(str, str)   # url, msg

    def __init__(
        self,
        data_dir: Path,
        url: str,
        it: MediaItem,
        xtream_profiles: Dict[str, dict],
        tmdb_key: str,
        omdb_key: str,
    ):
        super().__init__()
        self.data_dir = Path(data_dir)
        self.url = url
        self.it = it
        self.xtream_profiles = dict(xtream_profiles or {})
        self.tmdb_key = (tmdb_key or "").strip()
        self.omdb_key = (omdb_key or "").strip()

    def _normalize_host(self, host: str) -> str:
        """Usuwa port z hosta dla lepszego dopasowania"""
        if not host:
            return ""
        if ":" in host:
            host = host.split(":")[0]
        return host.strip().lower()

    def _meta_base(self) -> Dict[str, Any]:
        return {
            "title": self.it.name,
            "poster": (self.it.tvg_logo or "").strip()
            if (self.it.tvg_logo or "").strip().lower().startswith(("http://", "https://"))
            else "",
            "plot": "",
            "year": "",
            "duration": "",
            "genre": "",
            "rating": "",
            "cast": "",
            "source": "",
        }

    def _log(self, line: str) -> None:
        try:
            p = self.data_dir / "meta_fetch_log.txt"
            p.parent.mkdir(parents=True, exist_ok=True)
            with p.open("a", encoding="utf-8") as f:
                f.write(line.rstrip() + "\n")
        except Exception:
            pass

    def _pick_profile(self) -> Optional[dict]:
        host = (self.it.host or "").strip().lower()
        if not host:
            host = _infer_host(self.it.url)

        host_no_port = self._normalize_host(host)
        if not host_no_port:
            return None

        if host in self.xtream_profiles:
            return self.xtream_profiles[host]

        if host_no_port in self.xtream_profiles:
            return self.xtream_profiles[host_no_port]

        for profile_host, profile_data in self.xtream_profiles.items():
            profile_host_norm = self._normalize_host(profile_host)
            if profile_host_norm == host_no_port:
                return profile_data

        host_parts = host_no_port.split(".")
        if len(host_parts) >= 2:
            main_domain = f"{host_parts[-2]}.{host_parts[-1]}"
            for profile_host, profile_data in self.xtream_profiles.items():
                profile_host_norm = self._normalize_host(profile_host)
                if profile_host_norm.endswith(main_domain):
                    return profile_data

        return None

    def _server_meta(self) -> Optional[Dict[str, Any]]:
        if self.it.kind not in ("vod", "series"):
            return None

        prof = self._pick_profile()
        sid = self.it.stream_id
        typ = self.it.xt_type or ("vod" if self.it.kind == "vod" else "series")

        self._log("\n--- SERIES META TRY ---")
        self._log(f"ITEM: {self.it.name}")
        self._log(f"URL: {self.it.url}")
        self._log(f"HOST: {self.it.host} (inferred={_infer_host(self.it.url)})")
        self._log(f"HOST_NO_PORT: {self._normalize_host(self.it.host or _infer_host(self.it.url))}")
        self._log(f"KIND: {self.it.kind}  XT_TYPE: {typ}  STREAM_ID: {sid}")
        self._log(f"PROFILES: {list(self.xtream_profiles.keys())}")
        self._log(f"PICKED_PROFILE: {'YES' if prof else 'NO'}")

        if not prof:
            self._log("NO_PROFILE: brak profilu xtream dla hosta")
            for ph, pd in self.xtream_profiles.items():
                self._log(f"  PROFILE: {ph} -> base={pd.get('base')} user={pd.get('username')}")
            return None

        if not sid:
            self._log("NO_STREAM_ID: link nie wygląda na /series/.../ID lub seriesid=...")
            # Spróbuj wydobyć ID z URL inaczej
            if "seriesid=" in self.it.url.lower():
                import urllib.parse
                parsed = urllib.parse.urlparse(self.it.url)
                params = urllib.parse.parse_qs(parsed.query)
                series_id = params.get('seriesid') or params.get('id')
                if series_id:
                    try:
                        sid = int(series_id[0])
                        self._log(f"EXTRACTED SERIES_ID from query: {sid}")
                    except:
                        pass
            
            if not sid:
                self._log("STILL NO STREAM_ID")
                return None

        self._log(f"PROFILE_FOUND: base={prof.get('base')} user={prof.get('username')} host={prof.get('host')}")
        cli = XtreamClient(prof.get("base", ""), prof.get("username", ""), prof.get("password", ""))

        js = None
        if typ == "vod":
            js = cli.get_vod_info(int(sid))
        elif typ == "series":
            js = cli.get_series_info(int(sid))

        if not isinstance(js, dict):
            self._log("SERVER_META: not dict / empty")
            return None

        self._log(f"HTTP_STATUS: {js.get('_http_status')}")
        self._log(f"TOP_KEYS: {list(js.keys())[:40]}")
        info = js.get("info")
        self._log(f"INFO_TYPE: {type(info)}")

        if not isinstance(info, dict):
            info = {}

        stream_data = js.get("movie_data") or js.get("series_data") or js.get("info") or {}
        if not isinstance(stream_data, dict):
            stream_data = {}

        meta: Dict[str, Any] = {}
        meta["source"] = "SERVER"

        meta["title"] = (
            (info.get("name") or stream_data.get("name") or js.get("name") or self.it.name or "").strip()
        ) or (self.it.name or "Unknown")

        plot = (
            info.get("plot")
            or info.get("description")
            or info.get("overview")
            or stream_data.get("plot")
            or stream_data.get("description")
            or ""
        )
        meta["plot"] = (plot or "").strip()

        year = (
            info.get("releasedate")
            or info.get("release_date")
            or info.get("year")
            or stream_data.get("releasedate")
            or stream_data.get("release_date")
            or stream_data.get("year")
            or ""
        )
        year = (str(year).strip() if year is not None else "")
        if year and len(year) >= 4:
            meta["year"] = year[:4]

        dur = info.get("duration") or info.get("duration_secs") or info.get("runtime") or ""
        if isinstance(dur, int):
            if dur > 0:
                if dur > 1000:
                    meta["duration"] = f"{int(dur // 60)} min"
                else:
                    meta["duration"] = f"{dur} min"
        else:
            meta["duration"] = str(dur).strip()

        meta["genre"] = (info.get("genre") or info.get("genres") or "").strip()

        rating = info.get("rating") or info.get("tmdb_rating") or info.get("imdb_rating") or ""
        meta["rating"] = (str(rating).strip() if rating is not None else "")

        cast = info.get("cast") or info.get("actors") or ""
        meta["cast"] = (str(cast).strip() if cast is not None else "")

        poster = (
            info.get("movie_image")
            or info.get("cover")
            or info.get("poster")
            or info.get("stream_icon")
            or stream_data.get("cover")
            or stream_data.get("movie_image")
            or stream_data.get("stream_icon")
            or ""
        )
        poster = (str(poster).strip() if poster is not None else "")

        if not poster:
            poster = js.get("youtube_trailer") or ""
        if not poster:
            poster = js.get("backdrop_path") or ""

        if poster and not poster.lower().startswith(("http://", "https://")):
            if poster.startswith("/"):
                base_url = prof.get("base", "")
                if base_url:
                    poster = f"{base_url}{poster}"
            else:
                poster = f"{prof.get('base', '')}/{poster}" if prof.get("base") else poster

        if poster.lower().startswith(("http://", "https://")):
            meta["poster"] = poster
            self._log(f"POSTER_FOUND: {poster[:100]}...")
        else:
            meta["poster"] = ""
            self._log(f"NO_POSTER: poster value='{poster}'")

        self._log(
            f"PARSED: title={meta.get('title')} year={meta.get('year')} poster={'YES' if meta.get('poster') else 'NO'} plot_len={len(meta.get('plot') or '')}"
        )

        if not meta.get("plot") and not meta.get("poster") and not meta.get("year") and not meta.get("genre"):
            self._log("SERVER_META: empty meaningful fields -> treat as None")
            return None

        return meta

    def _tmdb(self, query_title: str, year: Optional[str], kind: str) -> Optional[Dict[str, Any]]:
        if not self.tmdb_key:
            return None

        base = "https://api.themoviedb.org/3"
        headers = {"Accept": "application/json"}
        params = {"api_key": self.tmdb_key, "query": query_title}
        if year and year.isdigit():
            if kind == "vod":
                params["year"] = year
            else:
                params["first_air_date_year"] = year

        search_path = "/search/movie" if kind == "vod" else "/search/tv"
        r = requests.get(base + search_path, params=params, headers=headers, timeout=15)
        if r.status_code != 200:
            return None
        js = r.json()
        results = js.get("results") if isinstance(js, dict) else None
        if not results:
            return None

        best = results[0]
        tmdb_id = best.get("id")
        if not tmdb_id:
            return None

        meta: Dict[str, Any] = {}
        meta["source"] = "TMDB"
        meta["title"] = best.get("title") or best.get("name") or query_title
        date = best.get("release_date") or best.get("first_air_date") or ""
        meta["year"] = (date[:4] if isinstance(date, str) else "") or (year or "")
        meta["plot"] = best.get("overview") or ""

        poster_path = best.get("poster_path") or ""
        if poster_path:
            meta["poster"] = f"https://image.tmdb.org/t/p/w500{poster_path}"

        det_path = f"/movie/{tmdb_id}" if kind == "vod" else f"/tv/{tmdb_id}"
        rd = requests.get(base + det_path, params={"api_key": self.tmdb_key}, headers=headers, timeout=15)
        if rd.status_code == 200:
            dj = rd.json() if rd.text else {}
            genres = dj.get("genres") or []
            if isinstance(genres, list):
                meta["genre"] = ", ".join([g.get("name") for g in genres if isinstance(g, dict) and g.get("name")][:6])

            if kind == "vod":
                rt = dj.get("runtime")
                if isinstance(rt, int) and rt > 0:
                    meta["duration"] = f"{rt} min"
            else:
                er = dj.get("episode_run_time")
                if isinstance(er, list) and er:
                    try:
                        meta["duration"] = f"{int(er[0])} min"
                    except Exception:
                        pass

            vote = dj.get("vote_average")
            if isinstance(vote, (int, float)):
                meta["rating"] = f"{vote:.1f}/10"

        cred_path = f"/movie/{tmdb_id}/credits" if kind == "vod" else f"/tv/{tmdb_id}/credits"
        rc = requests.get(base + cred_path, params={"api_key": self.tmdb_key}, headers=headers, timeout=15)
        if rc.status_code == 200:
            cj = rc.json() if rc.text else {}
            cast = cj.get("cast") or []
            if isinstance(cast, list):
                names = []
                for c in cast[:10]:
                    if isinstance(c, dict) and c.get("name"):
                        names.append(c.get("name"))
                meta["cast"] = ", ".join(names)

        return meta

    def _omdb(self, query_title: str, year: Optional[str], kind: str) -> Optional[Dict[str, Any]]:
        if not self.omdb_key:
            return None

        params = {
            "apikey": self.omdb_key,
            "t": query_title,
            "type": "movie" if kind == "vod" else "series",
            "plot": "full",
        }
        if year and year.isdigit():
            params["y"] = year

        r = requests.get("https://www.omdbapi.com/", params=params, timeout=15)
        if r.status_code != 200:
            return None
        js = r.json() if r.text else {}
        if not isinstance(js, dict):
            return None
        if (js.get("Response") or "").lower() != "true":
            return None

        meta: Dict[str, Any] = {}
        meta["source"] = "OMDb"
        meta["title"] = js.get("Title") or query_title
        meta["year"] = (js.get("Year") or "")[:4]
        meta["plot"] = js.get("Plot") or ""
        meta["genre"] = js.get("Genre") or ""
        meta["duration"] = js.get("Runtime") or ""
        meta["cast"] = js.get("Actors") or ""
        meta["rating"] = js.get("imdbRating") or ""

        poster = js.get("Poster") or ""
        if poster and poster.lower().startswith("http"):
            meta["poster"] = poster

        return meta

    def run(self) -> None:
        try:
            base = self._meta_base()

            # 1) TMDB (jeśli masz klucz) – najpierw, bo serwer często nie zwraca serii
            meta = None
            title, year = _clean_title_for_search(self.it.name)
            kind = "vod" if self.it.kind == "vod" else ("series" if self.it.kind == "series" else "vod")
            if self.tmdb_key:
                meta = self._tmdb(title, year, kind)

            # 2) SERWER (Xtream) – fallback
            if not meta:
                meta = self._server_meta()

            # 3) OMDb – fallback tylko jeśli masz klucz
            if not meta and self.omdb_key:
                meta = self._omdb(title, year, kind)

            if not meta:

                if not meta:
                    base["title"] = title
                    if year:
                        base["year"] = year
                    if self.tmdb_key or self.omdb_key:
                        base["plot"] = "Brak metadanych: serwer nie zwraca opisów, a TMDB/OMDb nic nie znalazło."
                    else:
                        base["plot"] = "Brak metadanych: serwer nie zwraca opisów. (TMDB/OMDb wyłączone - brak kluczy)"
                    self.done.emit(self.url, base)
                    return

            out = dict(base)
            out.update(meta)
            if not out.get("poster") and base.get("poster"):
                out["poster"] = base["poster"]

            self.done.emit(self.url, out)

        except Exception as e:
            self.error.emit(self.url, str(e))


# ----------------------------
# Meta panel widgets holder
# ----------------------------

@dataclass
class MetaPanelWidgets:
    panel: QFrame
    poster: QLabel
    title: QLabel
    line: QLabel
    cast: QLabel
    plot: QLabel


# ----------------------------
# Main Window
# ----------------------------

class MainWindow(QMainWindow):
    def __init__(self, base_dir: Path, data_dir: Path, settings: dict) -> None:
        super().__init__()
        self.base_dir = Path(base_dir)
        self.data_dir = Path(data_dir)
        self.settings = settings

        self.setWindowTitle("IPTV on the GO v.1.1  —  compiled by Kamaz")
        self.resize(1400, 850)

        self.player = Player(base_dir=self.base_dir)

        self.items: List[MediaItem] = []
        self.item_by_url: Dict[str, MediaItem] = {}

        self.epg_by_id: Dict[str, EpgNowNext] = {}
        self.epg_by_name: Dict[str, EpgNowNext] = {}
        self.icon_by_id: Dict[str, str] = {}
        self.icon_by_name: Dict[str, str] = {}

        self.xtream_profiles: Dict[str, dict] = {}

        self.section: str = "live"  # live | vod | series
        self.view_mode: str = "groups"          # groups | group_items | favorites
        self.current_group: Optional[str] = None

        # Series navigation
        self.series_view: str = "series_titles"  # series_titles | seasons | episodes
        self.current_series_title: Optional[str] = None
        self.current_season: Optional[int] = None
        self._series_tree: Dict[str, Dict[str, Dict[int, List[MediaItem]]]] = {}

        self.favorites: set[str] = set((settings.get("favorites") or []))
        self.current_playing: Optional[MediaItem] = None
        self.preview_item: Optional[MediaItem] = None  # NOWE: element podglądany (najechanie/strzałki)

        self._thr: Optional[RefreshThread] = None

        self._fs_host: Optional[FullscreenVideoHost] = None
        self._video_placeholder: Optional[QWidget] = None
        self._video_parent_layout = None
        self._video_index_in_layout: Optional[int] = None

        # TMDB/OMDb keys (settings.json)
        self.tmdb_key: str = (self.settings.get("tmdb_api_key") or "").strip()
        self.omdb_key: str = (self.settings.get("omdb_api_key") or "").strip()

        # metadata cache + loader
        self._meta_cache: Dict[str, dict] = {}
        self._meta_thread: Optional[MetaThread] = None
        self._meta_hover_timer = QTimer(self)
        self._meta_hover_timer.setSingleShot(True)
        self._meta_hover_timer.timeout.connect(self._meta_fetch_from_pending)
        self._pending_meta_item: Optional[MediaItem] = None

        # ROZDZIELONE panele dla VOD i Serii
        self.vod_meta: Optional[MetaPanelWidgets] = None
        self.series_meta: Optional[MetaPanelWidgets] = None

        # Esc navigation
        self._last_group_position: Optional[Tuple[str, int]] = None  # (group_name, row_index)

        # Nowe: zmienna do przewijania blokowego
        self.SCROLL_BLOCK_SIZE = 13  # liczba elementów do przewijania blokowego

        # Nowe: cache dla sekcji grup
        self._cached_group_items: Dict[str, Tuple[str, List[MediaItem]]] = {}  # group_name -> (section, items)
        self._last_visited_group: Optional[str] = None

        # Timer do ukrywania kursora
        self._cursor_hide_timer = QTimer(self)
        self._cursor_hide_timer.timeout.connect(self._hide_cursor)
        self._cursor_hidden = False
        self._last_keyboard_activity = time.time()

        # Timer do wykrywania aktywności myszki
        self._mouse_activity_timer = QTimer(self)
        self._mouse_activity_timer.timeout.connect(self._check_mouse_activity)
        self._mouse_activity_timer.start(100)  # Sprawdzaj co 100ms
        self._last_mouse_pos = QCursor.pos()

        # NOWE: Timer do wykrywania szybkiego dwukliku WSTECZ
        self._back_button_timer = QTimer(self)
        self._back_button_timer.setSingleShot(True)
        self._back_button_timer.timeout.connect(self._reset_back_button_count)
        self._back_button_count = 0
        self._back_double_click_timeout = 500  # 500ms na szybki dwuklik

        self._build_ui()
        self._apply_dark_style()
        self._update_toggle_colors()
        self._show_groups()

        # Dodaj obsługę klawiszy dla pola wyszukiwania
        self.search.keyPressEvent = self._handle_search_key_press

        # Rozpocznij ukrywanie kursora po 2 sekundach
        self._cursor_hide_timer.start(2000)

        # Instalacja event filter do wykrywania aktywności klawiatury
        self.installEventFilter(self)

        QTimer.singleShot(250, self.refresh_sources)

    # ---------- Event Filter dla wykrywania aktywności klawiatury ----------

    def eventFilter(self, obj, event):
        """Event filter do wykrywania aktywności klawiatury i myszki"""
        if event.type() == QEvent.Type.KeyPress:
            # FIX: event jest już QKeyEvent w PySide6 (nie twórz QKeyEvent(event))
            key_event = event  # type: ignore

            if key_event.key() in (Qt.Key_Escape, Qt.Key_Back, Qt.Key_Backspace):
                if self.view_mode == "groups" and not self._is_in_dialog():
                    self._handle_back_button()
                    return True


            # FIX: Pilot OK/Select -> traktuj jak Enter (kliknięcie przycisku / aktywacja elementu listy)
            if key_event.key() in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Select):
                fw = QApplication.focusWidget()

                # 1) Przyciski
                if isinstance(fw, QPushButton):
                    fw.click()
                    return True

                # 2) Listy (QListWidget) - OK ma działać jak Enter/dwuklik
                #    (to naprawia wybór sezonu/odcinka w Serialach z pilota)
                if isinstance(fw, QListWidget):
                    it = fw.currentItem()
                    if it is not None:
                        # emituj sygnał jak przy Enter/dwukliku
                        try:
                            fw.itemActivated.emit(it)
                        except Exception:
                            pass
                    return True
            self._last_keyboard_activity = time.time()
            if self._cursor_hidden:
                self._show_cursor()
            self._cursor_hide_timer.start(2000)
            return super().eventFilter(obj, event)

        if event.type() == QEvent.Type.MouseMove:
            self._show_cursor()
            self._last_keyboard_activity = time.time()
            self._cursor_hide_timer.start(2000)

        return super().eventFilter(obj, event)

    def _is_in_dialog(self):
        """Sprawdza czy aktualnie jest otwarty jakiś dialog"""
        focus_widget = QApplication.focusWidget()
        if focus_widget:
            parent = focus_widget.parent()
            while parent:
                if isinstance(parent, QDialog):
                    return True
                parent = parent.parent()
        return False

    def _handle_back_button(self):
        """Obsługa przycisku WSTECZ w głównym UI"""
        self._back_button_count += 1

        if self._back_button_count == 1:
            self._back_button_timer.start(self._back_double_click_timeout)
        elif self._back_button_count == 2:
            self._back_button_timer.stop()
            self._back_button_count = 0
            self._show_exit_confirmation()

    def _reset_back_button_count(self):
        """Resetuje licznik naciśnięć przycisku WSTECZ"""
        self._back_button_count = 0

    def _check_mouse_activity(self):
        """Sprawdza aktywność myszki (co 100ms)"""
        current_pos = QCursor.pos()
        if current_pos != self._last_mouse_pos:
            self._last_mouse_pos = current_pos
            self._show_cursor()
            self._last_keyboard_activity = time.time()
            self._cursor_hide_timer.start(2000)

    def _hide_cursor(self):
        """Ukryj kursor"""
        if not self._cursor_hidden:
            self.setCursor(Qt.BlankCursor)
            self._cursor_hidden = True

    def _show_cursor(self):
        """Pokaż kursor"""
        if self._cursor_hidden:
            self.unsetCursor()
            self._cursor_hidden = False

    # ---------- UI ----------

    def _build_ui(self) -> None:
        self.tb = QToolBar("Main")
        self.tb.setMovable(False)
        self.addToolBar(self.tb)

        self.btn_src_m3u = QPushButton("M3U")
        self.btn_src_stalker = QPushButton("STALKER")
        self.btn_src_xc = QPushButton("XC CODES")
        for b in (self.btn_src_m3u, self.btn_src_stalker, self.btn_src_xc):
            b.setCheckable(True)
            b.setMinimumHeight(28)
            b.setFocusPolicy(Qt.StrongFocus)

        src = self.settings.get("sources", {"m3u": True, "stalker": True, "xc": False})
        self.btn_src_m3u.setChecked(bool(src.get("m3u", True)))
        self.btn_src_stalker.setChecked(bool(src.get("stalker", True)))
        self.btn_src_xc.setChecked(bool(src.get("xc", False)))

        self.btn_src_m3u.toggled.connect(self._save_sources_settings)
        self.btn_src_stalker.toggled.connect(self._save_sources_settings)
        self.btn_src_xc.toggled.connect(self._save_sources_settings)

        self.tb.addWidget(self.btn_src_m3u)
        self.tb.addWidget(self.btn_src_stalker)
        self.tb.addWidget(self.btn_src_xc)

        self.tb.addSeparator()

        act_refresh = QAction("Odśwież źródła", self)
        act_refresh.triggered.connect(self.refresh_sources)
        self.tb.addAction(act_refresh)

        self.tb.addSeparator()

        self.search = QLineEdit()
        self.search.setPlaceholderText("Szukaj...")
        self.search.textChanged.connect(self._apply_filter)
        self.search.setMaximumWidth(360)
        self.search.setFocusPolicy(Qt.StrongFocus)
        self.tb.addWidget(self.search)

        root = QWidget()
        self.setCentralWidget(root)
        outer = QHBoxLayout(root)
        outer.setContentsMargins(0, 0, 0, 0)
        outer.setSpacing(0)

        # LEFT panel
        left = QFrame()
        left.setFixedWidth(260)
        ll = QVBoxLayout(left)
        ll.setContentsMargins(10, 10, 10, 10)
        ll.setSpacing(8)

        self.btn_live = QPushButton("Live TV")
        self.btn_vod = QPushButton("VOD")
        self.btn_series = QPushButton("Seriale")
        for b in (self.btn_live, self.btn_vod, self.btn_series):
            b.setMinimumHeight(40)
            bf = b.font()
            bf.setPointSize(11)
            bf.setBold(True)
            b.setFont(bf)
            b.setFocusPolicy(Qt.StrongFocus)

        self.btn_live.clicked.connect(lambda: self._set_section("live"))
        self.btn_vod.clicked.connect(lambda: self._set_section("vod"))
        self.btn_series.clicked.connect(lambda: self._set_section("series"))

        ll.addWidget(self.btn_live)
        ll.addWidget(self.btn_vod)
        ll.addWidget(self.btn_series)

        self.list_groups = QListWidget()
        self.list_groups.setUniformItemSizes(True)
        gf = self.list_groups.font()
        gf.setPointSize(12)
        self.list_groups.setFont(gf)
        self.list_groups.itemActivated.connect(self._open_group)
        self.list_groups.itemClicked.connect(self._open_group)
        self.list_groups.setFocusPolicy(Qt.StrongFocus)
        self.list_groups.keyPressEvent = self._handle_groups_key_press
        ll.addWidget(self.list_groups, 1)

        row = QHBoxLayout()
        self.btn_exit = QPushButton("WYJŚCIE")
        self.btn_fav = QPushButton("ULUBIONE")
        for b in (self.btn_exit, self.btn_fav):
            b.setMinimumHeight(44)
            bf = b.font()
            bf.setPointSize(11)
            bf.setBold(True)
            b.setFont(bf)
            b.setFocusPolicy(Qt.StrongFocus)

        self.btn_exit.setStyleSheet(
            """
            QPushButton {
                background: linear-gradient(to bottom, #3a1a1a, #2a0a0a);
                border: 2px solid #cc3a3a;
                border-radius: 8px;
                color: white;
                padding: 6px;
            }
            QPushButton:hover {
                background: linear-gradient(to bottom, #4a2a2a, #3a1a1a);
                border: 2px solid #dd4a4a;
            }
            QPushButton:focus {
                background: linear-gradient(to bottom, #5a3a3a, #4a2a2a);
                border: 3px solid #ee5a5a;
            }
        """
        )

        self.btn_exit.clicked.connect(self._show_exit_confirmation)
        # FIX: podpinasz keyPressEvent, bo metoda była, ale nigdy nieużywana
        self.btn_exit.keyPressEvent = self._handle_exit_key_press

        self.btn_fav.clicked.connect(self._show_favorites)
        row.addWidget(self.btn_exit)
        row.addWidget(self.btn_fav)
        ll.addLayout(row)

        self.counter_label = QLabel("Grupy: 0")
        self.counter_label.setStyleSheet("color:#cfcfcf; padding:6px;")
        ll.addWidget(self.counter_label)

        # MAIN stack
        self.stack = QStackedWidget()
        self.page_live = self._build_live_page()
        self.page_vod = self._build_vod_page()
        self.page_series = self._build_series_page()

        self.stack.addWidget(self.page_live)
        self.stack.addWidget(self.page_vod)
        self.stack.addWidget(self.page_series)

        outer.addWidget(left)
        outer.addWidget(self.stack)

    # ---------- Dialog wyjścia ----------

    def _show_exit_confirmation(self):
        """Pokazuje dialog potwierdzenia wyjścia"""
        dialog = ExitConfirmationDialog(self)
        if dialog.exec() == QDialog.Accepted:
            self.close()

    def _handle_exit_key_press(self, e: QKeyEvent):
        """Obsługa klawiatury dla przycisku WYJŚCIE"""
        if e.key() in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Select):
            self._show_exit_confirmation()
            e.accept()
        elif e.key() == Qt.Key_Up:
            if self.list_groups.count() > 0:
                self.list_groups.setCurrentRow(self.list_groups.count() - 1)
                self.list_groups.setFocus()
            e.accept()
        elif e.key() in (Qt.Key_Left, Qt.Key_Right):
            self.btn_fav.setFocus()
            e.accept()
        else:
            super(QPushButton, self.btn_exit).keyPressEvent(e)

    def _build_live_page(self) -> QWidget:
        w = QWidget()
        layout = QVBoxLayout(w)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(8)

        splitter = QSplitter(Qt.Horizontal)
        splitter.setChildrenCollapsible(False)

        # MID list
        mid = QWidget()
        ml = QVBoxLayout(mid)
        ml.setContentsMargins(0, 0, 0, 0)
        ml.setSpacing(6)

        self.list_live = QListWidget()
        self.list_live.setUniformItemSizes(True)
        cf = self.list_live.font()
        cf.setPointSize(12)
        self.list_live.setFont(cf)
        self.list_live.itemClicked.connect(self._on_live_item_clicked)
        self.list_live.itemActivated.connect(self._on_live_item_clicked)
        self.list_live.setFocusPolicy(Qt.StrongFocus)
        self.list_live.keyPressEvent = self._handle_live_key_press
        
        # Mouse tracking dla hover
        self.list_live.setMouseTracking(True)
        self.list_live.viewport().setMouseTracking(True)
        self.list_live.itemEntered.connect(self._on_live_item_hovered)
        
        ml.addWidget(self.list_live, 1)

        fav_row = QHBoxLayout()
        self.btn_add = QPushButton("DODAJ")
        self.btn_del = QPushButton("USUŃ")
        self.btn_add.setMinimumHeight(42)
        self.btn_del.setMinimumHeight(42)
        self.btn_add.clicked.connect(self._fav_add_current)
        self.btn_del.clicked.connect(self._fav_del_selected)
        fav_row.addWidget(self.btn_add)
        fav_row.addWidget(self.btn_del)
        ml.addLayout(fav_row)

        # RIGHT fixed layout
        right = QWidget()
        rl = QVBoxLayout(right)
        rl.setContentsMargins(0, 0, 0, 0)
        rl.setSpacing(6)

        head = QFrame()
        head.setFixedHeight(64)
        hl = QHBoxLayout(head)
        hl.setContentsMargins(10, 8, 10, 8)
        hl.setSpacing(10)

        self.lbl_picon = QLabel()
        self.lbl_picon.setFixedSize(46, 46)
        self.lbl_picon.setScaledContents(True)

        self.lbl_name = QLabel("—")
        self.lbl_name.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Fixed)
        self.lbl_name.setMaximumHeight(48)
        self.lbl_name.setWordWrap(False)
        self.lbl_name.setTextInteractionFlags(Qt.TextSelectableByMouse)
        fn = self.lbl_name.font()
        fn.setPointSize(14)
        fn.setBold(True)
        self.lbl_name.setFont(fn)

        hl.addWidget(self.lbl_picon)
        hl.addWidget(self.lbl_name, 1)

        self.video = QFrame()
        self.video.setStyleSheet("background:black; border:1px solid #222; border-radius:10px;")
        self.video.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.video.setFocusPolicy(Qt.StrongFocus)
        self.video.setAttribute(Qt.WA_NativeWindow, True)
        self.video.setAttribute(Qt.WA_DontCreateNativeAncestors, True)
        self.video.setAttribute(Qt.WA_NoSystemBackground, True)
        self.video.setAttribute(Qt.WA_OpaquePaintEvent, True)

        self.video.mouseDoubleClickEvent = lambda _e: self._toggle_video_fullscreen()

        self.player.set_video_widget(self.video)
        # Buffering/reconnect overlay + watchdog
        self._init_buffer_overlay()
        self._init_buffer_watchdog()


        box_now = QFrame()
        box_now.setFixedHeight(120)
        nl = QVBoxLayout(box_now)
        nl.setContentsMargins(12, 10, 12, 10)
        nl.setSpacing(6)

        self.lbl_now = QLabel("NOW: —")
        self.lbl_now.setWordWrap(True)
        self.lbl_now.setMaximumHeight(44)

        self.lbl_desc = QLabel("")
        self.lbl_desc.setWordWrap(True)
        self.lbl_desc.setMaximumHeight(64)

        nl.addWidget(self.lbl_now)
        nl.addWidget(self.lbl_desc)

        box_next = QFrame()
        box_next.setFixedHeight(56)
        bl = QVBoxLayout(box_next)
        bl.setContentsMargins(12, 8, 12, 8)
        bl.setSpacing(0)

        self.lbl_next = QLabel("NEXT: —")
        self.lbl_next.setWordWrap(True)
        self.lbl_next.setMaximumHeight(40)
        bl.addWidget(self.lbl_next)

        rl.addWidget(head, 0)
        rl.addWidget(self.video, 1)
        rl.addWidget(box_now, 0)
        rl.addWidget(box_next, 0)

        splitter.addWidget(mid)
        splitter.addWidget(right)
        splitter.setStretchFactor(0, 32)
        splitter.setStretchFactor(1, 68)
        splitter.setSizes([420, 980])

        layout.addWidget(splitter, 1)
        return w

    def _build_meta_panel(self) -> MetaPanelWidgets:
        """Tworzy nowy, niezależny panel metadanych"""
        panel = QFrame()
        panel.setMinimumWidth(420)
        panel.setMaximumWidth(520)

        vl = QVBoxLayout(panel)
        vl.setContentsMargins(14, 14, 14, 14)
        vl.setSpacing(10)

        poster = QLabel()
        poster.setFixedSize(240, 360)
        poster.setScaledContents(True)
        poster.setStyleSheet("background:#0b0b0b; border:1px solid #222; border-radius:10px;")

        title = QLabel("—")
        tf = title.font()
        tf.setPointSize(16)
        tf.setBold(True)
        title.setFont(tf)
        title.setWordWrap(True)
        title.setMaximumHeight(80)

        line = QLabel("")
        line.setWordWrap(True)
        line.setMaximumHeight(64)

        cast = QLabel("")
        cast.setWordWrap(True)
        cast.setMaximumHeight(80)

        plot = QLabel("")
        plot.setWordWrap(True)
        plot.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)

        top = QHBoxLayout()
        top.addWidget(poster, 0, Qt.AlignTop)

        right = QVBoxLayout()
        right.addWidget(title)
        right.addWidget(line)
        right.addWidget(cast)
        top.addLayout(right, 1)

        vl.addLayout(top)
        vl.addWidget(plot, 1)

        return MetaPanelWidgets(
            panel=panel,
            poster=poster,
            title=title,
            line=line,
            cast=cast,
            plot=plot
        )

    def _build_vod_page(self) -> QWidget:
        w = QWidget()
        layout = QVBoxLayout(w)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(8)

        splitter = QSplitter(Qt.Horizontal)
        splitter.setChildrenCollapsible(False)

        mid = QWidget()
        ml = QVBoxLayout(mid)
        ml.setContentsMargins(0, 0, 0, 0)
        ml.setSpacing(6)

        self.list_vod = QListWidget()
        self.list_vod.setUniformItemSizes(True)
        cf = self.list_vod.font()
        cf.setPointSize(12)
        self.list_vod.setFont(cf)
        self.list_vod.itemClicked.connect(self._on_vod_series_item_clicked)
        self.list_vod.itemActivated.connect(self._on_vod_series_item_clicked)
        self.list_vod.setFocusPolicy(Qt.StrongFocus)
        self.list_vod.keyPressEvent = self._handle_vod_series_key_press

        self.list_vod.setMouseTracking(True)
        self.list_vod.viewport().setMouseTracking(True)
        self.list_vod.itemEntered.connect(self._on_vod_series_item_hovered)

        ml.addWidget(self.list_vod, 1)

        splitter.addWidget(mid)
        
        # OSOBNY panel dla VOD
        self.vod_meta = self._build_meta_panel()
        splitter.addWidget(self.vod_meta.panel)

        splitter.setStretchFactor(0, 65)
        splitter.setStretchFactor(1, 35)
        splitter.setSizes([900, 500])

        layout.addWidget(splitter, 1)
        return w

    def _build_series_page(self) -> QWidget:
        w = QWidget()
        layout = QVBoxLayout(w)
        layout.setContentsMargins(10, 10, 10, 10)
        layout.setSpacing(8)

        splitter = QSplitter(Qt.Horizontal)
        splitter.setChildrenCollapsible(False)

        mid = QWidget()
        ml = QVBoxLayout(mid)
        ml.setContentsMargins(0, 0, 0, 0)
        ml.setSpacing(6)

        self.list_series = QListWidget()
        self.list_series.setUniformItemSizes(True)
        cf = self.list_series.font()
        cf.setPointSize(12)
        self.list_series.setFont(cf)
        self.list_series.itemClicked.connect(self._on_vod_series_item_clicked)
        self.list_series.itemActivated.connect(self._on_vod_series_item_clicked)
        self.list_series.setFocusPolicy(Qt.StrongFocus)
        self.list_series.keyPressEvent = self._handle_vod_series_key_press

        self.list_series.setMouseTracking(True)
        self.list_series.viewport().setMouseTracking(True)
        self.list_series.itemEntered.connect(self._on_vod_series_item_hovered)

        ml.addWidget(self.list_series, 1)

        splitter.addWidget(mid)
        
        # OSOBNY panel dla Serii
        self.series_meta = self._build_meta_panel()
        splitter.addWidget(self.series_meta.panel)

        splitter.setStretchFactor(0, 65)
        splitter.setStretchFactor(1, 35)
        splitter.setSizes([900, 500])

        layout.addWidget(splitter, 1)
        return w

    def _apply_dark_style(self) -> None:
        self.setStyleSheet("""
            QMainWindow { background: #121212; color: #e6e6e6; }
            QToolBar { background: #1b1b1b; border: none; }
            QLineEdit { background: #202020; border: 1px solid #333; padding: 6px; border-radius: 6px; color: #e6e6e6; }
            QPushButton { background: #222; border: 1px solid #333; border-radius: 8px; color: #e6e6e6; padding: 6px; }
            QPushButton:hover { background: #2a2a2a; }
            QListWidget { background: #161616; border: 1px solid #2a2a2a; }
            QListWidget::item { padding: 10px; border-bottom: 1px solid #222; }
            QListWidget::item:selected { background: #2a2a2a; }
            QLabel { color: #cfcfcf; padding: 2px; }
            QFrame { background: #0f0f0f; border: 1px solid #222; border-radius: 10px; }
        """)

    # ---------- KEYBOARD HANDLERS ----------
    
    def _handle_search_key_press(self, e: QKeyEvent):
        """Obsługa klawiatury dla pola wyszukiwania"""
        if e.key() == Qt.Key_Down:
            # TYLKO strzałka w dół wychodzi z pola do przycisku Live TV
            self.btn_live.setFocus()
            e.accept()
        elif e.key() == Qt.Key_Up:
            # Strzałka w górę - przejdź do przycisków źródeł
            self.btn_src_m3u.setFocus()
            e.accept()
        elif e.key() in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Select, Qt.Key_Execute, Qt.Key_Space):
            # Enter - zatwierdź wyszukiwanie (standardowe zachowanie)
            super(QLineEdit, self.search).keyPressEvent(e)
        elif e.key() in (Qt.Key_Escape, Qt.Key_Back, Qt.Key_Backspace):
            # ESC - nic nie robi, pozostaje w polu wyszukiwania
            e.accept()
        else:
            # Dla innych klawiszy - standardowe zachowanie
            super(QLineEdit, self.search).keyPressEvent(e)
    
    def _handle_groups_key_press(self, e: QKeyEvent) -> None:
        """Obsługa klawiatury dla listy grup"""
        # Obsługa przycisku WSTECZ z pilota (uniwersalna) - USUNIĘTE dla listy grup
        if e.key() in (Qt.Key_Escape, Qt.Key_Back, Qt.Key_Backspace):
            # ESC nie robi nic w liście grup
            e.accept()
            return
            
        current_row = self.list_groups.currentRow()
        max_row = self.list_groups.count() - 1
        
        if e.key() == Qt.Key_Up:
            if current_row > 0:
                self.list_groups.setCurrentRow(current_row - 1)
                # Zapisujemy pozycję dla ESC
                if self.view_mode == "groups":
                    self._save_group_position()
                e.accept()
            else:
                # Jesteśmy na pierwszej grupie - zostań w liście
                self.list_groups.setCurrentRow(0)
                e.accept()
        elif e.key() == Qt.Key_Down:
            if current_row < max_row:
                self.list_groups.setCurrentRow(current_row + 1)
                # Zapisujemy pozycję dla ESC
                if self.view_mode == "groups":
                    self._save_group_position()
                e.accept()
            else:
                # Jesteśmy na ostatniej grupie - zostań w liście
                self.list_groups.setCurrentRow(max_row)
                e.accept()
        elif e.key() == Qt.Key_Right:
            # Przejdź do aktywnej listy (Live/VOD/Seriale) - przywróć cache jeśli istnieje
            if self._last_visited_group and self._last_visited_group in self._cached_group_items:
                # Przywróć cache'owaną sekcję
                cached_section, cached_items = self._cached_group_items[self._last_visited_group]
                if cached_section == self.section:
                    # Jeśli cache jest dla aktualnej sekcji, przywróć
                    self._restore_cached_group(self._last_visited_group)
                else:
                    # W przeciwnym razie zacznij od początku
                    self._mid_list_widget().setFocus()
                    if self._mid_list_widget().count() > 0:
                        self._mid_list_widget().setCurrentRow(0)
                        self._trigger_item_selection_by_key()
            else:
                self._mid_list_widget().setFocus()
                if self._mid_list_widget().count() > 0:
                    self._mid_list_widget().setCurrentRow(0)
                    self._trigger_item_selection_by_key()
            e.accept()
        elif e.key() == Qt.Key_Left:
            # Strzałka w lewo z listy grup - przejdź do przycisku Live TV
            self.btn_live.setFocus()
            e.accept()
        elif e.key() in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Select, Qt.Key_Execute, Qt.Key_Space):
            # Zapisujemy pozycję przed otwarciem grupy
            self._save_group_position()
            self._open_group(self.list_groups.currentItem())
            e.accept()
        else:
            # Dla innych klawiszy - standardowe zachowanie
            super(QListWidget, self.list_groups).keyPressEvent(e)
    
    def _handle_live_key_press(self, e: QKeyEvent) -> None:
        """Obsługa klawiatury dla listy Live TV"""
        # Obsługa przycisku WSTECZ z pilota (uniwersalna)
        if e.key() in (Qt.Key_Escape, Qt.Key_Back, Qt.Key_Backspace):
            self._handle_escape_in_group_items()
            e.accept()
            return
            
        current_row = self.list_live.currentRow()
        max_row = self.list_live.count() - 1
        
        if e.key() == Qt.Key_Up:
            if current_row > 0:
                self.list_live.setCurrentRow(current_row - 1)
                self._trigger_live_selection_by_key()
                e.accept()
            else:
                # Jesteśmy na pierwszym elemencie - zostań w liście
                self.list_live.setCurrentRow(0)
                self._trigger_live_selection_by_key()
                e.accept()
        elif e.key() == Qt.Key_Down:
            if current_row < max_row:
                self.list_live.setCurrentRow(current_row + 1)
            else:
                self.list_live.setCurrentRow(max_row)
            self._trigger_live_selection_by_key()
            e.accept()
        elif e.key() == Qt.Key_Right:
            # PRZEWIJANIE BLOKOWE W PRAWO (15 elementów w dół)
            if self.view_mode == "group_items" and self.list_live.count() > 0:
                self._scroll_block_down(self.list_live)
            e.accept()
        elif e.key() == Qt.Key_Left:
            # PRZEWIJANIE BLOKOWE W LEWO (10 elementów w górę) — tak samo jak w prawo przewija w dół
            if self.list_live.count() > 0:
                self._scroll_block_up(self.list_live)
            e.accept()
        elif e.key() in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Select, Qt.Key_Execute, Qt.Key_Space):
            # Odtwórz kanał
            item = self.list_live.currentItem()
            if item:
                self._on_live_item_clicked(item)
            e.accept()
        else:
            super(QListWidget, self.list_live).keyPressEvent(e)
    
    def _handle_vod_series_key_press(self, e: QKeyEvent) -> None:
        """Obsługa klawiatury dla list VOD i Serii"""
        # Obsługa przycisku WSTECZ z pilota (uniwersalna)
        if e.key() in (Qt.Key_Escape, Qt.Key_Back, Qt.Key_Backspace):
            self._handle_escape_in_group_items()
            e.accept()
            return
            
        w = self._mid_list_widget()  # list_vod lub list_series
        current_row = w.currentRow()
        max_row = w.count() - 1
        
        if e.key() == Qt.Key_Up:
            if current_row > 0:
                w.setCurrentRow(current_row - 1)
                self._trigger_vod_series_selection_by_key()
                e.accept()
            else:
                # Jesteśmy na pierwszym elemencie - zostań w liście
                w.setCurrentRow(0)
                self._trigger_vod_series_selection_by_key()
                e.accept()
        elif e.key() == Qt.Key_Down:
            if current_row < max_row:
                w.setCurrentRow(current_row + 1)
            else:
                w.setCurrentRow(max_row)
            self._trigger_vod_series_selection_by_key()
            e.accept()
        elif e.key() == Qt.Key_Right:
            # PRZEWIJANIE BLOKOWE W PRAWO (15 elementów w dół)
            if self.view_mode == "group_items" and w.count() > 0:
                self._scroll_block_down(w)
            e.accept()
        elif e.key() == Qt.Key_Left:
            # PRZEWIJANIE BLOKOWE W LEWO (15 elementów w górę)
            if self.view_mode == "group_items" and w.count() > 0:
                self._scroll_block_up(w)
            e.accept()
        elif e.key() in (Qt.Key_Return, Qt.Key_Enter, Qt.Key_Select, Qt.Key_Execute, Qt.Key_Space):
            # OK/Enter na pilocie/klawiaturze = jak klik myszką na pozycji listy.
            item = w.currentItem()
            if item:
                if self.section == "vod":
                    # VOD: pokaż okno detalu (Oglądaj)
                    self._show_media_detail_dialog(item)
                else:
                    # SERIALE (tytuły/sezony/odcinki): wejdź/odtwórz jak po kliknięciu myszą
                    self._on_vod_series_item_clicked(item)
            e.accept()
        else:
            super(QListWidget, w).keyPressEvent(e)
    
    def _scroll_block_down(self, list_widget: QListWidget):
        """Przewija listę o jeden blok w dół"""
        current_row = list_widget.currentRow()
        max_row = list_widget.count() - 1
        
        if max_row <= self.SCROLL_BLOCK_SIZE:
            # Jeśli lista jest mniejsza niż blok, przejdź do końca
            if current_row < max_row:
                list_widget.setCurrentRow(max_row)
        else:
            # Przewiń o blok w dół
            new_row = min(max_row, current_row + self.SCROLL_BLOCK_SIZE)
            if new_row != current_row:
                list_widget.setCurrentRow(new_row)
                
        # Przewiń widok, aby zaznaczony element był widoczny
        list_widget.scrollToItem(list_widget.currentItem())
        
        # Wyzwól odpowiednią akcję dla zaznaczonego elementu
        if list_widget is self.list_live:
            self._trigger_live_selection_by_key()
        else:
            self._trigger_vod_series_selection_by_key()
    
    def _scroll_block_up(self, list_widget: QListWidget):
        """Przewija listę o jeden blok w górę"""
        current_row = list_widget.currentRow()
        
        if current_row <= self.SCROLL_BLOCK_SIZE:
            # Jeśli jesteśmy blisko początku, przejdź do początku
            if current_row > 0:
                list_widget.setCurrentRow(0)
        else:
            # Przewiń o blok w górę
            new_row = max(0, current_row - self.SCROLL_BLOCK_SIZE)
            if new_row != current_row:
                list_widget.setCurrentRow(new_row)
                
        # Przewiń widok, aby zaznaczony element był widoczny
        list_widget.scrollToItem(list_widget.currentItem())
        
        # Wyzwól odpowiednią akcję dla zaznaczonego elementu
        if list_widget is self.list_live:
            self._trigger_live_selection_by_key()
        else:
            self._trigger_vod_series_selection_by_key()
    
    def _handle_escape_in_group_items(self) -> None:
        """Obsługa klawisza ESC w trybie group_items"""
        if self.view_mode == "group_items":
            # Zapisujemy aktualną sekcję do cache przed powrotem
            if self.current_group:
                # Pobierz aktualne elementy z listy
                w = self._mid_list_widget()
                items = []
                for i in range(w.count()):
                    item = w.item(i)
                    data = item.data(Qt.UserRole)
                    if isinstance(data, MediaItem):
                        items.append(data)
                
                # Zapisz do cache
                self._cached_group_items[self.current_group] = (self.section, items)
                self._last_visited_group = self.current_group
            
            self._show_groups()
            # Przywróć zapisaną pozycję w liście grup
            if self._last_group_position:
                group_name, row_idx = self._last_group_position
                # Znajdź pozycję grupy na liście
                for i in range(self.list_groups.count()):
                    item = self.list_groups.item(i)
                    if item.data(Qt.UserRole) == group_name:
                        self.list_groups.setCurrentRow(i)
                        break
                else:
                    # Jeśli nie znaleziono, ustaw pierwszy element
                    if self.list_groups.count() > 0:
                        self.list_groups.setCurrentRow(0)
    
    def _save_group_position(self) -> None:
        """Zapisuje aktualną pozycję w liście grup"""
        current_item = self.list_groups.currentItem()
        if current_item:
            group_name = current_item.data(Qt.UserRole)
            current_row = self.list_groups.currentRow()
            self._last_group_position = (group_name, current_row)
    
    def _restore_cached_group(self, group_name: str):
        """Przywraca cache'owaną sekcję dla grupy"""
        if group_name in self._cached_group_items:
            cached_section, cached_items = self._cached_group_items[group_name]
            
            # Ustaw tryb group_items
            self.view_mode = "group_items"
            self.current_group = group_name
            
            # Wyczyść i wypełnij listę
            w = self._mid_list_widget()
            w.clear()
            
            for it in cached_items:
                if self.section == "live":
                    rec = self._epg_lookup(it)
                    now_txt = f"  •  NOW: {rec.now_title}" if rec and rec.now_title else ""
                    next_txt = f" | NEXT: {rec.next_title}" if rec and rec.next_title else ""
                    fav = " ★" if it.url in self.favorites else ""
                    li = QListWidgetItem(f"{it.name}{fav}{now_txt}{next_txt}")
                    li.setData(Qt.UserRole, it)
                    w.addItem(li)
                else:
                    fav = " ★" if it.url in self.favorites else ""
                    li = QListWidgetItem(f"{it.name}{fav}")
                    li.setData(Qt.UserRole, it)
                    w.addItem(li)
            
            self.counter_label.setText(f"{self.section.upper()} | {group_name}: {len(cached_items)}")
            if w.count() > 0:
                w.setCurrentRow(0)
                if self.section == "live":
                    first_item = w.item(0)
                    if first_item:
                        data = first_item.data(Qt.UserRole)
                        if isinstance(data, MediaItem):
                            self.preview_item = data
                            self._update_right_panel(data)
                else:
                    first = w.item(0)
                    if first:
                        data = first.data(Qt.UserRole)
                        if isinstance(data, MediaItem):
                            self._meta_set_loading(data)
                            self._meta_set_pending(data)
            
            w.setFocus()
    
    def _trigger_item_selection_by_key(self) -> None:
        """Wywołuje odpowiednią metodę dla aktywnej sekcji"""
        if self.section == "live":
            self._trigger_live_selection_by_key()
        else:
            self._trigger_vod_series_selection_by_key()
    
    def _trigger_live_selection_by_key(self) -> None:
        """Wywołuje pokazanie EPG dla aktualnie zaznaczonego kanału Live TV (dla klawiatury)"""
        item = self.list_live.currentItem()
        if not item:
            return
            
        data = item.data(Qt.UserRole)
        
        if isinstance(data, MediaItem):
            self.preview_item = data  # Ustawiamy podglądany element
            self._update_right_panel(data)
    
    def _series_pick_meta_item(self, data: tuple) -> Optional[MediaItem]:
        """Dla ('series_title', tytuł) i ('season', nr) wybiera reprezentatywny odcinek,
        aby pobrać poster/opis z tego samego mechanizmu co VOD.
        Zwraca nowy MediaItem z podmienioną nazwą (tytuł serialu / sezon).
        """
        try:
            if self.section != "series":
                return None

            kind = data[0]
            cat = (self.current_group or "").strip()
            by_title = self._series_tree.get(cat, {}) if hasattr(self, "_series_tree") else {}
            if not isinstance(by_title, dict) or not by_title:
                return None

            if kind == "series_title":
                title = str(data[1])
                seasons_map = by_title.get(title, {})
                if not isinstance(seasons_map, dict) or not seasons_map:
                    return None
                seasons = sorted(seasons_map.keys())
                if not seasons:
                    return None
                # Weź pierwszy sezon, pierwszy odcinek
                rep_list = seasons_map.get(seasons[0]) or []
                if not rep_list:
                    return None
                rep = rep_list[0]
                # DEBUG: zapisz info do logu
                self._log_series_debug(f"Picked series '{title}', season {seasons[0]}, episode URL: {rep.url}")
                return MediaItem(
                    name=title,
                    url=rep.url,
                    group=rep.group,
                    tvg_id=rep.tvg_id,
                    tvg_logo=rep.tvg_logo,
                    kind=rep.kind,
                    host=rep.host,
                    stream_id=rep.stream_id,
                    xt_type=rep.xt_type,
                )

            if kind == "season":
                if not self.current_series_title:
                    return None
                title = str(self.current_series_title)
                try:
                    season_no = int(data[1])
                except Exception:
                    return None
                seasons_map = by_title.get(title, {})
                rep_list = seasons_map.get(season_no) or []
                if not rep_list:
                    return None
                rep = rep_list[0]
                # DEBUG: zapisz info do logu
                self._log_series_debug(f"Picked season {season_no} of '{title}', episode URL: {rep.url}")
                return MediaItem(
                    name=f"{title} — Sezon {season_no}",
                    url=rep.url,
                    group=rep.group,
                    tvg_id=rep.tvg_id,
                    tvg_logo=rep.tvg_logo,
                    kind=rep.kind,
                    host=rep.host,
                    stream_id=rep.stream_id,
                    xt_type=rep.xt_type,
                )
        except Exception as e:
            self._log_series_debug(f"Error in _series_pick_meta_item: {e}")
            return None
        return None

    def _log_series_debug(self, msg: str):
        """Zapisuje debug info dla seriali"""
        try:
            log_file = self.data_dir / "series_debug.txt"
            with open(log_file, "a", encoding="utf-8") as f:
                f.write(f"{time.strftime('%Y-%m-%d %H:%M:%S')} - {msg}\n")
        except Exception:
            pass
    
    def _trigger_vod_series_selection_by_key(self) -> None:
        """Wywołuje pokazanie metadanych dla aktualnie zaznaczonego elementu VOD/Serii (dla klawiatury)"""
        w = self._mid_list_widget()
        item = w.currentItem()
        if not item:
            return
            
        data = item.data(Qt.UserRole)
        
        if self.section == "series" and isinstance(data, tuple):
            rep = self._series_pick_meta_item(data)
            if isinstance(rep, MediaItem):
                self._meta_set_loading(rep)
                self._meta_set_pending(rep)
            else:
                # Jeśli nie udało się znaleźć reprezentatywnego odcinka, wyczyść panel
                self._meta_clear_ui()
                # DEBUG
                self._log_series_debug(f"No meta item for {data}")
            return
        
        if isinstance(data, MediaItem):
            self._meta_set_loading(data)
            self._meta_set_pending(data)
        else:
            # Jeśli to nie MediaItem, wyczyść panel
            self._meta_clear_ui()

    # ---------- LIVE TV SPECIFIC ----------
    
    def _on_live_item_hovered(self, item: QListWidgetItem) -> None:
        """Obsługa najechania myszką na kanał Live TV"""
        data = item.data(Qt.UserRole)

        if item:
            self.list_live.setCurrentItem(item)

        if isinstance(data, MediaItem):
            self.preview_item = data  # Ustawiamy podglądany element
            self._update_right_panel(data)
    
    def _on_live_item_clicked(self, item: QListWidgetItem) -> None:
        """Obsługa kliknięcia na kanał Live TV"""
        data = item.data(Qt.UserRole)

        it: MediaItem = data
        if not it:
            return

        if self.current_playing and self.current_playing.url == it.url:
            self._toggle_video_fullscreen()
            return
        
        # Ustawiamy jako odtwarzany element
        self.current_playing = it
        self._play_item(it)
        
        # Aktualizujemy panel boczny z danymi klikniętego kanału
        self._update_right_panel(it)

    # ---------- VOD/SERIES SPECIFIC ----------
    
    def _on_vod_series_item_hovered(self, item: QListWidgetItem) -> None:
        """Obsługa najechania myszką na element VOD/Serii"""
        data = item.data(Qt.UserRole)

        w = self._mid_list_widget()
        if item:
            w.setCurrentItem(item)

        if self.section == "series" and isinstance(data, tuple):
            rep = self._series_pick_meta_item(data)
            if isinstance(rep, MediaItem):
                self._meta_set_loading(rep)
                self._meta_set_pending(rep)
            else:
                # Jeśli nie udało się znaleźć reprezentatywnego odcinka, wyczyść panel
                self._meta_clear_ui()
                # DEBUG
                self._log_series_debug(f"No meta item for {data} (hover)")
            return

        if isinstance(data, MediaItem):
            self._meta_set_loading(data)
            self._meta_set_pending(data)
        else:
            # Jeśli to nie MediaItem, wyczyść panel
            self._meta_clear_ui()
    
    def _on_vod_series_item_clicked(self, item: QListWidgetItem) -> None:
        """Obsługa kliknięcia na element VOD/Serii"""
        data = item.data(Qt.UserRole)

        if self.section == "series" and isinstance(data, tuple):
            kind = data[0]
            if kind == "series_title":
                self.current_series_title = data[1]
                self.series_view = "seasons"
                self.current_season = None
                self._render_group_items()
                return
            if kind == "season":
                self.current_season = int(data[1])
                self.series_view = "episodes"
                self._render_group_items()
                return

        it: MediaItem = data
        if not it:
            return

        # Dla VOD i Serii pokaż okno detalu zamiast od razu odtwarzać
        self._show_media_detail_dialog(item)

    def _show_media_detail_dialog(self, item: QListWidgetItem):
        """Pokazuje okno detalu filmu/serialu"""
        data = item.data(Qt.UserRole)
        
        if isinstance(data, tuple):
            # To jest tytuł serialu lub sezon, nie pokazuj okna detalu
            return
        
        it: MediaItem = data
        if not it:
            return
        
        # Pobierz metadane z cache lub załaduj
        if it.url in self._meta_cache:
            meta_data = self._meta_cache[it.url]
        else:
            # Jeśli nie ma w cache, pokaż okno z informacją o ładowaniu
            meta_data = {
                "title": it.name,
                "poster": it.tvg_logo if it.tvg_logo and it.tvg_logo.startswith(("http://", "https://")) else "",
                "plot": "Ładowanie metadanych...",
                "year": "",
                "duration": "",
                "genre": "",
                "rating": "",
                "cast": "",
                "source": "Ładowanie...",
            }
            # Rozpocznij ładowanie metadanych
            self._meta_set_pending(it)
        
        # Utwórz i pokaż okno detalu
        dialog = MediaDetailDialog(it, meta_data, self)
        if dialog.exec() == QDialog.Accepted:
            # Użytkownik kliknął "OGLĄDAJ"
            self.current_playing = it
            self._play_item(it)
            self._enter_video_fullscreen()

    # ---------- DEBUG FUNCTION ----------
    def debug_log_meta_info(self, it: MediaItem) -> None:
        """Loguje informacje o itemie dla debugowania"""
        import datetime
        log_file = self.data_dir / "vod_debug.txt"
        
        with open(log_file, "a", encoding="utf-8") as f:
            f.write(f"\n{'='*60}\n")
            f.write(f"Time: {datetime.datetime.now()}\n")
            f.write(f"VOD Item Debug:\n")
            f.write(f"  Name: {it.name}\n")
            f.write(f"  URL: {it.url}\n")
            f.write(f"  tvg-logo: {it.tvg_logo}\n")
            f.write(f"  host: {it.host}\n")
            f.write(f"  stream_id: {it.stream_id}\n")
            f.write(f"  xt_type: {it.xt_type}\n")
            f.write(f"  kind: {it.kind}\n")
            
            # Sprawdź czy URL ma format Xtream
            if "/movie/" in it.url.lower():
                f.write("  ✅ URL FORMAT: /movie/ (GOOD for metadata)\n")
            elif "/series/" in it.url.lower():
                f.write("  ✅ URL FORMAT: /series/ (GOOD for metadata)\n")
            else:
                f.write("  ❌ URL FORMAT: Not Xtream format (NO metadata)\n")
            
            f.write(f"{'='*60}\n")

    # ---------- Settings ----------

    def _write_settings(self) -> None:
        try:
            p = self.data_dir / "settings.json"
            p.write_text(json.dumps(self.settings, ensure_ascii=False, indent=2), encoding="utf-8")
        except Exception:
            pass

    def _save_sources_settings(self) -> None:
        self.settings["sources"] = {
            "m3u": self.btn_src_m3u.isChecked(),
            "stalker": self.btn_src_stalker.isChecked(),
            "xc": self.btn_src_xc.isChecked(),
        }
        self._write_settings()
        self._update_toggle_colors()

    def _update_toggle_colors(self) -> None:
        def style(btn: QPushButton) -> None:
            if btn.isChecked():
                btn.setStyleSheet("background:#163a16; border:1px solid #2ecc71; color:#e6ffe6; border-radius:8px; padding:6px;")
            else:
                btn.setStyleSheet("background:#222; border:1px solid #333; color:#e6e6e6; border-radius:8px; padding:6px;")
        style(self.btn_src_m3u)
        style(self.btn_src_stalker)
        style(self.btn_src_xc)

    def _save_favorites(self) -> None:
        self.settings["favorites"] = sorted(self.favorites)
        self._write_settings()

    # ---------- Section ----------

    def _set_section(self, section: str) -> None:
        if section not in ("live", "vod", "series"):
            return
        self.section = section
        self.stack.setCurrentIndex(0 if section == "live" else (1 if section == "vod" else 2))

        self.series_view = "series_titles"
        self.current_series_title = None
        self.current_season = None
        self.preview_item = None  # Reset podglądu

        self._meta_clear_ui()
        self._show_groups()

    # ---------- Active meta panel ----------

    def _active_meta(self) -> Optional[MetaPanelWidgets]:
        """Zwraca aktywny panel metadanych w zależności od sekcji"""
        if self.section == "vod":
            return self.vod_meta
        if self.section == "series":
            return self.series_meta
        return None

    # ---------- Refresh ----------

    def refresh_sources(self) -> None:
        if self._thr and self._thr.isRunning():
            return

        self.statusBar().showMessage("Odświeżanie źródeł...")
        self.list_groups.clear()
        self.list_live.clear()
        self.list_vod.clear()
        self.list_series.clear()
        self.counter_label.setText("Grupy: 0")
        self._clear_right_panel()
        self._meta_clear_ui()

        self._thr = RefreshThread(
            self.data_dir,
            self.btn_src_m3u.isChecked(),
            self.btn_src_stalker.isChecked(),
            self.btn_src_xc.isChecked(),
        )
        self._thr.done.connect(self._on_refresh_done)
        self._thr.error.connect(self._on_refresh_error)
        self._thr.start()

    def _on_refresh_done(self, items: list, epg_by_id: dict, name_index: dict, xtream_profiles: dict) -> None:
        self.items = list(items)
        self.item_by_url = {c.url: c for c in self.items if c.url}

        self.epg_by_id = dict(epg_by_id)
        self.epg_by_name = dict((name_index.get("epg_by_name") or {}))
        self.icon_by_id = dict((name_index.get("icon_by_id") or {}))
        self.icon_by_name = dict((name_index.get("icon_by_name") or {}))

        self.xtream_profiles = dict(xtream_profiles or {})

        self._build_series_tree()

        live_n = sum(1 for x in self.items if x.kind == "live")
        vod_n = sum(1 for x in self.items if x.kind == "vod")
        series_n = sum(1 for x in self.items if x.kind == "series")

        self.statusBar().showMessage(
            f"Gotowe. LIVE:{live_n} | VOD:{vod_n} | SERIALE:{series_n} | EPG IDs:{len(self.epg_by_id)} | EPG Names:{len(self.epg_by_name)}",
            8000,
        )

        if self.view_mode == "favorites":
            self._render_favorites()
        elif self.view_mode == "group_items":
            self._render_group_items()
        else:
            self._show_groups()

    def _on_refresh_error(self, msg: str) -> None:
        self.statusBar().showMessage("Błąd odświeżania.", 6000)
        QMessageBox.critical(self, "Błąd", msg)

    # ---------- Grouping ----------

    _PREF_CODES = {
        "pl": "PL", "poland": "PL", "polska": "PL",
        "uk": "UK", "gb": "UK",
        "de": "DE",
        "us": "US", "usa": "US",
        "fr": "FR", "it": "IT", "es": "ES", "pt": "PT", "nl": "NL",
        "cz": "CZ", "sk": "SK", "ro": "RO", "hu": "HU", "bg": "BG", "gr": "GR",
        "tr": "TR", "ru": "RU", "ua": "UA",
        "ca": "CA", "au": "AU",
    }

    def _infer_group(self, it: MediaItem) -> str:
        g = (it.group or "").strip()
        if g:
            return g[:80] if len(g) > 80 else g

        name = (it.name or "").strip()
        if "|" in name:
            pref = name.split("|", 1)[0].strip()
            if 1 <= len(pref) <= 24:
                key = re.sub(r"[^a-zA-Z0-9]+", "", pref).lower()
                if key in self._PREF_CODES:
                    return self._PREF_CODES[key]
                if 2 <= len(pref) <= 6 and pref.isupper():
                    return pref
                return pref

        m = re.match(r"^([A-Za-z]{2,6})\b", name)
        if m:
            tok = m.group(1)
            key = tok.lower()
            if key in self._PREF_CODES:
                return self._PREF_CODES[key]
            if tok.isupper() and 2 <= len(tok) <= 4:
                return tok

        return "Inne"

    def _items_for_section(self) -> List[MediaItem]:
        if self.section == "live":
            return [x for x in self.items if x.kind == "live"]
        if self.section == "vod":
            return [x for x in self.items if x.kind == "vod"]
        return [x for x in self.items if x.kind == "series"]

    # ---------- View modes ----------

    def _show_groups(self) -> None:
        self.view_mode = "groups"
        self.current_group = None
        self._render_groups()

        self.list_live.clear()
        self.list_vod.clear()
        self.list_series.clear()

        self.btn_add.setEnabled(self.section == "live")
        self.btn_del.setEnabled(False)
        self.list_groups.setFocus()

    def _open_group(self, item: QListWidgetItem) -> None:
        g = item.data(Qt.UserRole)
        if not g:
            return

        self.view_mode = "group_items"
        self.current_group = str(g)

        if self.section == "series":
            self.series_view = "series_titles"
            self.current_series_title = None
            self.current_season = None

        self._render_group_items()

        self.btn_add.setEnabled(self.section == "live")
        self.btn_del.setEnabled(self.view_mode == "favorites")
        self._mid_list_widget().setFocus()

    def _show_favorites(self) -> None:
        self.view_mode = "favorites"
        self.current_group = None
        self._render_favorites()
        self.btn_add.setEnabled(False)
        self.btn_del.setEnabled(True)
        self._mid_list_widget().setFocus()

    # ---------- Render groups ----------

    def _render_groups(self) -> None:
        self.list_groups.clear()
        q = (self.search.text() or "").strip().lower()

        counts: Dict[str, int] = {}
        for it in self._items_for_section():
            if q and q not in (it.name or "").lower():
                continue
            g = self._infer_group(it)
            counts[g] = counts.get(g, 0) + 1

        groups_sorted = sorted(counts.items(), key=lambda x: (-x[1], x[0].lower()))
        for g, n in groups_sorted:
            itw = QListWidgetItem(f"{g}  ({n})")
            itw.setData(Qt.UserRole, g)
            self.list_groups.addItem(itw)

        self.counter_label.setText(f"{self.section.upper()} | Grupy: {len(groups_sorted)}")
        if self.list_groups.count() > 0:
            self.list_groups.setCurrentRow(0)

    # ---------- EPG match ----------

    _STRIP_TOKENS = re.compile(r"\b(uhd|fhd|hd|sd|4k|8k|hevc|h\.?265|h\.?264|aac|ddp|dolby|multi|pl|pol|uk|de|fr|it|es)\b", re.IGNORECASE)

    def _epg_name_candidates(self, name: str) -> List[str]:
        n = (name or "").strip()
        out: List[str] = []
        if not n:
            return out
        out.append(n)
        if "|" in n:
            out.append(n.split("|", 1)[1].strip())
        nn = re.sub(r"[\[\]\(\)\{\}]", " ", n)
        nn = re.sub(r"\s+", " ", nn).strip()
        out.append(nn)
        nn2 = self._STRIP_TOKENS.sub(" ", nn)
        nn2 = re.sub(r"\s+", " ", nn2).strip()
        if nn2:
            out.append(nn2)

        seen = set()
        final = []
        for x in out:
            if x and x not in seen:
                seen.add(x)
                final.append(x)
        return final

    def _epg_lookup(self, it: MediaItem) -> Optional[EpgNowNext]:
        tid = (it.tvg_id or "").strip()
        if tid and tid in self.epg_by_id:
            return self.epg_by_id[tid]
        for cand in self._epg_name_candidates(it.name or ""):
            nm = normalize_name(cand)
            if nm and nm in self.epg_by_name:
                return self.epg_by_name[nm]
        return None

    # ---------- Picon lookup ----------

    def _best_icon_url(self, it: MediaItem) -> str:
        if (it.tvg_logo or "").strip().lower().startswith(("http://", "https://")):
            return (it.tvg_logo or "").strip()
        tid = (it.tvg_id or "").strip()
        if tid and tid in self.icon_by_id:
            return self.icon_by_id[tid]
        for cand in self._epg_name_candidates(it.name or ""):
            nm = normalize_name(cand)
            if nm and nm in self.icon_by_name:
                return self.icon_by_name[nm]
        return ""

    # ---------- Mid list helpers ----------

    def _mid_list_widget(self) -> QListWidget:
        if self.section == "live":
            return self.list_live
        if self.section == "vod":
            return self.list_vod
        return self.list_series

    # ---------- Series tree ----------

    _RE_SE = re.compile(r"(?:\bS(?P<s>\d{1,2})\s*E(?P<e>\d{1,3})\b)|(?:\b(?P<s2>\d{1,2})x(?P<e2>\d{1,3})\b)", re.IGNORECASE)

    def _series_title_and_season(self, name: str) -> Tuple[str, int]:
        n = (name or "").strip()
        if "|" in n:
            n = n.split("|", 1)[1].strip()

        m = self._RE_SE.search(n)
        season = 1
        if m:
            s = m.group("s") or m.group("s2")
            if s:
                try:
                    season = max(1, int(s))
                except Exception:
                    season = 1
            title = n[:m.start()].strip(" -._")
            if not title:
                title = n
        else:
            title = n

        title = self._STRIP_TOKENS.sub(" ", title)
        title = re.sub(r"\s+", " ", title).strip()
        if not title:
            title = (name or "Unknown").strip()
        return title, season

    def _build_series_tree(self) -> None:
        self._series_tree = {}
        for it in self.items:
            if it.kind != "series":
                continue
            cat = self._infer_group(it)
            title, season = self._series_title_and_season(it.name or "")
            self._series_tree.setdefault(cat, {}).setdefault(title, {}).setdefault(season, []).append(it)

        for cat, by_title in self._series_tree.items():
            for title, by_season in by_title.items():
                for s, eps in by_season.items():
                    by_season[s] = sorted(eps, key=lambda x: (x.name or "").lower())

    # ---------- Rendering ----------

    def _render_group_items(self) -> None:
        q = (self.search.text() or "").strip().lower()
        gsel = (self.current_group or "")

        w = self._mid_list_widget()
        w.clear()

        if self.section == "live":
            items = [x for x in self._items_for_section() if self._infer_group(x) == gsel]
            if q:
                items = [x for x in items if q in (x.name or "").lower()]

            for it in items:
                rec = self._epg_lookup(it)
                now_txt = f"  •  NOW: {rec.now_title}" if rec and rec.now_title else ""
                next_txt = f" | NEXT: {rec.next_title}" if rec and rec.next_title else ""
                fav = " ★" if it.url in self.favorites else ""
                li = QListWidgetItem(f"{it.name}{fav}{now_txt}{next_txt}")
                li.setData(Qt.UserRole, it)
                w.addItem(li)

            # Zapisz do cache
            self._cached_group_items[gsel] = (self.section, items)
            self._last_visited_group = gsel

            self.counter_label.setText(f"{self.section.upper()} | {gsel}: {len(items)}")
            if w.count() > 0:
                w.setCurrentRow(0)
                # Automatycznie pokaż EPG dla pierwszego elementu
                first_item = w.item(0)
                if first_item:
                    data = first_item.data(Qt.UserRole)
                    if isinstance(data, MediaItem):
                        self.preview_item = data
                        self._update_right_panel(data)
            return

        if self.section == "vod":
            items = [x for x in self._items_for_section() if self._infer_group(x) == gsel]
            if q:
                items = [x for x in items if q in (x.name or "").lower()]

            for it in items:
                fav = " ★" if it.url in self.favorites else ""
                li = QListWidgetItem(f"{it.name}{fav}")
                li.setData(Qt.UserRole, it)
                w.addItem(li)

            # Zapisz do cache
            self._cached_group_items[gsel] = (self.section, items)
            self._last_visited_group = gsel

            self.counter_label.setText(f"{self.section.upper()} | {gsel}: {len(items)}")
            if w.count() > 0:
                w.setCurrentRow(0)
                first = w.item(0)
                if first:
                    data = first.data(Qt.UserRole)
                    if isinstance(data, MediaItem):
                        self._meta_set_loading(data)
                        self._meta_set_pending(data)
            return

        # SERIES navigation
        cat = gsel
        by_title = self._series_tree.get(cat, {})
        titles = sorted(by_title.keys(), key=lambda x: x.lower())

        if self.series_view == "series_titles":
            shown = [t for t in titles if (not q or q in t.lower())]
            for t in shown:
                seasons = sorted(by_title.get(t, {}).keys())
                li = QListWidgetItem(f"{t}  (Sezony: {len(seasons)})")
                li.setData(Qt.UserRole, ("series_title", t))
                w.addItem(li)
            
            # Zapisz do cache
            items_for_cache = []
            for t in titles:
                seasons = by_title.get(t, {})
                for season_num, eps in seasons.items():
                    items_for_cache.extend(eps)
            self._cached_group_items[gsel] = (self.section, items_for_cache)
            self._last_visited_group = gsel
            
            self.counter_label.setText(f"SERIALE | {cat}: {len(shown)}")
            if w.count() > 0:
                w.setCurrentRow(0)
                # Dla seriali: wybierz pierwszy serial i pobierz jego metadane
                first_item = w.item(0)
                if first_item:
                    data = first_item.data(Qt.UserRole)
                    if isinstance(data, tuple) and data[0] == "series_title":
                        rep = self._series_pick_meta_item(data)
                        if isinstance(rep, MediaItem):
                            self._meta_set_loading(rep)
                            self._meta_set_pending(rep)
                        else:
                            # DEBUG
                            self._log_series_debug(f"Failed to pick meta item for series title: {data[1]}")
            return

        if self.series_view == "seasons" and self.current_series_title:
            seasons = sorted(by_title.get(self.current_series_title, {}).keys())
            for s in seasons:
                eps = by_title[self.current_series_title].get(s, [])
                li = QListWidgetItem(f"Sezon {s}  (Odcinki: {len(eps)})")
                li.setData(Qt.UserRole, ("season", s))
                w.addItem(li)
            self.counter_label.setText(f"SERIALE | {cat} | {self.current_series_title}")
            if w.count() > 0:
                w.setCurrentRow(0)
                # Dla sezonów: wybierz pierwszy sezon i pobierz jego metadane
                first_item = w.item(0)
                if first_item:
                    data = first_item.data(Qt.UserRole)
                    if isinstance(data, tuple) and data[0] == "season":
                        rep = self._series_pick_meta_item(data)
                        if isinstance(rep, MediaItem):
                            self._meta_set_loading(rep)
                            self._meta_set_pending(rep)
                        else:
                            # DEBUG
                            self._log_series_debug(f"Failed to pick meta item for season: {data[1]}")
            return

        if self.series_view == "episodes" and self.current_series_title and self.current_season:
            eps = by_title.get(self.current_series_title, {}).get(self.current_season, [])
            if q:
                eps = [x for x in eps if q in (x.name or "").lower()]
            for it in eps:
                li = QListWidgetItem(it.name)
                li.setData(Qt.UserRole, it)
                w.addItem(li)
            self.counter_label.setText(f"SERIALE | {cat} | {self.current_series_title} | Sezon {self.current_season}: {len(eps)}")
            if w.count() > 0:
                w.setCurrentRow(0)
                first = w.item(0)
                if first:
                    data = first.data(Qt.UserRole)
                    if isinstance(data, MediaItem):
                        self._meta_set_loading(data)
                        self._meta_set_pending(data)
            return

    def _render_favorites(self) -> None:
        q = (self.search.text() or "").strip().lower()
        w = self._mid_list_widget()
        w.clear()

        out: List[MediaItem] = []
        for url in sorted(self.favorites):
            it = self.item_by_url.get(url)
            if it is None:
                name = f"(BRAK W ŹRÓDŁACH) {url}"
                if q and q not in name.lower():
                    continue
                out.append(MediaItem(name=name, url=url, kind=self.section))
                continue
            if it.kind != self.section:
                continue
            if q and q not in (it.name or "").lower():
                continue
            out.append(it)

        for it in out:
            li = QListWidgetItem(f"{it.name} ★")
            li.setData(Qt.UserRole, it)
            w.addItem(li)

        self.counter_label.setText(f"{self.section.upper()} | ULUBIONE: {len(out)}")
        if w.count() > 0:
            w.setCurrentRow(0)
            if self.section in ("vod", "series") and out:
                self._meta_set_pending(out[0])

    def _apply_filter(self) -> None:
        if self.view_mode == "groups":
            self._render_groups()
            self.list_live.clear()
            self.list_vod.clear()
            self.list_series.clear()
            self._meta_clear_ui()
        elif self.view_mode == "group_items":
            self._render_group_items()
        else:
            self._render_favorites()

    # ---------- Picons (cache) ----------

    def _picon_cache_dir(self) -> Path:
        p = self.data_dir / "cache" / "picons"
        p.mkdir(parents=True, exist_ok=True)
        return p

    def _picon_path_for(self, it: MediaItem) -> Path:
        key = (it.tvg_id or it.name or "item").strip()
        key = re.sub(r"[^a-zA-Z0-9]+", "_", key)[:120]
        return self._picon_cache_dir() / f"{key}.png"

    def _load_picon_pixmap(self, it: MediaItem) -> Optional[QPixmap]:
        path = self._picon_path_for(it)
        if path.exists():
            px = QPixmap(str(path))
            if not px.isNull():
                return px

        url = self._best_icon_url(it)
        if not url.lower().startswith(("http://", "https://")):
            return None

        try:
            r = requests.get(url, timeout=20, headers={"User-Agent": "Mozilla/5.0 IPTV_on_the_GO/1.1"})
            r.raise_for_status()
            data = r.content
            px = QPixmap()
            if px.loadFromData(data):
                try:
                    path.write_bytes(data)
                except Exception:
                    pass
                return px
        except Exception:
            return None

        return None

    # ---------- Meta UI helpers ----------

    def _meta_clear_ui(self) -> None:
        """Czyści UI aktywnego panelu metadanych"""
        meta = self._active_meta()
        if not meta:
            return
        meta.title.setText("—")
        meta.line.setText("")
        meta.cast.setText("")
        meta.plot.setText("Najedź na film/serial aby pobrać opis i plakat z SERWERA (Xtream).")
        meta.poster.clear()

    def _meta_set_loading(self, it: MediaItem) -> None:
        """Ustawia stan ładowania w aktywnym panelu"""
        meta = self._active_meta()
        if not meta:
            return
        title, year = _clean_title_for_search(it.name)
        meta.title.setText(title)
        meta.line.setText(f"Rok: {year}" if year else "")
        meta.cast.setText("")
        meta.plot.setText("Ładowanie metadanych (serwer)...")
        meta.poster.clear()

    def _meta_set_ui(self, meta_data: dict) -> None:
        """Wyświetla metadane w aktywnym panelu"""
        meta = self._active_meta()
        if not meta:
            return

        title = (meta_data.get("title") or "—").strip()
        plot = (meta_data.get("plot") or "").strip()
        year = (meta_data.get("year") or "").strip()
        duration = (meta_data.get("duration") or "").strip()
        genre = (meta_data.get("genre") or "").strip()
        rating = (meta_data.get("rating") or "").strip()
        cast = (meta_data.get("cast") or "").strip()
        poster = (meta_data.get("poster") or "").strip()
        source = (meta_data.get("source") or "").strip()

        meta.title.setText(title)

        line_parts = []
        if year:
            line_parts.append(f"Rok: {year}")
        if duration:
            line_parts.append(f"Czas: {duration}")
        if genre:
            line_parts.append(f"Gatunek: {genre}")
        if rating:
            line_parts.append(f"Ocena: {rating}")
        if source:
            line_parts.append(f"Źródło: {source}")
        meta.line.setText("  •  ".join(line_parts))

        meta.cast.setText(f"Obsada: {cast}" if cast else "")
        
        # FALLBACK: Jeśli brak metadanych, pokaż info debug
        if not meta_data.get("plot") or meta_data.get("source") == "ERROR":
            plot = f"DEBUG INFO:\n"
            plot += f"Title: {title}\n"
            if self._pending_meta_item:
                plot += f"URL: {self._pending_meta_item.url}\n"
                if "/movie/" in self._pending_meta_item.url.lower():
                    plot += "URL TYPE: /movie/ (Should work with metadata)\n"
                elif "/series/" in self._pending_meta_item.url.lower():
                    plot += "URL TYPE: /series/ (Should work with metadata)\n"
                else:
                    plot += "URL TYPE: Not Xtream format (NO metadata support)\n"
            plot += "\nCheck data/vod_debug.txt and data/series_debug.txt for details"
            meta_data["plot"] = plot
        
        meta.plot.setText(plot if plot else "Brak opisu (serwer go nie zwraca).")

        if poster.lower().startswith(("http://", "https://")):
            px = self._load_any_image_cached(poster)
            if px and not px.isNull():
                meta.poster.setPixmap(px)
            else:
                meta.poster.clear()
        else:
            meta.poster.clear()

    def _poster_cache_dir(self) -> Path:
        p = self.data_dir / "cache" / "posters"
        p.mkdir(parents=True, exist_ok=True)
        return p

    def _load_any_image_cached(self, url: str) -> Optional[QPixmap]:
        u = (url or "").strip()
        if not u.lower().startswith(("http://", "https://")):
            return None
        key = re.sub(r"[^a-zA-Z0-9]+", "_", u)[-120:]
        path = self._poster_cache_dir() / f"{key}.img"

        if path.exists():
            px = QPixmap(str(path))
            if not px.isNull():
                return px

        try:
            r = requests.get(u, timeout=20, headers={"User-Agent": "Mozilla/5.0 IPTV_on_the_GO/1.1"})
            r.raise_for_status()
            data = r.content
            px = QPixmap()
            if px.loadFromData(data):
                try:
                    path.write_bytes(data)
                except Exception:
                    pass
                return px
        except Exception:
            return None
        return None


    # ---------------- Buffering / reconnect watchdog ----------------

    def _init_buffer_overlay(self) -> None:
        """Overlay shown on top of video when stream stalls/buffers."""
        if hasattr(self, "_buffer_overlay") and self._buffer_overlay:
            return

        # Put overlay inside the video frame so it also covers fullscreen.
        self._buffer_overlay = QWidget(self.video)
        self._buffer_overlay.setObjectName("bufferOverlay")
        self._buffer_overlay.setAttribute(Qt.WA_TransparentForMouseEvents, True)
        self._buffer_overlay.hide()

        self._buffer_overlay.setStyleSheet(
            "#bufferOverlay { background: rgba(0,0,0,150); border-radius: 12px; }"
        )

        lay = QVBoxLayout(self._buffer_overlay)
        lay.setContentsMargins(18, 18, 18, 18)
        lay.setSpacing(10)
        lay.setAlignment(Qt.AlignCenter)

        self._buffer_text = QLabel("Buforowanie…")
        self._buffer_text.setAlignment(Qt.AlignCenter)
        self._buffer_text.setStyleSheet("color: white; font-size: 18px;")

        self._buffer_bar = QProgressBar()
        self._buffer_bar.setTextVisible(False)
        # Busy/indeterminate animation:
        self._buffer_bar.setRange(0, 0)
        self._buffer_bar.setFixedWidth(260)

        lay.addWidget(self._buffer_text)
        lay.addWidget(self._buffer_bar)

        self._buffer_overlay.raise_()
        self._buffer_overlay.resize(self.video.size())

    def _init_buffer_watchdog(self) -> None:
        # playback context
        self._current_play_url: str = ""
        self._stall_active: bool = False
        self._stall_secs: int = 0
        self._stall_last_time_ms: int = -1
        self._buffer_overlay_shown_at: float = 0.0
        self._time_progress_supported: bool = False
        self._stall_started_monotonic: float = 0.0

        self._buffer_watch_timer = QTimer(self)
        self._buffer_watch_timer.setInterval(1000)
        self._buffer_watch_timer.timeout.connect(self._buffer_watch_tick)

        self._buffer_retry_timer = QTimer(self)
        self._buffer_retry_timer.setInterval(5000)
        self._buffer_retry_timer.timeout.connect(self._buffer_retry_tick)

    def _show_buffer_overlay(self, msg: str = "Buforowanie…") -> None:
        try:
            self._init_buffer_overlay()
            self._buffer_text.setText(msg)
            self._buffer_overlay.resize(self.video.size())
            self._buffer_overlay.show()
            self._buffer_overlay.raise_()
        except Exception:
            pass

    def _hide_buffer_overlay(self) -> None:
        try:
            if hasattr(self, "_buffer_overlay") and self._buffer_overlay:
                self._buffer_overlay.hide()
        except Exception:
            pass

    def _player_time_ms(self) -> int:
        """Best-effort current playback time in ms; returns -1 if unknown."""
        try:
            p = self.player
        except Exception:
            return -1

        # Common wrappers
        for attr in ("get_time", "time", "getTime"):
            fn = getattr(p, attr, None)
            if callable(fn):
                try:
                    t = int(fn())
                    return t
                except Exception:
                    pass

        # Sometimes wrapper exposes underlying vlc player as .mp or .media_player
        for inner in ("mp", "media_player", "_mp", "_player"):
            ip = getattr(p, inner, None)
            if ip is None:
                continue
            for attr in ("get_time", "time"):
                fn = getattr(ip, attr, None)
                if callable(fn):
                    try:
                        return int(fn())
                    except Exception:
                        pass

        return -1


def _player_state_name(self) -> str:
    """Best-effort VLC state name: Playing/Buffering/Opening/Paused/Stopped/Error/Unknown."""
    try:
        p = self.player
    except Exception:
        return "Unknown"

    # wrapper might expose state directly
    for attr in ("get_state", "state", "getState"):
        fn = getattr(p, attr, None)
        if callable(fn):
            try:
                st = fn()
                return str(st)
            except Exception:
                pass

    # underlying vlc player
    for inner in ("mp", "media_player", "_mp", "_player"):
        ip = getattr(p, inner, None)
        if ip is None:
            continue
        fn = getattr(ip, "get_state", None)
        if callable(fn):
            try:
                st = fn()
                return str(st)
            except Exception:
                pass
    return "Unknown"

    def _buffer_start_stall(self) -> None:
        if self._stall_active:
            return
        import time as _t
        self._stall_active = True
        self._stall_secs = 0
        self._stall_started_monotonic = _t.monotonic()
        self._show_buffer_overlay("Buforowanie…")
        self._buffer_retry_timer.start()

    def _buffer_clear_stall(self) -> None:
        if not self._stall_active:
            return
        self._stall_active = False
        self._stall_secs = 0
        self._hide_buffer_overlay()
        self._buffer_retry_timer.stop()

def _buffer_watch_tick(self) -> None:
    """Detect stalled playback; show overlay only when actually buffering/stalled."""
    if not getattr(self, "_current_play_url", ""):
        self._buffer_clear_stall()
        self._buffer_watch_timer.stop()
        return

    st = (self._player_state_name() or "").lower()

    # If VLC says it is playing, never show buffering overlay.
    if "playing" in st:
        self._stall_last_time_ms = self._player_time_ms()
        self._stall_secs = 0
        self._buffer_clear_stall()
        return

    # If VLC indicates buffering/opening, show after a short grace period.
    if ("buffer" in st) or ("opening" in st):
        self._stall_secs += 1
        if self._stall_secs >= 2:
            self._buffer_start_stall()
        return

    # Fallback: time movement check (only if time is available)
    t = self._player_time_ms()
    if t < 0:
        # Don't guess buffering if we can't read time (prevents false positives)
        self._buffer_clear_stall()
        self._buffer_watch_timer.stop()
        return

    if self._stall_last_time_ms < 0:
        self._stall_last_time_ms = t
        self._stall_secs = 0
        self._buffer_clear_stall()
        return

    if t > self._stall_last_time_ms:
        self._stall_last_time_ms = t
        self._stall_secs = 0
        self._buffer_clear_stall()
        return

    # time not moving; if paused -> not buffering
    if "pause" in st:
        self._buffer_clear_stall()
        return

    self._stall_secs += 1
    if self._stall_secs >= 3:
        self._buffer_start_stall()

    if self._stall_active and self._stall_secs >= 60:
        self._show_buffer_overlay("Brak połączenia z internetem/serwerem…\nPonawiam…")

    def _buffer_retry_tick(self) -> None:
        """Try to restart the current URL while we are stalled."""
        if not self._stall_active:
            return
        url = (self._current_play_url or "").strip()
        if not url:
            return
        try:
            # Re-play the same URL. VLC usually reconnects; if not, this forces it.
            self.player.play(url)
        except Exception:
            pass

    def resizeEvent(self, event) -> None:
        # keep overlay centered on resize/fullscreen changes
        try:
            if hasattr(self, "_buffer_overlay") and self._buffer_overlay and self.video:
                self._buffer_overlay.resize(self.video.size())
        except Exception:
            pass
        super().resizeEvent(event)


    def _meta_set_pending(self, it: MediaItem) -> None:
        # DODANE: Logowanie informacji debug
        self.debug_log_meta_info(it)  # <-- LOGUJ INFORMACJE
        
        self._pending_meta_item = it
        self._meta_hover_timer.start(180)

    def _meta_fetch_from_pending(self) -> None:
        it = self._pending_meta_item
        if not it:
            return

        if it.url in self._meta_cache:
            self._meta_set_ui(self._meta_cache[it.url])
            return

        if self._meta_thread and self._meta_thread.isRunning():
            try:
                self._meta_thread.terminate()
            except Exception:
                pass

        self._meta_thread = MetaThread(self.data_dir, it.url, it, self.xtream_profiles, self.tmdb_key, self.omdb_key)
        self._meta_thread.done.connect(self._on_meta_done)
        self._meta_thread.error.connect(self._on_meta_error)
        self._meta_thread.start()

    def _on_meta_done(self, url: str, meta: dict) -> None:
        self._meta_cache[url] = dict(meta or {})
        self._meta_set_ui(self._meta_cache[url])

    def _on_meta_error(self, url: str, msg: str) -> None:
        it = self.item_by_url.get(url)
        title, year = _clean_title_for_search(it.name if it else url)
        meta = {
            "title": title,
            "year": year or "",
            "poster": (it.tvg_logo if it else ""),
            "plot": f"(Błąd pobierania metadanych)\n{msg}\nSprawdź data/meta_fetch_log.txt",
            "duration": "",
            "genre": "",
            "rating": "",
            "cast": "",
            "source": "ERROR",
        }
        self._meta_cache[url] = meta
        self._meta_set_ui(meta)

    # ---------- Favorites ----------

    def _fav_add_current(self) -> None:
        if not self.current_playing or not self.current_playing.url:
            return
        self.favorites.add(self.current_playing.url)
        self._save_favorites()
        if self.view_mode == "group_items":
            self._render_group_items()

    def _fav_del_selected(self) -> None:
        w = self._mid_list_widget()
        item = w.currentItem()
        it = item.data(Qt.UserRole) if item else None
        if not it or isinstance(it, tuple):
            return
        if it.url in self.favorites:
            self.favorites.discard(it.url)
            self._save_favorites()
        if self.view_mode == "favorites":
            self._render_favorites()

    # ---------- Play item ----------

    def _play_item(self, it: MediaItem) -> None:
        url = (it.url or "").strip()
        if not url:
            return

        if url.startswith("stalker://"):
            rest = url[len("stalker://"):]
            try:
                _, ch_id, cmd = rest.split("::", 2)
            except Exception:
                QMessageBox.warning(self, "Błąd", "Nieprawidłowy URL Stalkera.")
                return

            real = (cmd or "").strip()
            low = real.lower()
            for pfx in ("ffmpeg ", "auto "):
                if low.startswith(pfx):
                    real = real[len(pfx):].strip()
                    break
            if "stream=&" in real and ch_id:
                real = real.replace("stream=&", f"stream={ch_id}&")

            # buffer watchdog context
            self._current_play_url = str(real)
            self._stall_last_time_ms = -1
            self._time_progress_supported = False

            self._stall_secs = 0
            if getattr(self, "current_playing", None) is not None and getattr(self.current_playing, "kind", "") != "live":
                self._buffer_watch_timer.start()
            self.player.play(real)
            return

        # buffer watchdog context
        self._current_play_url = str(url)
        self._stall_last_time_ms = -1
        self._time_progress_supported = False

        self._stall_secs = 0
        if getattr(self, "current_playing", None) is not None and getattr(self.current_playing, "kind", "") != "live":
            self._buffer_watch_timer.start()
        self.player.play(url)

    # ---------- Right panel (Live TV) ----------

    def _clear_right_panel(self) -> None:
        self.lbl_name.setText("—")
        self.lbl_picon.clear()
        self.lbl_now.setText("NOW: —")
        self.lbl_desc.setText("")
        self.lbl_next.setText("NEXT: —")

    def _update_right_panel(self, it: MediaItem) -> None:
        self.lbl_name.setText(it.name or "—")

        px = self._load_picon_pixmap(it)
        if px and not px.isNull():
            self.lbl_picon.setPixmap(px)
        else:
            self.lbl_picon.clear()

        rec = self._epg_lookup(it)
        if rec and rec.now_title:
            self.lbl_now.setText(f"NOW: {rec.now_title}")
            self.lbl_desc.setText(rec.now_desc or "")
            self.lbl_next.setText(f"NEXT: {rec.next_title or '—'}")
        else:
            self.lbl_now.setText("NOW: —")
            self.lbl_desc.setText("")
            self.lbl_next.setText("NEXT: —")

    # ---------- FULLSCREEN ----------

    def _toggle_video_fullscreen(self) -> None:
        if self._fs_host is None:
            self._enter_video_fullscreen()
        else:
            try:
                self._fs_host.close()
            except Exception:
                self._exit_video_fullscreen()


    def _get_fullscreen_infobar_data(self) -> dict:
        """Dane do infobara w fullscreen (LIVE)."""
        data = {
            "now_title": "—",
            "now_time": "",
            "next_title": "—",
            "next_time": "",
            "progress": None,
            "quality": "—",
            "fps": "",
            "clock": QDateTime.currentDateTime().toString("dd.MM.yyyy  HH:mm"),
            "picon_pixmap": None,
        }
        try:
            lw = getattr(self, "list_live", None)
            item = lw.currentItem() if lw else None
            it = item.data(Qt.UserRole) if item else None
            if it:
                # picon
                try:
                    icon_url = self._best_icon_url(it)
                    if icon_url:
                        px = self._load_any_image_cached(icon_url)
                        if px:
                            data["picon_pixmap"] = px
                except Exception:
                    pass

                # quality guess
                nm = (getattr(it, "name", "") or "").upper()
                q = "SD"
                if "UHD" in nm or "4K" in nm:
                    q = "UHD"
                elif "FHD" in nm:
                    q = "FHD"
                elif "HD" in nm:
                    q = "HD"
                data["quality"] = q

                # EPG now/next
                nn = self._epg_lookup(it)
                if nn:
                    now_title = getattr(nn, "now_title", None) or getattr(nn, "now", None) or ""
                    next_title = getattr(nn, "next_title", None) or getattr(nn, "next", None) or ""
                    if now_title:
                        data["now_title"] = str(now_title)
                    if next_title:
                        data["next_title"] = str(next_title)

                    ns = getattr(nn, "now_start", None)
                    ne = getattr(nn, "now_end", None)
                    xs = getattr(nn, "next_start", None)
                    xe = getattr(nn, "next_end", None)

                    def fmt(t):
                        if t is None:
                            return ""
                        if isinstance(t, (int, float)) and t > 100000:
                            return datetime.datetime.fromtimestamp(float(t)).strftime("%H:%M")
                        return str(t)

                    if ns and ne:
                        data["now_time"] = f"{fmt(ns)} - {fmt(ne)}"
                    if xs and xe:
                        data["next_time"] = f"{fmt(xs)} - {fmt(xe)}"

                    if isinstance(ns, (int, float)) and isinstance(ne, (int, float)) and float(ne) > float(ns):
                        now_ts = datetime.datetime.now().timestamp()
                        data["progress"] = (now_ts - float(ns)) / (float(ne) - float(ns))
        except Exception:
            pass
        return data

    def _enter_video_fullscreen(self) -> None:
        if not self.video:
            return

        self._video_placeholder = QWidget()
        self._video_parent_layout = self.video.parentWidget().layout()
        self._video_index_in_layout = self._video_parent_layout.indexOf(self.video)
        self._video_parent_layout.insertWidget(self._video_index_in_layout, self._video_placeholder)
        self.video.setParent(None)

        self._fs_host = FullscreenVideoHost(self.video)

        is_live_fs = (
            self.section == "live"
            and self.current_playing is not None
            and self.current_playing.kind == "live"
        )

        self._fs_host.set_infobar_enabled(is_live_fs)

        if is_live_fs:
            try:
                self._fs_host.set_info_callback(self._get_fullscreen_infobar_data)
            except Exception:
                pass

        self._fs_host.closed.connect(self._exit_video_fullscreen)
        self._fs_host.open_fullscreen()

        if is_live_fs:
            try:
                self._fs_host.show_info_bar()
            except Exception:
                pass


    def _exit_video_fullscreen(self) -> None:
        if self._fs_host is None:
            return

        host = self._fs_host
        self._fs_host = None

        try:
            host.closed.disconnect(self._exit_video_fullscreen)
        except Exception:
            pass

        lay = self._video_parent_layout
        idx = self._video_index_in_layout

        if lay is not None and idx is not None:
            if self._video_placeholder is not None:
                lay.removeWidget(self._video_placeholder)
                self._video_placeholder.deleteLater()
                self._video_placeholder = None
            lay.insertWidget(idx, self.video)

        self._video_parent_layout = None
        self._video_index_in_layout = None

        self.player.set_video_widget(self.video)

        self.activateWindow()
        self.raise_()
        self.list_live.setFocus()

    # ---------- Close handling (bez crashy QThread) ----------

    def closeEvent(self, e) -> None:
        try:
            if self._thr and self._thr.isRunning():
                self._thr.quit()
                self._thr.wait(800)
        except Exception:
            pass
        try:
            if self._meta_thread and self._meta_thread.isRunning():
                self._meta_thread.quit()
                self._meta_thread.wait(800)
        except Exception:
            pass
        super().closeEvent(e)
