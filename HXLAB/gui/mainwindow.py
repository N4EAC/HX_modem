from __future__ import annotations

import json
import base64
import ctypes
import hashlib
import os
import queue
import random
import re
import subprocess
import threading
import time
import uuid
import tkinter as tk
from tkinter import ttk, messagebox, filedialog
from pathlib import Path

import numpy as np
import sounddevice as sd

from HXLAB.core.modem import SAMPLE_RATE, SYMBOL_RATE, TONE_FREQ, choose_mode, add_awgn, hx_encode, hx_decode, estimate_tx_seconds
from HXLAB.audio.devices import filtered_rx_devices, filtered_tx_devices, format_device
from HXLAB.cat import CATManager, CATSettings, RadioState, available_ports
from HXLAB.audio.engine import (
    transmit,
    live_loopback,
    tx_audio_for_payload,
    save_wav,
    read_wav,
    decode_audio_capture,
    receive_stream_until_frame,
)

VERSION = "0.8.4 CAT Preview"
HX_PROTOCOL_VERSION = "1.0-draft"
HX_CAPABILITIES = ("MSG", "CQ", "SNR", "BEACON", "DIRECT", "SESSION", "BUSY", "PROFILE", "FILE")
APP_NAME = "HX – Hyper eXchange"
APP_SUBTITLE = ""
DOC_DIR = os.path.join(os.path.expanduser("~"), "Documents", "HX_Modem")
CONFIG_PATH = os.path.join(DOC_DIR, "hx_lab_config.json")
LOG_PATH = os.path.join(DOC_DIR, "hx_lab_session.log")
CHAT_DIR = os.path.join(DOC_DIR, "Chats")
RECEIVE_DIR = os.path.join(DOC_DIR, "Received_Files")
FILE_STATE_DIR = os.path.join(DOC_DIR, "File_State")
FILE_DEBUG_LOG_PATH = os.path.join(DOC_DIR, "hx_file_transfer_debug.log")

COLORS = {
    "bg": "#15181d",
    "panel": "#20252d",
    "panel2": "#171c23",
    "panel3": "#0d1117",
    "grid": "#2f3948",
    "text": "#e0e0e0",
    "muted": "#8b949e",
    "accent": "#58a6ff",
    "green": "#40d97b",
    "amber": "#ffc857",
    "red": "#ff5555",
    "blue": "#2f81f7",
}


class HXLAB(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(f"{APP_NAME} v{VERSION}")
        self.geometry("1040x680")
        self.minsize(820, 500)
        self.configure(bg=COLORS["bg"])
        self.set_app_icon()

        self.q = queue.Queue()
        self.rx_monitor = False
        self.rx_thread = None
        self._rx_thread_lock = threading.RLock()
        self._rx_generation = 0
        self._rx_start_pending = False
        self._recent_rx_frames = {}
        self._partial_rx_mark = None
        self.config_data = self.load_config()
        self.receive_dir = self.config_data.get("receive_dir", RECEIVE_DIR)
        saved_debug_level = str(self.config_data.get("debug_level", "NORMAL") or "NORMAL").strip().upper()
        if saved_debug_level not in ("NORMAL", "VERBOSE", "DEVELOPER"):
            saved_debug_level = "NORMAL"
        self.debug_level_var = tk.StringVar(value=saved_debug_level)
        self._last_normal_geometry = str(self.config_data.get("window_geometry", "1040x680") or "1040x680")
        self._geometry_save_after = None

        self.callsign_var = tk.StringVar(value=self.config_data.get("callsign", "NOCALL"))
        self.operator_name_var = tk.StringVar(value=self.config_data.get("operator_name", ""))
        self.operator_grid_var = tk.StringVar(value=self.config_data.get("operator_grid", ""))
        self.share_profile_var = tk.BooleanVar(value=bool(self.config_data.get("share_profile", True)))
        self.respond_external_snr_connected_var = tk.BooleanVar(value=bool(self.config_data.get("respond_external_snr_connected", True)))
        self.autoload_last_chat_var = tk.BooleanVar(value=bool(self.config_data.get("autoload_last_chat", False)))
        self._normalizing_callsign = False
        self._normalizing_to = False
        saved_mode = str(self.config_data.get("mode", "AUTO") or "AUTO").strip().upper()
        if saved_mode not in ("AUTO", "HX-F", "HX-N"):
            saved_mode = "AUTO"
            self.config_data["mode"] = "AUTO"
        self.mode_var = tk.StringVar(value=saved_mode)
        self.message_var = tk.StringVar(value="")
        self.to_var = tk.StringVar(value="ALL")  # v0.4.6: always default destination to ALL on program start
        self.recent_stations = self.load_recent_stations()
        self.heard_stations = {}  # session-only heard list: CALL -> {time, snr}
        self.station_caps_seen = {}  # CALL -> capability string seen on RX
        self.session_active = False
        self.session_peer = ""
        self.session_id = ""
        self.session_uuid = ""
        self.remote_profiles = {}
        self.qso_current = {
            "call": "--",
            "name": "--",
            "grid": "--",
            "rx_snr": "--",
            "tx_snr": "--",
            "status": "--",
            "start": "--",
            "end": "--",
            "duration": "--",
        }
        self.active_chat_file = None
        self.active_chat_peer = ""
        self.active_chat_started_ts = None
        self.session_started = None
        self.session_last_user_activity = time.time()
        self.last_keepalive_sent = 0.0
        self.keepalive_pending = False
        self.keepalive_missed = 0
        self.keepalive_attempts_sent = 0
        self.keepalive_idle_start_seconds = 120.0
        self.keepalive_repeat_seconds = 60.0
        self.session_idle_warning_active = False
        self.session_disconnect_deadline = None
        self.direct_voice_cooldown = {}  # CALL -> last direct voice announcement time
        self.connect_voice_cooldown = {}
        self.pending_connect_from = ""
        self.pending_connect_id = ""
        self.connect_pending = False
        self.connect_target = ""
        self.connect_retries_sent = 0
        self.connect_max_retries = 3
        self.connect_retry_interval = 30.0
        self.connect_next_retry_time = 0.0
        self.connect_guard_until = 0.0
        self.connect_random_backoff = 0.0
        self.tx_level_var = tk.DoubleVar(value=float(self.config_data.get("tx_level", 0.8)))
        self.output_volume_var = tk.IntVar(value=int(round(self.tx_level_var.get() * 100)))
        # The tune-tone stream reads this plain float from its audio callback,
        # allowing the TX GAIN slider to change the 1 kHz tone level in real time.
        self.tune_gain_live = float(self.tx_level_var.get())
        self.tune_active = False
        self.tune_stream = None
        self.tune_phase = 0.0
        self.tune_was_rx = False
        self.tune_ptt_asserted = False
        self.tx_device = self.config_data.get("tx_device")
        self.rx_device = self.config_data.get("rx_device")
        self.debug_rx_var = tk.BooleanVar(value=True)
        self.rx_capture_mode_var = tk.StringVar(value=self.config_data.get("rx_capture_mode", "OFF"))
        self.startup_sound_var = tk.BooleanVar(value=bool(self.config_data.get("startup_sound", False)))
        self.notification_sounds_var = tk.BooleanVar(value=bool(self.config_data.get("notification_sounds", True)))
        self.voice_announcements_var = tk.BooleanVar(value=bool(self.config_data.get("voice_announcements", True)))
        self.template_var = tk.StringVar(value="N/A")
        self.beacon_enabled_var = tk.BooleanVar(value=False)  # operator safety: beacon never auto-starts
        self.beacon_interval_var = tk.StringVar(value=str(self.config_data.get("beacon_interval_min", 15)))
        self.next_beacon_time: float | None = None
        self.beacon_tx_in_progress = False
        self.tx_busy = False
        self.last_rx_snr = None
        self.hx_channel_busy = False
        self.tx_hold_queue = []
        # Any non-file transmission requested while this station is sending a
        # file is kept completely separate from the protocol TX scheduler.
        # Mixing chat/profile/session traffic into tx_hold_queue can collide
        # with the peer's FILE_ACK turnaround or block FILE_OFFER/CHUNK traffic.
        self.file_deferred_manual = []
        # Profile requests made during an outbound file transfer are held in a
        # dedicated queue. They must not touch the normal TX queue, TX progress,
        # ACK timers, or session activity until the file owner releases TX.
        self.file_deferred_profile_requests = []
        # Post-transfer coordinator.  Deferred operator traffic drains before
        # keepalives resume.  The original file sender receives the first slot;
        # the receiver waits for a longer quiet window to avoid symmetric TX.
        self.post_transfer_drain_active = False
        self.post_transfer_role = ""
        self.post_transfer_not_before = 0.0
        self.post_transfer_quiet_since = 0.0
        self.post_transfer_release_started = False
        self.post_transfer_keepalive_resume_at = 0.0
        # Explicit post-transfer token handoff. Timing alone cannot arbitrate
        # two stations whose deferred queues become ready simultaneously.
        self.post_transfer_phase = ""
        self.post_transfer_token_sent_at = 0.0
        self.post_transfer_token_retries = 0
        self.post_transfer_remote_done = False
        self.post_transfer_token_acked = False
        self.post_transfer_ack_role = ""
        self._tx_hold_notice_time = 0.0
        self.tx_turnaround_guard_until = 0.0
        self.tx_guard_seconds = 2.5
        self.tx_queue_notice = None
        self.tx_queue_notice_var = tk.StringVar(value="")
        self.tx_queue_status_var = tk.StringVar(value="")
        self.profile_request_cooldown = {}  # CALL -> last PROFILE_REQ TX time
        # Reliable file transfer state (session-only; one transfer at a time)
        self.file_tx_active = False
        self.file_rx_active = False
        self.file_tx_cancel = False
        self.file_tx_cancel_pending = False
        self.file_tx_cancel_sending = False
        self.file_tx_cancel_origin = ""
        self.file_rx_cancel_pending = set()
        self.file_tx_ack_event = threading.Event()
        self.file_tx_ack_result = None
        self.file_tx_ack_chunk = -1
        self.file_tx_resume_from = 1
        self.file_tx_accept_announced = False
        self.file_tx_id = ""
        self.file_tx_peer = ""
        self.file_rx = None
        self.file_last_status = ""
        # When this operator presses DISCONNECT, the peer may be transmitting
        # and may not decode our DISCONNECT frame immediately.  During this
        # guard window, do not ACK/NACK incoming file chunks from that peer;
        # silence forces the sender into its normal retry / timeout path.
        self.local_disconnect_peer = ""
        self.local_disconnect_until = 0.0
        self.disconnect_pending = False
        self.disconnect_pending_peer = ""
        self.disconnect_pending_sid = ""
        self.disconnect_not_before = 0.0
        self.file_debug_lock = threading.Lock()
        # Windows awake guard. SetThreadExecutionState is thread-scoped, so all
        # acquire/release calls are marshalled onto the persistent Tk UI thread.
        # A reference count covers the sender and receiver paths independently.
        self.file_awake_refcount = 0
        self.file_tx_awake = False
        self.file_rx_awake = False
        self.tx_debug_seq = 0
        self.tx_debug_lock = threading.Lock()
        self.protocol_tx_mode_override = ""

        # Optional CAT/PTT subsystem. A previously saved CAT profile is treated
        # as the operator's intent to keep CAT enabled on the next launch.
        saved_cat_port = str(self.config_data.get("cat_port", "") or "").strip()
        saved_cat_profile = bool(saved_cat_port)
        self.cat_enabled_var = tk.BooleanVar(value=bool(self.config_data.get("cat_enabled", False)) or saved_cat_profile)
        self.cat_port_var = tk.StringVar(value=saved_cat_port)
        self.cat_baud_var = tk.StringVar(value=str(self.config_data.get("cat_baud", 38400)))
        self.cat_radio_var = tk.StringVar(value=str(self.config_data.get("cat_radio", "Yaesu FT-710") or "Yaesu FT-710"))
        self.ptt_method_var = tk.StringVar(value=str(self.config_data.get("ptt_method", "VOX") or "VOX").upper())
        self.cat_state = RadioState()
        self._last_cat_error = ""
        self.cat_manager = CATManager(self._current_cat_settings(), callback=lambda state: self.q.put(("catstate", state)))

        self.callsign_var.trace_add("write", lambda *_: self.normalize_callsign_var())
        self.to_var.trace_add("write", lambda *_: self.normalize_to_var())

        self.frames_ok = 0
        self.frames_fail = 0
        self.last_decode_hold_until = 0.0
        self.tx_meter_level = 0.0
        self.rx_meter_level = 0.0
        self.led_items: dict[str, tuple[int, int]] = {}
        self.last_rx_detect = "SEARCH"
        self.last_rx_mode = "--"
        self.spectrum_rx_samples = np.zeros(4096, dtype=np.float32)
        self.spectrum_tx_audio = np.zeros(0, dtype=np.float32)
        self.spectrum_tx_started = 0.0
        self.spectrum_tx_active = False
        self.spectrum_lock = threading.Lock()

        self.build_styles()
        self.build_ui()
        self.restore_window_state()
        self.protocol("WM_DELETE_WINDOW", self.on_app_close)
        self.bind("<Configure>", self.on_window_configure, add="+")
        self.update_session_controls()
        self.after(100, self.process_queue)
        self.after(100, self.refresh_meters)
        self.after(1000, self.beacon_tick)
        self.after(1000, self.session_tick)
        self.log(f"{APP_NAME} v{VERSION} ready. Live audio: {int(SAMPLE_RATE)} Hz, symbol rate: {SYMBOL_RATE} baud.")
        if APP_SUBTITLE:
            self.log(APP_SUBTITLE, "ok")
        self.log("Operator experience release: dynamic session control, BUSY, operator profile exchange, SNR controls, and chat transcripts; modem core unchanged.", "warn")
        self.log(f"HX Protocol {HX_PROTOCOL_VERSION}; capabilities: {', '.join(HX_CAPABILITIES)}", "ok")
        self.log("RX debug WAV capture: OFF by default. Enable in Setup > Advanced Dev Tools when needed.", "warn")
        self.log("Beacon defaulted to OFF at startup.", "warn")
        self.after(700, self.auto_start_rx_monitor)
        # One-shot delayed CAT auto-connect. This runs only when CAT was
        # enabled from the saved operator profile and leaves manual Connect
        # available if the radio is powered off or the COM port is unavailable.
        self.after(2000, self.auto_connect_cat)

    def _set_windows_file_awake(self, enable: bool):
        """Keep Windows and the display awake while an HX file transfer is active.

        This runs on the Tk UI thread so the ES_CONTINUOUS state remains tied
        to one long-lived thread. On non-Windows systems it safely does nothing.
        """
        if os.name != "nt":
            return
        try:
            ES_CONTINUOUS = 0x80000000
            ES_SYSTEM_REQUIRED = 0x00000001
            ES_DISPLAY_REQUIRED = 0x00000002
            flags = ES_CONTINUOUS
            if enable:
                flags |= ES_SYSTEM_REQUIRED | ES_DISPLAY_REQUIRED
            result = ctypes.windll.kernel32.SetThreadExecutionState(flags)
            if not result:
                raise ctypes.WinError()
            self.ftlog(f"POWER Windows awake mode {'enabled' if enable else 'released'} for file transfer")
        except Exception as e:
            self.ftlog(f"POWER Windows awake mode change failed enable={enable}: {e}")
            self.qlog(f"Windows awake mode could not be {'enabled' if enable else 'released'}: {e}", "warn")

    def acquire_file_awake(self, direction: str):
        """Acquire the process UI-thread awake guard for TX or RX once."""
        attr = "file_tx_awake" if direction == "tx" else "file_rx_awake"
        if getattr(self, attr, False):
            return
        setattr(self, attr, True)
        self.file_awake_refcount += 1
        self.ftlog(f"POWER awake acquire direction={direction} refs={self.file_awake_refcount}")
        if self.file_awake_refcount == 1:
            self._set_windows_file_awake(True)

    def release_file_awake(self, direction: str):
        """Release one TX/RX ownership of the awake guard."""
        attr = "file_tx_awake" if direction == "tx" else "file_rx_awake"
        if not getattr(self, attr, False):
            return
        setattr(self, attr, False)
        self.file_awake_refcount = max(0, self.file_awake_refcount - 1)
        self.ftlog(f"POWER awake release direction={direction} refs={self.file_awake_refcount}")
        if self.file_awake_refcount == 0:
            self._set_windows_file_awake(False)

    def force_release_file_awake(self):
        """Restore normal Windows power behavior during application shutdown."""
        self.file_tx_awake = False
        self.file_rx_awake = False
        self.file_awake_refcount = 0
        self._set_windows_file_awake(False)

    def restore_window_state(self):
        """Restore the last normal geometry and maximized state."""
        try:
            geometry = str(self.config_data.get("window_geometry", self._last_normal_geometry) or self._last_normal_geometry)
            if geometry:
                self.geometry(geometry)
                self._last_normal_geometry = geometry
            self.update_idletasks()
            if bool(self.config_data.get("window_maximized", False)):
                try:
                    self.state("zoomed")
                except Exception:
                    pass
        except Exception:
            pass

    def on_window_configure(self, _event=None):
        """Remember normal window geometry without writing the config on every pixel."""
        try:
            if self.state() == "normal":
                self._last_normal_geometry = self.geometry()
            if self._geometry_save_after is not None:
                try:
                    self.after_cancel(self._geometry_save_after)
                except Exception:
                    pass
            self._geometry_save_after = self.after(600, self.save_config)
        except Exception:
            pass

    def on_app_close(self):
        try:
            try:
                self.cat_manager.disconnect()
            except Exception:
                pass
            self.save_config()
            self.force_release_file_awake()
        finally:
            super().destroy()

    def destroy(self):
        try:
            try:
                self.cat_manager.disconnect()
            except Exception:
                pass
            self.save_config()
            self.force_release_file_awake()
        finally:
            super().destroy()

    def load_config(self):
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception:
            return {}

    def save_config(self):
        os.makedirs(DOC_DIR, exist_ok=True)
        try:
            with open(FILE_DEBUG_LOG_PATH, "a", encoding="utf-8") as f:
                f.write("\n" + "="*72 + "\n")
                f.write(f"HX {VERSION} started {time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime())} local={self.clean_callsign() if hasattr(self, 'callsign_var') else 'UNKNOWN'}\n")
        except Exception:
            pass
        data = {
            "mode": self.mode_var.get(),
            "tx_level": self.tx_level_var.get(),
            "tx_device": self.tx_device,
            "rx_device": self.rx_device,
            "receive_dir": getattr(self, "receive_dir", RECEIVE_DIR),
            "callsign": self.callsign_var.get().strip().upper() or "NOCALL",
            "operator_name": self.operator_name_var.get().strip() if hasattr(self, "operator_name_var") else "",
            "operator_grid": self.operator_grid_var.get().strip().upper() if hasattr(self, "operator_grid_var") else "",
            "share_profile": bool(self.share_profile_var.get()) if hasattr(self, "share_profile_var") else True,
            "respond_external_snr_connected": bool(self.respond_external_snr_connected_var.get()) if hasattr(self, "respond_external_snr_connected_var") else True,
            "autoload_last_chat": bool(self.autoload_last_chat_var.get()) if hasattr(self, "autoload_last_chat_var") else False,
            "recent_stations": self.recent_stations if hasattr(self, "recent_stations") else [],
            "beacon_interval_min": int(self.beacon_interval_var.get()) if hasattr(self, "beacon_interval_var") else 15,
            "startup_sound": bool(self.startup_sound_var.get()) if hasattr(self, "startup_sound_var") else False,
            "notification_sounds": bool(self.notification_sounds_var.get()) if hasattr(self, "notification_sounds_var") else True,
            "voice_announcements": bool(self.voice_announcements_var.get()) if hasattr(self, "voice_announcements_var") else True,
            "rx_capture_mode": self.rx_capture_mode_var.get() if hasattr(self, "rx_capture_mode_var") else "OFF",
            "debug_level": self.debug_level_var.get().strip().upper() if hasattr(self, "debug_level_var") else "NORMAL",
            "window_geometry": getattr(self, "_last_normal_geometry", "1040x680"),
            "window_maximized": (self.state() == "zoomed") if self.winfo_exists() else False,
            "cat_enabled": bool(self.cat_enabled_var.get()) if hasattr(self, "cat_enabled_var") else False,
            "cat_port": self.cat_port_var.get().strip() if hasattr(self, "cat_port_var") else "",
            "cat_baud": int(self.cat_baud_var.get()) if hasattr(self, "cat_baud_var") and self.cat_baud_var.get().isdigit() else 38400,
            "cat_radio": self.cat_radio_var.get().strip() if hasattr(self, "cat_radio_var") else "Yaesu FT-710",
            "ptt_method": self.ptt_method_var.get().strip().upper() if hasattr(self, "ptt_method_var") else "VOX",
        }
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)

    def set_app_icon(self):
        """Set the HX hand application icon when available. Safe if missing."""
        try:
            base = Path(getattr(__import__("sys"), "_MEIPASS", Path(__file__).resolve().parents[1]))
            candidates = [
                base / "HXLAB" / "resources" / "hx_hand.ico",
                Path(__file__).resolve().parents[1] / "resources" / "hx_hand.ico",
            ]
            for icon in candidates:
                if icon.exists():
                    self.iconbitmap(str(icon))
                    break
        except Exception:
            pass

    def build_styles(self):
        s = ttk.Style(self)
        try:
            s.theme_use("clam")
        except Exception:
            pass
        s.configure("TFrame", background=COLORS["bg"])
        s.configure("Panel.TFrame", background=COLORS["panel"], relief="flat")
        s.configure("TLabel", background=COLORS["bg"], foreground=COLORS["text"])
        s.configure("Panel.TLabel", background=COLORS["panel"], foreground=COLORS["text"])
        s.configure("Muted.TLabel", background=COLORS["panel"], foreground=COLORS["muted"])
        s.configure("Title.TLabel", background=COLORS["bg"], foreground=COLORS["text"], font=("Segoe UI", 18, "bold"))
        s.configure("Section.TLabel", background=COLORS["panel"], foreground=COLORS["text"], font=("Segoe UI", 10, "bold"))
        s.configure("Purple.Section.TLabel", background=COLORS["panel"], foreground="#c084fc", font=("Segoe UI", 10, "bold"))
        s.configure("QSO.TLabel", background=COLORS["panel"], foreground=COLORS["text"], font=("Segoe UI", 8))
        s.configure("QSO.Muted.TLabel", background=COLORS["panel"], foreground=COLORS["muted"], font=("Segoe UI", 8))
        s.configure("Big.TLabel", background=COLORS["panel"], foreground=COLORS["green"], font=("Consolas", 20, "bold"))
        s.configure("Frequency.TLabel", background=COLORS["panel"], foreground=COLORS["green"], font=("Consolas", 19, "bold"))
        s.configure("TButton", padding=3, background="#000000", foreground="#ffffff", bordercolor=COLORS["grid"], lightcolor="#000000", darkcolor="#000000")
        s.map("TButton", background=[("active", "#1b1f27"), ("pressed", "#111111")], foreground=[("active", "#ffffff")])
        s.configure("TCheckbutton", background=COLORS["panel"], foreground=COLORS["text"], focuscolor=COLORS["panel"])
        # Dark HX-themed radio buttons for the Debug / Event Log level selector.
        s.configure(
            "Debug.TRadiobutton",
            background=COLORS["panel"], foreground=COLORS["text"],
            focuscolor=COLORS["panel"], padding=(4, 2),
            indicatorbackground=COLORS["panel3"], indicatorforeground=COLORS["green"],
            bordercolor=COLORS["grid"], lightcolor=COLORS["panel3"], darkcolor=COLORS["panel3"],
        )
        s.map(
            "Debug.TRadiobutton",
            background=[("active", COLORS["panel"]), ("selected", COLORS["panel"])],
            foreground=[("active", COLORS["text"]), ("selected", COLORS["green"])],
            indicatorbackground=[("selected", COLORS["green"]), ("!selected", COLORS["panel3"])],
            indicatorforeground=[("selected", COLORS["panel3"]), ("!selected", COLORS["muted"])],
        )
        s.map("TCheckbutton", background=[("active", "#30363d"), ("pressed", "#20252d")], foreground=[("active", COLORS["text"]), ("pressed", COLORS["text"])])
        s.configure("TCombobox", fieldbackground=COLORS["panel3"], background=COLORS["panel3"], foreground=COLORS["text"], arrowcolor=COLORS["text"], selectbackground=COLORS["panel3"], selectforeground=COLORS["text"])
        s.map("TCombobox", fieldbackground=[("readonly", COLORS["panel3"])], foreground=[("readonly", COLORS["text"])], background=[("readonly", COLORS["panel3"])])
        self.option_add("*TCombobox*Listbox.background", COLORS["panel3"])
        self.option_add("*TCombobox*Listbox.foreground", COLORS["text"])
        self.option_add("*TCombobox*Listbox.selectBackground", COLORS["accent"])
        self.option_add("*TCombobox*Listbox.selectForeground", "#ffffff")
        s.configure("HX.Horizontal.TProgressbar", troughcolor=COLORS["panel3"], background=COLORS["accent"], bordercolor=COLORS["grid"], lightcolor=COLORS["accent"], darkcolor=COLORS["accent"])
        s.configure("Treeview", background=COLORS["panel3"], fieldbackground=COLORS["panel3"], foreground=COLORS["text"], rowheight=22, bordercolor=COLORS["grid"])
        s.map("Treeview", background=[("selected", COLORS["accent"])], foreground=[("selected", "#ffffff")])
        s.configure("Treeview.Heading", background=COLORS["panel"], foreground=COLORS["text"], relief="flat")
        s.configure("Heard.Treeview", background=COLORS["panel3"], fieldbackground=COLORS["panel3"], foreground="#c084fc", rowheight=22, bordercolor=COLORS["grid"], font=("Consolas", 9))
        s.map("Heard.Treeview", background=[("selected", COLORS["accent"])], foreground=[("selected", "#ffffff")])
        s.configure("Heard.Treeview.Heading", background=COLORS["panel"], foreground=COLORS["text"], relief="flat", font=("Segoe UI", 9, "bold"))

    def build_statusbar(self):
        # Dedicated bottom frame packed before the main content. This reserves
        # the status bar outside the resizable panel stack so it remains visible
        # on smaller windows.
        status_frame = tk.Frame(self, bg="#0d1117")
        status_frame.pack(fill="x", side="bottom")
        self.modem_led_canvas = tk.Canvas(status_frame, width=20, height=18, bg="#0d1117", highlightthickness=0)
        self.modem_led_canvas.pack(side="left", padx=(8, 2))
        self.modem_led = self.modem_led_canvas.create_oval(4, 3, 16, 15, fill=COLORS["green"], outline="#000000")
        self.modem_led_label = tk.Label(status_frame, text="MODEM RX", anchor="w", bg="#0d1117", fg=COLORS["green"], font=("Segoe UI", 9, "bold"))
        self.modem_led_label.pack(side="left", padx=(0, 12))
        self.mycall_label = tk.Label(status_frame, text=f"{self.clean_callsign()}", anchor="w", bg="#0d1117", fg=COLORS["accent"], font=("Segoe UI", 8, "bold"))
        self.mycall_label.pack(side="left", padx=(0, 12))
        self.cat_led_canvas = tk.Canvas(status_frame, width=18, height=18, bg="#0d1117", highlightthickness=0)
        self.cat_led_canvas.pack(side="left", padx=(0, 2))
        self.cat_led = self.cat_led_canvas.create_oval(4, 3, 15, 14, fill=COLORS["muted"], outline="#000000")
        self.cat_status_label = tk.Label(status_frame, text="CAT OFF", anchor="w", bg="#0d1117", fg=COLORS["muted"], font=("Segoe UI", 8, "bold"))
        self.cat_status_label.pack(side="left", padx=(0, 12))
        self.radio_mode_label = tk.Label(status_frame, text="RADIO --", anchor="w", bg="#0d1117", fg=COLORS["muted"], font=("Segoe UI", 8, "bold"))
        self.radio_mode_label.pack(side="left", padx=(0, 12))
        self.statusbar = tk.Label(status_frame, text="Audio 44.1 kHz  |  Mode --  |  TX --  |  RX --", anchor="w", bg="#0d1117", fg=COLORS["muted"], font=("Segoe UI", 8))
        self.statusbar.pack(fill="x", side="left", expand=True)
        self.set_modem_state("rx")
        self.update_statusbar()

    def build_ui(self):
        self.build_menu()
        self.build_statusbar()
        root = ttk.Frame(self, padding=8)
        root.pack(side="top", fill="both", expand=True)

        header = ttk.Frame(root)
        header.grid(row=0, column=0, columnspan=3, sticky="ew")
        ttk.Label(header, text="HX – Hyper eXchange", style="Title.TLabel").pack(side="left")
        if APP_SUBTITLE:
            ttk.Label(header, text=APP_SUBTITLE, foreground=COLORS["muted"], background=COLORS["bg"]).pack(side="left", padx=14)
        ttk.Label(header, text=f"v{VERSION}", foreground=COLORS["accent"], background=COLORS["bg"], font=("Consolas", 11, "bold")).pack(side="right")

        left = ttk.Frame(root, style="Panel.TFrame", padding=8)
        left.grid(row=1, column=0, sticky="ns", pady=8, padx=(0, 8))
        left.configure(width=185)
        left.grid_propagate(False)
        right = ttk.Frame(root, padding=0)
        right.grid(row=1, column=1, sticky="nsew", pady=8)

        heard = ttk.Frame(root, style="Panel.TFrame", padding=8)
        heard.grid(row=1, column=2, sticky="ns", pady=8, padx=(8, 0))
        heard.configure(width=235)
        heard.grid_propagate(False)

        self.build_left(left)
        self.build_right(right)
        self.build_heard_panel(heard)

        root.columnconfigure(0, weight=0)
        root.columnconfigure(1, weight=1)
        root.columnconfigure(2, weight=0)
        root.rowconfigure(1, weight=1)

    def _prepare_dialog_parent(self):
        """Bring HX forward so native dialogs open centered over the main window."""
        try:
            self.update_idletasks()
            self.deiconify()
            self.lift()
            self.focus_force()
            self.attributes("-topmost", True)
            self.after(250, lambda: self.attributes("-topmost", False))
        except Exception:
            pass
        return self

    def show_info(self, title, message, **kwargs):
        kwargs.setdefault("parent", self._prepare_dialog_parent())
        return messagebox.showinfo(title, message, **kwargs)

    def show_error(self, title, message, **kwargs):
        kwargs.setdefault("parent", self._prepare_dialog_parent())
        return messagebox.showerror(title, message, **kwargs)

    def _themed_choice_dialog(self, title, message, choices, default=None, timeout_ms=None):
        """HX-themed modal choice dialog. Tk keeps processing RX/TX while open."""
        parent = self._prepare_dialog_parent()
        result = tk.StringVar(value="")
        dlg = tk.Toplevel(parent)
        dlg.title(title)
        dlg.configure(bg=COLORS["bg"])
        dlg.resizable(False, False)
        dlg.transient(parent)
        try:
            dlg.attributes("-topmost", True)
        except Exception:
            pass
        body = ttk.Frame(dlg, style="Panel.TFrame", padding=16)
        body.pack(fill="both", expand=True)
        ttk.Label(body, text=title, style="Section.TLabel").pack(anchor="w", pady=(0, 10))
        ttk.Label(body, text=message, style="Panel.TLabel", justify="left", wraplength=430).pack(anchor="w", fill="x")
        countdown_var = tk.StringVar(value="")
        countdown_label = ttk.Label(body, textvariable=countdown_var, style="Muted.TLabel")
        countdown_label.pack(anchor="w", pady=(8, 0))
        buttons = ttk.Frame(body, style="Panel.TFrame")
        buttons.pack(fill="x", pady=(14, 0))

        def choose(value):
            if not result.get():
                result.set(value)

        for label, value in choices:
            ttk.Button(buttons, text=label, command=lambda v=value: choose(v)).pack(side="right", padx=(8, 0))

        def on_close():
            choose(default if default is not None else choices[-1][1])
        dlg.protocol("WM_DELETE_WINDOW", on_close)

        deadline = None
        if timeout_ms:
            deadline = time.monotonic() + (float(timeout_ms) / 1000.0)
            def update_countdown():
                if result.get() or not dlg.winfo_exists():
                    return
                remain = max(0, int((deadline - time.monotonic()) + 0.999))
                countdown_var.set(f"Automatically rejecting in {remain} second{'s' if remain != 1 else ''}…")
                if remain <= 0:
                    choose(default)
                else:
                    dlg.after(200, update_countdown)
            dlg.after(0, update_countdown)
        else:
            countdown_label.pack_forget()

        dlg.update_idletasks()
        x = parent.winfo_rootx() + max(0, (parent.winfo_width() - dlg.winfo_reqwidth()) // 2)
        y = parent.winfo_rooty() + max(0, (parent.winfo_height() - dlg.winfo_reqheight()) // 2)
        dlg.geometry(f"+{x}+{y}")
        dlg.lift()
        dlg.focus_force()
        try:
            dlg.grab_set()
        except Exception:
            pass
        dlg.after(250, lambda: dlg.attributes("-topmost", False) if dlg.winfo_exists() else None)
        dlg.wait_variable(result)
        value = result.get()
        try:
            dlg.grab_release()
        except Exception:
            pass
        try:
            dlg.destroy()
        except Exception:
            pass
        return value

    def ask_yes_no(self, title, message, **kwargs):
        return self._themed_choice_dialog(title, message, (("No", "no"), ("Yes", "yes")), default="no") == "yes"

    def ask_yes_no_timeout(self, title, message, timeout_ms=5000):
        return self._themed_choice_dialog(
            title, message, (("Reject", "no"), ("Accept", "yes")), default="no", timeout_ms=timeout_ms
        ) == "yes"

    def ask_yes_no_cancel(self, title, message, **kwargs):
        value = self._themed_choice_dialog(
            title, message, (("Cancel", "cancel"), ("No", "no"), ("Yes", "yes")), default="cancel"
        )
        return True if value == "yes" else False if value == "no" else None

    def build_menu(self):
        m = tk.Menu(self)
        filem = tk.Menu(m, tearoff=0)
        filem.add_command(label="Save TX WAV", command=self.save_tx_wav)
        filem.add_command(label="Decode WAV", command=self.decode_wav)
        filem.add_separator()
        filem.add_command(label="Exit", command=self.destroy)
        m.add_cascade(label="File", menu=filem)

        setup = tk.Menu(m, tearoff=0)
        setup.add_command(label="Audio Devices", command=self.audio_setup)
        setup.add_command(label="CAT / PTT Manager", command=self.cat_setup)
        setup.add_command(label="Operator Profile", command=self.operator_profile_setup)
        setup.add_command(label="Sound Settings", command=self.sound_settings_setup)
        setup.add_command(label="Receive Files Folder", command=self.receive_folder_setup)
        setup.add_separator()
        setup.add_checkbutton(label="Respond to external SNR requests while connected", variable=self.respond_external_snr_connected_var, command=self.save_config)
        setup.add_checkbutton(label="Auto-load last chat history", variable=self.autoload_last_chat_var, command=self.save_config)
        setup.add_checkbutton(label="Share operator profile on connect", variable=self.share_profile_var, command=self.save_config)
        setup.add_separator()
        setup.add_command(label="Open Chat Transcript", command=self.open_active_chat_transcript)
        setup.add_command(label="Open Log File", command=self.open_log_file)
        setup.add_command(label="Open Traffic / File Debug Log", command=self.open_file_transfer_debug_log)
        setup.add_command(label="Delete Traffic / File Debug Log", command=self.delete_file_transfer_debug_log)
        setup.add_command(label="Advanced Dev Tools", command=self.advanced_dev_tools_setup)
        setup.add_separator()
        setup.add_command(label="Clear Recent Stations", command=self.clear_recent_stations)
        setup.add_command(label="Reset Audio Devices to Defaults", command=self.reset_devices)
        m.add_cascade(label="Operating", menu=setup)


        helpm = tk.Menu(m, tearoff=0)
        helpm.add_command(label="About", command=lambda: self.show_info(
            "About",
            f"HX – Hyper eXchange\n\nHX Protocol Draft 1.0\nHX LAB Reference Implementation v{VERSION}\n\nCreated by Eduardo de Carvalho\n\nDesigned for operators. Built for experimentation. Open by design.\n\nHX-F and HX-N active; experimental HX-R removed."
        ))
        m.add_cascade(label="Help", menu=helpm)
        self.config(menu=m)

    def build_left(self, parent):
        ttk.Label(parent, text="MODE", style="Section.TLabel").pack(anchor="w")
        for mode in ["AUTO", "HX-F", "HX-N"]:
            rb = tk.Radiobutton(parent, text=mode, variable=self.mode_var, value=mode,
                                bg=COLORS["panel"], fg=COLORS["text"], selectcolor=COLORS["panel2"],
                                activebackground=COLORS["panel"], activeforeground=COLORS["accent"],
                                command=self.on_mode_changed)
            rb.pack(anchor="w", pady=2)

        self.rule(parent)
        self.frequency_label = ttk.Label(parent, text="---.---.---", style="Frequency.TLabel")
        self.frequency_label.pack(anchor="w", pady=(2, 2))
        self.frequency_mode_label = ttk.Label(parent, text="RADIO --", style="Muted.TLabel")
        self.frequency_mode_label.pack(anchor="w", pady=(0, 8))

        self.rule(parent)
        ttk.Label(parent, text="STATUS", style="Section.TLabel").pack(anchor="w")
        self.status_canvas = tk.Canvas(parent, width=165, height=118, bg=COLORS["panel"], highlightthickness=0)
        self.status_canvas.pack(anchor="w", fill="x", pady=4)
        self.make_led("RX", 10, 16, "off")
        self.make_led("TX", 10, 38, "off")
        self.make_led("Pilot", 10, 60, "off")
        self.make_led("Timing", 10, 82, "off")
        self.make_led("CRC", 10, 104, "off")

        self.rule(parent)
        ttk.Label(parent, text="SNR", style="Muted.TLabel").pack(anchor="w")
        self.snr_label = ttk.Label(parent, text="--.- dB", style="Big.TLabel")
        self.snr_label.pack(anchor="w")

        self.rule(parent)
        ttk.Label(parent, text="AUDIO LEVEL", style="Section.TLabel").pack(anchor="w")
        self.rx_meter = tk.Canvas(parent, width=165, height=20, bg=COLORS["panel3"], highlightthickness=1, highlightbackground=COLORS["grid"])
        self.rx_meter.pack(fill="x", pady=(6, 2))
        ttk.Label(parent, text="RX", style="Muted.TLabel").pack(anchor="w")
        self.tx_meter = tk.Canvas(parent, width=165, height=20, bg=COLORS["panel3"], highlightthickness=1, highlightbackground=COLORS["grid"])
        self.tx_meter.pack(fill="x", pady=(6, 2))
        ttk.Label(parent, text="TX", style="Muted.TLabel").pack(anchor="w")

        self.rule(parent)
        self.stats_label = ttk.Label(parent, text="Frames OK: 0\nFrames Fail: 0", style="Panel.TLabel")
        self.stats_label.pack(anchor="w")

        ttk.Label(parent, text="DECODER OUTPUT", style="Muted.TLabel").pack(anchor="w", pady=(8, 2))
        self.decode_output = tk.Text(
            parent, height=5, width=24, wrap="word",
            bg="#020702", fg="#9aa0a6", insertbackground="#9aa0a6",
            relief="sunken", borderwidth=1, highlightthickness=1,
            highlightbackground=COLORS["grid"], font=("Consolas", 8),
            state="disabled", takefocus=0,
        )
        self.decode_output.pack(anchor="w", fill="x")
        self.append_decode_output("MONITORING")

        ttk.Label(parent, text="HX SPECTRUM", style="Muted.TLabel").pack(anchor="w", pady=(8, 2))
        self.spectrum_canvas = tk.Canvas(
            parent, height=78, width=165, bg="#020702",
            highlightthickness=1, highlightbackground=COLORS["grid"],
        )
        self.spectrum_canvas.pack(anchor="w", fill="x")

    def append_decode_output(self, text: str):
        """Append a compact decoder trace to the operator-facing RX panel."""
        if not hasattr(self, "decode_output"):
            return
        line = str(text).strip()
        if not line:
            return
        if getattr(self, "_last_decode_output_line", None) == line:
            return
        self._last_decode_output_line = line
        self.decode_output.configure(state="normal")
        self.decode_output.insert("end", line + "\n")
        # Keep the panel bounded so long monitoring sessions cannot grow memory.
        try:
            line_count = int(self.decode_output.index("end-1c").split(".")[0])
            if line_count > 40:
                self.decode_output.delete("1.0", f"{line_count - 40}.0")
        except Exception:
            pass
        self.decode_output.see("end")
        self.decode_output.configure(state="disabled")

    def build_right(self, parent):
        parent.columnconfigure(0, weight=1)
        # Operator messages are now the main station panel. Debug remains available but compact.
        parent.rowconfigure(0, weight=0, minsize=72)
        parent.rowconfigure(1, weight=7)
        parent.rowconfigure(2, weight=0, minsize=120)
        parent.rowconfigure(3, weight=0, minsize=42)

        qsop = ttk.Frame(parent, style="Panel.TFrame", padding=(12, 8))
        qsop.grid(row=0, column=0, sticky="ew", pady=(0, 10))
        self.build_qso_panel(qsop)

        msgp = ttk.Frame(parent, style="Panel.TFrame", padding=12)
        msgp.grid(row=1, column=0, sticky="nsew", pady=(0, 10))
        self.build_message_panel(msgp)

        txp = ttk.Frame(parent, style="Panel.TFrame", padding=12)
        txp.grid(row=2, column=0, sticky="ew", pady=(0, 10))
        self.build_tx_panel(txp)

        logp = ttk.Frame(parent, style="Panel.TFrame", padding=12)
        logp.grid(row=3, column=0, sticky="nsew")
        self.build_log_panel(logp)


    def build_qso_panel(self, parent):
        top = ttk.Frame(parent, style="Panel.TFrame")
        top.pack(fill="x")
        ttk.Label(top, text="Station / QSO Information", style="Section.TLabel").pack(side="left")
        self.qso_clear_button = ttk.Button(top, text="Clear", command=self.reset_qso_panel)
        self.qso_clear_button.pack(side="right")

        grid = ttk.Frame(parent, style="Panel.TFrame")
        grid.pack(fill="x", pady=(5, 0))
        self.qso_value_labels = {}
        fields = [
            ("Call", "call", 0, 0),
            ("Name", "name", 0, 2),
            ("Grid", "grid", 0, 4),
            ("RX", "rx_snr", 0, 6),
            ("TX", "tx_snr", 0, 8),
            ("Status", "status", 0, 10),
            ("Start", "start", 1, 0),
            ("End", "end", 1, 2),
            ("Dur", "duration", 1, 4),
        ]
        for label, key, row, col in fields:
            ttk.Label(grid, text=f"{label}:", style="QSO.Muted.TLabel").grid(row=row, column=col, sticky="w", padx=(0 if col == 0 else 10, 3), pady=(0, 1))
            val = ttk.Label(grid, text="--", style="QSO.TLabel")
            val.grid(row=row, column=col + 1, sticky="w", pady=(0, 1))
            self.qso_value_labels[key] = val
        grid.columnconfigure(11, weight=1)
        self.update_qso_panel()

    def build_heard_panel(self, parent):
        ttk.Label(parent, text="LAST HEARD", style="Section.TLabel").pack(anchor="w")
        ttk.Label(parent, text="Select station to address", style="Muted.TLabel").pack(anchor="w", pady=(2, 8))

        self.heard_tree = ttk.Treeview(parent, columns=("call", "time", "snr"), show="headings", height=16, selectmode="browse", style="Heard.Treeview")
        self.heard_tree.heading("call", text="Call")
        self.heard_tree.heading("time", text="Last")
        self.heard_tree.heading("snr", text="SNR")
        self.heard_tree.column("call", width=96, anchor="w", stretch=False)
        self.heard_tree.column("time", width=62, anchor="center", stretch=False)
        self.heard_tree.column("snr", width=62, anchor="e", stretch=False)
        self.heard_tree.pack(fill="both", expand=True)
        self.heard_tree.bind("<<TreeviewSelect>>", self.on_heard_select)
        self.heard_tree.bind("<Button-3>", self.on_heard_context_menu)

        session_row = ttk.Frame(parent, style="Panel.TFrame")
        session_row.pack(fill="x", pady=(8, 0))
        self.session_button = ttk.Button(session_row, text="CONNECT", command=self.session_button_action)
        self.session_button.pack(side="left", fill="x", expand=True)
        # Compatibility aliases used by older update paths.
        self.connect_button = self.session_button
        self.disconnect_button = self.session_button

        ttk.Button(parent, text="CLEAR LIST", command=self.clear_heard_stations).pack(fill="x", pady=(8, 0))

    def build_rx_panel(self, parent):
        ttk.Label(parent, text="RECEIVE / STATION MONITOR", style="Section.TLabel").grid(row=0, column=0, sticky="w", columnspan=4)
        self.rx_btn = ttk.Button(parent, text="RX MONITOR OFF", command=self.toggle_rx_monitor)
        self.rx_btn.grid(row=1, column=0, sticky="w", pady=10)
        ttk.Checkbutton(parent, text="Debug RX acquisition", variable=self.debug_rx_var).grid(row=1, column=1, sticky="w", padx=12)
        self.rx_debug_label = ttk.Label(parent, text="RX debug WAV capture is controlled in Setup > Advanced Dev Tools", style="Muted.TLabel")
        self.rx_debug_label.grid(row=2, column=0, sticky="w", columnspan=4)
        self.rx_state_label = ttk.Label(parent, text="RX state: idle", style="Panel.TLabel")
        self.rx_state_label.grid(row=3, column=0, sticky="w", columnspan=4, pady=(4, 0))
        parent.columnconfigure(3, weight=1)

    def build_tx_panel(self, parent):
        ttk.Label(parent, text="TRANSMIT", style="Section.TLabel").grid(row=0, column=0, sticky="w")
        self.tx_queue_status_label = tk.Label(
            parent,
            textvariable=self.tx_queue_status_var,
            bg=COLORS["panel"],
            fg=COLORS["amber"],
            font=("Segoe UI", 8, "bold"),
            anchor="w",
            padx=8,
        )
        self.tx_queue_status_label.grid(row=0, column=1, sticky="ew", padx=8, columnspan=4)

        # Compact options row above the message box. Moving destination, tag, and
        # beacon controls here prevents the action row from forcing the entire
        # transmit panel to become unnecessarily wide.
        options_row = ttk.Frame(parent, style="Panel.TFrame")
        options_row.grid(row=1, column=1, sticky="ew", padx=8, pady=(3, 2))

        ttk.Label(options_row, text="Tag", style="Panel.TLabel").pack(side="left", padx=(0, 4))
        self.template_combo = ttk.Combobox(
            options_row,
            textvariable=self.template_var,
            values=["N/A", "CQ", "SNR?", "SEND PROFILE", "REQUEST PROFILE"],
            width=9,
            state="readonly",
        )
        self.template_combo.pack(side="left", padx=(0, 12))
        self.template_combo.bind("<<ComboboxSelected>>", self.apply_message_template)

        self.beacon_check = tk.Checkbutton(
            options_row,
            text="Beacon",
            variable=self.beacon_enabled_var,
            command=self.on_beacon_changed,
            bg=COLORS["panel"],
            fg=COLORS["text"],
            activebackground="#30363d",
            activeforeground=COLORS["text"],
            selectcolor=COLORS["panel3"],
            highlightthickness=0,
            relief="flat",
        )
        self.beacon_check.pack(side="left", padx=(0, 4))
        ttk.Label(options_row, text="every", style="Panel.TLabel").pack(side="left")
        self.beacon_interval_combo = ttk.Combobox(
            options_row,
            textvariable=self.beacon_interval_var,
            values=["5", "10", "15", "30", "45", "60"],
            width=5,
            state="readonly",
        )
        self.beacon_interval_combo.pack(side="left", padx=(4, 2))
        self.beacon_interval_combo.bind("<<ComboboxSelected>>", lambda _e=None: self.on_beacon_changed())
        ttk.Label(options_row, text="min", style="Panel.TLabel").pack(side="left", padx=(0, 8))
        self.beacon_now_button = ttk.Button(options_row, text="BEACON NOW", command=self.send_beacon_now)
        self.beacon_now_button.pack(side="left", padx=(0, 16))

        ttk.Label(options_row, text="To", style="Panel.TLabel").pack(side="left", padx=(0, 4))
        # Combined editable destination field and station picker.  The drop-down
        # contains ALL, CQ, and recently heard stations, while operators may
        # still type a callsign directly into the same field.
        self.to_entry = ttk.Combobox(
            options_row,
            textvariable=self.to_var,
            values=self.destination_values(),
            width=13,
            state="normal",
        )
        self.to_entry.pack(side="left")
        self.to_entry.bind("<<ComboboxSelected>>", self.on_destination_selected)
        self.to_entry.bind("<FocusOut>", self.on_destination_commit)
        self.to_entry.bind("<Return>", self.on_destination_commit)

        ttk.Label(parent, text="Message", style="Panel.TLabel").grid(row=2, column=0, sticky="nw", pady=6)

        # Text widget is used instead of Entry so HX LAB can color characters red
        # progressively while they are being transmitted. This is an operator UI
        # feature only; it does not change the modem payload/framing/FEC.
        self.tx_text = tk.Text(
            parent,
            height=4,
            wrap="word",
            bg=COLORS["panel3"],
            fg=COLORS["text"],
            insertbackground=COLORS["text"],
            relief="flat",
        )
        self.tx_text.grid(row=2, column=1, sticky="nsew", padx=8, pady=(2, 2), rowspan=2)
        self.tx_text.insert("1.0", self.message_var.get())
        self.tx_text.tag_configure("sent", foreground=COLORS["red"])
        self.tx_text.bind("<Return>", self.on_tx_enter)

        # TX Gain is vertical like a radio/software audio gain control.
        gain_frame = ttk.Frame(parent, style="Panel.TFrame")
        gain_frame.grid(row=1, column=2, rowspan=6, sticky="ns", padx=(8, 2), pady=(2, 2))
        ttk.Label(gain_frame, text="TX GAIN", style="Panel.TLabel").pack(anchor="center")
        self.output_volume_scale = tk.Scale(
            gain_frame, from_=100, to=5, orient="vertical", showvalue=False,
            variable=self.output_volume_var, command=self.on_output_volume_change,
            bg=COLORS["panel"], fg=COLORS["text"], troughcolor=COLORS["panel3"],
            highlightthickness=0, length=120, resolution=1
        )
        self.output_volume_scale.pack(anchor="center", pady=(2, 0))
        self.output_volume_label = ttk.Label(gain_frame, text=f"{self.output_volume_var.get()}%", style="Panel.TLabel")
        self.output_volume_label.pack(anchor="center")

        # Keep only the primary actions below the message box.
        control_row = ttk.Frame(parent, style="Panel.TFrame")
        control_row.grid(row=4, column=1, sticky="w", padx=8, pady=(4, 0))

        self.send_button = ttk.Button(control_row, text="SEND", command=self.start_tx)
        self.send_button.pack(side="left", padx=(0, 8))
        self.send_file_button = ttk.Button(control_row, text="SEND FILE", command=self.start_file_send)
        self.send_file_button.pack(side="left", padx=(0, 8))
        self.cancel_file_button = ttk.Button(control_row, text="CANCEL FILE", command=self.cancel_file_transfer)
        self.cancel_file_button.pack(side="left", padx=(0, 8))
        self.tune_button = ttk.Button(control_row, text="1KHz", command=self.toggle_1khz_tune)
        self.tune_button.pack(side="left")

        self.tx_progress = tk.Canvas(parent, height=24, bg=COLORS["panel3"], highlightthickness=1, highlightbackground=COLORS["grid"])
        self.tx_progress.grid(row=5, column=1, sticky="ew", pady=(6, 0), padx=8)
        self.tx_progress_pct = 0.0
        self.tx_progress_text = "Idle"
        # Redraw whenever Tk assigns the final width. Without this, the initial
        # fallback width can leave the Idle label centered in only part of the bar.
        self.tx_progress.bind(
            "<Configure>",
            lambda _event: self.draw_tx_progress(self.tx_progress_pct, self.tx_progress_text),
            add="+",
        )
        self.draw_tx_progress(0.0, "Idle")

        parent.columnconfigure(1, weight=1)

    def build_message_panel(self, parent):
        top = ttk.Frame(parent, style="Panel.TFrame")
        top.pack(fill="x")
        ttk.Label(top, text="RX / TX MESSAGES", style="Section.TLabel").pack(side="left")
        ttk.Label(top, text="Operator-facing message history", style="Muted.TLabel").pack(side="left", padx=12)
        ttk.Button(top, text="CLEAR MESSAGES", command=self.clear_message_history).pack(side="right")
        self.msgbox = tk.Text(parent, height=16, bg=COLORS["panel3"], fg=COLORS["text"], insertbackground=COLORS["text"], relief="flat")
        # Message history color tags.  These are presentation-only and do not
        # change the modem payload, framing, FEC, or RX detection.
        # User-authored traffic is visually distinct from HX-generated service
        # traffic: operator TX is cyan, operator RX is light green, and system
        # frames/events (CQ, SNR?, beacons, profiles, keep-alives, session
        # events, etc.) are purple.
        self.msgbox.tag_configure("tx_user", foreground="#67e8f9")
        self.msgbox.tag_configure("rx_user", foreground="#86efac")
        self.msgbox.tag_configure("system", foreground="#c084fc")
        # Backward-compatible aliases used by older helper paths.
        self.msgbox.tag_configure("rx", foreground="#86efac")
        self.msgbox.tag_configure("tx", foreground="#67e8f9")
        self.msgbox.tag_configure("direct", foreground="#c084fc")
        self.msgbox.tag_configure("cq", foreground="#c084fc")
        self.msgbox.tag_configure("beacon", foreground="#c084fc")
        self.msgbox.tag_configure("snr", foreground="#c084fc")
        self.msgbox.tag_configure("profile", foreground="#c084fc")
        self.msgbox.tag_configure("rx_partial", foreground="#86efac")
        self.msgbox.tag_configure("rx_unverified", foreground="#86efac")
        self.msgbox.pack(fill="both", expand=True, pady=(8, 0))
        self.msgbox.configure(state="disabled")

    def message_history_insert(self, text: str, tag: str | None = None):
        """Append to the RX/TX history while keeping the panel read-only to operators."""
        if not hasattr(self, "msgbox"):
            return
        try:
            self.msgbox.configure(state="normal")
            if tag:
                self.msgbox.insert("end", text, tag)
            else:
                self.msgbox.insert("end", text)
            self.msgbox.see("end")
        finally:
            try:
                self.msgbox.configure(state="disabled")
            except Exception:
                pass

    def update_partial_rx_text(self, preview: str, final_failed: bool = False):
        """Show or update a provisional human-readable RX line in place."""
        if not hasattr(self, "msgbox"):
            return
        preview = (preview or "").strip()
        if not preview:
            return
        try:
            self.msgbox.configure(state="normal")
            if self._partial_rx_mark is None:
                self._partial_rx_mark = "rx_partial_live"
                self.msgbox.mark_set(self._partial_rx_mark, "end-1c")
                self.msgbox.mark_gravity(self._partial_rx_mark, "left")
            start = self.msgbox.index(self._partial_rx_mark)
            self.msgbox.delete(start, "end-1c")
            prefix = "RX (unverified): " if final_failed else "RX decoding: "
            tag = "rx_unverified" if final_failed else "rx_partial"
            self.msgbox.insert("end", prefix + preview + "\n", tag)
            self.msgbox.see("end")
            if final_failed:
                self._partial_rx_mark = None
        finally:
            self.msgbox.configure(state="disabled")

    def clear_partial_rx_text(self):
        if not hasattr(self, "msgbox") or self._partial_rx_mark is None:
            return
        try:
            self.msgbox.configure(state="normal")
            start = self.msgbox.index(self._partial_rx_mark)
            self.msgbox.delete(start, "end-1c")
            self.msgbox.mark_unset(self._partial_rx_mark)
        except Exception:
            pass
        finally:
            self._partial_rx_mark = None
            try:
                self.msgbox.configure(state="disabled")
            except Exception:
                pass

    def is_duplicate_rx_frame(self, callsign: str, to_call: str, text: str, mode: str) -> bool:
        """Suppress accidental duplicate delivery while retaining protocol integrity."""
        import hashlib
        now = time.time()
        key = hashlib.sha256(f"{callsign}|{to_call}|{mode}|{text}".encode("utf-8", errors="replace")).hexdigest()
        self._recent_rx_frames = {k: ts for k, ts in self._recent_rx_frames.items() if now - ts < 15.0}
        if key in self._recent_rx_frames:
            return True
        self._recent_rx_frames[key] = now
        return False

    def clear_message_history(self):
        """Clear RX/TX history without making it editable to operators."""
        if not hasattr(self, "msgbox"):
            return
        try:
            self.msgbox.configure(state="normal")
            self.msgbox.delete("1.0", "end")
        finally:
            try:
                self.msgbox.configure(state="disabled")
            except Exception:
                pass

    def build_log_panel(self, parent):
        top = ttk.Frame(parent, style="Panel.TFrame")
        top.pack(fill="x")
        ttk.Label(top, text="DEBUG / EVENT LOG", style="Section.TLabel").pack(side="left")

        level_row = ttk.Frame(top, style="Panel.TFrame")
        level_row.pack(side="left", padx=(18, 0))
        for text, value in (("Normal", "NORMAL"), ("Verbose", "VERBOSE"), ("Developer", "DEVELOPER")):
            ttk.Radiobutton(
                level_row,
                text=text,
                value=value,
                variable=self.debug_level_var,
                command=self.on_debug_level_changed,
                style="Debug.TRadiobutton",
            ).pack(side="left", padx=(0, 8))

        ttk.Button(top, text="CLEAR LOG", command=lambda: self.logbox.delete("1.0", "end")).pack(side="right")
        self.logbox = tk.Text(parent, height=3, bg=COLORS["panel3"], fg=COLORS["text"], insertbackground=COLORS["text"], relief="flat")
        self.logbox.tag_configure("info", foreground=COLORS["text"])
        self.logbox.tag_configure("ok", foreground=COLORS["green"])
        self.logbox.tag_configure("warn", foreground=COLORS["amber"])
        self.logbox.tag_configure("err", foreground=COLORS["red"])
        self.logbox.tag_configure("debug", foreground=COLORS["accent"])
        self.logbox.pack(fill="both", expand=True, pady=(8, 0))

    def on_debug_level_changed(self):
        self.save_config()
        selected = self.debug_level_var.get().strip().title()
        self.log(f"Debug level changed to {selected}", "info", force=True)

    @staticmethod
    def is_developer_log_message(msg: str) -> bool:
        low = str(msg or "").lower()
        markers = (
            "rx_diag", "rx_state cycle=", "pilot score=", "captured_samples=",
            "idle level peak=", "timing_recovery", "payload_soft_",
            "header_wait error=", "candidate_start=", "probe_samples=",
            "exact_decode", "stream_open mode=", "energy_start peak=",
            "cat transport", "cat polling stopped", "ptt release skipped",
        )
        return any(marker in low for marker in markers)

    def should_show_log(self, msg: str, level: str) -> bool:
        selected = self.debug_level_var.get().strip().upper() if hasattr(self, "debug_level_var") else "NORMAL"
        if selected == "DEVELOPER":
            return True
        if str(level).lower() != "debug":
            return True
        if selected == "NORMAL":
            return False
        return not self.is_developer_log_message(msg)

    def rule(self, parent):
        ttk.Separator(parent).pack(fill="x", pady=8)

    def make_led(self, name: str, x: int, y: int, state: str):
        color = self.led_color(state)
        oval = self.status_canvas.create_oval(x, y - 7, x + 14, y + 7, fill=color, outline="#000000")
        text = self.status_canvas.create_text(x + 24, y, anchor="w", fill=COLORS["text"], font=("Segoe UI", 8), text=f"{name}: {state.upper() if state != 'off' else '--'}")
        self.led_items[name] = (oval, text)

    def led_color(self, state: str):
        return {"ok": COLORS["green"], "warn": COLORS["amber"], "bad": COLORS["red"], "active": COLORS["blue"], "off": "#4a5562"}.get(state, "#4a5562")

    def set_led(self, name: str, state: str, label: str | None = None):
        if name not in self.led_items:
            return
        oval, text = self.led_items[name]
        self.status_canvas.itemconfigure(oval, fill=self.led_color(state))
        self.status_canvas.itemconfigure(text, text=f"{name}: {label if label is not None else (state.upper() if state != 'off' else '--')}")

    def draw_meter(self, canvas: tk.Canvas, level: float, label: str):
        canvas.delete("all")
        w = max(100, canvas.winfo_width() or 165)
        h = max(16, canvas.winfo_height() or 20)
        canvas.create_rectangle(0, 0, w, h, fill=COLORS["panel3"], outline=COLORS["grid"])
        level = max(0.0, min(1.2, float(level)))
        fill_w = int(min(1.0, level) * (w - 4))
        if str(label).upper() == "TX":
            color = COLORS["red"]
        else:
            color = COLORS["green"] if level < 0.85 else COLORS["amber"] if level < 1.0 else COLORS["red"]
        canvas.create_rectangle(2, 2, 2 + fill_w, h - 2, fill=color, outline="")
        canvas.create_text(8, h // 2, anchor="w", fill="#000000" if fill_w > 60 else COLORS["text"], text=f"{label} {level:.3f}", font=("Consolas", 8, "bold"))

    def update_spectrum_rx_samples(self, samples):
        try:
            arr = np.asarray(samples, dtype=np.float32).reshape(-1)
            if arr.size == 0:
                return
            with self.spectrum_lock:
                if arr.size >= 4096:
                    self.spectrum_rx_samples = arr[-4096:].copy()
                else:
                    keep = max(0, 4096 - arr.size)
                    self.spectrum_rx_samples = np.concatenate((self.spectrum_rx_samples[-keep:], arr)).astype(np.float32, copy=False)
        except Exception:
            pass

    def set_spectrum_tx_audio(self, audio):
        try:
            arr = np.asarray(audio, dtype=np.float32).reshape(-1).copy()
        except Exception:
            arr = np.zeros(0, dtype=np.float32)
        with self.spectrum_lock:
            self.spectrum_tx_audio = arr
            self.spectrum_tx_started = time.monotonic()
            self.spectrum_tx_active = bool(arr.size)

    def clear_spectrum_tx(self):
        with self.spectrum_lock:
            self.spectrum_tx_active = False
            self.spectrum_tx_audio = np.zeros(0, dtype=np.float32)

    def draw_spectrum(self):
        if not hasattr(self, "spectrum_canvas"):
            return
        c = self.spectrum_canvas
        c.delete("all")
        w = max(120, c.winfo_width() or 165)
        h = max(60, c.winfo_height() or 78)
        c.create_rectangle(0, 0, w, h, fill="#020702", outline=COLORS["grid"])
        left, right, top, bottom = 5, w - 5, 5, h - 15
        for frac in (0.25, 0.5, 0.75):
            x = left + int((right-left)*frac)
            c.create_line(x, top, x, bottom, fill="#172119")
        c.create_line(left, bottom, right, bottom, fill="#39434d")

        with self.spectrum_lock:
            tx_active = self.spectrum_tx_active and self.spectrum_tx_audio.size > 0
            if tx_active:
                audio = self.spectrum_tx_audio
                pos = int((time.monotonic() - self.spectrum_tx_started) * SAMPLE_RATE)
                if audio.size:
                    pos %= audio.size
                start = max(0, min(pos, max(0, audio.size - 4096)))
                samples = audio[start:start+4096]
                if samples.size < 4096 and audio.size:
                    samples = np.concatenate((samples, audio[:4096-samples.size]))
                trace_color = COLORS["red"]
                label = "TX"
            else:
                samples = self.spectrum_rx_samples.copy()
                trace_color = COLORS["green"]
                label = "RX"
        if samples.size < 128:
            samples = np.zeros(4096, dtype=np.float32)
        nfft = 4096
        if samples.size < nfft:
            samples = np.pad(samples, (0, nfft-samples.size))
        else:
            samples = samples[-nfft:]
        window = np.hanning(nfft).astype(np.float32)
        mag = np.abs(np.fft.rfft(samples * window))
        freqs = np.fft.rfftfreq(nfft, 1.0 / SAMPLE_RATE)
        mask = (freqs >= 300.0) & (freqs <= 3000.0)
        vals = 20.0 * np.log10(mag[mask] + 1e-8)
        if vals.size:
            floor = max(-100.0, float(np.percentile(vals, 10)))
            ceiling = max(floor + 25.0, float(np.max(vals)))
            norm = np.clip((vals - floor) / (ceiling - floor), 0.0, 1.0)
            max_points = max(40, right-left)
            idx = np.linspace(0, len(norm)-1, max_points).astype(int)
            points=[]
            for i, v in enumerate(norm[idx]):
                x = left + (right-left) * i / max(1, len(idx)-1)
                y = bottom - float(v) * (bottom-top)
                points.extend((x,y))
            if len(points) >= 4:
                c.create_line(*points, fill=trace_color, width=1.2, smooth=False)
        c.create_text(left+2, top+2, anchor="nw", text=label, fill=trace_color, font=("Consolas", 7, "bold"))
        c.create_text(left, h-3, anchor="sw", text="300", fill=COLORS["muted"], font=("Consolas", 6))
        c.create_text((left+right)//2, h-3, anchor="s", text="1650", fill=COLORS["muted"], font=("Consolas", 6))
        c.create_text(right, h-3, anchor="se", text="3000 Hz", fill=COLORS["muted"], font=("Consolas", 6))

    def draw_tx_progress(self, pct: float, text: str):
        if not hasattr(self, "tx_progress"):
            return
        self.tx_progress_pct = max(0.0, min(100.0, float(pct)))
        self.tx_progress_text = str(text)
        c = self.tx_progress
        c.delete("all")
        w = max(180, c.winfo_width() or 360)
        h = max(20, c.winfo_height() or 24)
        pct = self.tx_progress_pct
        c.create_rectangle(0, 0, w, h, fill=COLORS["panel3"], outline=COLORS["grid"])
        fill_w = int((pct / 100.0) * (w - 2))
        if fill_w > 0:
            c.create_rectangle(1, 1, 1 + fill_w, h - 1, fill="#8b5cf6", outline="")
        label = self.tx_progress_text
        if pct > 0 and "%" not in label:
            label = f"{label} {pct:.0f}%"
        c.create_text(w // 2, h // 2, text=label, fill="#ffffff", font=("Segoe UI", 9, "bold"))

    def refresh_meters(self):
        self.draw_meter(self.rx_meter, self.rx_meter_level, "RX")
        self.draw_meter(self.tx_meter, self.tx_meter_level, "TX")
        self.draw_spectrum()
        self.tx_meter_level *= 0.92
        self.rx_meter_level *= 0.96
        self.update_statusbar()
        now = time.monotonic()
        if now - getattr(self, "_last_heard_age_refresh", 0.0) >= 1.0:
            self._last_heard_age_refresh = now
            self.refresh_heard_list()
        self.after(100, self.refresh_meters)

    def update_statusbar(self):
        mode = self.mode_display_text()
        beacon_state = "ON" if (hasattr(self, "beacon_enabled_var") and self.beacon_enabled_var.get()) else "OFF"
        if beacon_state == "ON" and self.next_beacon_time:
            remain = max(0, int(self.next_beacon_time - time.time()))
            beacon = f"Beacon: ON    Next beacon: {remain//60:02d}:{remain%60:02d}"
        else:
            beacon = "Beacon: OFF    Next beacon: --"
        if self.session_active:
            elapsed = 0
            if self.session_started:
                elapsed = max(0, int(time.time() - self.session_started))
            if self.session_disconnect_deadline:
                remain = max(0, int(self.session_disconnect_deadline - time.time()))
                session_text = f"Session: IDLE {self.session_peer} disconnect {remain:02d}s"
            else:
                session_text = f"Session: CONNECTED {self.session_peer} {elapsed//60:02d}:{elapsed%60:02d}"
        else:
            session_text = "Session: Open"
        busy_text = "  |  HX Busy" if getattr(self, "hx_channel_busy", False) else ""
        q_text = f"  |  TX Hold {len(self.tx_hold_queue)}" if getattr(self, "tx_hold_queue", []) else ""
        self.statusbar.configure(text=f"Audio {int(SAMPLE_RATE)} Hz  |  Tone {int(TONE_FREQ)} Hz  |  TX Mode {mode}  |  RX Mode {getattr(self, 'last_rx_mode', '--')}  |  TX {self.tx_device}  |  RX {self.rx_device}  |  OK {self.frames_ok}  FAIL {self.frames_fail}  |  {session_text}  |  {beacon}{busy_text}{q_text}")
        if hasattr(self, "mycall_label"):
            self.mycall_label.configure(text=f"{self.clean_callsign()}")

    def on_output_volume_change(self, value=None):
        try:
            pct = int(float(value if value is not None else self.output_volume_var.get()))
        except Exception:
            pct = 80
        pct = max(5, min(100, pct))
        self.tx_level_var.set(pct / 100.0)
        self.tune_gain_live = pct / 100.0
        if hasattr(self, "output_volume_label"):
            self.output_volume_label.configure(text=f"{pct}%")
        self.save_config()


    def append_text_log(self, line: str):
        try:
            os.makedirs(DOC_DIR, exist_ok=True)
            new_file = not os.path.exists(LOG_PATH)
            with open(LOG_PATH, "a", encoding="utf-8") as f:
                if new_file:
                    f.write("HX – Hyper eXchange\n")
                    f.write("Adaptive Digital Communications for Amateur Radio\n")
                    f.write(f"HX Protocol {HX_PROTOCOL_VERSION}; HX LAB Reference Implementation v{VERSION}\n")
                    f.write("-" * 72 + "\n")
                f.write(line + "\n")
        except Exception:
            pass

    def open_log_file(self):
        os.makedirs(DOC_DIR, exist_ok=True)
        if not os.path.exists(LOG_PATH):
            with open(LOG_PATH, "w", encoding="utf-8") as f:
                f.write("HX – Hyper eXchange session log created.\n")
        try:
            os.startfile(LOG_PATH)  # type: ignore[attr-defined]
        except Exception:
            try:
                subprocess.Popen(["notepad.exe", LOG_PATH])
            except Exception as e:
                self.show_error("Open Log File", f"Unable to open log file:\n{LOG_PATH}\n\n{e}")

    def chat_safe_name(self, name: str) -> str:
        name = (name or "UNKNOWN").strip().upper()
        return re.sub(r"[^A-Z0-9_\-/]", "_", name).replace("/", "_") or "UNKNOWN"

    def chat_station_dir(self, callsign: str) -> str:
        path = os.path.join(CHAT_DIR, self.chat_safe_name(callsign))
        os.makedirs(path, exist_ok=True)
        return path

    def qso_time_text(self, ts: float | None = None) -> str:
        if ts is None:
            ts = time.time()
        return time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime(ts))

    def update_qso_panel(self):
        if not hasattr(self, "qso_value_labels"):
            return
        for key, label in self.qso_value_labels.items():
            try:
                label.configure(text=str(self.qso_current.get(key, "--") or "--"))
            except Exception:
                pass
        try:
            if hasattr(self, "qso_clear_button"):
                self.qso_clear_button.configure(state=("disabled" if self.session_active else "normal"))
        except Exception:
            pass

    def reset_qso_panel(self):
        if getattr(self, "session_active", False):
            try:
                self.show_tx_queue_notice("QSO panel locked during active session")
            except Exception:
                self.qlog("QSO panel locked during active session", "warn")
            return
        self.qso_current = {
            "call": "--",
            "name": "--",
            "grid": "--",
            "rx_snr": "--",
            "tx_snr": "--",
            "status": "--",
            "start": "--",
            "end": "--",
            "duration": "--",
        }
        self.update_qso_panel()

    def update_qso_from_profile(self, callsign: str, profile: dict):
        """Refresh Station / QSO Information from a received HXPROFILE.

        Profiles are useful even outside an active session.  If a station
        responds to a manual profile request before CONNECT, show that station
        immediately as Heard.  If the same station later connects, the existing
        information becomes the QSO record and session fields are added.
        """
        call = (callsign or "UNKNOWN").strip().upper()
        if not call:
            return
        if self.session_active and call != self.session_peer:
            # Do not let an outside profile overwrite the active QSO card.
            return

        current_call = (self.qso_current.get("call") or "--").strip().upper()
        if current_call not in ("--", "", call) and not (self.session_active and call == self.session_peer):
            # A different station profile was received while no session is
            # protecting the panel; replace the card with the latest station.
            self.reset_qso_panel()

        self.qso_current["call"] = call
        name = (profile.get("name") or "").strip()
        grid = (profile.get("grid") or "").strip().upper()
        if name:
            self.qso_current["name"] = name
        if grid:
            self.qso_current["grid"] = grid

        try:
            heard = self.heard_stations.get(call, {}) if hasattr(self, "heard_stations") else {}
            snr = heard.get("snr")
            if snr not in (None, ""):
                try:
                    self.qso_current["rx_snr"] = f"{float(snr):+.1f} dB"
                except Exception:
                    self.qso_current["rx_snr"] = str(snr)
        except Exception:
            pass

        if self.session_active and call == self.session_peer:
            self.qso_current["status"] = "Connected"
        else:
            self.qso_current["status"] = "Heard"
        self.update_qso_panel()

    def start_chat_session(self, peer: str):
        """Create a per-QSO chat transcript and optionally load last history."""
        try:
            peer = self.chat_safe_name(peer)
            folder = self.chat_station_dir(peer)
            now = time.time()
            stamp = time.strftime("%Y-%m-%d_%H%M%S", time.gmtime(now))
            self.active_chat_peer = peer
            self.active_chat_started_ts = now
            self.active_chat_file = os.path.join(folder, f"{stamp}_{peer}.log")
            if self.autoload_last_chat_var.get() and hasattr(self, "msgbox"):
                last_path = os.path.join(folder, "last.json")
                try:
                    with open(last_path, "r", encoding="utf-8") as f:
                        info = json.load(f)
                    prev = os.path.join(folder, info.get("last_chat_file", ""))
                    if os.path.exists(prev):
                        self.message_history_insert(f"--- Previous chat with {peer} from {info.get('started', 'unknown')} ---\n", "profile")
                        with open(prev, "r", encoding="utf-8", errors="replace") as pf:
                            lines = pf.readlines()[-120:]
                        for line in lines:
                            self.message_history_insert(line)
                        self.message_history_insert(f"--- New session started {time.strftime('%Y-%m-%d %H:%M:%S', time.gmtime())} ---\n", "profile")
                        self.msgbox.see("end")
                except Exception:
                    pass
            with open(self.active_chat_file, "a", encoding="utf-8") as f:
                f.write("HX – Hyper eXchange Chat Transcript\n")
                f.write(f"Local Station: {self.clean_callsign()}\n")
                f.write(f"Remote Station: {peer}\n")
                f.write(f"Session UUID: {self.session_uuid}\n")
                f.write("-" * 72 + "\n")
        except Exception as e:
            self.qlog(f"Chat transcript setup failed: {e}", "warn")

    def append_chat_transcript(self, line: str):
        try:
            if self.active_chat_file:
                with open(self.active_chat_file, "a", encoding="utf-8") as f:
                    f.write(line.rstrip("\n") + "\n")
        except Exception:
            pass

    def finish_chat_session(self, peer: str, start_ts: float | None):
        try:
            if not self.active_chat_file or not peer:
                return
            end_ts = time.time()
            start_ts = start_ts or end_ts
            duration = max(0, int(end_ts - start_ts))
            duration_txt = f"{duration//3600:02d}:{(duration%3600)//60:02d}:{duration%60:02d}"
            folder = self.chat_station_dir(peer)
            info = {
                "callsign": peer,
                "last_chat_file": os.path.basename(self.active_chat_file),
                "started": time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime(start_ts)),
                "ended": time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime(end_ts)),
                "duration": duration_txt,
                "session_uuid": self.session_uuid,
            }
            with open(os.path.join(folder, "last.json"), "w", encoding="utf-8") as f:
                json.dump(info, f, indent=2)
        except Exception as e:
            self.qlog(f"Chat transcript close failed: {e}", "warn")

    def open_active_chat_transcript(self):
        path = self.active_chat_file
        if not path:
            # Fall back to the Chats folder if there is no active transcript.
            os.makedirs(CHAT_DIR, exist_ok=True)
            path = CHAT_DIR
        try:
            os.startfile(path)  # type: ignore[attr-defined]
        except Exception:
            try:
                subprocess.Popen(["explorer.exe", path])
            except Exception as e:
                self.show_error("Open Chat Transcript", f"Unable to open:\n{path}\n\n{e}")

    def operator_profile_dict(self) -> dict:
        return {
            "callsign": self.clean_callsign(),
            "name": self.operator_name_var.get().strip(),
            "grid": self.operator_grid_var.get().strip().upper(),
            "software": f"HX {VERSION}",
            "protocol": HX_PROTOCOL_VERSION,
            "caps": ",".join(HX_CAPABILITIES),
        }

    def operator_profile_json(self) -> str:
        return json.dumps(self.operator_profile_dict(), separators=(",", ":"))

    def file_exchange_metadata(self, peer: str | None = None) -> dict:
        """Profile and the best available peer SNR bundled in file setup frames.

        FILE_OFFER and FILE_ACCEPT both carry this metadata, so each station
        reports the SNR it currently observes from the other station before the
        first chunk is sent.  No separate SNR? RF request is needed.
        """
        snr = None
        peer_call = (peer or getattr(self, "session_peer", "") or "").strip().upper()
        if peer_call:
            try:
                snr = self.heard_stations.get(peer_call, {}).get("snr")
            except Exception:
                snr = None
        if snr is None:
            snr = self.last_rx_snr
        return {
            "profile": self.operator_profile_dict() if self.share_profile_var.get() else {"callsign": self.clean_callsign()},
            "snr": float(snr) if snr is not None else None,
        }

    def apply_file_exchange_metadata(self, call: str, info: dict, direction: str = "file transfer"):
        if not isinstance(info, dict):
            return
        prof = info.get("profile")
        if isinstance(prof, dict):
            prof_call = (prof.get("callsign") or call).strip().upper()
            self.remote_profiles[prof_call] = prof
            self.update_qso_from_profile(prof_call, prof)
            self.q.put(("session_event", f"Operator profile received automatically from {prof_call} for {direction}"))
        snr = info.get("snr")
        if snr is not None:
            try:
                snr = float(snr)
                # The value bundled by the peer is that peer's measurement of
                # our signal.  Therefore it is this station's TX SNR and must
                # update the same shared QSO field used by normal SNR reports.
                self.update_station_tx_snr(call, snr)
                self.q.put(("session_event", f"SNR report received automatically from {call}: {snr:+.1f} dB"))
                self.qlog(f"Automatic file-transfer SNR report from {call}: {snr:+.1f} dB; TX display synchronized", "info")
            except Exception:
                pass

    def send_operator_profile(self, to_call: str):
        if not self.share_profile_var.get():
            self.qlog("Operator profile not sent: sharing disabled", "warn")
            return False
        dest = self.clean_destination(to_call)
        payload = "HXCTL|PROFILE|" + self.operator_profile_json()
        self.qlog(f"Operator profile queued to {dest}", "info")
        self.q.put(("session_event", f"Operator profile sent to {dest}"))
        self.mark_session_traffic("profile tx")
        return self.start_background_tx(payload, animate_text=False, clear_after=False, reason="session", override_to=dest)

    def request_operator_profile(self, to_call: str):
        dest = self.clean_destination(to_call)
        sid = self.session_id or self.pending_connect_id or self.new_session_id()
        now = time.time()
        last = self.profile_request_cooldown.get(dest, 0.0)
        if now - last < 15.0:
            self.qlog(f"Profile request to {dest} held: cooldown active", "warn")
            self.show_info("Operator Profile", f"Please wait a few seconds before requesting {dest}'s profile again.")
            return False

        # Profile and SNR exchange automatically in FILE_OFFER/FILE_ACCEPT.
        # Do not queue redundant requests during a transfer.
        if getattr(self, "file_tx_active", False) or getattr(self, "file_rx_active", False):
            self.qlog(f"Profile request disabled during file transfer: {dest}", "warn")
            self.show_info("Operator Profile", "Profile and SNR information are exchanged automatically during file transfer.")
            return False

        self.profile_request_cooldown[dest] = now
        self.qlog(f"Operator profile request queued to {dest}", "info")
        self.q.put(("session_event", f"Operator profile requested from {dest}"))
        return self.start_background_tx(f"HXCTL|PROFILE_REQ|{sid}", animate_text=False, clear_after=False, reason="session", override_to=dest)

    def operator_profile_setup(self):
        win = tk.Toplevel(self)
        win.title("Operator Profile")
        win.geometry("460x260")
        win.configure(bg=COLORS["bg"])
        frm = ttk.Frame(win, padding=14)
        frm.pack(fill="both", expand=True)
        ttk.Label(frm, text="Operator Profile", style="Section.TLabel").grid(row=0, column=0, columnspan=2, sticky="w", pady=(0, 10))
        ttk.Label(frm, text="Callsign", style="Panel.TLabel").grid(row=1, column=0, sticky="w", pady=4)
        callsign_entry = ttk.Entry(frm, textvariable=self.callsign_var)
        callsign_entry.grid(row=1, column=1, sticky="ew", pady=4)
        ttk.Label(frm, text="Name", style="Panel.TLabel").grid(row=2, column=0, sticky="w", pady=4)
        name_entry = ttk.Entry(frm, textvariable=self.operator_name_var)
        name_entry.grid(row=2, column=1, sticky="ew", pady=4)
        ttk.Label(frm, text="Grid", style="Panel.TLabel").grid(row=3, column=0, sticky="w", pady=4)
        grid_entry = ttk.Entry(frm, textvariable=self.operator_grid_var)
        grid_entry.grid(row=3, column=1, sticky="ew", pady=4)
        ttk.Checkbutton(frm, text="Allow profile sharing when manually requested", variable=self.share_profile_var).grid(row=4, column=0, columnspan=2, sticky="w", pady=(10, 2))
        ttk.Checkbutton(frm, text="Auto-load last chat history", variable=self.autoload_last_chat_var).grid(row=5, column=0, columnspan=2, sticky="w", pady=2)
        ttk.Checkbutton(frm, text="Respond to external SNR requests while connected", variable=self.respond_external_snr_connected_var).grid(row=6, column=0, columnspan=2, sticky="w", pady=2)
        frm.columnconfigure(1, weight=1)
        def save():
            self.callsign_var.set(self.clean_callsign())
            self.operator_grid_var.set(self.operator_grid_var.get().strip().upper())
            self.save_config()
            self.qlog("Operator profile saved", "ok")
            win.destroy()
        win.protocol("WM_DELETE_WINDOW", save)
        row = ttk.Frame(frm)
        row.grid(row=7, column=0, columnspan=2, sticky="ew", pady=(14, 0))
        ttk.Button(row, text="OK", command=save).pack(side="right")
        for entry in (callsign_entry, name_entry, grid_entry):
            entry.bind("<Return>", lambda _event: (save(), "break")[1])
        win.bind("<KP_Enter>", lambda _event: (save(), "break")[1])
        callsign_entry.focus_set()

    def log(self, msg, level="info", force=False):
        if not force and not self.should_show_log(str(msg), str(level)):
            return
        ts = time.strftime("%H:%M:%S", time.gmtime())
        tag = level
        if level == "auto":
            low = msg.lower()
            tag = "err" if "error" in low or "fail" in low else "ok" if "decoded" in low or "ok" in low else "warn" if "warning" in low else "info"
        line = f"{ts}  {msg}"
        self.logbox.insert("end", line + "\n", tag)
        self.logbox.see("end")
        self.append_text_log(line)

    def qlog(self, msg, level="auto"):
        self.q.put(("log", (msg, level)))

    def ftlog(self, msg: str, transfer_id: str = "", peer: str = ""):
        """Append detailed file-transfer diagnostics to a dedicated log file.

        This log is intentionally separate from the operator/event log so test
        reports can include a compact, high-signal trace of file-transfer state.
        It is safe to call from worker threads.
        """
        try:
            os.makedirs(DOC_DIR, exist_ok=True)
            ts = time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime())
            th = threading.current_thread().name
            tid = (transfer_id or getattr(self, "file_tx_id", "") or "-")
            pr = (peer or getattr(self, "file_tx_peer", "") or (self.file_rx.get("peer") if getattr(self, "file_rx", None) else "") or "-")
            line = f"{ts} [{th}] peer={pr} id={tid} {msg}\n"
            with self.file_debug_lock:
                with open(FILE_DEBUG_LOG_PATH, "a", encoding="utf-8") as f:
                    f.write(line)
        except Exception:
            pass

    def open_file_transfer_debug_log(self):
        try:
            os.makedirs(DOC_DIR, exist_ok=True)
            if not os.path.exists(FILE_DEBUG_LOG_PATH):
                with open(FILE_DEBUG_LOG_PATH, "w", encoding="utf-8") as f:
                    f.write("HX Traffic and File Transfer Debug Log\n")
            if os.name == "nt":
                os.startfile(FILE_DEBUG_LOG_PATH)  # type: ignore[attr-defined]
            else:
                subprocess.Popen(["xdg-open", FILE_DEBUG_LOG_PATH])
        except Exception as e:
            self.show_error("Open Traffic / File Debug Log", f"Unable to open traffic / file debug log:\n{FILE_DEBUG_LOG_PATH}\n\n{e}")

    def delete_file_transfer_debug_log(self):
        try:
            if not os.path.exists(FILE_DEBUG_LOG_PATH):
                self.show_info("Delete Debug Log", "The traffic / file debug log does not exist.")
                return
            if not self.ask_yes_no("Delete Debug Log", f"Delete the traffic / file debug log?\n\n{FILE_DEBUG_LOG_PATH}"):
                return
            os.remove(FILE_DEBUG_LOG_PATH)
            self.qlog("Traffic / file debug log deleted", "ok")
        except Exception as e:
            self.show_error("Delete Debug Log", f"Unable to delete debug log:\n{FILE_DEBUG_LOG_PATH}\n\n{e}")

    def process_queue(self):
        try:
            while True:
                kind, payload = self.q.get_nowait()
                if kind == "log":
                    msg, level = payload if isinstance(payload, tuple) else (payload, "auto")
                    self.log(msg, level)
                elif kind == "status":
                    self.update_decode_status(payload)
                elif kind == "meter":
                    which, val = payload
                    if which == "tx":
                        self.tx_meter_level = max(self.tx_meter_level, float(val))
                    else:
                        self.rx_meter_level = max(self.rx_meter_level, float(val))
                elif kind == "spectrum_rx":
                    self.update_spectrum_rx_samples(payload)
                elif kind == "spectrum_tx":
                    self.set_spectrum_tx_audio(payload)
                elif kind == "spectrum_tx_clear":
                    self.clear_spectrum_tx()
                elif kind == "rxstate":
                    if hasattr(self, "rx_state_label"):
                        self.rx_state_label.configure(text=payload)
                elif kind == "decodeout":
                    self.append_decode_output(payload)
                elif kind == "led":
                    name, state, label = payload
                    self.set_led(name, state, label)
                elif kind == "message":
                    if len(payload) == 4:
                        direction, callsign, message, to_call = payload
                    else:
                        direction, callsign, message = payload
                        to_call = "ALL"
                    self.add_message_line(direction, callsign, message, to_call)
                    if str(direction).upper() == "RX":
                        self.remember_station(callsign)
                elif kind == "heard":
                    call, snr = payload
                    self.update_heard_station(call, snr)
                elif kind == "txprogress":
                    pct, label = payload
                    self.draw_tx_progress(float(pct), str(label))
                elif kind == "clear_tx":
                    self.clear_tx_text_widget()
                elif kind == "txcharprogress":
                    self.mark_tx_chars_sent(payload)
                elif kind == "template_reset":
                    if hasattr(self, "template_var"):
                        self.template_var.set("N/A")
                elif kind == "txbusy":
                    busy = bool(payload)
                    self.tx_busy = busy
                    state = "disabled" if busy else "normal"
                    if hasattr(self, "send_button"):
                        self.send_button.configure(state=state)
                    if hasattr(self, "send_file_button"):
                        self.send_file_button.configure(state="normal" if (not busy and self.session_active and not self.file_tx_active and not self.file_rx_active) else "disabled")
                    if hasattr(self, "cancel_file_button"):
                        self.cancel_file_button.configure(state="normal" if (self.file_tx_active or self.file_rx_active) else "disabled")
                    if hasattr(self, "beacon_now_button"):
                        self.beacon_now_button.configure(state=state)
                    self.update_session_controls()
                elif kind == "rxdetect":
                    self.last_rx_detect = str(payload)
                elif kind == "modemstate":
                    self.set_modem_state(str(payload))
                elif kind == "catstate":
                    self.apply_cat_state(payload)
                elif kind == "connect_request":
                    call, sid = payload
                    self.handle_connect_request(call, sid)
                elif kind == "file_offer":
                    self.handle_file_offer_ui(*payload)
                elif kind == "file_complete_prompt":
                    self.file_receive_complete_ui(payload)
                elif kind == "session_event":
                    self.add_session_event(str(payload))
                    self.update_session_controls()
        except queue.Empty:
            pass
        self.after(100, self.process_queue)

    def on_mode_changed(self):
        self.save_config()
        self.update_statusbar()

    def auto_mode_from_snr(self, snr: float | None, conservative: bool = False) -> str:
        """Choose an effective HX mode for AUTO.

        AUTO is the operator-friendly default.  The selected on-air mode is
        derived from the latest locally observed RX SNR.  File transfer uses a
        slightly more conservative threshold than normal chat/control traffic.
        Unknown SNR preserves the previous fast behavior and starts at HX-F.
        """
        try:
            val = float(snr) if snr is not None else 99.0
        except Exception:
            val = 99.0
        if conservative:
            if val < 18.0:
                return "HX-N"
            return "HX-F"
        return choose_mode(val)

    def auto_tx_mode(self) -> str:
        return self.auto_mode_from_snr(getattr(self, "last_rx_snr", None), conservative=False)

    def selected_mode(self):
        m = (self.mode_var.get() or "AUTO").strip().upper()
        if m not in ("AUTO", "HX-F", "HX-N"):
            m = "AUTO"
            self.mode_var.set("AUTO")
        return self.auto_tx_mode() if m == "AUTO" else m

    def mode_display_text(self) -> str:
        m = (self.mode_var.get() or "AUTO").strip().upper()
        if m == "AUTO":
            return f"AUTO ({self.auto_tx_mode()})"
        return m

    def selected_rx_mode(self):
        # RX Monitor must always use AUTO acquisition.
        # The mode selector controls TX only; using it for RX caused the
        # station monitor to miss valid frames when TX/RX modes differed.
        return "AUTO"

    def update_decode_status(self, res):
        self.last_decode_hold_until = time.time() + 4.0
        snr = float(res["snr"])
        self.last_rx_snr = snr
        self.snr_label.configure(text=f"{snr:.2f} dB")
        self.update_statusbar()
        self.last_rx_detect = res.get("mode_header", "--")
        self.last_rx_mode = self.last_rx_detect
        self.set_led("RX", "ok", "DECODED")
        self.set_led("Pilot", "ok", "LOCK")
        self.set_led("Timing", "ok", "LOCK")
        self.set_led("CRC", "ok", "OK")
        self.frames_ok += 1
        self.stats_label.configure(text=f"Frames OK: {self.frames_ok}\nFrames Fail: {self.frames_fail}")

    def set_modem_state(self, state: str):
        """Bottom status LED: green RX/listening, amber active receive, red TX."""
        colors = {
            "rx": COLORS["green"],
            "tx": COLORS["red"],
            "receive": COLORS["amber"],
            "off": "#4a5562",
        }
        labels = {
            "rx": (f"MODEM: Connected {self.session_peer}" if self.session_active else f"MODEM: Listening ({self.selected_rx_mode()})"),
            "tx": f"MODEM: Sending ({self.mode_display_text()})",
            "receive": f"MODEM: Receiving ({self.last_rx_detect})",
            "off": "MODEM: Idle",
        }
        color = colors.get(state, COLORS["green"])
        if hasattr(self, "modem_led_canvas"):
            self.modem_led_canvas.itemconfigure(self.modem_led, fill=color)
        if hasattr(self, "modem_led_label"):
            self.modem_led_label.configure(text=labels.get(state, "MODEM"), fg=color)

    def load_recent_stations(self) -> list[str]:
        raw = self.config_data.get("recent_stations", [])
        if not isinstance(raw, list):
            return []
        out: list[str] = []
        for item in raw:
            call = str(item).strip().upper()
            if call and call not in ("ALL", "CQ", self.clean_callsign()) and call not in out:
                out.append(call)
        return out[:12]

    def destination_values(self) -> list[str]:
        vals = ["ALL", "CQ"]
        for call in getattr(self, "recent_stations", []):
            if call not in vals:
                vals.append(call)
        return vals

    def refresh_destination_list(self):
        if hasattr(self, "to_entry"):
            self.to_entry.configure(values=self.destination_values())

    def on_destination_selected(self, _event=None):
        dest = (self.to_var.get() or "ALL").strip().upper()
        self.to_var.set(dest or "ALL")

    def on_destination_commit(self, _event=None):
        dest = (self.to_var.get() or "ALL").strip().upper()
        self.to_var.set(dest or "ALL")

    def remember_station(self, call: str):
        call = (call or "").strip().upper()
        # Do not suppress own callsign here: in lab/two-instance testing both
        # stations may use the same configured call, and HEARD should still
        # reflect what was actually received over the modem.
        if not call or call in ("ALL", "CQ", "UNKNOWN"):
            return
        if call in self.recent_stations:
            self.recent_stations.remove(call)
        self.recent_stations.insert(0, call)
        self.recent_stations = self.recent_stations[:12]
        self.refresh_destination_list()
        self.save_config()

    def clear_recent_stations(self):
        self.recent_stations = []
        if hasattr(self, "to_var") and self.to_var.get().strip().upper() not in ("ALL", "CQ"):
            self.to_var.set("ALL")
        self.refresh_destination_list()
        self.save_config()
        self.log("Recent stations cleared.", "ok")

    def update_heard_station(self, call: str, snr: float | None = None):
        call = (call or "").strip().upper()
        # Do not suppress own callsign here: in lab/two-instance testing both
        # stations may use the same configured call, and HEARD should still
        # reflect what was actually received over the modem.
        if not call or call in ("ALL", "CQ", "UNKNOWN"):
            return
        try:
            snr_val = float(snr) if snr is not None else None
        except Exception:
            snr_val = None
        self.heard_stations[call] = {"snr": snr_val, "updated": time.time()}
        if snr_val is not None:
            self.last_rx_snr = snr_val
            self.update_statusbar()

        # RX SNR is the signal level this station observes from the other
        # station.  It is station information, not only session information.
        # Therefore it should update the Station / QSO Information panel
        # whenever the panel is already showing this station, even before a
        # CONNECT session exists.  Protect active QSOs from third-party updates.
        if snr_val is not None:
            current_call = (self.qso_current.get("call") or "--").strip().upper()
            should_update_card = False
            if self.session_active:
                should_update_card = (call == self.session_peer)
            else:
                should_update_card = current_call in ("--", "", call)
            if should_update_card:
                if current_call in ("--", ""):
                    self.qso_current["call"] = call
                    self.qso_current["status"] = "Heard"
                self.qso_current["rx_snr"] = f"{snr_val:+.1f} dB"
                self.update_qso_panel()

        self.refresh_heard_list()

    @staticmethod
    def format_age(seconds: float) -> str:
        seconds = max(0, int(seconds))
        if seconds < 5:
            return "now"
        if seconds < 60:
            return f"{seconds}s"
        minutes = seconds // 60
        if minutes < 60:
            return f"{minutes}m"
        hours = minutes // 60
        if hours < 24:
            return f"{hours}h"
        days = hours // 24
        return f"{days}d"

    def refresh_heard_list(self):
        if not hasattr(self, "heard_tree"):
            return
        selected = set(self.heard_tree.selection())
        self.heard_tree.delete(*self.heard_tree.get_children())
        now = time.time()
        items = sorted(self.heard_stations.items(), key=lambda kv: kv[1].get("updated", 0), reverse=True)
        for call, info in items:
            snr = info.get("snr")
            snr_text = "--" if snr is None else f"{snr:+.1f}"
            updated = float(info.get("updated", 0) or 0)
            age_text = self.format_age(now - updated) if updated > 0 else "--"
            self.heard_tree.insert("", "end", iid=call, values=(call, age_text, snr_text))
        for call in selected:
            if self.heard_tree.exists(call):
                self.heard_tree.selection_add(call)

    def on_heard_select(self, _event=None):
        if not hasattr(self, "heard_tree"):
            return
        sel = self.heard_tree.selection()
        if not sel:
            return
        call = str(sel[0]).strip().upper()
        if call:
            current = (self.to_var.get() or "").strip().upper()
            if current == call:
                return
            self.to_var.set(call)
            self.remember_station(call)
            self.save_config()
            self.update_session_controls()
            self.qlog(f"Destination changed to {call} (Last Heard selection)", "info")

    def connect_selected_heard(self):
        """Connect to the station selected in Last Heard.

        Capture the row callsign before the context menu is destroyed and pass
        it explicitly to start_connect().  This avoids depending on a later
        Treeview selection read or a transient To-field callback.
        """
        if not hasattr(self, "heard_tree"):
            return
        sel = self.heard_tree.selection()
        if not sel:
            self.qlog("CONNECT ignored: no Last Heard station selected", "warn")
            return
        call = str(sel[0]).strip().upper()
        if not call:
            return
        self.to_var.set(call)
        self.after_idle(lambda c=call: self.start_connect(c))

    def send_message_to_selected_heard(self):
        if not hasattr(self, "heard_tree"):
            return
        sel = self.heard_tree.selection()
        if sel:
            self.to_var.set(str(sel[0]).strip().upper())
            if hasattr(self, "tx_text"):
                self.tx_text.focus_set()

    def copy_selected_heard_callsign(self):
        if not hasattr(self, "heard_tree"):
            return
        sel = self.heard_tree.selection()
        if sel:
            self.clipboard_clear()
            self.clipboard_append(str(sel[0]).strip().upper())
            self.qlog(f"Copied callsign {str(sel[0]).strip().upper()}", "ok")

    def remove_selected_heard(self):
        if not hasattr(self, "heard_tree"):
            return
        sel = self.heard_tree.selection()
        if sel:
            call = str(sel[0]).strip().upper()
            self.heard_stations.pop(call, None)
            if hasattr(self, "to_var") and (self.to_var.get() or "").strip().upper() == call:
                self.to_var.set("ALL")
                self.save_config()
            self.refresh_heard_list()
            self.qlog(f"Removed {call} from heard list", "ok")

    def on_heard_context_menu(self, event):
        if not hasattr(self, "heard_tree"):
            return
        row = self.heard_tree.identify_row(event.y)
        if row:
            self.heard_tree.selection_set(row)
            self.to_var.set(str(row).strip().upper())
        menu = tk.Menu(self, tearoff=0, bg=COLORS["panel3"], fg=COLORS["text"], activebackground=COLORS["accent"], activeforeground="#ffffff")
        menu.add_command(label="Connect", command=self.connect_selected_heard, state=("normal" if (row and (not self.session_active) and (not self.tx_busy) and self.is_valid_station_destination(str(row))) else "disabled"))
        menu.add_command(label="Disconnect", command=self.disconnect_session, state=("normal" if (self.session_active and not self.tx_busy) else "disabled"))
        menu.add_separator()
        menu.add_command(label="Send Message", command=self.send_message_to_selected_heard, state=("normal" if row else "disabled"))
        menu.add_command(label="Request Profile", command=lambda r=row: self.request_operator_profile(str(r).strip().upper()) if r else None, state=("normal" if (row and not self.file_tx_active and not self.file_rx_active) else "disabled"))
        menu.add_command(label="Copy Callsign", command=self.copy_selected_heard_callsign, state=("normal" if row else "disabled"))
        menu.add_command(label="Remove", command=self.remove_selected_heard, state=("normal" if row else "disabled"))
        menu.add_separator()
        menu.add_command(label="Clear List", command=self.clear_heard_stations)
        try:
            menu.tk_popup(event.x_root, event.y_root)
        finally:
            menu.grab_release()

    def clear_heard_stations(self):
        self.heard_stations = {}
        if hasattr(self, "to_var") and (self.to_var.get() or "").strip().upper() not in ("ALL", "CQ"):
            self.to_var.set("ALL")
            self.save_config()
        if hasattr(self, "heard_tree"):
            self.heard_tree.delete(*self.heard_tree.get_children())
        self.qlog("Heard stations cleared.", "ok")

    def apply_message_template(self, _event=None):
        tag = (self.template_var.get() or "N/A").strip().upper()
        if (self.file_tx_active or self.file_rx_active) and tag in ("SNR?", "REQUEST PROFILE"):
            self.template_var.set("N/A")
            self.show_info("HX File Transfer", "Profile and SNR requests are disabled because both are exchanged automatically during the file transfer.")
            return
        if tag == "CQ":
            self.to_var.set("CQ")
            msg = "CQ CQ CQ"
        elif tag == "SNR?":
            current_dest = (self.to_var.get() or "").strip().upper()
            if not current_dest or current_dest == "CQ":
                self.to_var.set("ALL")
            msg = "SNR?"
        elif tag == "SEND PROFILE":
            current_dest = self.clean_destination()
            if current_dest in ("ALL", "CQ"):
                self.show_info("Operator Profile", "Select or type a station callsign before sending your profile.")
                self.template_var.set("N/A")
                return
            self.send_operator_profile(current_dest)
            self.template_var.set("N/A")
            return
        elif tag == "REQUEST PROFILE":
            current_dest = self.clean_destination()
            if current_dest in ("ALL", "CQ"):
                self.show_info("Operator Profile", "Select or type a station callsign before requesting profile information.")
                self.template_var.set("N/A")
                return
            self.request_operator_profile(current_dest)
            self.template_var.set("N/A")
            return
        else:
            return
        if hasattr(self, "tx_text"):
            self.tx_text.delete("1.0", "end")
            self.tx_text.insert("1.0", msg)
            self.tx_text.focus_set()
        self.message_var.set(msg)
        self.template_var.set("N/A")

    def on_beacon_changed(self):
        self.save_config()
        if self.beacon_enabled_var.get():
            self.schedule_next_beacon(reset=True)
            self.qlog(f"Beacon enabled: every {self.beacon_interval_var.get()} minutes", "ok")
        else:
            self.next_beacon_time = None
            self.qlog("Beacon disabled.", "warn")
        self.update_statusbar()

    def beacon_interval_seconds(self) -> int:
        try:
            mins = int(self.beacon_interval_var.get())
        except Exception:
            mins = 15
        return max(5, mins) * 60

    def schedule_next_beacon(self, reset: bool = False):
        if reset or not self.next_beacon_time:
            self.next_beacon_time = time.time() + self.beacon_interval_seconds()

    def beacon_message(self) -> str:
        """Build the beacon text, including the operator profile grid when set."""
        grid = self.operator_grid_var.get().strip().upper()
        return f"Beacon GRID={grid}" if grid else "Beacon"

    def send_beacon_now(self):
        """Transmit a beacon immediately and restart the countdown."""
        msg = self.beacon_message()
        self.qlog(f"Beacon TX now: {msg}", "info")
        if self.start_background_tx(msg, animate_text=False, clear_after=False, reason="beacon", override_to="ALL"):
            self.beacon_tx_in_progress = True
            self.next_beacon_time = time.time() + self.beacon_interval_seconds()
            self.update_statusbar()

    def beacon_tick(self):
        try:
            if self.beacon_enabled_var.get():
                self.schedule_next_beacon()
                if self.next_beacon_time and time.time() >= self.next_beacon_time and not self.beacon_tx_in_progress:
                    msg = self.beacon_message()
                    self.qlog(f"Beacon TX due: {msg}", "info")
                    if self.start_background_tx(msg, animate_text=False, clear_after=False, reason="beacon", override_to="ALL"):
                        self.beacon_tx_in_progress = True
                        self.next_beacon_time = time.time() + self.beacon_interval_seconds()
        finally:
            self.update_statusbar()
            self.after(1000, self.beacon_tick)

    def maybe_speak_tag(self, message: str):
        """First operator tag: any standalone CQ in received text announces CQ message."""
        if not re.search(r"\bCQ\b", message or "", re.IGNORECASE):
            return
        threading.Thread(target=self.speak_text, args=("CQ message",), daemon=True).start()

    def maybe_speak_direct(self, from_call: str, to_call: str):
        """Voice alert for directed messages addressed to this station.

        Suppressed during an active session with that peer, and rate-limited
        per callsign outside sessions so repeated directed messages do not
        become annoying.
        """
        mycall = self.clean_callsign()
        dest = (to_call or "ALL").strip().upper()
        src = (from_call or "UNKNOWN").strip().upper()
        if dest != mycall or src == mycall:
            return
        if self.session_active and src == self.session_peer:
            return
        now = time.time()
        last = self.direct_voice_cooldown.get(src, 0.0)
        if now - last < 60.0:
            return
        self.direct_voice_cooldown[src] = now
        threading.Thread(target=self.speak_text, args=("Direct message",), daemon=True).start()

    def speak_text(self, text: str):
        if hasattr(self, "voice_announcements_var") and not self.voice_announcements_var.get():
            return
        try:
            safe = text.replace("'", "''")
            script = (
                "Add-Type -AssemblyName System.Speech; "
                "$s=New-Object System.Speech.Synthesis.SpeechSynthesizer; "
                "$v=$s.GetInstalledVoices() | Where-Object { $_.VoiceInfo.Gender -eq 'Female' } | Select-Object -First 1; "
                "if ($v) { $s.SelectVoice($v.VoiceInfo.Name) }; "
                f"$s.Speak('{safe}')"
            )
            flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
            subprocess.Popen(["powershell", "-NoProfile", "-Command", script], creationflags=flags)
        except Exception as e:
            self.qlog(f"Voice alert failed: {e}", "warn")

    def maybe_auto_reply_snr(self, from_call: str, to_call: str, message: str, snr: float):
        # First simple service tag: if a received message asks SNR?, reply with
        # a directed SNR report to that station.  The trigger is plain text,
        # intentionally simple for early station-to-station testing.
        if not re.search(r"(^|\s)(SNR\?|SIGNAL\?)(\s|$)", message or "", re.IGNORECASE):
            return
        reply_to = (from_call or "UNKNOWN").strip().upper() or "UNKNOWN"
        # Only auto-reply if the request is broadcast or addressed to this station.
        dest = (to_call or "ALL").strip().upper()
        if dest not in ("ALL", "CQ", self.clean_callsign()):
            return
        # Operator preference: while connected, optionally suppress external SNR replies.
        if self.session_active and reply_to != self.session_peer and not self.respond_external_snr_connected_var.get():
            self.qlog(f"External SNR request ignored from {reply_to}: active session with {self.session_peer}", "debug")
            return
        # FROM/TO are now protocol metadata, so keep the operator text clean.
        # Display will show: FROM → TO: SNR +NN.N dB
        reply = f"SNR {snr:+.1f} dB"
        self.qlog(f"Auto SNR reply queued to {reply_to}: {reply}", "info")
        self.start_background_tx(reply, animate_text=False, clear_after=False, reason="SNR auto-reply", override_to=reply_to)


    def mark_user_activity(self, reason: str = "user"):
        """Reset the session idle timer for true user traffic.

        KEEPALIVE/ACK traffic deliberately does not call this.
        """
        now = time.time()
        self.session_last_user_activity = now
        if getattr(self, "post_transfer_drain_active", False):
            self.post_transfer_quiet_since = now
        self.session_idle_warning_active = False
        self.session_disconnect_deadline = None
        self.keepalive_pending = False
        self.keepalive_missed = 0
        self.keepalive_attempts_sent = 0
        self.update_statusbar()

    def disable_beacon_for_activity(self, reason: str):
        """Stop automatic beaconing when real operator/session activity starts."""
        if hasattr(self, "beacon_enabled_var") and self.beacon_enabled_var.get():
            self.beacon_enabled_var.set(False)
            self.next_beacon_time = None
            self.qlog(f"Beacon disabled: {reason}", "warn")
            self.update_session_controls()

    def is_keepalive_control_payload(self, payload) -> bool:
        msg = (payload or "").strip().upper() if isinstance(payload, str) else ""
        return msg.startswith("HXCTL|KEEPALIVE|") or msg.startswith("HXCTL|ACK_KEEPALIVE|")

    def mark_session_traffic(self, reason: str = "session traffic"):
        """Reset session idle/keepalive timers for real session traffic.

        KEEPALIVE and ACK_KEEPALIVE do not call this; they are link-health
        traffic and must not keep an otherwise idle session alive forever.
        """
        if self.session_active:
            self.mark_user_activity(reason)

    def set_session_active(self, peer: str, sid: str):
        new_peer = (peer or "UNKNOWN").strip().upper()
        already_active = self.session_active and self.session_peer == new_peer
        previous_call = (self.qso_current.get("call") or "--").strip().upper()
        if (not already_active) and previous_call not in ("--", "", new_peer):
            self.reset_qso_panel()
        self.session_active = True
        self.session_peer = new_peer
        self.session_id = sid or self.new_session_id()

        # A previous user-requested DISCONNECT may have left a temporary
        # file-transfer guard active so that late chunks from the old session
        # would not be ACKed.  Once a new session with the same station is
        # explicitly established, that old guard must be cleared; otherwise
        # a valid FILE_OFFER/FILE_ACCEPT resume exchange is silently ignored.
        guard_peer = (getattr(self, "local_disconnect_peer", "") or "").strip().upper()
        if guard_peer in ("", new_peer):
            if getattr(self, "local_disconnect_until", 0.0) > 0.0:
                self.ftlog(f"LOCAL_DISCONNECT_GUARD cleared on new session with {new_peer}", peer=new_peer)
            self.local_disconnect_peer = ""
            self.local_disconnect_until = 0.0
        if not self.session_uuid:
            self.session_uuid = uuid.uuid4().hex[:8].upper()
        if not self.session_started:
            self.session_started = time.time()
        self.qso_current.update({
            "call": self.session_peer,
            "name": self.remote_profiles.get(self.session_peer, {}).get("name", self.qso_current.get("name", "--")) or "--",
            "grid": self.remote_profiles.get(self.session_peer, {}).get("grid", self.qso_current.get("grid", "--")) or "--",
            "rx_snr": self.qso_current.get("rx_snr", "--") or "--",
            "tx_snr": "--",
            "status": "Connected",
            "start": self.qso_time_text(self.session_started),
            "end": "--",
            "duration": "--",
        })
        self.update_qso_panel()
        self.connect_pending = False
        self.connect_target = ""
        self.connect_retries_sent = 0
        self.connect_next_retry_time = 0.0
        self.mark_user_activity("session")
        self.disable_beacon_for_activity("session established")
        if not self.active_chat_file:
            self.start_chat_session(self.session_peer)
        # v0.4.6: do not automatically change the To: destination when a
        # session is established.  Directed chat should be an explicit operator
        # choice; startup/disconnect default remains ALL.
        self.update_session_controls()
        # v0.2.54b: profile exchange is manual only.
        # Automatic post-connect profile transmission was removed because it
        # can collide with ACCEPT/other queued session traffic during real use.

    def session_tick(self):
        """Session keep-alive, connect retry, and idle-timeout manager.

        v0.2.54d keeps KEEPALIVE quiet until 120 seconds of true session idle.
        v0.2.53 makes CONNECT retries channel-aware.  Retries do not fire
        while another HX burst is being received/decoded, while TX is active,
        or during the post-RX guard interval.  This prevents a caller from
        sending a second CONNECT while the called station is decoding or
        transmitting ACCEPT/REJECT.
        """
        try:
            now = time.time()

            # Pending CONNECT: retry only after a clear-channel window.
            if getattr(self, "connect_pending", False) and not self.session_active:
                if self.tx_busy or getattr(self, "hx_channel_busy", False):
                    # Keep pushing the retry window out while HX traffic is present.
                    self.connect_next_retry_time = max(
                        float(getattr(self, "connect_next_retry_time", 0.0) or 0.0),
                        now + 1.0,
                    )
                elif now < float(getattr(self, "connect_guard_until", 0.0) or 0.0):
                    # Recently decoded an HX burst; give the other side time to answer.
                    self.connect_next_retry_time = max(
                        float(getattr(self, "connect_next_retry_time", 0.0) or 0.0),
                        float(getattr(self, "connect_guard_until", 0.0) or 0.0),
                    )
                elif now >= float(getattr(self, "connect_next_retry_time", 0.0) or 0.0):
                    target = getattr(self, "connect_target", "") or getattr(self, "pending_connect_from", "")
                    sid = getattr(self, "pending_connect_id", "") or self.new_session_id()
                    if self.connect_retries_sent < self.connect_max_retries:
                        self.connect_retries_sent += 1
                        backoff = random.uniform(1.0, 3.0)
                        self.connect_random_backoff = backoff
                        self.connect_next_retry_time = now + self.connect_retry_interval + backoff
                        self.add_session_event(f"CONNECT retry {self.connect_retries_sent} of {self.connect_max_retries} to {target}")
                        self.qlog(f"Session CONNECT retry {self.connect_retries_sent}/{self.connect_max_retries} to {target} id={sid}; next window {self.connect_retry_interval:.0f}s + {backoff:.1f}s", "warn")
                        self.start_background_tx(f"HXCTL|CONNECT|{sid}", animate_text=False, clear_after=False, reason="session", override_to=target)
                    else:
                        self.connect_attempt_timeout()

            if self.session_active and not self.tx_busy:
                # Deferred traffic owns the post-transfer channel.  Keepalive
                # must not compete with profile/text/disconnect traffic while
                # either side is draining its queue.
                if getattr(self, "post_transfer_drain_active", False):
                    self._post_transfer_drain_tick(now)
                    return
                idle = now - float(self.session_last_user_activity or self.session_started or now)

                if self.session_disconnect_deadline:
                    if now >= self.session_disconnect_deadline:
                        peer = self.session_peer
                        sid = self.session_id or self.new_session_id()
                        self.qlog(f"Session idle timeout after keep-alive attempts: disconnecting from {peer}", "warn")
                        self.start_background_tx(f"HXCTL|DISCONNECT|{sid}", animate_text=False, clear_after=False, reason="session", override_to=peer)
                        threading.Thread(target=self.speak_text, args=("Connection closed",), daemon=True).start()
                        self.clear_session(local_notice=True)
                    else:
                        self.update_statusbar()
                elif idle >= self.keepalive_idle_start_seconds and (now - self.last_keepalive_sent) >= self.keepalive_repeat_seconds:
                    if getattr(self, "hx_channel_busy", False):
                        # Polite channel access: do not send keepalive over HX traffic.
                        self.last_keepalive_sent = now - (self.keepalive_repeat_seconds - 5.0)
                    else:
                        # v0.2.54n: ACKs prove the peer is still there, but they
                        # must not keep an otherwise idle session alive forever.
                        # Count total keepalive attempts after true session idle;
                        # only real non-keepalive traffic resets this counter.
                        if self.keepalive_attempts_sent >= 5:
                            self.session_idle_warning_active = True
                            self.session_disconnect_deadline = now + 60.0
                            self.add_session_event("Session idle after 5 KEEPALIVE attempts; disconnecting in 60 seconds")
                            self.qlog("Session idle: 5 KEEPALIVE attempts completed; disconnecting in 60 seconds unless user traffic resumes", "warn")
                            threading.Thread(target=self.speak_text, args=("Session idle",), daemon=True).start()
                            self.update_statusbar()
                        else:
                            sid = self.session_id or self.new_session_id()
                            self.last_keepalive_sent = now
                            self.keepalive_pending = True
                            self.keepalive_attempts_sent += 1
                            attempt = self.keepalive_attempts_sent
                            self.add_session_event(f"KEEPALIVE {attempt}/5 sent to {self.session_peer}")
                            self.qlog(f"Session KEEPALIVE {attempt}/5 sent to {self.session_peer} id={sid}", "debug")
                            self.start_background_tx(f"HXCTL|KEEPALIVE|{sid}", animate_text=False, clear_after=False, reason="session", override_to=self.session_peer)
        finally:
            self.after(1000, self.session_tick)

    # HX Session Layer Phase 1
    # -------------------------
    def new_session_id(self) -> str:
        return f"{np.random.randint(0, 0x10000):04X}"

    def is_valid_station_destination(self, dest: str | None = None) -> bool:
        call = self.clean_destination(dest)
        return bool(call and call not in ("ALL", "CQ", "NOCALL", self.clean_callsign()))

    def normalize_callsign_var(self):
        if getattr(self, "_normalizing_callsign", False):
            return
        try:
            val = (self.callsign_var.get() or "").upper()
            allowed = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789/-_"
            val = "".join(ch for ch in val if ch in allowed)
            if val != self.callsign_var.get():
                self._normalizing_callsign = True
                self.callsign_var.set(val)
        finally:
            self._normalizing_callsign = False
        if hasattr(self, "mycall_label"):
            self.mycall_label.configure(text=f"{self.clean_callsign()}")
        if hasattr(self, "connect_button"):
            self.update_session_controls()

    def normalize_to_var(self):
        if getattr(self, "_normalizing_to", False):
            return
        try:
            val = (self.to_var.get() or "").upper()
            allowed = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789/-_"
            val = "".join(ch for ch in val if ch in allowed)
            if val != self.to_var.get():
                self._normalizing_to = True
                self.to_var.set(val)
        finally:
            self._normalizing_to = False
        if hasattr(self, "connect_button"):
            self.update_session_controls()

    def session_button_action(self):
        """Single session button: CONNECT when idle, CANCEL while calling, DISCONNECT when connected."""
        try:
            if getattr(self, "connect_pending", False):
                self.cancel_connect_attempt()
            elif self.session_active:
                self.disconnect_session()
            else:
                # Snapshot the editable combobox value before any focus-change
                # callback can alter it, then start on the Tk idle queue.
                dest = self.clean_destination()
                self.after_idle(lambda d=dest: self.start_connect(d))
        except Exception as exc:
            self.qlog(f"CONNECT action failed: {type(exc).__name__}: {exc}", "err")
            self.show_error("HX Session", f"Could not start connection:\n{exc}")

    def set_file_transfer_text_lock(self, active: bool):
        """Disable all operator text/service entry while a file transfer owns TX."""
        if not hasattr(self, "tx_text"):
            return
        placeholder = "Text messages disabled during file transfer. Please wait."
        active = bool(active)
        try:
            if active:
                if not getattr(self, "_file_text_locked", False):
                    self._file_text_saved = self.tx_text.get("1.0", "end-1c")
                    self.tx_text.configure(state="normal")
                    self.tx_text.delete("1.0", "end")
                    self.tx_text.insert("1.0", placeholder)
                    self.tx_text.configure(fg=COLORS["muted"], state="disabled")
                    self._file_text_locked = True
            elif getattr(self, "_file_text_locked", False):
                saved = getattr(self, "_file_text_saved", "")
                self.tx_text.configure(state="normal", fg=COLORS["text"])
                self.tx_text.delete("1.0", "end")
                if saved:
                    self.tx_text.insert("1.0", saved)
                self._file_text_saved = ""
                self._file_text_locked = False
        except Exception:
            pass

    def update_session_controls(self):
        connecting = bool(getattr(self, "connect_pending", False))
        can_connect = (not self.session_active) and (not self.tx_busy) and self.is_valid_station_destination()
        can_disconnect = self.session_active and (not self.tx_busy) and (not getattr(self, "disconnect_pending", False))
        if hasattr(self, "session_button"):
            if connecting:
                self.session_button.configure(text="CANCEL", state="normal" if not self.tx_busy else "disabled")
            elif self.session_active:
                self.session_button.configure(text="DISCONNECT", state="normal" if can_disconnect else "disabled")
            else:
                self.session_button.configure(text="CONNECT", state="normal" if can_connect else "disabled")
        elif hasattr(self, "connect_button"):
            if connecting:
                self.connect_button.configure(text="CANCEL", state="normal" if not self.tx_busy else "disabled")
            else:
                self.connect_button.configure(text="CONNECT", state="normal" if can_connect else "disabled")
        if hasattr(self, "disconnect_button") and self.disconnect_button is not getattr(self, "session_button", None):
            self.disconnect_button.configure(state="normal" if can_disconnect else "disabled")
        if hasattr(self, "to_entry"):
            try:
                self.to_entry.configure(state="disabled" if (self.session_active or connecting) else "normal")
            except Exception:
                pass
        file_active = bool(getattr(self, "file_tx_active", False) or getattr(self, "file_rx_active", False))
        self.set_file_transfer_text_lock(file_active)
        if hasattr(self, "send_button"):
            try:
                self.send_button.configure(state="disabled" if (self.tx_busy or connecting or file_active) else "normal")
            except Exception:
                pass
        if hasattr(self, "send_file_button"):
            try:
                self.send_file_button.configure(state="normal" if (self.session_active and not self.tx_busy and not connecting and not self.file_tx_active and not self.file_rx_active) else "disabled")
            except Exception:
                pass
        if hasattr(self, "cancel_file_button"):
            try:
                self.cancel_file_button.configure(state="normal" if (self.file_tx_active or self.file_rx_active) else "disabled")
            except Exception:
                pass
        if hasattr(self, "template_combo"):
            try:
                if file_active:
                    self.template_var.set("N/A")
                    self.template_combo.configure(values=("N/A",), state="disabled")
                else:
                    self.template_combo.configure(values=("N/A", "CQ", "SNR?", "SEND PROFILE", "REQUEST PROFILE"), state="readonly")
            except Exception:
                pass
        # Beacon is intentionally unavailable during an active session, pending connection, or any TX.
        beacon_state = "disabled" if self.session_active or connecting or self.tx_busy else "normal"
        for name in ("beacon_check", "beacon_interval_combo", "beacon_now_button"):
            if hasattr(self, name):
                try:
                    getattr(self, name).configure(state=beacon_state)
                except Exception:
                    pass

    def add_session_event(self, text: str):
        ts = time.strftime("%H:%M:%S", time.gmtime())
        if hasattr(self, "msgbox"):
            line = f"{ts}  SESSION  {text}"
            self.message_history_insert(line + "\n", "direct")
            self.append_chat_transcript(line)

    def start_connect(self, dest_override: str | None = None):
        """Begin a CONNECT attempt and never fail silently.

        The destination may be supplied explicitly by the Last Heard context
        menu.  CONNECT itself still uses the shared TX arbitration queue, but
        pending/session UI state is established immediately so the operator can
        see that the request was accepted.
        """
        try:
            if getattr(self, "connect_pending", False):
                self.cancel_connect_attempt()
                return
            dest = self.clean_destination(dest_override)
            self.qlog(f"CONNECT action requested for {dest}", "info")
            if not self.is_valid_station_destination(dest):
                self.show_info("HX Session", "Enter or select a station callsign in the To field before connecting.")
                return
            if self.session_active:
                self.show_info("HX Session", f"Already connected to {self.session_peer}.")
                return

            # Keep the visible destination synchronized with the explicit
            # context-menu target.
            self.to_var.set(dest)
            self.disable_beacon_for_activity("session connect requested")
            self.mark_user_activity("connect")
            sid = self.new_session_id()
            self.pending_connect_id = sid
            self.pending_connect_from = dest
            self.connect_pending = True
            self.connect_target = dest
            self.connect_retries_sent = 0
            self.connect_next_retry_time = time.time() + self.connect_retry_interval
            self.connect_guard_until = 0.0
            self.connect_random_backoff = 0.0
            self.qlog(f"Session CONNECT requested to {dest} id={sid}", "info")
            self.add_session_event(f"CONNECT request sent to {dest}")
            self.update_session_controls()

            accepted = self.start_background_tx(
                f"HXCTL|CONNECT|{sid}", animate_text=False,
                clear_after=False, reason="session", override_to=dest
            )
            if not accepted:
                # Roll back a request that the scheduler genuinely refused
                # (for example while the 1 kHz tune tone is active).
                self.connect_pending = False
                self.connect_target = ""
                self.pending_connect_from = ""
                self.pending_connect_id = ""
                self.update_session_controls()
                self.qlog(f"Session CONNECT could not be queued for {dest}", "err")
                self.show_error("HX Session", "The connection request could not be queued. Stop any active tune tone and try again.")
                return

            # Ensure a request held by RX/turnaround arbitration is reevaluated
            # promptly even when no further state-change callback occurs.
            self.after(50, self.process_tx_hold_queue)
        except Exception as exc:
            self.connect_pending = False
            self.connect_target = ""
            self.pending_connect_from = ""
            self.pending_connect_id = ""
            self.update_session_controls()
            self.qlog(f"CONNECT start failed: {type(exc).__name__}: {exc}", "err")
            self.show_error("HX Session", f"Could not start connection:\n{exc}")

    def cancel_connect_attempt(self):
        target = getattr(self, "connect_target", "") or getattr(self, "pending_connect_from", "")
        self.connect_pending = False
        self.connect_target = ""
        self.pending_connect_from = ""
        self.pending_connect_id = ""
        self.connect_retries_sent = 0
        self.connect_next_retry_time = 0.0
        self.connect_guard_until = 0.0
        self.connect_random_backoff = 0.0
        self.add_session_event(f"CONNECT attempt canceled" + (f" for {target}" if target else ""))
        self.qlog(f"Session CONNECT canceled" + (f" to {target}" if target else ""), "warn")
        self.update_session_controls()

    def connect_attempt_timeout(self):
        target = getattr(self, "connect_target", "") or getattr(self, "pending_connect_from", "") or "station"
        self.connect_pending = False
        self.connect_target = ""
        self.pending_connect_from = ""
        self.pending_connect_id = ""
        self.connect_retries_sent = 0
        self.connect_next_retry_time = 0.0
        self.connect_guard_until = 0.0
        self.connect_random_backoff = 0.0
        self.add_session_event(f"Station not responding: {target}")
        self.qlog(f"Session CONNECT timed out: {target} not responding", "err")
        threading.Thread(target=self.speak_text, args=("Station not responding",), daemon=True).start()
        self.play_hx_chime("error")
        self.update_session_controls()

    def handle_connect_request(self, call: str, sid: str):
        call = (call or "UNKNOWN").strip().upper()
        sid = (sid or "").strip().upper()

        # HX Session Rule: one active session at a time.
        # If already connected to another station, do not pop up a dialog and
        # do not interrupt the current session. Reply BUSY so the caller stops retrying.
        if self.session_active and self.session_peer != call:
            self.qlog(f"Session CONNECT from {call}: station busy with {self.session_peer}", "warn")
            self.start_background_tx(f"HXCTL|BUSY|{sid}", animate_text=False, clear_after=False, reason="session", override_to=call)
            return

        # If the peer retries CONNECT because our ACCEPT was missed, answer
        # with ACCEPT again instead of opening another dialog.
        if self.session_active and self.session_peer == call:
            self.qlog(f"Duplicate CONNECT from active peer {call}; re-sending ACCEPT id={sid or self.session_id}", "warn")
            self.start_background_tx(f"HXCTL|ACCEPT|{sid or self.session_id}", animate_text=False, clear_after=False, reason="session", override_to=call)
            return

        try:
            self.speak_text("Connection request")
        except Exception:
            pass
        accept = self.ask_yes_no_timeout(
            "HX Session Request",
            f"{call} wishes to establish an HX session.\n\nAccept?",
            timeout_ms=5000,
        )
        if accept:
            self.set_session_active(call, sid)
            self.add_session_event(f"Connection with {call} established at {time.strftime("%H:%M:%S", time.gmtime())}")
            self.qlog(f"Session accepted from {call} id={sid}", "ok")
            self.play_hx_chime("connected")
            threading.Thread(target=self.speak_text, args=("Connection established",), daemon=True).start()
            self.update_session_controls()
            self.start_background_tx(f"HXCTL|ACCEPT|{sid}", animate_text=False, clear_after=False, reason="session", override_to=call)
        else:
            self.add_session_event(f"Rejected session request from {call}")
            self.qlog(f"Session rejected from {call} id={sid}", "warn")
            self.start_background_tx(f"HXCTL|REJECT|{sid}", animate_text=False, clear_after=False, reason="session", override_to=call)

    def disconnect_session(self):
        """Queue a polite disconnect and transmit only after RX/turnaround clears."""
        if not self.session_active or self.disconnect_pending:
            return
        peer = self.session_peer
        sid = self.session_id or self.new_session_id()

        # Remember the operator's intent immediately, but do not transmit yet.
        # A short observation window lets an arriving KEEPALIVE assert HX busy;
        # after that, normal channel-busy and turnaround guards arbitrate TX.
        self.disconnect_pending = True
        self.disconnect_pending_peer = (peer or "").strip().upper()
        self.disconnect_pending_sid = sid
        self.disconnect_not_before = time.time() + 1.25

        self.local_disconnect_peer = self.disconnect_pending_peer
        self.local_disconnect_until = time.time() + 300.0
        if self.file_rx_active or self.file_rx:
            self.ftlog("LOCAL_DISCONNECT: incoming file RX marked abandoned; future chunks will be ignored during guard", peer=peer)
        self.file_rx_active = False
        self.file_rx = None
        self.release_file_awake("rx")
        if self.file_tx_active:
            self.file_tx_cancel = True

        self.add_session_event(f"Disconnect requested from {peer}; waiting for clear channel")
        self.qlog(f"Session DISCONNECT queued for {peer} id={sid}", "info")
        self.update_session_controls()
        self.after(100, self._process_pending_disconnect)

    def _process_pending_disconnect(self):
        if not getattr(self, "disconnect_pending", False):
            return
        peer = self.disconnect_pending_peer
        sid = self.disconnect_pending_sid
        if not self.session_active or (self.session_peer or "").strip().upper() != peer:
            self.disconnect_pending = False
            self.disconnect_pending_peer = ""
            self.disconnect_pending_sid = ""
            return
        now = time.time()
        state_blocked, _state_reason = self.rx_tx_blocked()
        hold = (
            now < float(getattr(self, "disconnect_not_before", 0.0) or 0.0)
            or state_blocked
        )
        if hold:
            self.after(150, self._process_pending_disconnect)
            return

        self.disconnect_pending = False
        self.disconnect_pending_peer = ""
        self.disconnect_pending_sid = ""
        self.add_session_event(f"Disconnecting from {peer}")
        self.qlog(f"Session DISCONNECT sent to {peer} id={sid}", "info")
        self.start_background_tx(f"HXCTL|DISCONNECT|{sid}", animate_text=False, clear_after=False, reason="session", override_to=peer)
        self.clear_session(local_notice=False)
        threading.Thread(target=self.speak_text, args=("Connection closed",), daemon=True).start()

    def clear_session(self, local_notice: bool = True):
        self.disconnect_pending = False
        self.disconnect_pending_peer = ""
        self.disconnect_pending_sid = ""
        self.disconnect_not_before = 0.0
        peer = self.session_peer
        start_ts = self.session_started
        # A remote disconnect or idle timeout must also release any receive-side
        # power request. The TX worker sees the session change and releases its
        # own reference from its finally block.
        if self.file_rx_active or self.file_rx:
            self.file_rx_active = False
            self.file_rx = None
            self.release_file_awake("rx")
        if self.file_tx_active:
            self.file_tx_cancel = True
        if peer:
            end_ts = time.time()
            end_clock = time.strftime("%H:%M:%S", time.gmtime(end_ts))
            duration = max(0, int(end_ts - float(start_ts or end_ts)))
            duration_txt = f"{duration//3600:02d}:{(duration%3600)//60:02d}:{duration%60:02d}"
            self.qso_current["end"] = self.qso_time_text(end_ts)
            self.qso_current["duration"] = duration_txt
            self.qso_current["status"] = "Last QSO"
            self.update_qso_panel()
            self.add_session_event(f"Connection with {peer} closed at {end_clock}. Duration {duration_txt}")
            self.finish_chat_session(peer, start_ts)
        self.session_active = False
        self.session_peer = ""
        self.session_id = ""
        self.remote_profiles = {}
        # Keep the QSO panel populated after a connection closes so it can
        # serve as Station / QSO Information. The Clear button or a new connection
        # to a different station will clear/replace these fields.
        self.active_chat_file = None
        self.active_chat_peer = ""
        self.active_chat_started_ts = None
        self.session_uuid = ""
        self.session_started = None
        self.session_last_user_activity = time.time()
        self.last_keepalive_sent = 0.0
        self.keepalive_pending = False
        self.keepalive_missed = 0
        self.keepalive_attempts_sent = 0
        self.session_idle_warning_active = False
        self.session_disconnect_deadline = None
        self.direct_voice_cooldown = {}  # CALL -> last direct voice announcement time
        self.connect_voice_cooldown = {}
        self.pending_connect_from = ""
        self.pending_connect_id = ""
        self.connect_pending = False
        self.connect_target = ""
        self.connect_retries_sent = 0
        self.connect_max_retries = 3
        self.connect_retry_interval = 30.0
        self.connect_next_retry_time = 0.0
        self.connect_guard_until = 0.0
        self.connect_random_backoff = 0.0
        if local_notice and peer:
            self.add_session_event(f"Connection closed with {peer}")
        # v0.4.6: after any disconnect/session clear, return destination to ALL
        # to avoid accidentally sending later chat to the previous station.
        try:
            if hasattr(self, "to_var"):
                self.to_var.set("ALL")
                self.save_config()
        except Exception:
            pass
        self.update_qso_panel()
        self.update_session_controls()

    def handle_session_control_rx(self, call: str, to_call: str, text: str) -> bool:
        msg = (text or "").strip()
        if not msg.startswith("HXCTL|"):
            return False
        parts = msg.split("|", 2)
        cmd = parts[1].upper() if len(parts) > 1 else ""
        # Keep the raw third HXCTL field intact because newer control frames
        # may carry JSON.  Uppercasing JSON corrupts field names such as
        # "id" and "next_chunk", which breaks FILE_ACCEPT parsing.
        sid_raw_field = (parts[2] if len(parts) > 2 else "").strip()
        sid = sid_raw_field.upper()
        call = (call or "UNKNOWN").strip().upper()
        dest = (to_call or "ALL").strip().upper()
        mycall = self.clean_callsign()

        # Critical session-routing rule: session control frames are processed
        # only when addressed to this local station.  Other HX stations may
        # decode the RF frame, but they must not show dialogs or alter state.
        if dest != mycall:
            self.qlog(f"Session control ignored: {cmd or 'UNKNOWN'} from {call} to {dest} (local {mycall})", "debug")
            return True

        # Local disconnect guard: after this operator presses DISCONNECT, the
        # other station may still be sending file frames because it was in TX
        # and missed our disconnect packet.  Do not answer FILE_* frames during
        # the guard window.  No ACK/NACK makes the sender retry and eventually
        # fall back to its timeout/keep-alive disconnect behavior.
        if cmd.startswith("FILE_") and getattr(self, "local_disconnect_until", 0.0) > time.time():
            guard_peer = (getattr(self, "local_disconnect_peer", "") or "").strip().upper()
            if not guard_peer or call == guard_peer:
                self.ftlog(f"LOCAL_DISCONNECT_GUARD ignoring {cmd} from={call}; no file ACK/NACK will be sent", peer=call)
                return True

        if cmd not in ("KEEPALIVE", "ACK_KEEPALIVE"):
            self.mark_session_traffic(f"rx {cmd.lower() or 'control'}")

        if cmd == "CONNECT":
            self.qlog(f"Session CONNECT received from {call} id={sid}", "info")
            self.q.put(("connect_request", (call, sid)))
            return True

        if cmd == "BUSY":
            if self.connect_pending and (not self.connect_target or call == self.connect_target):
                self.q.put(("session_event", f"Station busy: {call}"))
                self.qlog(f"Session BUSY received from {call} id={sid}", "warn")
                self.connect_pending = False
                self.connect_target = ""
                self.pending_connect_from = ""
                self.pending_connect_id = ""
                self.connect_next_retry_time = 0.0
                self.play_hx_chime("error")
                threading.Thread(target=self.speak_text, args=("Station busy",), daemon=True).start()
                self.update_session_controls()
            else:
                self.qlog(f"Session BUSY ignored from {call}; no matching pending CONNECT", "debug")
            return True

        if cmd in ("POST_DRAIN_DONE", "POST_DRAIN_ACK"):
            # Compatibility only. v0.7.2 no longer emits post-transfer drain
            # frames because all operator text/profile/SNR controls are locked
            # during file transfer. Never expose these internal frames to users.
            self.ftlog(f"Legacy {cmd} ignored from={call}", peer=call)
            return True

        if cmd == "PROFILE_REQ":
            self.qlog(f"Operator profile request received from {call}", "info")
            self.send_operator_profile(call)
            return True

        if cmd == "PROFILE":
            raw = msg.split("|", 2)[2] if msg.count("|") >= 2 else "{}"
            try:
                prof = json.loads(raw)
            except Exception:
                prof = {"callsign": call}
            prof_call = (prof.get("callsign") or call).strip().upper()
            self.remote_profiles[prof_call] = prof
            self.update_qso_from_profile(prof_call, prof)
            name = (prof.get("name") or "").strip()
            grid = (prof.get("grid") or "").strip().upper()
            details = " ".join(x for x in (name, grid) if x)
            self.q.put(("session_event", f"Operator profile received from {prof_call}" + (f" ({details})" if details else "")))
            self.qlog(f"Operator profile received from {prof_call}: name={name or '--'} grid={grid or '--'}", "info")
            return True

        if cmd == "ACCEPT":
            if not self.connect_pending:
                self.qlog(f"Session ACCEPT ignored from {call}; no pending CONNECT", "debug")
                return True
            if self.connect_target and call != self.connect_target:
                self.qlog(f"Session ACCEPT ignored from {call}; waiting for {self.connect_target}", "debug")
                return True
            if self.pending_connect_id and sid and sid != self.pending_connect_id:
                self.qlog(f"Session ACCEPT ignored from {call}; session id {sid} != pending {self.pending_connect_id}", "debug")
                return True
            self.set_session_active(call, sid or self.pending_connect_id or self.new_session_id())
            self.q.put(("session_event", f"Connected to {call}"))
            self.qlog(f"Session accepted by {call} id={self.session_id}", "ok")
            self.play_hx_chime("connected")
            threading.Thread(target=self.speak_text, args=("Connection established",), daemon=True).start()
            return True

        if cmd == "REJECT":
            if not self.connect_pending:
                self.qlog(f"Session REJECT ignored from {call}; no pending CONNECT", "debug")
                return True
            if self.connect_target and call != self.connect_target:
                self.qlog(f"Session REJECT ignored from {call}; waiting for {self.connect_target}", "debug")
                return True
            if self.pending_connect_id and sid and sid != self.pending_connect_id:
                self.qlog(f"Session REJECT ignored from {call}; session id {sid} != pending {self.pending_connect_id}", "debug")
                return True
            self.connect_pending = False
            self.connect_target = ""
            self.pending_connect_from = ""
            self.pending_connect_id = ""
            self.connect_next_retry_time = 0.0
            self.q.put(("session_event", f"Connection rejected by {call}"))
            self.qlog(f"Session rejected by {call} id={sid}", "warn")
            self.play_hx_chime("error")
            self.clear_session(local_notice=False)
            return True

        if cmd == "DISCONNECT":
            if not self.session_active or call != self.session_peer:
                self.qlog(f"Session DISCONNECT ignored from {call}; active peer is {self.session_peer or 'none'}", "debug")
                return True
            if self.session_id and sid and sid != self.session_id:
                self.qlog(f"Session DISCONNECT ignored from {call}; session id {sid} != active {self.session_id}", "debug")
                return True
            self.q.put(("session_event", f"Connection closed by {call}"))
            self.qlog(f"Session disconnect received from {call} id={sid}", "warn")
            self.clear_session(local_notice=False)
            threading.Thread(target=self.speak_text, args=("Connection closed",), daemon=True).start()
            return True

        if cmd == "FILE_OFFER":
            self.ftlog(f"RX FILE_OFFER raw={msg[:220]}", peer=call)
            raw = msg.split("|", 2)[2] if msg.count("|") >= 2 else "{}"
            try:
                info = json.loads(raw)
            except Exception:
                info = {}
            transfer_id = (info.get("id") or "").strip().upper()
            if not self.session_active or call != self.session_peer:
                self.qlog(f"FILE offer ignored from {call}; no active session with peer", "warn")
                return True
            if not transfer_id:
                self.qlog("FILE offer ignored: missing transfer id", "warn")
                return True
            # For JSON-based file frames, the transfer id lives inside the
            # JSON payload. Do not use the third HXCTL field as sid here,
            # because that field is the entire JSON document for FILE_OFFER.
            self.apply_file_exchange_metadata(call, info, "incoming file offer")
            self.ftlog(f"QUEUE file_offer to UI transfer_id={transfer_id} name={info.get('name')} size={info.get('size')} chunks={info.get('chunks')}", transfer_id, call)
            self.q.put(("file_offer", (call, transfer_id, info)))
            return True

        if cmd == "FILE_ACCEPT":
            # FILE_ACCEPT may be either the legacy form:
            #   HXCTL|FILE_ACCEPT|TRANSFER_ID
            # or the resume-capable JSON form:
            #   HXCTL|FILE_ACCEPT|{"id":"TRANSFER_ID","next_chunk":N}
            # Use sid_raw_field here, not sid, because sid is uppercased for
            # legacy routing and would corrupt JSON key names.
            accept_info = {}
            sid_raw = sid_raw_field.strip()
            transfer_id = sid_raw.upper()
            if sid_raw.startswith("{"):
                try:
                    accept_info = json.loads(sid_raw)
                    transfer_id = (accept_info.get("id") or "").strip().upper()
                except Exception as e:
                    accept_info = {}
                    transfer_id = ""
                    self.ftlog(f"RX FILE_ACCEPT JSON parse failed: {e}; raw={sid_raw[:120]}", peer=call)
            self.ftlog(
                f"RX FILE_ACCEPT from={call} transfer_id={transfer_id} next_chunk={accept_info.get('next_chunk')} expected={getattr(self, 'file_tx_id', '')} peer_expected={getattr(self, 'file_tx_peer', '')}",
                transfer_id,
                call,
            )
            if call == self.file_tx_peer and transfer_id == self.file_tx_id:
                self.apply_file_exchange_metadata(call, accept_info, "file acceptance")
                try:
                    self.file_tx_resume_from = max(1, int(accept_info.get("next_chunk", 1) or 1))
                except Exception:
                    self.file_tx_resume_from = 1
                self.file_tx_ack_result = "ACCEPT"
                self.file_tx_ack_event.set()
                self.add_session_event(f"File accepted by {call}" + (f"; resume chunk {self.file_tx_resume_from}" if self.file_tx_resume_from > 1 else ""))
                if not getattr(self, "file_tx_accept_announced", False):
                    self.file_tx_accept_announced = True
                    threading.Thread(target=self.speak_text, args=("File transfer accepted",), daemon=True).start()
            else:
                self.qlog(f"FILE_ACCEPT ignored from {call}: id={transfer_id or '--'} expected={self.file_tx_id or '--'}", "debug")
            return True

        if cmd == "FILE_REJECT":
            transfer_id = (sid or "").strip().upper()
            self.ftlog(f"RX FILE_REJECT from={call} transfer_id={transfer_id} expected={getattr(self, 'file_tx_id', '')}", transfer_id, call)
            if call == self.file_tx_peer and transfer_id == self.file_tx_id:
                self.file_tx_ack_result = "REJECT"
                self.file_tx_ack_event.set()
                self.add_session_event(f"File rejected by {call}")
                threading.Thread(target=self.speak_text, args=("File transfer not accepted",), daemon=True).start()
            else:
                self.qlog(f"FILE_REJECT ignored from {call}: id={transfer_id or '--'} expected={self.file_tx_id or '--'}", "debug")
            return True

        if cmd == "FILE_CHUNK":
            self.ftlog(f"RX FILE_CHUNK raw_len={len(msg)} raw_head={msg[:160]}", peer=call)
            self.handle_file_chunk_rx(call, "", msg)
            return True

        if cmd == "FILE_ACK":
            self.ftlog(f"RX FILE_ACK raw={msg[:180]}", peer=call)
            raw = msg.split("|", 2)[2] if msg.count("|") >= 2 else "{}"
            try:
                ack = json.loads(raw)
            except Exception:
                ack = {}
            transfer_id = (ack.get("id") or "").strip().upper()
            if call == self.file_tx_peer and transfer_id == self.file_tx_id:
                self.file_tx_ack_chunk = int(ack.get("chunk", -1))
                try:
                    ack_snr = ack.get("snr", None)
                    if ack_snr is not None:
                        self.update_station_tx_snr(call, float(ack_snr))
                        self.ftlog(f"RX FILE_ACK includes peer-reported SNR={float(ack_snr):.1f} dB", transfer_id, call)
                except Exception:
                    pass
                self.file_tx_ack_result = "ACK"
                self.file_tx_ack_event.set()
            else:
                self.qlog(f"FILE_ACK ignored from {call}: id={transfer_id or '--'} expected={self.file_tx_id or '--'}", "debug")
            return True

        if cmd == "FILE_NACK":
            self.ftlog(f"RX FILE_NACK raw={msg[:180]}", peer=call)
            raw = msg.split("|", 2)[2] if msg.count("|") >= 2 else "{}"
            try:
                nack = json.loads(raw)
            except Exception:
                nack = {}
            transfer_id = (nack.get("id") or "").strip().upper()
            if call == self.file_tx_peer and transfer_id == self.file_tx_id:
                self.file_tx_ack_chunk = int(nack.get("chunk", -1))
                self.file_tx_ack_result = "NACK"
                self.file_tx_ack_event.set()
            else:
                self.qlog(f"FILE_NACK ignored from {call}: id={transfer_id or '--'} expected={self.file_tx_id or '--'}", "debug")
            return True

        if cmd == "FILE_DONE":
            self.ftlog(f"RX FILE_DONE raw={msg[:180]}", peer=call)
            self.handle_file_done_rx(call, "", msg)
            return True

        if cmd == "FILE_CANCEL":
            transfer_id = (sid or "").strip().upper()
            self.ftlog(f"RX FILE_CANCEL from={call} id={transfer_id}", transfer_id, call)
            if self.file_rx_active and self.file_rx and self.file_rx.get("id") == transfer_id:
                self.add_session_event(f"File transfer cancelled by {call}")
                self.file_rx_active = False
                self.file_rx = None
                self.release_file_awake("rx")
                self.update_session_controls()
            elif self.file_tx_active and call == self.file_tx_peer and transfer_id == self.file_tx_id:
                self.file_tx_cancel = True
                self.file_tx_cancel_origin = "remote"
                self.file_tx_ack_result = "CANCEL"
                self.file_tx_ack_event.set()
                self.add_session_event(f"Remote station {call} cancelled the file transfer")
            return True

        if cmd == "KEEPALIVE":
            if not self.session_active or call != self.session_peer:
                self.qlog(f"Session KEEPALIVE ignored from {call}; active peer is {self.session_peer or 'none'}", "debug")
                return True
            if self.session_id and sid and sid != self.session_id:
                self.qlog(f"Session KEEPALIVE ignored from {call}; session id {sid} != active {self.session_id}", "debug")
                return True
            self.add_session_event(f"KEEPALIVE received from {call}")
            self.qlog(f"Session KEEPALIVE received from {call} id={sid}", "debug")
            self.start_background_tx(f"HXCTL|ACK_KEEPALIVE|{sid}", animate_text=False, clear_after=False, reason="session", override_to=call)
            return True

        if cmd == "ACK_KEEPALIVE":
            if not self.session_active or call != self.session_peer:
                self.qlog(f"Session KEEPALIVE ACK ignored from {call}; active peer is {self.session_peer or 'none'}", "debug")
                return True
            if self.session_id and sid and sid != self.session_id:
                self.qlog(f"Session KEEPALIVE ACK ignored from {call}; session id {sid} != active {self.session_id}", "debug")
                return True
            self.add_session_event(f"KEEPALIVE ACK received from {call}")
            self.qlog(f"Session KEEPALIVE ACK received from {call} id={sid}", "debug")
            self.keepalive_pending = False
            # ACK confirms the peer, but does not reset idle/attempt counters.
            return True
        return True

    def clean_callsign(self) -> str:
        call = (self.callsign_var.get() or "NOCALL").strip().upper()
        allowed = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789/-_"
        call = "".join(ch for ch in call if ch in allowed)
        return call or "NOCALL"

    def clean_destination(self, to_call: str | None = None) -> str:
        dest = (to_call if to_call is not None else self.to_var.get() if hasattr(self, "to_var") else "ALL")
        dest = (dest or "ALL").strip().upper()
        allowed = "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789/-_"
        dest = "".join(ch for ch in dest if ch in allowed)
        return dest or "ALL"

    def make_outgoing_payload(self, message: str, to_call: str | None = None) -> bytes:
        # Application-layer wrapper only; modem framing/FEC/pilot format is unchanged.
        # HXMSG4 places the operator text immediately after a compact fixed
        # prefix so progressive RX can display it near the start of reception.
        # Metadata follows the text and remains protected by the final frame CRC.
        call = self.clean_callsign()
        dest = self.clean_destination(to_call)
        caps = ",".join(HX_CAPABILITIES)
        msg = message.replace("\r", " ").replace("\n", " ").strip()
        msg_bytes = msg.encode("utf-8")
        if len(msg_bytes) > 65535:
            msg_bytes = msg_bytes[:65535]
        meta = f"|{HX_PROTOCOL_VERSION}|{caps}|{call}|{dest}".encode("utf-8")
        return b"HX4" + len(msg_bytes).to_bytes(2, "big") + msg_bytes + meta

    def parse_message_payload_meta(self, payload: bytes) -> dict:
        if payload.startswith(b"HX4") and len(payload) >= 5:
            msg_len = int.from_bytes(payload[3:5], "big")
            msg_end = 5 + msg_len
            if msg_end <= len(payload):
                message = payload[5:msg_end].decode("utf-8", errors="replace")
                meta_text = payload[msg_end:].decode("utf-8", errors="replace")
                if meta_text.startswith("|"):
                    parts = meta_text[1:].split("|", 3)
                    if len(parts) == 4:
                        return {
                            "version": parts[0] or "unknown",
                            "caps": parts[1] or "",
                            "from": parts[2] or "UNKNOWN",
                            "to": parts[3] or "ALL",
                            "text": message,
                            "format": "HXMSG4",
                        }
        text = payload.decode("utf-8", errors="replace")
        if text.startswith("HXMSG3|"):
            parts = text.split("|", 5)
            if len(parts) == 6:
                return {
                    "version": parts[1] or "unknown",
                    "caps": parts[2] or "",
                    "from": parts[3] or "UNKNOWN",
                    "to": parts[4] or "ALL",
                    "text": parts[5],
                    "format": "HXMSG3",
                }
        if text.startswith("HXMSG2|"):
            parts = text.split("|", 3)
            if len(parts) == 4:
                return {"version": "legacy", "caps": "MSG,DIRECT", "from": parts[1] or "UNKNOWN", "to": parts[2] or "ALL", "text": parts[3], "format": "HXMSG2"}
        if text.startswith("HXMSG1|"):
            parts = text.split("|", 2)
            if len(parts) == 3:
                return {"version": "legacy", "caps": "MSG", "from": parts[1] or "UNKNOWN", "to": "ALL", "text": parts[2], "format": "HXMSG1"}
        return {"version": "legacy", "caps": "", "from": "UNKNOWN", "to": "ALL", "text": text, "format": "plain"}

    def parse_message_payload(self, payload: bytes) -> tuple[str, str, str]:
        meta = self.parse_message_payload_meta(payload)
        return meta["from"], meta["to"], meta["text"]

    def note_station_capabilities(self, callsign: str, version: str, caps: str):
        call = (callsign or "UNKNOWN").strip().upper() or "UNKNOWN"
        caps_clean = (caps or "").strip()
        key = (version or "unknown", caps_clean)
        if self.station_caps_seen.get(call) == key:
            return
        self.station_caps_seen[call] = key
        if caps_clean:
            self.qlog(f"Station {call} supports HX {version}: {caps_clean}", "info")
        else:
            self.qlog(f"Station {call} uses HX {version} with no capability advertisement", "info")

    def normalize_display_message(self, callsign: str, message: str) -> str:
        """Keep protocol callsign separate from operator text.

        Older/test payloads sometimes included the sender callsign inside the
        text itself (for example, "N4EAC beacon").  Display code already
        shows the sender callsign, so strip a duplicate leading callsign only
        for presentation.  The modem payload itself is not changed here.
        """
        msg = (message or "").strip()
        call = (callsign or "").strip().upper()
        if not call:
            return msg
        # Match a leading sender callsign followed by common separators or space.
        pattern = r"^" + re.escape(call) + r"\s*(?::|->|>|-|—)?\s+"
        return re.sub(pattern, "", msg, count=1, flags=re.IGNORECASE).strip() or msg

    def is_snr_message(self, message: str) -> bool:
        msg = (message or "").strip().upper()
        return bool(re.search(r"\b(SNR\?|SIGNAL\?|SNR\s*[+-]?\d+(?:\.\d+)?\s*DB)\b", msg))

    def is_beacon_message(self, message: str) -> bool:
        return bool(re.search(r"\bBEACON\b", (message or "").strip().upper()))

    def is_cq_message(self, dest: str, message: str) -> bool:
        msg_upper = (message or "").strip().upper()
        dest_upper = (dest or "ALL").strip().upper()
        # SNR? must not be displayed as CQ even if the destination was accidentally CQ.
        if self.is_snr_message(message):
            return False
        return dest_upper == "CQ" or bool(re.search(r"\bCQ\b", msg_upper))

    def classify_message_tag(self, direction: str, dest: str, message: str) -> str:
        """Return a display color tag for the RX/TX history.

        Operator-authored conversational text is colored by direction:
        - TX typed by this operator: cyan
        - RX typed by the other station: light green

        HX-generated service traffic is purple.  This includes CQ/SNR service
        tags, beacons, profiles, keep-alives, session controls, and any raw
        HXCTL frame that might appear during debugging.
        """
        dest_upper = (dest or "ALL").strip().upper()
        msg_upper = (message or "").strip().upper()
        if (
            msg_upper.startswith("HXCTL|")
            or msg_upper.startswith("HXPROFILE")
            or msg_upper.startswith("PROFILE")
            or msg_upper.startswith("KEEPALIVE")
            or msg_upper.startswith("ACK_KEEPALIVE")
            or self.is_snr_message(message)
            or self.is_cq_message(dest_upper, message)
            or self.is_beacon_message(message)
        ):
            return "system"
        return "tx_user" if direction.upper() == "TX" else "rx_user"

    def clean_snr_display_text(self, callsign: str, to_call: str, message: str) -> str:
        """Remove duplicated ham-style SNR routing text from display only.

        Older auto-replies used text like "N4EAC de W1ABC SNR +41.0 dB".
        Since HXMSG2 already carries FROM and TO, the history should display
        just "SNR +41.0 dB" after the prefix.
        """
        msg = (message or "").strip()
        if not msg:
            return msg
        call = (callsign or "").strip().upper()
        dest = (to_call or "").strip().upper()
        calls = [c for c in (dest, call) if c]
        for first in calls:
            for second in calls:
                pattern = r"^" + re.escape(first) + r"\s+de\s+" + re.escape(second) + r"\s+(SNR\s*[+-]?\d+(?:\.\d+)?\s*dB)$"
                m = re.match(pattern, msg, flags=re.IGNORECASE)
                if m:
                    return m.group(1)
        return msg

    def extract_snr_report_db(self, message: str) -> float | None:
        """Return numeric dB value from a clean SNR report, not from an SNR request.

        RX SNR is measured locally from the received waveform. TX SNR must come
        from the other station's report of how it received us, usually text like
        "SNR +8.4 dB".
        """
        msg = (message or "").strip()
        if "?" in msg:
            return None
        m = re.search(r"\bSNR\s*([+-]?\d+(?:\.\d+)?)\s*dB\b", msg, flags=re.IGNORECASE)
        if not m:
            return None
        try:
            return float(m.group(1))
        except Exception:
            return None

    def update_station_tx_snr(self, callsign: str, snr_db: float):
        """Update Station / QSO Information TX SNR from a peer report.

        TX SNR means how the other station reports receiving this station.
        It can arrive through a human SNR reply or a protocol ACK carrying
        SNR during file transfer.
        """
        call = (callsign or "").strip().upper()
        if not call or call in ("ALL", "CQ", "UNKNOWN"):
            return
        if self.session_active and call != self.session_peer:
            return
        current_call = (self.qso_current.get("call") or "--").strip().upper()
        if current_call not in ("--", "", call) and not self.session_active:
            self.reset_qso_panel()
        self.qso_current["call"] = call
        if not self.session_active:
            self.qso_current["status"] = "Heard"
        elif call == self.session_peer:
            self.qso_current["status"] = "Connected"
        self.qso_current["tx_snr"] = f"{float(snr_db):+.1f} dB"
        try:
            heard = self.heard_stations.get(call, {}) if hasattr(self, "heard_stations") else {}
            rx_val = heard.get("snr")
            if rx_val not in (None, ""):
                self.qso_current["rx_snr"] = f"{float(rx_val):+.1f} dB"
        except Exception:
            pass
        self.update_qso_panel()

    def update_qso_tx_snr_from_report(self, from_call: str, to_call: str, message: str):
        """Update TX SNR from any valid SNR report addressed to this station.

        Station Information and QSO Information are related but separate:
        RX SNR is what this station observes from the other station; TX SNR is
        what the other station reports receiving from us.  A connected session
        is not required to learn that value; a manual SNR? request outside a
        connection should update the Station / QSO Information panel too.
        """
        val = self.extract_snr_report_db(message)
        if val is None:
            return

        src = (from_call or "").strip().upper()
        dest = (to_call or "ALL").strip().upper()
        mycall = self.clean_callsign()
        if not src or src in ("ALL", "CQ", "UNKNOWN"):
            return
        if dest not in (mycall, "ALL", "CQ"):
            return

        # Do not let a third station overwrite the live card during an active QSO.
        if self.session_active and src != self.session_peer:
            return

        current_call = (self.qso_current.get("call") or "--").strip().upper()
        if current_call not in ("--", "", src) and not self.session_active:
            self.reset_qso_panel()

        self.qso_current["call"] = src

        # The SNR report itself is also a received HX frame, so update RX SNR
        # from the most recent local observation of that station.  This makes
        # manual SNR? checks populate both sides of the Station / QSO
        # Information panel even outside an active session.
        try:
            heard = self.heard_stations.get(src, {}) if hasattr(self, "heard_stations") else {}
            rx_val = heard.get("snr")
            if rx_val not in (None, ""):
                self.qso_current["rx_snr"] = f"{float(rx_val):+.1f} dB"
        except Exception:
            pass

        # Preserve any profile details already learned for this station.
        prof = self.remote_profiles.get(src, {}) if hasattr(self, "remote_profiles") else {}
        name = (prof.get("name") or "").strip()
        grid = (prof.get("grid") or "").strip().upper()
        if name and self.qso_current.get("name") in ("--", "", None):
            self.qso_current["name"] = name
        if grid and self.qso_current.get("grid") in ("--", "", None):
            self.qso_current["grid"] = grid

        if not self.session_active:
            self.qso_current["status"] = "Heard"
        elif src == self.session_peer:
            self.qso_current["status"] = "Connected"

        self.qso_current["tx_snr"] = f"{val:+.1f} dB"
        self.update_qso_panel()

    def add_message_line(self, direction: str, callsign: str, message: str, to_call: str = "ALL"):
        ts = time.strftime("%H:%M:%S", time.gmtime())
        dest = (to_call or "ALL").strip().upper()
        message = self.normalize_display_message(callsign, message)
        message = self.clean_snr_display_text(callsign, dest, message)
        if direction.upper() == "RX":
            self.update_qso_tx_snr_from_report(callsign, dest, message)

        # SNR? is an SNR request, not a CQ display, even if older UI state left dest=CQ.
        display_dest = "ALL" if self.is_snr_message(message) and dest == "CQ" else dest

        if display_dest and display_dest not in ("ALL", "CQ"):
            prefix = f"{callsign} → {display_dest}"
        elif display_dest == "CQ":
            prefix = callsign
        else:
            prefix = callsign

        tag = self.classify_message_tag(direction, display_dest, message)

        # Add light-weight badges without making the message text repetitive.
        badge = ""
        if self.is_cq_message(display_dest, message):
            badge = "[CQ] "
        elif self.is_beacon_message(message):
            badge = "[BEACON] "
        elif self.is_snr_message(message) and "?" in message:
            badge = "[SNR?] "
        elif self.is_snr_message(message):
            badge = "[SNR] "

        if badge == "[BEACON] ":
            # The badge already identifies the traffic type. Keep "BEACON" in
            # the over-the-air text for backward compatibility, but suppress
            # the repeated word in the operator display.
            display_message = re.sub(r"^BEACON\b[ :|-]*", "", message, count=1, flags=re.IGNORECASE).strip()
            line = f"{ts}  {badge}{prefix}"
            if display_message:
                line += f" {display_message}"
        else:
            line = f"{ts}  {badge}{prefix}: {message}"
        self.message_history_insert(line + "\n", tag)
        self.append_chat_transcript(line)

    def get_tx_message_text(self) -> str:
        if hasattr(self, "tx_text"):
            return self.tx_text.get("1.0", "end-1c")
        return self.message_var.get()

    def on_tx_enter(self, _event=None):
        # Enter sends. Shift+Enter still inserts a newline if the platform sends it.
        self.start_tx()
        return "break"

    def clear_tx_text_widget(self):
        if hasattr(self, "tx_text"):
            self.tx_text.delete("1.0", "end")
            self.tx_text.tag_remove("sent", "1.0", "end")
        self.message_var.set("")

    def mark_tx_chars_sent(self, pct: float):
        if not hasattr(self, "tx_text"):
            return
        total = len(self.tx_text.get("1.0", "end-1c"))
        if total <= 0:
            return
        count = max(0, min(total, int(round((float(pct) / 100.0) * total))))
        self.tx_text.tag_remove("sent", "1.0", "end")
        if count > 0:
            self.tx_text.tag_add("sent", "1.0", f"1.0+{count}c")

    def start_tx_progress(self, audio: np.ndarray, duration: float, animate_text: bool = True, clear_after: bool = True):
        """Animate TX progress and meter from the actual generated audio.

        This is UI-only.  The audio sent to the modem is still generated by
        the unchanged audio/modem path; this meter simply follows the same
        waveform envelope so TX level reflects what is being transmitted.
        """
        stop_event = threading.Event()
        audio = np.asarray(audio, dtype=np.float32)
        chunk = max(1, int(0.10 * SAMPLE_RATE))
        total = max(1, len(audio))

        def worker():
            start = time.time()
            while not stop_event.is_set():
                elapsed = time.time() - start
                pct = min(99.0, (elapsed / max(0.1, duration)) * 100.0)
                idx = min(total, int((pct / 100.0) * total))
                lo = max(0, idx - chunk)
                seg = audio[lo:idx] if idx > lo else audio[:min(chunk, total)]
                if len(seg):
                    # Peak is more useful than RMS for clipping/drive awareness.
                    level = float(np.max(np.abs(seg)))
                else:
                    level = 0.0
                self.q.put(("txprogress", (pct, f"Sending... {pct:5.1f}%")))
                if animate_text:
                    self.q.put(("txcharprogress", pct))
                self.q.put(("meter", ("tx", level)))
                time.sleep(0.1)
            self.q.put(("txprogress", (100.0, "Sent 100%")))
            if animate_text:
                self.q.put(("txcharprogress", 100.0))
            self.q.put(("meter", ("tx", 0.0)))
            time.sleep(0.35)
            if clear_after:
                self.q.put(("clear_tx", None))
            self.q.put(("txprogress", (0.0, "Idle")))

        threading.Thread(target=worker, daemon=True).start()
        return stop_event

    def set_hx_channel_busy(self, busy: bool, label: str = ""):
        """Track when a valid-looking HX burst is occupying the audio channel.

        This is intentionally HX-specific. It does not try to detect voice,
        static, FT8, JS8, VARA, etc.; it only reacts to the HX receiver's own
        trigger/capture path so HX stations avoid transmitting over each other.
        """
        old = getattr(self, "hx_channel_busy", False)
        self.hx_channel_busy = bool(busy)
        now = time.time()
        if busy:
            self.q.put(("modemstate", "receive"))
            self.show_tx_queue_notice("Waiting for HX channel to clear…")
        elif old:
            self.q.put(("modemstate", "rx"))
            # Post-RX turnaround guard: after any HX burst, wait before queued TX
            # or CONNECT retry. This gives the peer time to finish decode and
            # re-arm RX before we release our queue.
            self.tx_turnaround_guard_until = max(float(getattr(self, "tx_turnaround_guard_until", 0.0) or 0.0), now + self.tx_guard_seconds)
            self.connect_guard_until = max(float(getattr(self, "connect_guard_until", 0.0) or 0.0), now + 5.0)
            self.after(int(self.tx_guard_seconds * 1000), self.process_tx_hold_queue)
        self.update_tx_queue_notice()
        self.update_session_controls()

    def tx_guard_remaining(self) -> float:
        return max(0.0, float(getattr(self, "tx_turnaround_guard_until", 0.0) or 0.0) - time.time())

    def rx_tx_blocked(self) -> tuple[bool, str]:
        """Return whether a real RX/TX state currently blocks a new transmit.

        The RX monitor thread itself is deliberately *not* a blocking state. It
        should normally remain open while HX is idle. Only an active HX frame,
        an active local transmission, or the post-RX/TX turnaround guard may
        hold the scheduler.
        """
        if bool(getattr(self, "tx_busy", False)):
            return True, "previous transmission"
        if bool(getattr(self, "hx_channel_busy", False)):
            return True, "active HX reception"
        guard = self.tx_guard_remaining()
        if guard > 0.0:
            return True, f"turnaround guard {guard:0.1f}s"
        return False, ""

    def should_hold_tx(self, reason: str = "") -> tuple[bool, str]:
        # Manual chat during an outbound file transfer is handled by a dedicated
        # deferred-message queue in start_background_tx(). It must never enter
        # the shared protocol queue. The RX monitor's existence is not a busy
        # condition; rx_tx_blocked() consults only actual modem/channel states.
        blocked, why = self.rx_tx_blocked()
        if not blocked:
            return False, ""
        if why == "previous transmission":
            return True, "Waiting for previous transmission…"
        if why == "active HX reception":
            return True, "Waiting for HX channel to clear…"
        return True, f"Waiting {why}…"

    def show_tx_queue_notice(self, text: str = "TX queued"):
        """Show queued-TX status in the TX panel instead of a floating popup.

        This keeps the operator informed without stealing focus or adding
        another window.  The line is reserved for manual/operator-visible
        queued transmissions; background keepalive/session traffic stays quiet.
        """
        try:
            has_regular_queue = bool(getattr(self, "tx_hold_queue", []))
            has_file_deferred = bool(getattr(self, "file_deferred_manual", []))
            has_profile_deferred = bool(getattr(self, "file_deferred_profile_requests", []))
            if not has_regular_queue and not has_file_deferred and not has_profile_deferred:
                self.tx_queue_status_var.set("")
                return
            self.tx_queue_status_var.set(text)
        except Exception:
            pass

    def close_tx_queue_notice(self):
        try:
            self.tx_queue_status_var.set("")
        except Exception:
            pass
        self.tx_queue_notice = None

    def update_tx_queue_notice(self):
        if getattr(self, "file_deferred_profile_requests", []):
            self.show_tx_queue_notice("REQUEST QUEUED — waiting for outbound file transfer to finish…")
            if getattr(self, "file_tx_active", False):
                self.after(500, self.update_tx_queue_notice)
            return
        if getattr(self, "file_deferred_manual", []):
            first_reason = self.file_deferred_manual[0][3] if self.file_deferred_manual else "manual"
            notice = (
                "MESSAGE QUEUED — waiting for outbound file transfer to finish…"
                if first_reason == "manual"
                else "REQUEST QUEUED — waiting for outbound file transfer to finish…"
            )
            self.show_tx_queue_notice(notice)
            if getattr(self, "file_tx_active", False):
                self.after(500, self.update_tx_queue_notice)
            return
        if not getattr(self, "tx_hold_queue", []):
            self.close_tx_queue_notice()
            return
        queued_reason = self.tx_hold_queue[0][3] if self.tx_hold_queue else ""
        hold, hold_reason = self.should_hold_tx(queued_reason)
        if not hold:
            hold_reason = "TX QUEUED — Channel clear, transmitting shortly…"
        else:
            hold_reason = f"TX QUEUED — {hold_reason}"
        self.show_tx_queue_notice(hold_reason)
        if getattr(self, "tx_hold_queue", []):
            self.after(250, self.update_tx_queue_notice)

    def cancel_tx_hold_queue(self):
        n = len(getattr(self, "tx_hold_queue", []))
        self.tx_hold_queue.clear()
        self.close_tx_queue_notice()
        if n:
            self.qlog(f"Canceled {n} queued TX request(s)", "warn")
            self.q.put(("txprogress", (0.0, "Idle")))
            self.update_statusbar()

    def queue_tx_hold(self, override_message, animate_text, clear_after, reason, override_to) -> bool:
        self.tx_hold_queue.append((override_message, animate_text, clear_after, reason, override_to))
        now = time.time()
        if now - getattr(self, "_tx_hold_notice_time", 0.0) > 2.0:
            self._tx_hold_notice_time = now
            self.qlog(f"TX queued — waiting for HX channel/turnaround ({reason})", "warn")
        self.q.put(("txprogress", (0.0, "TX queued")))
        # Show only for operator-visible actions; keep background keepalive/session chatter quiet.
        if reason in ("manual", "beacon"):
            self.after(0, lambda: self.show_tx_queue_notice("TX QUEUED — waiting…"))
        self.update_statusbar()
        self.after(250, self.process_tx_hold_queue)
        return True

    def process_tx_hold_queue(self):
        if not getattr(self, "tx_hold_queue", []):
            self.close_tx_queue_notice()
            return
        # During post-transfer handoff, old after() callbacks must not release
        # the shared queue. Only the station currently holding the explicit
        # drain token may transmit deferred traffic. This is the key guard that
        # prevents both peers from sending PROFILE_REQ/text at the same time.
        next_reason = self.tx_hold_queue[0][3] if self.tx_hold_queue else ""
        if getattr(self, "post_transfer_drain_active", False):
            phase = str(getattr(self, "post_transfer_phase", "") or "")
            role = str(getattr(self, "post_transfer_role", "") or "")
            allowed = (
                next_reason == "post-transfer-ack"
                or (role == "sender" and phase == "SENDER_DRAINING")
                or (role == "receiver" and phase == "RECEIVER_DRAINING")
            )
            if not allowed:
                self.show_tx_queue_notice("TX QUEUED — waiting for post-transfer token…")
                self.after(250, self.process_tx_hold_queue)
                return
        hold, why = self.should_hold_tx(next_reason)
        if hold:
            self.update_tx_queue_notice()
            self.after(250, self.process_tx_hold_queue)
            return
        override_message, animate_text, clear_after, reason, override_to = self.tx_hold_queue.pop(0)
        self.close_tx_queue_notice()
        self.qlog(f"HX channel clear — transmitting queued {reason}", "ok")
        self.start_background_tx(override_message, animate_text, clear_after, reason, override_to)

    def file_transfer_mode(self) -> str:
        """Choose and lock the mode used for one file transfer.

        If the operator selected a fixed HX mode, that fixed mode is honored.
        If AUTO is selected, HX chooses a conservative effective mode from the
        latest RX SNR before the transfer begins.  That mode is then advertised
        in FILE_OFFER and remains fixed until FILE_DONE / cancel / failure.
        """
        requested = (self.mode_var.get() or "AUTO").strip().upper()
        if requested in ("HX-F", "HX-N"):
            return requested
        return self.auto_mode_from_snr(getattr(self, "last_rx_snr", None), conservative=True)

    def estimate_file_chunk_airtime(self, raw_bytes: int, mode: str, total_chunks: int = 999) -> float:
        """Estimate seconds for one FILE_CHUNK frame carrying raw_bytes payload."""
        raw_bytes = max(1, int(raw_bytes))
        packet = {
            "id": "12345678",
            "chunk": min(999, max(1, total_chunks)),
            "total": max(1, total_chunks),
            "data": base64.b64encode(bytes(raw_bytes)).decode("ascii"),
            "crc": "0" * 16,
        }
        frame = "HXCTL|FILE_CHUNK|" + json.dumps(packet, separators=(",", ":"))
        try:
            return float(estimate_tx_seconds(frame, mode))
        except Exception:
            # Safe fallback if the estimator is unavailable for any reason.
            return 999.0

    def file_chunk_size_for_mode(self, mode: str) -> int:
        """Return a raw-byte chunk size selected by target airtime.

        File transfer should feel predictable on the air.  Instead of fixed
        arbitrary byte sizes, HX estimates how long one FILE_CHUNK frame will
        take in the selected mode and chooses the largest chunk that stays near
        the target airtime.
        """
        mode = (mode or "HX-F").upper()
        targets = {"HX-F": 22.0, "HX-N": 26.0}
        maximums = {"HX-F": 224, "HX-N": 32}
        minimums = {"HX-F": 32, "HX-N": 4}
        target = targets.get(mode, 22.0)
        lo = minimums.get(mode, 8)
        hi = maximums.get(mode, 96)
        best = lo
        while lo <= hi:
            mid = (lo + hi) // 2
            airtime = self.estimate_file_chunk_airtime(mid, mode)
            if airtime <= target:
                best = mid
                lo = mid + 1
            else:
                hi = mid - 1
        return max(1, int(best))

    def file_ack_timeout_for_mode(self, mode: str) -> float:
        # ACK timeout must cover: receiver decode time + ACK transmit airtime +
        # sender decode time + guard margin.  These values are intentionally
        # generous while file transfer is still experimental.
        if mode == "HX-F":
            return 70.0
        if mode == "HX-N":
            return 110.0
        return 160.0

    def wait_for_tx_idle(self, timeout: float = 180.0, label: str = "TX", dest: str = "", ignore_manual_holds: bool = False):
        start = time.time()
        last_log = 0.0
        while time.time() - start < timeout:
            busy = bool(getattr(self, "tx_busy", False))
            queue = list(getattr(self, "tx_hold_queue", []))
            if ignore_manual_holds:
                # A manual chat message may intentionally remain deferred for the
                # entire outbound file transfer.  It must not make a completed
                # FILE_OFFER/CHUNK appear perpetually busy to the file worker.
                blocking = [item for item in queue if len(item) < 4 or item[3] != "manual"]
            else:
                blocking = queue
            qlen = len(queue)
            blocking_len = len(blocking)
            if not busy and blocking_len == 0:
                self.ftlog(f"TX_IDLE observed label={label} elapsed={time.time()-start:.2f}s deferred_manual={qlen-blocking_len}", peer=dest)
                return True
            now = time.time()
            if now - last_log >= 5.0:
                self.ftlog(f"TX_IDLE_WAIT label={label} elapsed={now-start:.1f}s tx_busy={busy} queue={qlen} blocking={blocking_len} hx_busy={getattr(self,'hx_channel_busy',None)} guard={self.tx_guard_remaining():.2f}s", peer=dest)
                last_log = now
            time.sleep(0.15)
        self.ftlog(f"TX_IDLE_TIMEOUT label={label} timeout={timeout}s tx_busy={getattr(self,'tx_busy',None)} queue={len(getattr(self,'tx_hold_queue', []))} hx_busy={getattr(self,'hx_channel_busy',None)} guard={self.tx_guard_remaining():.2f}s", peer=dest)
        return False

    def send_protocol_frame_and_wait(self, text: str, dest: str, label: str = "TX", timeout: float = 240.0, mode_override: str | None = None) -> bool:
        self.ftlog(f"TX_REQUEST label={label} dest={dest} bytes={len(text.encode('utf-8', 'ignore'))} tx_busy={getattr(self, 'tx_busy', None)} queue={len(getattr(self, 'tx_hold_queue', []))} head={text[:140]}", peer=dest)
        try:
            reason = f"protocol@{mode_override}" if mode_override in ("HX-F", "HX-N") else "protocol"
            started = self.start_background_tx(text, animate_text=False, clear_after=False, reason=reason, override_to=dest)
            self.ftlog(f"TX_REQUEST start_background_tx returned {started} label={label} tx_busy={getattr(self, 'tx_busy', None)} queue={len(getattr(self, 'tx_hold_queue', []))}", peer=dest)
        except Exception as e:
            self.ftlog(f"TX_REQUEST exception label={label}: {e}", peer=dest)
            self.qlog(f"{label} TX exception: {e}", "err")
            return False
        # Give the TX scheduler a moment to either start or queue, then wait for completion.
        time.sleep(0.25)
        ok = self.wait_for_tx_idle(timeout=timeout, label=label, dest=dest, ignore_manual_holds=True)
        self.ftlog(f"TX_COMPLETE_WAIT label={label} ok={ok} tx_busy={getattr(self, 'tx_busy', None)} queue={len(getattr(self, 'tx_hold_queue', []))}", peer=dest)
        if not ok:
            self.qlog(f"{label} did not complete before timeout", "err")
        return ok

    def file_state_path(self, peer: str, transfer_id: str) -> str:
        safe_peer = re.sub(r"[^A-Za-z0-9_-]", "_", (peer or "UNKNOWN").upper())
        safe_id = re.sub(r"[^A-Za-z0-9_-]", "_", (transfer_id or "transfer").upper())
        return os.path.join(FILE_STATE_DIR, f"{safe_peer}_{safe_id}.json")

    def find_file_resume_states(self, peer: str) -> list[dict]:
        out = []
        try:
            if not os.path.isdir(FILE_STATE_DIR):
                return out
            safe_peer = re.sub(r"[^A-Za-z0-9_-]", "_", (peer or "UNKNOWN").upper())
            for name in os.listdir(FILE_STATE_DIR):
                if not name.upper().startswith(safe_peer + "_") or not name.lower().endswith(".json"):
                    continue
                path = os.path.join(FILE_STATE_DIR, name)
                try:
                    with open(path, "r", encoding="utf-8") as f:
                        st = json.load(f)
                    if (st.get("direction") or "tx") == "tx":
                        st["_state_path"] = path
                        out.append(st)
                except Exception:
                    continue
            out.sort(key=lambda x: x.get("saved", ""), reverse=True)
        except Exception:
            pass
        return out

    def delete_file_state(self, peer: str, transfer_id: str):
        try:
            path = self.file_state_path(peer, transfer_id)
            if os.path.exists(path):
                os.remove(path)
        except Exception as e:
            self.qlog(f"Could not delete file resume state: {e}", "warn")

    def save_rx_resume_state(self):
        try:
            if not self.file_rx:
                return
            os.makedirs(FILE_STATE_DIR, exist_ok=True)
            peer = self.file_rx.get("peer", "UNKNOWN")
            info = self.file_rx.get("info", {}) or {}
            transfer_id = self.file_rx.get("id") or info.get("id") or "transfer"
            chunks = self.file_rx.get("chunks", {}) or {}
            state = {
                "direction": "rx",
                "peer": peer,
                "id": transfer_id,
                "info": info,
                "path": self.file_rx.get("path", ""),
                "chunks": {str(k): base64.b64encode(v).decode("ascii") for k, v in chunks.items()},
                "next_chunk": (max(chunks.keys()) + 1) if chunks else 1,
                "session_uuid": self.session_uuid,
                "saved": time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime()),
            }
            with open(self.file_state_path(peer, transfer_id) + ".rx", "w", encoding="utf-8") as f:
                json.dump(state, f, indent=2)
        except Exception as e:
            self.qlog(f"Could not save incoming file resume state: {e}", "warn")

    def load_rx_resume_state(self, peer: str, transfer_id: str) -> dict | None:
        try:
            path = self.file_state_path(peer, transfer_id) + ".rx"
            if not os.path.exists(path):
                return None
            with open(path, "r", encoding="utf-8") as f:
                st = json.load(f)
            return st
        except Exception:
            return None

    def delete_rx_resume_state(self, peer: str, transfer_id: str):
        try:
            path = self.file_state_path(peer, transfer_id) + ".rx"
            if os.path.exists(path):
                os.remove(path)
        except Exception:
            pass

    def start_file_send(self):
        self.ftlog(f"UI Send File clicked session_active={self.session_active} peer={getattr(self, 'session_peer', '')} tx_active={self.file_tx_active} rx_active={self.file_rx_active}")
        if not self.session_active:
            self.show_info("HX File Transfer", "Connect to a station before sending a file.")
            return
        if self.file_tx_active or self.file_rx_active:
            self.show_info("HX File Transfer", "A file transfer is already active.")
            return

        peer = self.session_peer
        resume_states = self.find_file_resume_states(peer)
        if resume_states:
            st = resume_states[0]
            r_path = st.get("path", "")
            r_name = st.get("name") or os.path.basename(r_path) or "file"
            r_next = int(st.get("next_chunk", 1) or 1)
            r_chunks = int(st.get("chunks", 0) or 0)
            if r_path and os.path.exists(r_path):
                ans = self.ask_yes_no_cancel(
                    "HX File Transfer Resume",
                    f"Incomplete transfer found with {peer}.\n\n{r_name}\nNext chunk: {r_next} of {r_chunks}\n\nYes = Resume\nNo = Start a different file\nCancel = Do nothing"
                )
                if ans is None:
                    return
                if ans:
                    self.file_tx_cancel = False
                    self.ftlog(f"UI resume selected path={r_path} id={st.get('id')} next_chunk={r_next}")
                    threading.Thread(target=self.file_send_worker, args=(r_path, st), daemon=True, name="HXFileTX").start()
                    return
            else:
                try:
                    os.remove(st.get("_state_path", ""))
                except Exception:
                    pass

        path = filedialog.askopenfilename(title="Select file to send over HX")
        if not path:
            return
        try:
            size = os.path.getsize(path)
        except Exception as e:
            self.show_error("HX File Transfer", f"Unable to read file:\n{e}")
            return
        mode = self.file_transfer_mode()
        chunk_size = self.file_chunk_size_for_mode(mode)
        chunks = max(1, (size + chunk_size - 1) // chunk_size)
        if not self.ask_yes_no(
            "HX File Transfer",
            f"Send file to {self.session_peer}?\n\n{os.path.basename(path)}\n{size} bytes\n{chunks} chunks using {mode}\nApprox. {self.estimate_file_chunk_airtime(chunk_size, mode):.0f}s per chunk\n\nContinue?"
        ):
            return
        self.file_tx_cancel = False
        self.ftlog(f"UI selected file path={path} size={os.path.getsize(path) if os.path.exists(path) else 'missing'}")
        threading.Thread(target=self.file_send_worker, args=(path,), daemon=True, name="HXFileTX").start()

    def cancel_file_transfer(self):
        if self.file_tx_active:
            # Do not interrupt the current FILE_CHUNK / FILE_ACK exchange.  A
            # local cancel is a high-priority file command, but it must still
            # wait for the peer's current ACK transmission and the normal
            # post-RX turnaround guard.  Waking the ACK wait here used to make
            # FILE_CANCEL transmit on top of the peer's ACK.
            if not self.file_tx_cancel_pending and not self.file_tx_cancel_sending:
                self.file_tx_cancel_pending = True
                self.file_tx_cancel_origin = "local"
                self.add_session_event("File transfer cancellation queued")
                self.ftlog(
                    f"TX_CANCEL queued id={self.file_tx_id or '--'} peer={self.file_tx_peer or self.session_peer or '--'}; "
                    "waiting for current ACK/turnaround",
                    self.file_tx_id,
                    self.file_tx_peer or self.session_peer,
                )
                self.q.put(("txprogress", (0.0, "Cancelling...")))
                try:
                    self.cancel_file_button.configure(state="disabled")
                except Exception:
                    pass
        if self.file_rx_active and self.file_rx:
            sid = (self.file_rx.get("id", "") or "").strip().upper()
            peer = self.file_rx.get("peer", self.session_peer)
            if sid:
                self.file_rx_cancel_pending.add(sid)
            # Stop accepting/ACKing this transfer immediately in the UI.  The
            # FILE_CANCEL frame is sent asynchronously at the first safe TX
            # opportunity after the current receive burst completes.
            self.file_rx_active = False
            self.file_rx = None
            self.release_file_awake("rx")
            self.add_session_event(f"Incoming file cancellation requested; notifying {peer}")
            self.ftlog(f"RX_CANCEL local request id={sid}; FILE_CANCEL queued for {peer}", sid, peer)
            def _send_cancel():
                ok = self.send_protocol_frame_and_wait(f"HXCTL|FILE_CANCEL|{sid}", peer, "FILE_CANCEL", timeout=60.0)
                self.ftlog(f"RX_CANCEL FILE_CANCEL sent ok={ok}", sid, peer)
                if ok:
                    self.add_session_event(f"File transfer cancelled; {peer} notified")
                else:
                    self.add_session_event(f"File cancellation pending; unable to notify {peer} yet")
            threading.Thread(target=_send_cancel, name="HXFileCancelTX", daemon=True).start()
        self.update_session_controls()

    def _send_local_file_cancel_safely(self, peer: str, transfer_id: str, mode: str, next_chunk: int, offer: dict | None = None) -> None:
        """Send FILE_CANCEL only after the active chunk/ACK exchange is clear.

        This routine is called by the outbound file worker, so FILE_CANCEL stays
        inside the file-transfer TX owner and cannot race an incoming FILE_ACK.
        """
        if not self.file_tx_cancel_pending:
            return
        if self.file_tx_cancel_sending:
            return
        self.file_tx_cancel_sending = True
        try:
            if offer is not None:
                try:
                    self.save_file_resume_state(peer, offer, next_chunk, getattr(self, "_file_tx_path", ""))
                except Exception as e:
                    self.ftlog(f"TX_CANCEL could not save resume state next_chunk={next_chunk}: {e}", transfer_id, peer)
            self.add_session_event("Waiting for safe transmit window to cancel file transfer")
            self.ftlog(
                f"TX_CANCEL safe-wait begin next_chunk={next_chunk} "
                f"tx_busy={getattr(self,'tx_busy',None)} hx_busy={getattr(self,'hx_channel_busy',None)} "
                f"guard={self.tx_guard_remaining():.2f}s",
                transfer_id,
                peer,
            )
            # send_protocol_frame_and_wait enters the normal HX scheduler.  If
            # the peer is still sending the ACK, should_hold_tx() queues this
            # frame until RX completes and the turnaround guard expires.
            ok = self.send_protocol_frame_and_wait(
                f"HXCTL|FILE_CANCEL|{transfer_id}",
                peer,
                "FILE_CANCEL",
                timeout=max(90.0, self.file_ack_timeout_for_mode(mode)),
                mode_override=mode,
            )
            self.ftlog(f"TX_CANCEL sent ok={ok}", transfer_id, peer)
            self.file_tx_cancel = True
            self.file_tx_cancel_pending = False
            if ok:
                self.add_session_event(f"File transfer cancelled; {peer} notified")
            else:
                self.add_session_event(f"File transfer cancelled locally; unable to confirm notification to {peer}")
        finally:
            self.file_tx_cancel_sending = False

    def file_send_worker(self, path: str, resume_state: dict | None = None):
        self.ftlog(f"TX_WORKER start path={path}")
        peer = self.session_peer
        tx_session_uuid = self.session_uuid
        tx_session_id = self.session_id
        mode = (resume_state or {}).get("mode") or self.file_transfer_mode()
        transfer_id = ((resume_state or {}).get("id") or uuid.uuid4().hex[:8]).upper()
        resume_next_chunk = max(1, int((resume_state or {}).get("next_chunk", 1) or 1))
        self.file_tx_active = True
        self.file_tx_cancel_pending = False
        self.file_tx_cancel_sending = False
        self.file_tx_accept_announced = False
        self._file_tx_path = path
        self.file_tx_id = transfer_id
        self.file_tx_peer = peer
        # Marshal onto the persistent Tk thread; this prevents Windows sleep
        # and screensaver/display power-down for the complete outbound transfer.
        self.after(0, lambda: self.acquire_file_awake("tx"))
        self.file_tx_ack_result = None
        self.file_tx_ack_chunk = -1
        self.update_session_controls()

        def _session_still_valid() -> bool:
            return (
                (not self.file_tx_cancel)
                and bool(self.session_active)
                and (self.session_peer == peer)
                and (self.session_uuid == tx_session_uuid)
                and (self.session_id == tx_session_id)
            )

        def _abort_if_session_changed(next_chunk: int, offer_info: dict | None = None):
            if _session_still_valid():
                return
            if self.file_tx_cancel:
                if self.file_tx_cancel_origin == "remote" or self.file_tx_ack_result == "CANCEL":
                    raise RuntimeError(f"file transfer cancelled by {peer}")
                raise RuntimeError("file transfer cancelled locally")
            if offer_info is not None:
                try:
                    self.save_file_resume_state(peer, offer_info, next_chunk, path)
                except Exception as e:
                    self.ftlog(f"TX_SESSION_GUARD could not save resume state next_chunk={next_chunk}: {e}", transfer_id, peer)
            self.ftlog(
                f"TX_SESSION_GUARD aborting stale file worker next_chunk={next_chunk} "
                f"active={self.session_active} peer_now={self.session_peer} "
                f"uuid_start={tx_session_uuid} uuid_now={self.session_uuid}",
                transfer_id, peer,
            )
            raise RuntimeError("file transfer stopped because session changed")

        try:
            data = Path(path).read_bytes()
            self.ftlog(f"TX_WORKER loaded file name={os.path.basename(path)} size={len(data)}", transfer_id, peer)
            size = len(data)
            chunk_size = self.file_chunk_size_for_mode(mode)
            chunks = max(1, (size + chunk_size - 1) // chunk_size)
            sha = hashlib.sha256(data).hexdigest()
            transfer_started = time.time()
            offer = {
                "id": transfer_id,
                "name": os.path.basename(path),
                "size": size,
                "chunks": chunks,
                "chunk_size": chunk_size,
                "sha256": sha,
                "mode": mode,
                "resume": bool(resume_state),
                "resume_from": resume_next_chunk,
                **self.file_exchange_metadata(peer),
            }
            self.ftlog(f"TX_OFFER prepared name={offer['name']} size={size} chunks={chunks} chunk_size={chunk_size} mode={mode} resume={bool(resume_state)} resume_from={resume_next_chunk} chunk_airtime={self.estimate_file_chunk_airtime(chunk_size, mode):.2f}s sha={sha}", transfer_id, peer)
            self.add_session_event(f"File mode {mode}, chunk {chunk_size} bytes, ~{self.estimate_file_chunk_airtime(chunk_size, mode):.0f}s/chunk")
            self.add_session_event(f"File offer to {peer}: {offer['name']} ({size} bytes, {chunks} chunks)")
            self.q.put(("txprogress", (0.0, f"Offering {offer['name']}")))
            _abort_if_session_changed(resume_next_chunk, offer)
            self.file_tx_ack_event.clear()
            if not self.send_protocol_frame_and_wait("HXCTL|FILE_OFFER|" + json.dumps(offer, separators=(",", ":")), peer, "FILE_OFFER", mode_override=mode):
                self.ftlog("TX_OFFER transmit failed", transfer_id, peer)
                raise RuntimeError("file offer TX failed")
            offer_timeout = max(180.0, self.file_ack_timeout_for_mode(mode))
            self.ftlog(f"TX_OFFER sent; waiting for ACCEPT timeout={offer_timeout}", transfer_id, peer)
            accepted = self.file_tx_ack_event.wait(offer_timeout)
            self.ftlog(f"TX_OFFER wait done event={accepted} result={self.file_tx_ack_result}", transfer_id, peer)
            if self.file_tx_cancel_pending:
                self._send_local_file_cancel_safely(peer, transfer_id, mode, resume_next_chunk, offer)
                raise RuntimeError("file transfer cancelled locally")
            _abort_if_session_changed(resume_next_chunk, offer)
            if not accepted or self.file_tx_ack_result != "ACCEPT":
                if self.file_tx_ack_result == "REJECT":
                    raise RuntimeError("receiver rejected file")
                raise RuntimeError("no file accept ACK")
            start_idx = max(0, min(chunks - 1, int(getattr(self, "file_tx_resume_from", resume_next_chunk) or resume_next_chunk) - 1))
            if start_idx > 0:
                self.add_session_event(f"Resuming file transfer at chunk {start_idx + 1}/{chunks}")
                self.ftlog(f"TX_RESUME starting at chunk={start_idx + 1}/{chunks}", transfer_id, peer)
            for idx in range(start_idx, chunks):
                if self.file_tx_cancel_pending:
                    self._send_local_file_cancel_safely(peer, transfer_id, mode, idx + 1, offer)
                    raise RuntimeError("file transfer cancelled locally")
                if self.file_tx_cancel:
                    self.save_file_resume_state(peer, offer, idx + 1, path)
                    if self.file_tx_cancel_origin == "remote":
                        raise RuntimeError(f"file transfer cancelled by {peer}")
                    raise RuntimeError("file transfer cancelled")
                _abort_if_session_changed(idx + 1, offer)
                raw = data[idx * chunk_size:(idx + 1) * chunk_size]
                packet = {
                    "id": transfer_id,
                    "chunk": idx + 1,
                    "total": chunks,
                    "data": base64.b64encode(raw).decode("ascii"),
                    "crc": hashlib.sha256(raw).hexdigest()[:16],
                }
                attempts = 0
                while attempts < 3:
                    _abort_if_session_changed(idx + 1, offer)
                    attempts += 1
                    pct = ((idx) / chunks) * 100.0
                    self.q.put(("txprogress", (pct, f"File chunk {idx+1}/{chunks} TX attempt {attempts}")))
                    self.add_session_event(f"File chunk {idx+1}/{chunks} sent; waiting ACK")
                    self.file_tx_ack_result = None
                    self.file_tx_ack_chunk = -1
                    self.file_tx_ack_event.clear()
                    self.ftlog(f"TX_CHUNK attempt={attempts} chunk={idx+1}/{chunks} raw_bytes={len(raw)} payload_chars={len(json.dumps(packet, separators=(',', ':')))}", transfer_id, peer)
                    if not self.send_protocol_frame_and_wait("HXCTL|FILE_CHUNK|" + json.dumps(packet, separators=(",", ":")), peer, "FILE_CHUNK", mode_override=mode):
                        self.qlog(f"File chunk {idx+1} TX completion timeout", "err")
                    timeout = self.file_ack_timeout_for_mode(mode)
                    self.ftlog(f"TX_CHUNK sent chunk={idx+1}; waiting ACK timeout={timeout}", transfer_id, peer)
                    got = self.file_tx_ack_event.wait(timeout)
                    self.ftlog(f"TX_CHUNK wait result chunk={idx+1} event={got} result={self.file_tx_ack_result} ack_chunk={self.file_tx_ack_chunk}", transfer_id, peer)
                    if self.file_tx_cancel_pending:
                        # If an ACK was received, the RX state machine has also
                        # established the post-RX guard.  If no ACK arrived, the
                        # timeout still prevents an immediate collision with the
                        # peer's expected response window.
                        self._send_local_file_cancel_safely(peer, transfer_id, mode, idx + 1, offer)
                        raise RuntimeError("file transfer cancelled locally")
                    _abort_if_session_changed(idx + 1, offer)
                    if got and self.file_tx_ack_result == "ACK" and self.file_tx_ack_chunk == idx + 1:
                        pct = ((idx + 1) / chunks) * 100.0
                        self.q.put(("txprogress", (pct, f"ACK {idx+1}/{chunks}")))
                        self.save_file_resume_state(peer, offer, idx + 2, path)
                        break
                    self.add_session_event(f"File chunk {idx+1}/{chunks} retry {attempts}/3")
                else:
                    self.save_file_resume_state(peer, offer, idx + 1, path)
                    raise RuntimeError(f"no ACK for chunk {idx+1}")
            if self.file_tx_cancel_pending:
                self._send_local_file_cancel_safely(peer, transfer_id, mode, chunks + 1, offer)
                raise RuntimeError("file transfer cancelled locally")
            _abort_if_session_changed(chunks + 1, offer)
            done = {"id": transfer_id, "sha256": sha, "chunks": chunks, "size": size, "name": os.path.basename(path)}
            self.ftlog(f"TX_DONE sending done={done}", transfer_id, peer)
            self.send_protocol_frame_and_wait("HXCTL|FILE_DONE|" + json.dumps(done, separators=(",", ":")), peer, "FILE_DONE", mode_override=mode)
            elapsed = max(0.1, time.time() - transfer_started)
            rate = size / elapsed
            self.ftlog(f"TX_STATS completed size={size} elapsed={elapsed:.1f}s rate={rate:.2f}Bps chunks={chunks} mode={mode}", transfer_id, peer)
            self.add_session_event(f"File transfer completed: {os.path.basename(path)} ({rate:.1f} B/s)")
            self.q.put(("txprogress", (100.0, f"File transfer completed ({rate:.1f} B/s)")))
            # Receive-side completion uses the remote sender callsign (`call`).
            # `peer` is not defined in this handler and previously caused a false
            # "File receive failed" message after the file had been written.
            self.delete_file_state(peer, transfer_id)
            threading.Thread(target=self.speak_text, args=("File transfer completed",), daemon=True).start()
        except Exception as e:
            self.ftlog(f"TX_WORKER exception: {e}")
            error_text = str(e)
            if error_text == "receiver rejected file":
                # FILE_REJECT already announced "File transfer not accepted"
                # when it was received. Do not follow it with the misleading
                # generic failure announcement reserved for timeout/no-ACK cases.
                self.add_session_event("File transfer not accepted by remote station")
                self.q.put(("txprogress", (0.0, "File transfer not accepted")))
            elif error_text == "file transfer cancelled locally":
                self.add_session_event("File transfer cancelled locally")
                self.q.put(("txprogress", (0.0, "File transfer cancelled")))
            elif error_text.startswith("file transfer cancelled by "):
                # A deliberate remote cancellation is not a transfer failure.
                # Preserve the peer in the session log and announce cancellation
                # distinctly from timeout/no-ACK failures.
                self.add_session_event(error_text[:1].upper() + error_text[1:])
                self.q.put(("txprogress", (0.0, "File transfer cancelled")))
                threading.Thread(target=self.speak_text, args=("File transfer cancelled",), daemon=True).start()
            else:
                self.add_session_event(f"File transfer failed: {e}")
                self.q.put(("txprogress", (0.0, "File transfer failed")))
                threading.Thread(target=self.speak_text, args=("File transfer failed",), daemon=True).start()
        finally:
            self.ftlog(f"TX_WORKER finally active={self.file_tx_active} cancel={self.file_tx_cancel}")
            self.after(0, lambda: self.release_file_awake("tx"))
            self.file_tx_active = False
            self.file_tx_cancel = False
            self.file_tx_cancel_pending = False
            self.file_tx_cancel_sending = False
            self.file_tx_cancel_origin = ""
            self._file_tx_path = ""
            self.file_tx_id = ""
            self.file_tx_peer = ""
            self.file_tx_accept_announced = False
            self.update_session_controls()
            self.release_post_file_deferred("sender")
            self.after(2500, lambda: self.q.put(("txprogress", (0.0, "Idle"))))

    def _finish_post_transfer_drain(self, reason: str = "complete"):
        now = time.time()
        self.post_transfer_drain_active = False
        self.post_transfer_role = ""
        self.post_transfer_phase = ""
        self.post_transfer_release_started = False
        self.post_transfer_keepalive_resume_at = 0.0
        self.post_transfer_token_sent_at = 0.0
        self.post_transfer_token_retries = 0
        self.post_transfer_remote_done = False
        self.post_transfer_token_acked = False
        self.post_transfer_ack_role = ""
        self.last_keepalive_sent = now
        self.close_tx_queue_notice()
        self.ftlog(f"POST_TRANSFER_DRAIN complete reason={reason}; keepalives resumed")

    def _send_post_transfer_token(self, role: str) -> bool:
        peer = (getattr(self, "session_peer", "") or "").strip().upper()
        if not peer or not getattr(self, "session_active", False):
            self._finish_post_transfer_drain("session ended")
            return False
        payload = json.dumps({
            "sid": (getattr(self, "session_id", "") or "").strip().upper(),
            "role": str(role or "").strip().lower(),
        }, separators=(",", ":"))
        ok = self.start_background_tx(
            f"HXCTL|POST_DRAIN_DONE|{payload}",
            animate_text=False,
            clear_after=False,
            reason="post-transfer-token",
            override_to=peer,
        )
        if ok:
            self.post_transfer_token_acked = False
            self.post_transfer_ack_role = ""
            self.post_transfer_token_sent_at = time.time()
            self.post_transfer_token_retries += 1
            self.ftlog(
                f"POST_TRANSFER_TOKEN sent role={role} retry={self.post_transfer_token_retries}",
                peer=peer,
            )
        return bool(ok)

    def _post_transfer_drain_tick(self, now: float | None = None):
        """Drain deferred traffic using an explicit two-station token handoff.

        The original file sender drains first and sends POST_DRAIN_DONE.  The
        receiver does not release anything until that frame is decoded.  After
        its own queue drains, the receiver returns POST_DRAIN_DONE.  Keepalives
        remain suspended until the exchange finishes.
        """
        now = float(now or time.time())
        if not getattr(self, "post_transfer_drain_active", False):
            return
        if getattr(self, "file_tx_active", False) or getattr(self, "file_rx_active", False):
            return
        if getattr(self, "hx_channel_busy", False) or getattr(self, "tx_busy", False):
            self.post_transfer_quiet_since = now
            return
        if self.tx_guard_remaining() > 0.0:
            return

        phase = str(getattr(self, "post_transfer_phase", "") or "")
        quiet_for = now - float(getattr(self, "post_transfer_quiet_since", 0.0) or now)
        queues_empty = not bool(getattr(self, "tx_hold_queue", []))

        if phase == "SENDER_WAIT_RELEASE":
            if now < float(getattr(self, "post_transfer_not_before", 0.0) or 0.0) or quiet_for < 2.0:
                return
            self.post_transfer_release_started = True
            self.post_transfer_phase = "SENDER_DRAINING"
            self.ftlog(f"POST_TRANSFER_DRAIN sender release quiet={quiet_for:.1f}s")
            if not queues_empty:
                self.process_tx_hold_queue()
            return

        if phase == "SENDER_DRAINING":
            if not queues_empty:
                self.process_tx_hold_queue()
                return
            # Allow replies generated by our deferred requests to arrive before
            # handing the channel to the receiver.
            if quiet_for < 3.0:
                return
            if self._send_post_transfer_token("sender"):
                self.post_transfer_phase = "SENDER_WAIT_TOKEN_ACK"
            return

        if phase == "SENDER_WAIT_TOKEN_ACK":
            if self.post_transfer_token_acked and self.post_transfer_ack_role == "sender":
                self.post_transfer_phase = "SENDER_WAIT_RECEIVER_DONE"
                return
            sent_at = float(getattr(self, "post_transfer_token_sent_at", 0.0) or 0.0)
            if sent_at and now - sent_at >= 20.0 and quiet_for >= 3.0:
                self._send_post_transfer_token("sender")
            return

        if phase == "SENDER_WAIT_RECEIVER_DONE":
            return

        if phase == "SENDER_ACKING_RECEIVER":
            if not self.tx_busy and quiet_for >= 2.0:
                self._finish_post_transfer_drain("receiver token acknowledged")
            return

        if phase == "RECEIVER_WAIT_TOKEN":
            # No timer-based release here: the explicit sender token is the
            # authority that prevents symmetric transmissions.
            return

        if phase == "RECEIVER_ACKING_SENDER":
            if self.tx_busy or quiet_for < 2.0:
                return
            self.post_transfer_phase = "RECEIVER_WAIT_RELEASE"
            self.post_transfer_not_before = now + 1.0
            return

        if phase == "RECEIVER_WAIT_RELEASE":
            if now < float(getattr(self, "post_transfer_not_before", 0.0) or 0.0) or quiet_for < 2.0:
                return
            self.post_transfer_release_started = True
            self.post_transfer_phase = "RECEIVER_DRAINING"
            self.ftlog(f"POST_TRANSFER_DRAIN receiver release quiet={quiet_for:.1f}s")
            if not queues_empty:
                self.process_tx_hold_queue()
            return

        if phase == "RECEIVER_DRAINING":
            if not queues_empty:
                self.process_tx_hold_queue()
                return
            if quiet_for < 3.0:
                return
            if self._send_post_transfer_token("receiver"):
                self.post_transfer_phase = "RECEIVER_WAIT_TOKEN_ACK"
            return

        if phase == "RECEIVER_WAIT_TOKEN_ACK":
            if self.post_transfer_token_acked and self.post_transfer_ack_role == "receiver":
                self._finish_post_transfer_drain("receiver token acknowledged")
                return
            sent_at = float(getattr(self, "post_transfer_token_sent_at", 0.0) or 0.0)
            if sent_at and now - sent_at >= 20.0 and quiet_for >= 3.0:
                self._send_post_transfer_token("receiver")
            return

    def release_post_file_deferred(self, role: str):
        """Return directly to normal operation after file ownership ends.

        Operator text, profile requests and SNR requests are disabled throughout
        the transfer, so there is no deferred user queue to arbitrate and no
        POST_DRAIN control traffic is required.
        """
        self.file_deferred_profile_requests.clear()
        self.file_deferred_manual.clear()
        self.tx_hold_queue.clear()
        self.post_transfer_drain_active = False
        self.post_transfer_role = ""
        self.post_transfer_phase = ""
        self.post_transfer_release_started = False
        self.post_transfer_token_sent_at = 0.0
        self.post_transfer_token_retries = 0
        self.post_transfer_token_acked = False
        self.post_transfer_ack_role = ""
        self.last_keepalive_sent = time.time()
        self.close_tx_queue_notice()
        self.ftlog(f"FILE_TRANSFER ownership released role={role}; no post-drain RF frames")
        self.after(0, self.update_session_controls)

    def save_file_resume_state(self, peer: str, offer: dict, next_chunk: int, path: str = ""):
        try:
            os.makedirs(FILE_STATE_DIR, exist_ok=True)
            chunks = int(offer.get("chunks", 0) or 0)
            if chunks and next_chunk > chunks:
                self.delete_file_state(peer, offer.get("id", "transfer"))
                return
            state = dict(offer)
            state.update({
                "direction": "tx",
                "peer": peer,
                "path": path,
                "next_chunk": max(1, int(next_chunk)),
                "session_uuid": self.session_uuid,
                "saved": time.strftime("%Y-%m-%d %H:%M:%S", time.gmtime()),
            })
            with open(self.file_state_path(peer, offer.get('id','transfer')), "w", encoding="utf-8") as f:
                json.dump(state, f, indent=2)
            self.ftlog(f"TX_RESUME_STATE saved next_chunk={state['next_chunk']} path={path}", offer.get("id", ""), peer)
        except Exception as e:
            self.qlog(f"Could not save file resume state: {e}", "err")

    def timed_file_offer_prompt(self, call: str, name: str, size: int, chunks: int, resume_next: int, timeout_seconds: int = 45) -> bool:
        """Modal YES/NO file-offer dialog that auto-rejects on timeout."""
        result = {"accepted": False, "done": False}
        dlg = tk.Toplevel(self)
        dlg.title("HX File Transfer")
        dlg.transient(self)
        dlg.resizable(False, False)
        try:
            dlg.grab_set()
        except Exception:
            pass
        body = ttk.Frame(dlg, padding=16)
        body.pack(fill="both", expand=True)
        text = f"{call} is sending you {name}.\n\n{size} bytes, {chunks} chunks."
        if resume_next > 1:
            text += f"\n\nPartial transfer found. Resume from chunk {resume_next}?"
        text += "\n\nAccept?"
        ttk.Label(body, text=text, justify="left", wraplength=430).pack(anchor="w")
        countdown = tk.StringVar(value=f"Automatically rejecting in {timeout_seconds} seconds")
        ttk.Label(body, textvariable=countdown).pack(anchor="w", pady=(12, 8))
        row = ttk.Frame(body)
        row.pack(fill="x", pady=(4, 0))
        def finish(value: bool):
            if result["done"]:
                return
            result["accepted"] = bool(value)
            result["done"] = True
            try:
                dlg.grab_release()
            except Exception:
                pass
            dlg.destroy()
        ttk.Button(row, text="NO", command=lambda: finish(False)).pack(side="right")
        ttk.Button(row, text="YES", command=lambda: finish(True)).pack(side="right", padx=(0, 8))
        dlg.protocol("WM_DELETE_WINDOW", lambda: finish(False))
        dlg.bind("<Return>", lambda _e: finish(True))
        dlg.bind("<KP_Enter>", lambda _e: finish(True))
        deadline = time.monotonic() + max(5, int(timeout_seconds))
        def tick():
            if result["done"] or not dlg.winfo_exists():
                return
            left = max(0, int(deadline - time.monotonic() + 0.999))
            countdown.set(f"Automatically rejecting in {left} second{'s' if left != 1 else ''}")
            if left <= 0:
                self.ftlog(f"RX_OFFER dialog timeout auto-reject call={call} name={name}")
                finish(False)
                return
            dlg.after(250, tick)
        tick()
        dlg.update_idletasks()
        try:
            x = self.winfo_rootx() + max(0, (self.winfo_width() - dlg.winfo_reqwidth()) // 2)
            y = self.winfo_rooty() + max(0, (self.winfo_height() - dlg.winfo_reqheight()) // 2)
            dlg.geometry(f"+{x}+{y}")
        except Exception:
            pass
        self.wait_window(dlg)
        return bool(result["accepted"])

    def send_file_reject_async(self, call: str, sid: str, timeout: float = 60.0, reason: str = "busy"):
        """Queue FILE_REJECT without ever blocking the Tk main thread.

        The earlier synchronous busy-reject path waited inside MainThread while
        the queued frame needed Tk ``after`` callbacks to clear its guard. That
        deadlocked the queue until timeout and made the peer appear frozen in RX.
        """
        def _worker():
            self.ftlog(f"RX_OFFER FILE_REJECT async start reason={reason}", sid, call)
            ok = self.send_protocol_frame_and_wait(
                f"HXCTL|FILE_REJECT|{sid}", call, "FILE_REJECT", timeout=timeout
            )
            self.ftlog(f"RX_OFFER FILE_REJECT async done ok={ok} reason={reason}", sid, call)
        threading.Thread(target=_worker, name="HXFileRejectTX", daemon=True).start()

    def handle_file_offer_ui(self, call: str, sid: str, info: dict):
        self.ftlog(f"RX_OFFER_UI call={call} sid={sid} info={info}", sid, call)
        name = info.get("name", "file")
        size = int(info.get("size", 0) or 0)
        chunks = int(info.get("chunks", 0) or 0)
        if self.file_rx_active and self.file_rx:
            old_peer = (self.file_rx.get("peer", "") or "").strip().upper()
            old_chunks = self.file_rx.get("chunks", {}) or {}
            old_info = self.file_rx.get("info", {}) or {}
            old_sha = (old_info.get("sha256") or "").strip().lower()
            new_sha = (info.get("sha256") or "").strip().lower()
            old_age = time.time() - float(self.file_rx.get("last_activity", self.file_rx.get("started", time.time())) or time.time())
            same_file = bool(old_sha and new_sha and old_sha == new_sha)
            # Replace stale receive ownership from the same peer/file. This is
            # common after a cancelled or timed-out resume attempt: saved chunks
            # may exist, but no transfer traffic has occurred for a long time.
            stale_same_transfer = old_peer == call and same_file and old_age >= 60.0
            orphan_without_chunks = old_peer == call and not old_chunks and old_age >= 30.0
            if stale_same_transfer or orphan_without_chunks:
                why = "stale same-file state" if stale_same_transfer else "orphaned empty state"
                self.ftlog(
                    f"RX_OFFER clearing {why} old_id={self.file_rx.get('id')} age={old_age:.1f}s chunks={len(old_chunks)}",
                    sid, call
                )
                self.file_rx_active = False
                self.file_rx = None
                self.release_file_awake("rx")
            else:
                self.ftlog(f"RX_OFFER rejected busy rx_active={self.file_rx_active} tx_active={self.file_tx_active}", sid, call)
                self.send_file_reject_async(call, sid, timeout=60.0, reason="receive busy")
                return
        if self.file_tx_active:
            self.ftlog(f"RX_OFFER rejected busy rx_active={self.file_rx_active} tx_active={self.file_tx_active}", sid, call)
            self.send_file_reject_async(call, sid, timeout=60.0, reason="transmit busy")
            return

        rx_state = self.load_rx_resume_state(call, sid)
        resume_chunks = {}
        resume_path = ""
        resume_next = 1
        if rx_state and (rx_state.get("info", {}) or {}).get("sha256") == info.get("sha256"):
            try:
                resume_chunks = {int(k): base64.b64decode(v) for k, v in (rx_state.get("chunks", {}) or {}).items()}
                resume_next = (max(resume_chunks.keys()) + 1) if resume_chunks else 1
                resume_path = rx_state.get("path", "")
            except Exception:
                resume_chunks = {}
                resume_next = 1
                resume_path = ""

        prompt = f"{call} is sending you {name}.\n\n{size} bytes, {chunks} chunks."
        if resume_next > 1:
            prompt += f"\n\nPartial transfer found. Resume from chunk {resume_next}?"
        prompt += "\n\nAccept?"
        accepted = self.timed_file_offer_prompt(call, name, size, chunks, resume_next, timeout_seconds=45)
        self.ftlog(f"RX_OFFER user_response accepted={accepted} resume_next={resume_next}", sid, call)
        if not accepted:
            # Send away from the Tk thread so the dialog closes immediately and
            # queued turnaround callbacks remain free to run.
            self.send_file_reject_async(call, sid, timeout=60.0, reason="operator reject/timeout")
            self.add_session_event(f"Incoming file offer rejected or timed out: {name}")
            return
        os.makedirs(getattr(self, "receive_dir", RECEIVE_DIR), exist_ok=True)
        if resume_path:
            path = resume_path
        else:
            safe = re.sub(r"[^A-Za-z0-9._ -]", "_", os.path.basename(name)) or "received_file"
            path = os.path.join(getattr(self, "receive_dir", RECEIVE_DIR), safe)
            if os.path.exists(path):
                stem, ext = os.path.splitext(path)
                path = stem + "_" + time.strftime("%Y%m%d_%H%M%S", time.gmtime()) + ext
        self.file_rx = {"id": sid, "peer": call, "info": info, "path": path, "chunks": resume_chunks, "started": time.time(), "last_activity": time.time()}
        self.file_rx_active = True
        self.acquire_file_awake("rx")
        self.ftlog(f"RX_OFFER accepted path={path}; sending FILE_ACCEPT next_chunk={resume_next}", sid, call)
        self.add_session_event(f"Incoming file accepted: {name} ({size} bytes)" + (f"; resume chunk {resume_next}" if resume_next > 1 else ""))
        self.update_session_controls()
        def _send_accept():
            accept = {"id": sid, "next_chunk": resume_next, **self.file_exchange_metadata(call)}
            ok = self.send_protocol_frame_and_wait("HXCTL|FILE_ACCEPT|" + json.dumps(accept, separators=(",", ":")), call, "FILE_ACCEPT", timeout=60.0, mode_override=(info.get("mode") if isinstance(info, dict) else None))
            self.ftlog(f"RX_OFFER FILE_ACCEPT sent ok={ok} next_chunk={resume_next}", sid, call)
            if not ok:
                self.qlog("FILE_ACCEPT did not complete; see traffic / file debug log", "err")
        threading.Thread(target=_send_accept, name="HXFileAcceptTX", daemon=True).start()

    def handle_file_chunk_rx(self, call: str, sid: str, msg: str):
        self.ftlog(f"RX_CHUNK handler enter call={call} sid={sid} msg_len={len(msg)}", sid, call)
        raw = msg.split("|", 2)[2] if msg.count("|") >= 2 else "{}"
        try:
            packet = json.loads(raw)
            transfer_id = (packet.get("id") or "").strip().upper()
            idx = int(packet.get("chunk", 0))
            if transfer_id in self.file_rx_cancel_pending:
                self.ftlog(f"RX_CHUNK ignored after local cancel idx={idx}; no ACK/NACK", transfer_id, call)
                return
            if not self.file_rx_active or not self.file_rx or self.file_rx.get("id") != transfer_id:
                self.ftlog(f"RX_CHUNK unexpected transfer_id={transfer_id} active={self.file_rx_active} current={(self.file_rx or {}).get('id')}", transfer_id, call)
                if not self.session_active:
                    self.ftlog(f"RX_CHUNK ignored without NACK because no active session with {call}", transfer_id, call)
                    return
                nack = {"id": transfer_id, "chunk": idx if idx else -1}
                self.send_protocol_frame_and_wait("HXCTL|FILE_NACK|" + json.dumps(nack, separators=(",", ":")), call, "FILE_NACK", timeout=30.0)
                return
            data = base64.b64decode(packet.get("data", ""), validate=True)
            crc = hashlib.sha256(data).hexdigest()[:16]
            if crc != packet.get("crc"):
                raise ValueError("chunk checksum mismatch")
            self.ftlog(f"RX_CHUNK decoded idx={idx} bytes={len(data)} crc_ok={crc}", transfer_id, call)
            self.file_rx["chunks"][idx] = data
            self.file_rx["last_activity"] = time.time()
            self.save_rx_resume_state()
            total = int(packet.get("total", self.file_rx.get("info", {}).get("chunks", 0)) or 0)
            pct = (len(self.file_rx["chunks"]) / max(1, total)) * 100.0
            self.q.put(("txprogress", (pct, f"Receiving file {idx}/{total}")))
            self.add_session_event(f"File chunk {idx}/{total} received")
            ack = {"id": transfer_id, "chunk": idx, "snr": float(self.last_rx_snr) if self.last_rx_snr is not None else None}
            ok = self.send_protocol_frame_and_wait("HXCTL|FILE_ACK|" + json.dumps(ack, separators=(",", ":")), call, "FILE_ACK", timeout=30.0, mode_override=((self.file_rx or {}).get("info", {}) or {}).get("mode"))
            self.ftlog(f"RX_CHUNK ACK sent idx={idx} ok={ok}", transfer_id, call)
        except Exception as e:
            self.ftlog(f"RX_CHUNK exception: {e}", peer=call)
            self.qlog(f"File chunk RX error: {e}", "err")
            try:
                obj = json.loads(raw)
                transfer_id = (obj.get("id") or "").strip().upper()
                idx = int(obj.get("chunk", -1))
            except Exception:
                transfer_id = sid
                idx = -1
            nack = {"id": transfer_id, "chunk": idx}
            self.send_protocol_frame_and_wait("HXCTL|FILE_NACK|" + json.dumps(nack, separators=(",", ":")), call, "FILE_NACK", timeout=30.0)

    def handle_file_done_rx(self, call: str, sid: str, msg: str):
        self.ftlog(f"RX_DONE handler enter call={call} sid={sid} msg={msg[:180]}", sid, call)
        raw = msg.split("|", 2)[2] if msg.count("|") >= 2 else "{}"
        try:
            done_info = json.loads(raw)
        except Exception:
            done_info = {}
        transfer_id = (done_info.get("id") or sid or "").strip().upper()
        if not self.file_rx_active or not self.file_rx or self.file_rx.get("id") != transfer_id:
            self.ftlog(f"RX_DONE ignored active={self.file_rx_active} current={(self.file_rx or {}).get('id')} transfer_id={transfer_id}", transfer_id, call)
            return
        info = self.file_rx.get("info", {})
        total = int(info.get("chunks", 0) or 0)
        path = self.file_rx.get("path")
        try:
            if len(self.file_rx["chunks"]) != total:
                raise RuntimeError(f"missing chunks: have {len(self.file_rx['chunks'])}, need {total}")
            data = b"".join(self.file_rx["chunks"][i] for i in range(1, total + 1))
            sha = hashlib.sha256(data).hexdigest()
            if info.get("sha256") and sha != info.get("sha256"):
                raise RuntimeError("final SHA-256 mismatch")
            self.ftlog(f"RX_DONE writing file path={path} bytes={len(data)} sha={sha}", transfer_id, call)
            Path(path).write_bytes(data)
            self.delete_rx_resume_state(call, transfer_id)
            self.add_session_event(f"File received: {os.path.basename(path)}")
            self.q.put(("txprogress", (100.0, "File received")))
            self.delete_file_state(call, transfer_id)
            threading.Thread(target=self.speak_text, args=("File transfer completed",), daemon=True).start()
            self.q.put(("file_complete_prompt", path))
        except Exception as e:
            self.ftlog(f"RX_DONE exception: {e}", transfer_id, call)
            self.add_session_event(f"File receive failed: {e}")
            threading.Thread(target=self.speak_text, args=("File transfer failed",), daemon=True).start()
        finally:
            self.ftlog(f"RX_DONE finally clearing rx state", transfer_id, call)
            self.file_rx_active = False
            self.file_rx = None
            self.release_file_awake("rx")
            self.update_session_controls()
            self.release_post_file_deferred("receiver")
            self.after(2500, lambda: self.q.put(("txprogress", (0.0, "Idle"))))

    def file_receive_complete_ui(self, path: str):
        """Show a non-blocking, auto-closing received-file notification."""
        try:
            dlg = tk.Toplevel(self)
            dlg.title("HX File Transfer")
            dlg.transient(self)
            dlg.resizable(False, False)
            dlg.attributes("-topmost", True)
            body = ttk.Frame(dlg, padding=14)
            body.pack(fill="both", expand=True)
            ttk.Label(body, text=f"File received:\n\n{path}\n\nOpen receive folder?", justify="left").pack(anchor="w")
            buttons = ttk.Frame(body)
            buttons.pack(fill="x", pady=(12, 0))
            def close_only():
                try: dlg.destroy()
                except Exception: pass
            def open_folder():
                close_only()
                try:
                    os.startfile(os.path.dirname(path))
                except Exception as e:
                    self.show_error("HX File Transfer", f"Could not open folder:\n{e}")
            ttk.Button(buttons, text="Open Folder", command=open_folder).pack(side="left")
            ttk.Button(buttons, text="Later", command=close_only).pack(side="right")
            self.update_idletasks()
            dlg.update_idletasks()
            x = self.winfo_rootx() + max(0, (self.winfo_width() - dlg.winfo_reqwidth()) // 2)
            y = self.winfo_rooty() + max(0, (self.winfo_height() - dlg.winfo_reqheight()) // 2)
            dlg.geometry(f"+{x}+{y}")
            dlg.lift()
            dlg.focus_force()
            dlg.after(5000, close_only)
            dlg.after(300, lambda: dlg.attributes("-topmost", False) if dlg.winfo_exists() else None)
        except Exception as e:
            self.qlog(f"Received-file notification failed: {e}", "warn")

    def start_background_tx(self, override_message: str | None = None, animate_text: bool = True, clear_after: bool = True, reason: str = "manual", override_to: str | None = None) -> bool:
        """Start a transmit safely through the HX TX scheduler.

        All outgoing traffic goes through the same arbitration point so profile
        requests, beacons, chat, keepalives, and future file chunks cannot
        double-transmit or collide with a just-finished HX receive cycle.
        """
        if getattr(self, "tune_active", False):
            self.qlog("TX held: stop the 1 kHz tune tone first", "warn")
            return False
        # While this station is the file sender, the file worker exclusively owns
        # the TX scheduler.  Only FILE_* protocol frames belonging to that worker
        # may transmit.  Operator chat, profile requests/replies, SNR requests,
        # beacons, keepalives, and other session traffic remain deferred until the
        # entire transfer finishes.  This prevents a queued request from starting
        # during the peer's FILE_ACK transmission/turnaround window.
        is_file_protocol = bool(
            isinstance(override_message, str)
            and override_message.upper().startswith("HXCTL|FILE_")
        )
        if (getattr(self, "file_tx_active", False) or getattr(self, "file_rx_active", False)) and not is_file_protocol:
            self.file_deferred_manual.append((override_message, animate_text, clear_after, reason, override_to))
            notice = (
                "MESSAGE QUEUED — waiting for file transfer to finish…"
                if reason == "manual"
                else "REQUEST QUEUED — waiting for file transfer to finish…"
            )
            self.show_tx_queue_notice(notice)
            self.after(500, self.update_tx_queue_notice)
            # Do not overwrite the active file-transfer progress bar and do not
            # wake or influence the file worker's ACK/idle state.
            self.qlog(f"{reason} TX deferred until file transfer ends", "warn")
            return True
        hold, _why = self.should_hold_tx(reason)
        if hold:
            return self.queue_tx_hold(override_message, animate_text, clear_after, reason, override_to)
        if reason == "manual":
            self.disable_beacon_for_activity("manual message")
            self.mark_user_activity("manual tx")
        elif self.session_active and (reason in ("session", "SNR auto-reply") or str(reason).startswith("protocol")) and not self.is_keepalive_control_payload(override_message):
            self.mark_session_traffic(f"{reason} tx")
        self.close_tx_queue_notice()
        self.tx_busy = True
        self.q.put(("txbusy", True))
        threading.Thread(target=self.do_tx, args=(override_message, animate_text, clear_after, override_to, reason), daemon=True).start()
        return True

    def start_tx(self):
        if getattr(self, "file_tx_active", False) or getattr(self, "file_rx_active", False):
            self.qlog("Text transmission blocked during file transfer", "warn")
            return
        self.start_background_tx(None, True, True, "manual")

    def do_tx(self, override_message: str | None = None, animate_text: bool = True, clear_after: bool = True, override_to: str | None = None, reason: str = "manual") :
        progress_stop = None
        tx_seq = 0
        plain_msg = ""
        dest = ""
        mode = ""
        was_rx = False
        try:
            with self.tx_debug_lock:
                self.tx_debug_seq += 1
                tx_seq = self.tx_debug_seq
            was_rx = bool(self.rx_monitor)
            plain_msg = override_message if override_message is not None else self.get_tx_message_text()
            dest = self.clean_destination(override_to if override_to is not None else (self.session_peer if self.session_active and reason == "manual" else None))
            mode = self.selected_mode()
            if str(reason).startswith("protocol@"):
                try:
                    _m = str(reason).split("@", 1)[1].strip().upper()
                    if _m in ("HX-F", "HX-N"):
                        mode = _m
                except Exception:
                    pass
            traffic_preview = (plain_msg or "").replace("\r", " ").replace("\n", " ")
            if len(traffic_preview) > 240:
                traffic_preview = traffic_preview[:240] + "…"
            traffic_kind = "CONTROL" if traffic_preview.startswith("HXCTL|") else ("BEACON" if reason == "beacon" else "TEXT")
            self.ftlog(f"TRAFFIC_TX kind={traffic_kind} reason={reason} from={self.clean_callsign()} to={dest} text={traffic_preview}", peer=dest)
            self.ftlog(f"TX_ENGINE[{tx_seq}] ENTER reason={reason} dest={dest} bytes={len((plain_msg or '').encode('utf-8','ignore'))} was_rx={was_rx} tx_device={self.tx_device} rx_device={self.rx_device}", peer=dest)
            if was_rx:
                self.ftlog(f"TX_ENGINE[{tx_seq}] RX_STOP_REQUEST", peer=dest)
                self.set_rx_monitor(False)
                wait_start = time.time()
                while getattr(self, "rx_thread", None) and self.rx_thread.is_alive() and time.time() - wait_start < 3.0:
                    time.sleep(0.05)
                self.ftlog(f"TX_ENGINE[{tx_seq}] RX_STOP_DONE alive={bool(getattr(self,'rx_thread',None) and self.rx_thread.is_alive())} waited={time.time()-wait_start:.2f}s", peer=dest)
                # Even if the RX thread is still unwinding, give sounddevice a small device-turnaround window.
                time.sleep(0.35)
            self.set_led("TX", "active", "ACTIVE")
            self.q.put(("modemstate", "tx"))
            msg = self.make_outgoing_payload(plain_msg, dest)
            if not plain_msg.strip():
                self.qlog("TX skipped: message is empty", "warn")
                self.ftlog(f"TX_ENGINE[{tx_seq}] SKIP_EMPTY", peer=dest)
                return
            try:
                expected_audio = tx_audio_for_payload(msg, mode, self.tx_level_var.get())
                expected_tx_time = len(expected_audio) / SAMPLE_RATE
            except Exception as e:
                self.ftlog(f"TX_ENGINE[{tx_seq}] AUDIO_ESTIMATE_FAILED {e}", peer=dest)
                expected_audio = np.zeros(int(SAMPLE_RATE), dtype=np.float32)
                expected_tx_time = 1.0
            self.q.put(("spectrum_tx", expected_audio))
            progress_stop = self.start_tx_progress(expected_audio, expected_tx_time, animate_text=animate_text, clear_after=clear_after)
            self.qlog(f"TX started: mode={mode}, device={self.tx_device}, level={self.tx_level_var.get():.2f}")
            self.ftlog(f"TX_ENGINE[{tx_seq}] PTT_ON TX_START mode={mode} expected={expected_tx_time:.2f}s", peer=dest)
            self.tx_meter_level = max(self.tx_meter_level, self.tx_level_var.get())
            tx_start = time.time()
            self.cat_ptt_on()
            tx_time = transmit(msg, mode, self.tx_device, self.tx_level_var.get())
            self.ftlog(f"TX_ENGINE[{tx_seq}] TX_COMPLETE reported={tx_time:.2f}s wall={time.time()-tx_start:.2f}s", peer=dest)
            progress_stop.set()
            self.qlog(f"TX done. TX time={tx_time:.2f}s", "ok")
            if reason == "beacon":
                self.play_hx_chime("success")
                threading.Thread(target=self.speak_text, args=("Beacon transmitted",), daemon=True).start()
            # Protocol/control frames should not appear as operator chat.
            if reason != "session" and not str(reason).startswith("protocol"):
                self.q.put(("message", ("TX", self.clean_callsign(), plain_msg, dest)))
            self.q.put(("template_reset", None))
        except Exception as e:
            self.ftlog(f"TX_ENGINE[{tx_seq}] EXCEPTION {type(e).__name__}: {e}", peer=dest)
            self.qlog(f"TX error: {e}", "err")
        finally:
            self.ftlog(f"TX_ENGINE[{tx_seq}] FINALLY begin tx_busy={getattr(self,'tx_busy',None)}", peer=dest)
            self.cat_ptt_off()
            if progress_stop is not None:
                progress_stop.set()
            self.set_led("TX", "off")
            self.q.put(("modemstate", "rx"))
            self.q.put(("spectrum_tx_clear", None))
            self.beacon_tx_in_progress = False
            self.tx_busy = False
            self.q.put(("txbusy", False))
            self.ftlog(f"TX_ENGINE[{tx_seq}] MODEM_IDLE tx_busy={getattr(self,'tx_busy',None)}", peer=dest)
            if was_rx:
                def _restart_rx_once_previous_exits():
                    old_thread = getattr(self, "rx_thread", None)
                    if old_thread is not None and old_thread.is_alive():
                        self.after(100, _restart_rx_once_previous_exits)
                        return
                    self.rx_thread = None
                    self.set_rx_monitor(True)
                    self.ftlog(f"TX_ENGINE[{tx_seq}] RX_RESTART_REQUESTED", peer=dest)
                self.after(100, _restart_rx_once_previous_exits)
            # Post-TX guard gives the other station time to capture, decode, and re-arm RX.
            self.tx_turnaround_guard_until = max(float(getattr(self, "tx_turnaround_guard_until", 0.0) or 0.0), time.time() + self.tx_guard_seconds)
            self.after(int(self.tx_guard_seconds * 1000), self.process_tx_hold_queue)

    def toggle_1khz_tune(self):
        """Start/stop a continuous 1 kHz calibration tone.

        Unlike framed HX transmissions, the audio callback reads tune_gain_live
        for every block, so moving TX GAIN changes tone amplitude immediately.
        """
        if self.tune_active:
            self.stop_1khz_tune()
        else:
            self.start_1khz_tune()

    def start_1khz_tune(self):
        if self.tune_active:
            return
        if self.tx_busy or self.file_tx_active or self.file_rx_active:
            self.show_info("1 kHz Tune", "Wait for the current transmission or file transfer to finish.")
            return
        try:
            self.tune_was_rx = bool(self.rx_monitor)
            if self.tune_was_rx:
                self.set_rx_monitor(False)
                deadline = time.time() + 3.0
                while self.rx_thread and self.rx_thread.is_alive() and time.time() < deadline:
                    self.update_idletasks()
                    time.sleep(0.05)
                time.sleep(0.25)

            # Use the same optional CAT/PTT path as normal HX transmissions.
            # CAT-disabled and VOX operation remain no-ops here.
            self.ftlog("TUNE_PTT_ON request")
            self.cat_ptt_on()
            self.tune_ptt_asserted = True

            self.tune_active = True
            self.tune_phase = 0.0
            phase_step = 2.0 * np.pi * 1000.0 / float(SAMPLE_RATE)

            def callback(outdata, frames, _time_info, status):
                if status:
                    self.ftlog(f"TUNE audio status={status}")
                idx = np.arange(frames, dtype=np.float64)
                phase = self.tune_phase + phase_step * idx
                samples = np.sin(phase) * float(self.tune_gain_live)
                self.tune_phase = float((phase[-1] + phase_step) % (2.0 * np.pi)) if frames else self.tune_phase
                outdata[:, 0] = samples.astype(np.float32)

            self.tune_stream = sd.OutputStream(
                samplerate=int(SAMPLE_RATE), channels=1, dtype="float32",
                device=self.tx_device, callback=callback, blocksize=1024,
            )
            self.tune_stream.start()
            self.tune_button.configure(text="STOP 1KHz")
            self.tx_meter_level = max(self.tx_meter_level, self.tune_gain_live)
            self.qlog("1 kHz tune tone started; TX GAIN is live", "warn")
            self.ftlog(f"TUNE_START freq=1000Hz device={self.tx_device} gain={self.tune_gain_live:.2f}")
        except Exception as e:
            self.tune_active = False
            self.tune_stream = None
            if self.tune_ptt_asserted:
                self.cat_ptt_off()
                self.tune_ptt_asserted = False
                self.ftlog("TUNE_PTT_OFF startup_failure")
            self.qlog(f"1 kHz tune error: {e}", "err")
            self.show_error("1 kHz Tune", f"Could not start tune tone:\n{e}")
            if self.tune_was_rx:
                self.set_rx_monitor(True)

    def stop_1khz_tune(self):
        if not self.tune_active and self.tune_stream is None:
            return
        self.tune_active = False
        try:
            if self.tune_stream is not None:
                self.tune_stream.stop()
                self.tune_stream.close()
        except Exception as e:
            self.ftlog(f"TUNE_STOP warning={e}")
        finally:
            self.tune_stream = None
            if self.tune_ptt_asserted:
                self.cat_ptt_off()
                self.tune_ptt_asserted = False
                self.ftlog("TUNE_PTT_OFF stop")
            if hasattr(self, "tune_button"):
                self.tune_button.configure(text="1KHz")
            self.qlog("1 kHz tune tone stopped", "ok")
            self.ftlog("TUNE_STOP")
            if self.tune_was_rx:
                self.tune_was_rx = False
                self.set_rx_monitor(True)

    def auto_start_rx_monitor(self):
        """Start station monitoring automatically. TX pauses and resumes it as needed."""
        if not self.rx_monitor:
            self.set_rx_monitor(True)

    def toggle_rx_monitor(self):
        self.set_rx_monitor(not self.rx_monitor)

    def _start_rx_generation_when_ready(self, generation: int):
        old = None
        with self._rx_thread_lock:
            old = self.rx_thread
        if old and old.is_alive() and old is not threading.current_thread():
            old.join(timeout=3.0)
        with self._rx_thread_lock:
            self._rx_start_pending = False
            if not self.rx_monitor or generation != self._rx_generation:
                return
            if self.rx_thread and self.rx_thread.is_alive():
                return
            self.rx_thread = threading.Thread(target=self.rx_monitor_loop, args=(generation,), daemon=True)
            self.rx_thread.start()

    def set_rx_monitor(self, state: bool):
        state = bool(state)
        with self._rx_thread_lock:
            self._rx_generation += 1
            generation = self._rx_generation
            self.rx_monitor = state
            old_alive = bool(self.rx_thread and self.rx_thread.is_alive())
        if state:
            if hasattr(self, "rx_btn"):
                self.rx_btn.configure(text="RX MONITOR ON")
            self.set_led("RX", "active", "SEARCH")
            self.q.put(("modemstate", "rx"))
            self.set_led("Pilot", "warn", "SEARCH")
            self.set_led("Timing", "off", "--")
            self.set_led("CRC", "off", "--")
            self.last_rx_detect = "SEARCH"
            self.q.put(("rxdetect", "SEARCH"))
            self.q.put(("rxstate", "RX state: monitor enabled, waiting for signal"))
            self.qlog("RX Monitor enabled.")
            with self._rx_thread_lock:
                if not self._rx_start_pending:
                    self._rx_start_pending = True
                    threading.Thread(target=self._start_rx_generation_when_ready, args=(generation,), daemon=True).start()
        else:
            if hasattr(self, "rx_btn"):
                self.rx_btn.configure(text="RX MONITOR OFF")
            self.set_hx_channel_busy(False, "RX monitor disabled")
            self.set_led("RX", "off")
            self.q.put(("modemstate", "off"))
            self.set_led("Pilot", "off")
            self.set_led("Timing", "off")
            self.set_led("CRC", "off")
            self.q.put(("rxstate", "RX state: idle"))
            self.qlog("RX Monitor disabled.")

    def rx_monitor_loop(self, generation: int):
        self.qlog("RX Monitor searching...", "info")
        def generation_active():
            return self.rx_monitor and generation == self._rx_generation
        while generation_active():
            try:
                mode = self.selected_rx_mode()
                self.q.put(("rxdetect", "SEARCH"))
                self.set_led("RX", "active", "SEARCH")
                if time.time() >= self.last_decode_hold_until:
                    self.set_led("Pilot", "warn", "SEARCH")
                    self.set_led("Timing", "off", "--")
                    self.set_led("CRC", "off", "--")
                cap_path = os.path.join(DOC_DIR, "last_rx_monitor_capture.wav")

                hx_candidate_confirmed = False

                def dbg(msg: str):
                    nonlocal hx_candidate_confirmed
                    # v0.4.18: always preserve the decoder state trace in the
                    # traffic/file debug log. The on-screen DEBUG RX option
                    # still controls verbose UI messages.
                    self.ftlog(f"RX_DECODER {msg}")
                    low = msg.lower()
                    # Compact real-time trace shown beside frame counters.
                    if "hx preamble confirmed" in low:
                        mode_text = "HX"
                        for candidate_mode in ("HX-F", "HX-N"):
                            if candidate_mode.lower() in low:
                                mode_text = candidate_mode
                                break
                        self.q.put(("decodeout", f"PILOT {mode_text} LOCK"))
                    elif "header_valid" in low or "valid hx header" in low:
                        self.q.put(("decodeout", "HEADER CRC OK"))
                    elif "state=decoding" in low and "captured_seconds=" in low:
                        try:
                            sec = low.split("captured_seconds=", 1)[1].split()[0]
                            self.q.put(("decodeout", f"DECODING {float(sec):.1f}s"))
                        except Exception:
                            pass
                    elif "payload_soft_decode" in low:
                        self.q.put(("decodeout", "PAYLOAD SOFT DECODE"))
                    elif "payload_soft_miss" in low:
                        self.q.put(("decodeout", "SOFT CRC MISS"))
                    elif "payload_hard_fallback" in low:
                        self.q.put(("decodeout", "HARD FALLBACK"))
                    elif "payload_soft_success" in low or "payload_hard_success" in low:
                        self.q.put(("decodeout", "FRAME CRC OK"))
                    elif "timing_recovery_try" in low:
                        self.q.put(("decodeout", "SOFT/TIMING RETRY"))
                    elif "frame_final result=crc_ok" in low or "frame completed before silence" in low or "decode success after bounded timing recovery" in low:
                        self.q.put(("decodeout", "FRAME CRC OK"))
                    elif "frame_final result=unrecoverable" in low:
                        if "payload_crc" in low:
                            self.q.put(("decodeout", "FRAME UNRECOVERABLE - PAYLOAD CRC"))
                        elif "header_crc" in low:
                            self.q.put(("decodeout", "FRAME UNRECOVERABLE - HEADER CRC"))
                        else:
                            self.q.put(("decodeout", "FRAME UNRECOVERABLE"))
                        # A failed HX candidate is complete at this point. Do not
                        # leave the operator-facing modem state latched in
                        # Receiving merely because unrelated SSB/audio energy
                        # continues. Return to Listening immediately while the
                        # red CRC indication remains visible.
                        self.set_hx_channel_busy(False, "CRC failure")
                        hx_candidate_confirmed = False
                        self.q.put(("rxdetect", "SEARCH"))
                        self.q.put(("modemstate", "rx"))
                        self.q.put(("led", ("RX", "active", "SEARCH")))
                        self.q.put(("led", ("Pilot", "warn", "SEARCH")))
                        self.q.put(("led", ("Timing", "off", "--")))
                        self.q.put(("led", ("CRC", "bad", "ERROR")))
                    elif "stream_open" in low:
                        self.q.put(("decodeout", "MONITORING"))

                    if "audio energy detected" in low:
                        # Informational only: ordinary RF energy must never
                        # block TX.  Busy protection begins only after the
                        # exact HX pilot has been confirmed.
                        self.q.put(("rxdetect", "SIGNAL"))
                        self.q.put(("modemstate", "rx"))
                        self.q.put(("led", ("RX", "active", "MONITOR")))
                        self.q.put(("led", ("Pilot", "warn", "CHECK")))
                        self.q.put(("led", ("Timing", "off", "--")))
                    elif "hx preamble confirmed" in low:
                        hx_candidate_confirmed = True
                        self.set_hx_channel_busy(True, "HX preamble")
                        self.q.put(("rxdetect", "HX SIGNAL"))
                        self.q.put(("modemstate", "receive"))
                        self.q.put(("led", ("RX", "active", "HX")))
                        self.q.put(("led", ("Pilot", "active", "LOCK")))
                        self.q.put(("led", ("Timing", "warn", "SYNC")))
                    elif "frame completed before silence" in low or "decode success after bounded timing recovery" in low:
                        hx_candidate_confirmed = False
                        self.q.put(("rxdetect", "DECODED"))
                        self.q.put(("led", ("Pilot", "active", "LOCK")))
                        self.q.put(("led", ("Timing", "active", "DONE")))
                        self.q.put(("led", ("CRC", "active", "OK")))
                    elif "burst captured" in low:
                        self.q.put(("rxdetect", "DECODE"))
                        self.q.put(("led", ("Pilot", "warn", "DECODE")))
                        self.q.put(("led", ("Timing", "warn", "DECODE")))
                    elif "decode miss" in low:
                        self.set_hx_channel_busy(False, "miss")
                        self.q.put(("rxdetect", "MISS"))
                        # Ordinary RF bursts with no confirmed HX pilot are not
                        # CRC failures. Only a genuine HX candidate may turn the
                        # operator-facing CRC indicator red.
                        if hx_candidate_confirmed:
                            self.q.put(("led", ("CRC", "bad", "MISS")))
                        hx_candidate_confirmed = False
                    if self.debug_rx_var.get():
                        self.qlog(msg, "debug")
                        self.q.put(("rxstate", f"RX state: {msg}"))

                try:
                    res = receive_stream_until_frame(
                        mode,
                        self.rx_device,
                        should_continue=generation_active,
                        on_level=lambda level: self.q.put(("meter", ("rx", level))),
                        on_samples=lambda samples: self.q.put(("spectrum_rx", samples)),
                        on_debug=dbg,
                        debug_capture_path=cap_path,
                        debug_capture_mode=self.rx_capture_mode_var.get(),
                    )
                finally:
                    # Never allow a decoder exit, exception, stop request, or
                    # failed candidate to leave HX busy latched indefinitely.
                    self.set_hx_channel_busy(False, "decoder cycle ended")

                if not generation_active():
                    self.set_hx_channel_busy(False, "stopped")
                    break
                if res is None:
                    self.set_hx_channel_busy(False, "no frame")
                    continue

                self.set_hx_channel_busy(False, "decoded")
                meta = self.parse_message_payload_meta(res["payload"])
                call, to_call, text = meta["from"], meta["to"], meta["text"]
                self.q.put(("partialclear", None))
                if self.is_duplicate_rx_frame(call, to_call, text, str(res.get("mode_header", ""))):
                    self.ftlog(f"TRAFFIC_RX duplicate_suppressed from={call} to={to_call} mode={res.get('mode_header','-')}", peer=call)
                    continue
                self.note_station_capabilities(call, meta.get("version", "unknown"), meta.get("caps", ""))
                self.rx_meter_level = max(self.rx_meter_level, float(res.get("peak", 0.0)))
                rx_preview = (text or "").replace("\r", " ").replace("\n", " ")
                if len(rx_preview) > 240:
                    rx_preview = rx_preview[:240] + "…"
                rx_kind = "CONTROL" if rx_preview.startswith("HXCTL|") else ("BEACON" if self.is_beacon_message(rx_preview) else "TEXT")
                self.ftlog(f"TRAFFIC_RX kind={rx_kind} from={call} to={to_call} mode={res['mode_header']} snr={res['snr']:.2f} text={rx_preview}", peer=call)
                self.qlog(f"RX decoded: {call}: {text} mode={res['mode_header']} SNR={res['snr']:.2f} dB", "ok")
                self.q.put(("heard", (call, float(res.get("snr", 0.0)))))
                if self.handle_session_control_rx(call, to_call, text):
                    self.q.put(("status", res))
                    time.sleep(0.35)
                    if self.rx_monitor:
                        self.q.put(("rxdetect", "SEARCH"))
                        self.q.put(("modemstate", "rx"))
                        self.qlog("RX Monitor searching...", "info")
                    continue
                if self.session_active and call == self.session_peer:
                    self.mark_user_activity("rx message")
                self.q.put(("message", ("RX", call, text, to_call)))
                self.maybe_speak_tag(text)
                self.maybe_speak_direct(call, to_call)
                self.maybe_auto_reply_snr(call, to_call, text, float(res.get("snr", 0.0)))
                self.q.put(("status", res))
                time.sleep(0.35)
                if self.rx_monitor:
                    self.q.put(("rxdetect", "SEARCH"))
                    self.q.put(("modemstate", "rx"))
                    self.qlog("RX Monitor searching...", "info")
            except Exception as e:
                self.set_hx_channel_busy(False, "error")
                self.frames_fail += 1
                self.set_led("CRC", "bad", "FAIL")
                self.qlog(f"RX monitor error: {e}", "err")
                time.sleep(1.0)

    def start_loopback(self):
        threading.Thread(target=self.do_loopback, daemon=True).start()

    def do_loopback(self):
        try:
            plain_msg = self.get_tx_message_text()
            dest = self.clean_destination()
            msg = self.make_outgoing_payload(plain_msg, dest)
            mode = self.selected_mode()
            path = os.path.join(DOC_DIR, "last_live_capture.wav")
            self.set_led("RX", "active", "CAPTURE")
            self.set_led("TX", "active", "ACTIVE")
            self.qlog(f"Live loopback started: mode={mode}, TX={self.tx_device}, RX={self.rx_device}, capture={path}")
            self.tx_meter_level = max(self.tx_meter_level, self.tx_level_var.get())
            res = live_loopback(msg, mode, self.tx_device, self.rx_device, path, self.tx_level_var.get())
            self.rx_meter_level = max(self.rx_meter_level, float(res.get("peak", 0.0)))
            self.qlog(f"Live capture peak={res['peak']:.6f}, TX time={res['tx_time']:.2f}s, capture time={res['capture_time']:.2f}s")
            call, to_call, text = self.parse_message_payload(res["payload"])
            self.qlog(f"Live loopback decoded: {call}: {text}", "ok")
            if reason != "session":
                self.q.put(("message", ("TX", self.clean_callsign(), plain_msg, dest)))
            self.q.put(("template_reset", None))
            self.q.put(("message", ("RX", call, text, to_call)))
            self.qlog(f"Live mode header={res['mode_header']}, estimated SNR={res['snr']:.2f} dB, suggested={choose_mode(res['snr'])}", "ok")
            self.q.put(("status", res))
        except Exception as e:
            self.frames_fail += 1
            self.set_led("CRC", "bad", "FAIL")
            self.qlog(f"Live loopback error: {e}", "err")
        finally:
            self.set_led("TX", "off")
            self.set_led("RX", "off")

    def local_sim_test(self):
        for mode in ["HX-F", "HX-N"]:
            try:
                msg = b"HELLO HX"
                tx = hx_encode(msg, mode)
                rx = add_awgn(tx, 30.0)
                _, hdr, payload = hx_decode(rx, mode)
                self.log(f"Local sim decoded: {payload.decode()} mode={hdr}", "ok")
            except Exception as e:
                self.log(f"Local sim failed {mode}: {e}", "err")

    def save_tx_wav(self):
        path = filedialog.asksaveasfilename(defaultextension=".wav", filetypes=[("WAV files", "*.wav")])
        if not path:
            return
        audio = tx_audio_for_payload(self.make_outgoing_payload(self.get_tx_message_text()), self.selected_mode(), self.tx_level_var.get())
        save_wav(path, audio)
        self.tx_meter_level = max(self.tx_meter_level, float(np.max(np.abs(audio))))
        self.log(f"Saved TX WAV: {path}", "ok")

    def decode_wav(self):
        path = filedialog.askopenfilename(filetypes=[("WAV files", "*.wav")])
        if not path:
            return
        try:
            audio = read_wav(path)
            res = decode_audio_capture(audio, self.selected_mode())
            call, to_call, text = self.parse_message_payload(res["payload"])
            self.log(f"Decoded WAV: {call}: {text} mode={res['mode_header']} SNR={res['snr']:.2f} dB", "ok")
            self.update_heard_station(call, float(res.get("snr", 0.0)))
            self.add_message_line("RX", call, text, to_call)
            self.remember_station(call)
            self.update_decode_status(res)
        except Exception as e:
            self.log(f"Decode WAV error: {e}", "err")


    def play_hx_chime(self, kind: str = "startup"):
        """Play local HX UI identity sounds only.

        These sounds are application/UI notifications. They are not routed
        through the selected HX transmit audio device and do not alter modem
        framing, encoding, decoding, synchronization, or over-the-air payload.
        """
        if kind == "startup" and hasattr(self, "startup_sound_var") and not self.startup_sound_var.get():
            return
        if kind != "startup" and hasattr(self, "notification_sounds_var") and not self.notification_sounds_var.get():
            return
        motifs = {
            "startup": [(523, 120), (784, 120), (1319, 170)],   # C5, G5, E6
            "connected": [(523, 95), (659, 95), (784, 130)],    # C5, E5, G5
            "success": [(659, 90), (784, 120)],                 # E5, G5
            "error": [(784, 120), (659, 120), (523, 170)],      # G5, E5, C5
        }
        notes = motifs.get(kind, motifs["success"])
        def worker():
            try:
                # Windows-local UI beeps. This is intentionally separate from
                # the sounddevice TX path used by the HX modem audio engine.
                script_parts = []
                for freq, dur in notes:
                    script_parts.append(f"[console]::beep({int(freq)},{int(dur)})")
                    script_parts.append("Start-Sleep -Milliseconds 35")
                script = "; ".join(script_parts)
                flags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
                subprocess.Popen(["powershell", "-NoProfile", "-Command", script], creationflags=flags)
            except Exception as e:
                self.qlog(f"HX sound failed: {e}", "warn")
        threading.Thread(target=worker, daemon=True).start()

    def _current_cat_settings(self):
        try:
            baud = int(self.cat_baud_var.get())
        except Exception:
            baud = 38400
        return CATSettings(
            enabled=bool(self.cat_enabled_var.get()),
            port=self.cat_port_var.get().strip(),
            baud=baud,
            radio_model=self.cat_radio_var.get().strip() or "Yaesu FT-710",
            ptt_method=self.ptt_method_var.get().strip().upper() or "VOX",
        )

    @staticmethod
    def format_cat_frequency(frequency_hz):
        if frequency_hz is None:
            return "---.---.---"
        return f"{int(frequency_hz):09,d}".replace(",", ".")

    def apply_cat_state(self, state):
        previous_connected = bool(getattr(self.cat_state, "connected", False))
        self.cat_state = state
        connected = bool(state.connected)
        enabled = bool(self.cat_enabled_var.get())
        error_text = str(getattr(state, "error", "") or "").strip()
        if error_text and error_text != self._last_cat_error:
            # A powered-off or unplugged radio is an expected operator condition,
            # not a Normal-level application failure. Preserve the technical
            # detail for Developer debug without cluttering the normal event log.
            self.qlog(f"CAT transport unavailable: {error_text}", "debug")
            self._last_cat_error = error_text
        elif connected:
            self._last_cat_error = ""
        if previous_connected and not connected and error_text:
            self.qlog("CAT polling stopped after the radio or COM port became unavailable", "debug")
        if connected:
            color = COLORS["green"]
            text = "CAT CONNECTED"
        elif enabled:
            color = COLORS["amber"] if not state.error else COLORS["red"]
            text = "CAT READY" if not state.error else "CAT ERROR"
        else:
            color = COLORS["muted"]
            text = "CAT OFF"
        if hasattr(self, "cat_led_canvas"):
            self.cat_led_canvas.itemconfig(self.cat_led, fill=color)
            self.cat_status_label.configure(text=text, fg=color)
            mode_text = f"RADIO {state.mode or '--'}"
            self.radio_mode_label.configure(text=mode_text, fg=COLORS["accent"] if connected else COLORS["muted"])
        if hasattr(self, "frequency_label"):
            self.frequency_label.configure(text=self.format_cat_frequency(state.frequency_hz) if connected else "---.---.---")
            self.frequency_mode_label.configure(text=f"RADIO {state.mode or '--'}")

    def auto_connect_cat(self):
        """Attempt one quiet CAT connection after the GUI has initialized."""
        settings = self._current_cat_settings()
        if not settings.enabled or not settings.port or self.cat_manager.connected:
            return
        self.cat_manager.set_settings(settings)
        try:
            self.cat_manager.connect()
            self.log(
                f"CAT auto-connected: {settings.radio_model} on {settings.port} at {settings.baud} baud",
                "ok",
            )
        except Exception as exc:
            # Startup without the radio is a normal operating condition. The
            # CAT state indicator reports the failure; technical details remain
            # available only in Developer debug and no popup interrupts startup.
            self.qlog(f"CAT auto-connect unavailable: {exc}", "debug")

    def cat_connect(self):
        settings = self._current_cat_settings()
        self.cat_manager.set_settings(settings)
        if not settings.enabled:
            self.show_info("CAT / PTT", "Enable CAT before connecting.")
            return
        try:
            self.cat_manager.connect()
            self.log(f"CAT connected: {settings.radio_model} on {settings.port} at {settings.baud} baud", "ok")
        except Exception as exc:
            self.show_error("CAT Connection", str(exc))
            self.log(f"CAT connection failed: {exc}", "err")

    def cat_disconnect(self):
        try:
            self.cat_manager.disconnect()
        finally:
            self.apply_cat_state(RadioState())
            self.log("CAT disconnected", "warn")

    def cat_ptt_on(self):
        settings = self._current_cat_settings()
        if not settings.enabled or settings.ptt_method == "VOX":
            return
        self.cat_manager.set_settings(settings)
        self.cat_manager.ptt_on()
        time.sleep(0.12)

    def cat_ptt_off(self):
        settings = self._current_cat_settings()
        if not settings.enabled or settings.ptt_method == "VOX":
            return
        try:
            self.cat_manager.set_settings(settings)
            self.cat_manager.ptt_off()
            time.sleep(0.08)
        except Exception as exc:
            # Common when the operator powers the radio off before closing HX.
            # Keep the diagnostic available in Developer debug only.
            self.qlog(f"PTT release skipped because CAT is unavailable: {exc}", "debug")

    def cat_setup(self):
        win = tk.Toplevel(self)
        win.title("CAT / PTT Manager")
        win.geometry("510x390")
        win.configure(bg=COLORS["panel"])
        win.resizable(False, False)
        frm = ttk.Frame(win, style="Panel.TFrame", padding=14)
        frm.pack(fill="both", expand=True)
        ttk.Label(frm, text="CAT Manager", style="Section.TLabel").grid(row=0, column=0, columnspan=3, sticky="w", pady=(0, 10))
        ttk.Checkbutton(frm, text="Enable CAT (optional)", variable=self.cat_enabled_var).grid(row=1, column=0, columnspan=3, sticky="w", pady=4)
        ttk.Label(frm, text="Radio model", style="Panel.TLabel").grid(row=2, column=0, sticky="w", pady=6)
        ttk.Combobox(frm, textvariable=self.cat_radio_var, values=["Yaesu FT-710", "Kenwood TS-2000"], state="readonly", width=28).grid(row=2, column=1, columnspan=2, sticky="ew")
        ttk.Label(frm, text="COM port", style="Panel.TLabel").grid(row=3, column=0, sticky="w", pady=6)
        port_combo = ttk.Combobox(frm, textvariable=self.cat_port_var, values=available_ports(), width=20)
        port_combo.grid(row=3, column=1, sticky="ew")
        ttk.Button(frm, text="REFRESH", command=lambda: port_combo.configure(values=available_ports())).grid(row=3, column=2, padx=(8, 0))
        ttk.Label(frm, text="Baud rate", style="Panel.TLabel").grid(row=4, column=0, sticky="w", pady=6)
        ttk.Combobox(frm, textvariable=self.cat_baud_var, values=["4800", "9600", "19200", "38400", "57600", "115200"], state="readonly", width=20).grid(row=4, column=1, sticky="ew")
        ttk.Label(frm, text="PTT method", style="Panel.TLabel").grid(row=5, column=0, sticky="w", pady=6)
        ttk.Combobox(frm, textvariable=self.ptt_method_var, values=["VOX", "CAT", "RTS", "DTR"], state="readonly", width=20).grid(row=5, column=1, sticky="ew")
        ttk.Label(frm, text="VOX leaves radio keying entirely external. CAT uses the selected radio's native TX/RX commands. RTS/DTR drive the selected serial control line.", style="Muted.TLabel", wraplength=465, justify="left").grid(row=6, column=0, columnspan=3, sticky="w", pady=(8, 12))
        state_var = tk.StringVar(value="Connected" if self.cat_manager.connected else "Disconnected")
        ttk.Label(frm, textvariable=state_var, style="Panel.TLabel").grid(row=7, column=0, columnspan=3, sticky="w", pady=(0, 10))
        def connect_now():
            self.save_config()
            self.cat_connect()
            state_var.set("Connected" if self.cat_manager.connected else "Disconnected")
        def disconnect_now():
            self.cat_disconnect()
            state_var.set("Disconnected")
        buttons = ttk.Frame(frm, style="Panel.TFrame")
        buttons.grid(row=8, column=0, columnspan=3, sticky="ew", pady=(8, 0))
        ttk.Button(buttons, text="CONNECT", command=connect_now).pack(side="left")
        ttk.Button(buttons, text="DISCONNECT", command=disconnect_now).pack(side="left", padx=8)
        ttk.Button(buttons, text="SAVE / CLOSE", command=lambda: (self.save_config(), win.destroy())).pack(side="right")
        frm.columnconfigure(1, weight=1)

    def sound_settings_setup(self):
        win = tk.Toplevel(self)
        win.title("Sound Settings")
        win.configure(bg=COLORS["panel"])
        win.resizable(False, False)
        frm = ttk.Frame(win, style="Panel.TFrame", padding=14)
        frm.pack(fill="both", expand=True)
        ttk.Label(frm, text="HX Sound Identity", style="Section.TLabel").pack(anchor="w", pady=(0, 8))
        ttk.Checkbutton(frm, text="Enable HX startup sound", variable=self.startup_sound_var, command=self.save_config).pack(anchor="w", pady=3)
        ttk.Checkbutton(frm, text="Enable notification sounds", variable=self.notification_sounds_var, command=self.save_config).pack(anchor="w", pady=3)
        ttk.Checkbutton(frm, text="Enable voice announcements", variable=self.voice_announcements_var, command=self.save_config).pack(anchor="w", pady=3)
        btns = ttk.Frame(frm, style="Panel.TFrame")
        btns.pack(fill="x", pady=(12, 0))
        ttk.Button(btns, text="TEST CHIME", command=lambda: self.play_hx_chime("startup")).pack(side="left")
        ttk.Button(btns, text="OK", command=win.destroy).pack(side="right")

    def receive_folder_setup(self):
        folder = filedialog.askdirectory(title="Select HX receive files folder", initialdir=getattr(self, "receive_dir", RECEIVE_DIR) or RECEIVE_DIR)
        if folder:
            self.receive_dir = folder
            self.save_config()
            self.show_info("HX Receive Files", f"Received files will be saved to:\n\n{folder}")

    def advanced_dev_tools_setup(self):
        win = tk.Toplevel(self)
        win.title("Advanced Dev Tools")
        win.configure(bg=COLORS["panel"])
        win.resizable(False, False)
        frm = ttk.Frame(win, style="Panel.TFrame", padding=14)
        frm.pack(fill="both", expand=True)

        ttk.Label(frm, text="Advanced Developer Tools", style="Section.TLabel").pack(anchor="w", pady=(0, 8))
        ttk.Label(frm, text="RX debug WAV capture", style="Panel.TLabel").pack(anchor="w")
        ttk.Label(frm, text="Default is OFF. Enable only when troubleshooting decode issues.", style="Muted.TLabel").pack(anchor="w", pady=(2, 6))

        row = ttk.Frame(frm, style="Panel.TFrame")
        row.pack(fill="x", pady=(0, 10))
        cb = ttk.Combobox(row, textvariable=self.rx_capture_mode_var, values=["OFF", "ERRORS ONLY", "ALL"], state="readonly", width=14)
        cb.pack(side="left")

        ttk.Label(frm, text="OFF: no WAV files saved.\nERRORS ONLY: save failed decode bursts.\nALL: save every received burst as last_rx_monitor_capture.wav.", style="Muted.TLabel", justify="left").pack(anchor="w", pady=(4, 8))

        def save_and_close():
            self.save_config()
            self.log(f"RX debug WAV capture set to: {self.rx_capture_mode_var.get()}", "info")
            win.destroy()

        btns = ttk.Frame(frm, style="Panel.TFrame")
        btns.pack(fill="x", pady=(8, 0))
        ttk.Button(btns, text="SAVE", command=save_and_close).pack(side="right")
        ttk.Button(btns, text="CANCEL", command=win.destroy).pack(side="right", padx=(0, 8))

    def audio_setup(self):
        win = tk.Toplevel(self)
        win.title("Audio Devices")
        win.geometry("840x430")
        win.configure(bg=COLORS["bg"])
        tx_devs = filtered_tx_devices()
        rx_devs = filtered_rx_devices()
        tx_map = {format_device(d): d["index"] for d in tx_devs}
        rx_map = {format_device(d): d["index"] for d in rx_devs}
        ttk.Label(win, text="TX Device", background=COLORS["bg"], foreground=COLORS["text"]).pack(anchor="w", padx=10, pady=(10, 2))
        tx_var = tk.StringVar(value=next((k for k, v in tx_map.items() if v == self.tx_device), ""))
        ttk.Combobox(win, textvariable=tx_var, values=list(tx_map.keys()), width=112).pack(fill="x", padx=10)
        ttk.Label(win, text="RX Device", background=COLORS["bg"], foreground=COLORS["text"]).pack(anchor="w", padx=10, pady=(12, 2))
        rx_var = tk.StringVar(value=next((k for k, v in rx_map.items() if v == self.rx_device), ""))
        ttk.Combobox(win, textvariable=rx_var, values=list(rx_map.keys()), width=112).pack(fill="x", padx=10)
        out = tk.Text(win, height=10, bg=COLORS["panel3"], fg=COLORS["text"], relief="flat")
        out.pack(fill="both", expand=True, padx=10, pady=10)

        def say(x):
            out.insert("end", x + "\n")
            out.see("end")

        def save():
            self.tx_device = tx_map.get(tx_var.get())
            self.rx_device = rx_map.get(rx_var.get())
            self.save_config()
            self.log(f"Audio setup saved: TX={self.tx_device}, RX={self.rx_device}")
            self.update_statusbar()
            win.destroy()

        def test_tx():
            try:
                transmit(b"TEST", "HX-F", tx_map.get(tx_var.get()), 0.3)
                say("TEST OK TX")
            except Exception as e:
                say(f"TEST TX ERROR: {e}")

        def test_rx():
            try:
                import sounddevice as sd
                data = sd.rec(int(0.5 * SAMPLE_RATE), samplerate=int(SAMPLE_RATE), channels=1, dtype="float32", device=rx_map.get(rx_var.get()))
                sd.wait()
                say(f"TEST OK RX peak={float(np.max(np.abs(data))):.6f}")
            except Exception as e:
                say(f"TEST RX ERROR: {e}")

        row = ttk.Frame(win)
        row.pack(fill="x", padx=10, pady=(0, 10))
        ttk.Button(row, text="Test TX", command=test_tx).pack(side="left")
        ttk.Button(row, text="Test RX", command=test_rx).pack(side="left", padx=8)
        ttk.Button(row, text="Save", command=save).pack(side="right")

    def station_identity_setup(self):
        win = tk.Toplevel(self)
        win.title("Station Identity")
        win.geometry("420x180")
        win.configure(bg=COLORS["bg"])
        ttk.Label(win, text="Station Callsign", background=COLORS["bg"], foreground=COLORS["text"], font=("Segoe UI", 10, "bold")).pack(anchor="w", padx=14, pady=(14, 4))
        ttk.Label(win, text="This callsign is included with every transmitted HX message.", background=COLORS["bg"], foreground=COLORS["muted"]).pack(anchor="w", padx=14, pady=(0, 8))
        entry_var = tk.StringVar(value=self.clean_callsign())
        ent = tk.Entry(win, textvariable=entry_var, bg=COLORS["panel3"], fg=COLORS["text"], insertbackground=COLORS["text"], relief="flat", font=("Consolas", 14, "bold"))
        ent.pack(fill="x", padx=14, pady=6)
        ent.focus_set()

        def save():
            self.callsign_var.set(entry_var.get().strip().upper() or "NOCALL")
            self.save_config()
            self.log(f"Station identity saved: {self.clean_callsign()}", "ok")
            win.destroy()

        row = ttk.Frame(win)
        row.pack(fill="x", padx=14, pady=14)
        ttk.Button(row, text="Save", command=save).pack(side="right")
        ttk.Button(row, text="Cancel", command=win.destroy).pack(side="right", padx=8)

    def reset_devices(self):
        self.tx_device = None
        self.rx_device = None
        self.save_config()
        self.update_statusbar()
        self.log("Audio devices reset to Windows defaults.")


def main():
    app = HXLAB()
    app.mainloop()


if __name__ == "__main__":
    main()
