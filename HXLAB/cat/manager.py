from __future__ import annotations

from dataclasses import dataclass
import threading
import time
from typing import Callable, Optional

try:
    import serial
    from serial.tools import list_ports
except Exception:  # CAT remains optional when pyserial is unavailable
    serial = None
    list_ports = None


YAESU_MODE_NAMES = {
    "0": "--", "1": "LSB", "2": "USB", "3": "CW-U", "4": "FM", "5": "AM",
    "6": "RTTY-L", "7": "CW-L", "8": "DATA-L", "9": "RTTY-U", "A": "DATA-FM",
    "B": "FM-N", "C": "DATA-U", "D": "AM-N", "E": "PSK", "F": "DATA-FM-N",
}

KENWOOD_MODE_NAMES = {
    "1": "LSB", "2": "USB", "3": "CW", "4": "FM", "5": "AM",
    "6": "FSK", "7": "CW-R", "8": "--", "9": "FSK-R",
}


@dataclass
class CATSettings:
    enabled: bool = False
    port: str = ""
    baud: int = 38400
    radio_model: str = "Yaesu FT-710"
    ptt_method: str = "VOX"  # VOX, CAT, RTS, DTR
    poll_interval: float = 0.75


@dataclass
class RadioState:
    connected: bool = False
    frequency_hz: Optional[int] = None
    mode: str = "--"
    ptt: bool = False
    error: str = ""


def available_ports() -> list[str]:
    if list_ports is None:
        return []
    return [p.device for p in list_ports.comports()]


class CATManager:
    """Threaded optional CAT manager for supported serial-controlled radios."""

    def __init__(self, settings: CATSettings, callback: Optional[Callable[[RadioState], None]] = None):
        self.settings = settings
        self.callback = callback
        self.state = RadioState()
        self._serial = None
        self._lock = threading.RLock()
        self._stop = threading.Event()
        self._thread: Optional[threading.Thread] = None
        self._rx_buffer = ""

    @property
    def connected(self) -> bool:
        return bool(self.state.connected and self._serial is not None)

    @property
    def is_kenwood_ts2000(self) -> bool:
        return "TS-2000" in (self.settings.radio_model or "").upper()

    def connect(self) -> None:
        if not self.settings.enabled:
            raise RuntimeError("CAT is disabled")
        if serial is None:
            raise RuntimeError("pyserial is not installed")
        if not self.settings.port:
            raise RuntimeError("No COM port selected")
        self.disconnect()
        try:
            ser = serial.Serial(
                port=self.settings.port,
                baudrate=int(self.settings.baud),
                bytesize=serial.EIGHTBITS,
                parity=serial.PARITY_NONE,
                stopbits=serial.STOPBITS_ONE,
                timeout=0.15,
                write_timeout=0.5,
                rtscts=False,
                dsrdtr=False,
            )
            # Avoid an unintended keying edge on open.
            ser.rts = False
            ser.dtr = False
            self._serial = ser
            self._rx_buffer = ""
            self._stop.clear()
            self.state = RadioState(connected=True)
            self._emit()
            self._thread = threading.Thread(target=self._poll_loop, name="HX-CAT", daemon=True)
            self._thread.start()
        except Exception as exc:
            self._serial = None
            self.state = RadioState(error=str(exc))
            self._emit()
            raise

    def disconnect(self) -> None:
        self._stop.set()
        with self._lock:
            ser = self._serial
            self._serial = None
            if ser is not None:
                try:
                    ser.rts = False
                    ser.dtr = False
                except Exception:
                    pass
                try:
                    ser.close()
                except Exception:
                    pass
        self.state.connected = False
        self.state.ptt = False
        self._emit()

    def set_settings(self, settings: CATSettings) -> None:
        self.settings = settings

    def ptt_on(self) -> None:
        method = self.settings.ptt_method.upper()
        if method == "VOX":
            return
        self._require_connected()
        with self._lock:
            if method == "CAT":
                self._write("TX;" if self.is_kenwood_ts2000 else "TX1;")
            elif method == "RTS":
                self._serial.rts = True
            elif method == "DTR":
                self._serial.dtr = True
            else:
                raise RuntimeError(f"Unsupported PTT method: {method}")
        self.state.ptt = True
        self._emit()

    def ptt_off(self) -> None:
        method = self.settings.ptt_method.upper()
        if method == "VOX":
            return
        if not self.connected:
            return
        with self._lock:
            if method == "CAT":
                self._write("RX;" if self.is_kenwood_ts2000 else "TX0;")
            elif method == "RTS":
                self._serial.rts = False
            elif method == "DTR":
                self._serial.dtr = False
        self.state.ptt = False
        self._emit()

    def _require_connected(self) -> None:
        if not self.connected:
            raise RuntimeError("CAT is not connected")

    def _write(self, command: str) -> None:
        self._require_connected()
        self._serial.write(command.encode("ascii"))
        self._serial.flush()

    def _query(self, command: str, prefix: str, timeout: float = 0.55) -> Optional[str]:
        deadline = time.monotonic() + timeout
        with self._lock:
            self._write(command)
            while time.monotonic() < deadline and not self._stop.is_set():
                chunk = self._serial.read(128)
                if chunk:
                    self._rx_buffer += chunk.decode("ascii", errors="ignore")
                    while ";" in self._rx_buffer:
                        response, self._rx_buffer = self._rx_buffer.split(";", 1)
                        response += ";"
                        if response.startswith(prefix):
                            return response
                else:
                    time.sleep(0.01)
        return None

    def _poll_loop(self) -> None:
        try:
            while not self._stop.is_set() and self.connected:
                if self.is_kenwood_ts2000:
                    self._poll_kenwood_ts2000()
                else:
                    self._poll_yaesu_ft710()
                self._stop.wait(max(0.2, float(self.settings.poll_interval)))
        except Exception as exc:
            self.state.error = str(exc)
            self.state.connected = False
            self._emit()
            self.disconnect()

    def _poll_yaesu_ft710(self) -> None:
        freq = self._query("FA;", "FA")
        mode = self._query("MD0;", "MD0")
        ptt = self._query("TX;", "TX")
        changed = False
        if freq and len(freq) >= 12:
            try:
                value = int(freq[2:-1])
                if value != self.state.frequency_hz:
                    self.state.frequency_hz = value
                    changed = True
            except ValueError:
                pass
        if mode and len(mode) >= 5:
            value = YAESU_MODE_NAMES.get(mode[3], f"MODE-{mode[3]}")
            if value != self.state.mode:
                self.state.mode = value
                changed = True
        if ptt and len(ptt) >= 4:
            value = ptt[2] in ("1", "2")
            if value != self.state.ptt:
                self.state.ptt = value
                changed = True
        self._finish_poll(changed)

    def _poll_kenwood_ts2000(self) -> None:
        # TS-2000 query commands differ subtly from Yaesu. In particular, an
        # unparameterized TX command keys the transmitter, so PTT state is read
        # from the IF status response instead of ever issuing TX as a query.
        freq = self._query("FA;", "FA")
        mode = self._query("MD;", "MD")
        info = self._query("IF;", "IF")
        changed = False
        if freq and len(freq) >= 14:
            try:
                value = int(freq[2:-1])
                if value != self.state.frequency_hz:
                    self.state.frequency_hz = value
                    changed = True
            except ValueError:
                pass
        if mode and len(mode) >= 4:
            mode_code = mode[2]
            value = KENWOOD_MODE_NAMES.get(mode_code, f"MODE-{mode_code}")
            if value != self.state.mode:
                self.state.mode = value
                changed = True
        # Kenwood IF response: after the 2-character command are frequency,
        # step, RIT/XIT and memory fields; the TX/RX flag follows at index 28
        # (0=RX, 1=TX) in the standard TS-2000 fixed-width response.
        if info and len(info) > 29 and info[28] in ("0", "1"):
            value = info[28] == "1"
            if value != self.state.ptt:
                self.state.ptt = value
                changed = True
        self._finish_poll(changed)

    def _finish_poll(self, changed: bool) -> None:
        if changed or self.state.error:
            self.state.error = ""
            self._emit()

    def _emit(self) -> None:
        if self.callback:
            snapshot = RadioState(**self.state.__dict__)
            try:
                self.callback(snapshot)
            except Exception:
                pass
