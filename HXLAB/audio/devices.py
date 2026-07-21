from __future__ import annotations
import sounddevice as sd

BLOCKED_HOSTS = {"Windows WDM-KS"}


def hostapi_name(index: int) -> str:
    try:
        info = sd.query_hostapis(index)
        return info.get("name", "")
    except Exception:
        return ""


def query_devices():
    devices = sd.query_devices()
    hostapis = sd.query_hostapis()
    rows = []
    for idx, d in enumerate(devices):
        hidx = d.get("hostapi", -1)
        hname = hostapis[hidx].get("name", "") if 0 <= hidx < len(hostapis) else "Unknown"
        rows.append({
            "index": idx,
            "name": d.get("name", ""),
            "hostapi": hname,
            "in": int(d.get("max_input_channels", 0)),
            "out": int(d.get("max_output_channels", 0)),
            "default_sr": float(d.get("default_samplerate", 0.0)),
        })
    return rows


def filtered_rx_devices():
    return [d for d in query_devices() if d["in"] > 0 and d["hostapi"] not in BLOCKED_HOSTS]


def filtered_tx_devices():
    return [d for d in query_devices() if d["out"] > 0 and d["hostapi"] not in BLOCKED_HOSTS]


def format_device(d: dict) -> str:
    return f'{d["index"]}: {d["name"]} [{d["hostapi"]}] in={d["in"]} out={d["out"]} sr={d["default_sr"]:.0f}'
