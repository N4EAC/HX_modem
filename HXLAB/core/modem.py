import numpy as np
from .fec import MODES, fec_encode, fec_decode, fec_decode_soft
from .frame import PILOT_BITS, build_frame_bits, split_frame_bits, parse_payload_bits

SAMPLE_RATE = 44100.0
SYMBOL_RATE = 122.5
SAMPLES_PER_SYMBOL = int(SAMPLE_RATE / SYMBOL_RATE)  # 360 at 44100 / 122.5
TONE_FREQ = 1470.0
# Retained only so dormant experimental decoder helpers can import safely.
# HX-R is not exposed, selected, transmitted, or detected in v0.5.3.
HX_R_CARRIERS = (735.0, 1470.0, 2205.0)
HX_R_PAYLOAD_COPIES = 5
HXR_PILOT_BITS = np.array([int(b) for b in "010001100101010010001110010001011111111010101000001011001011010010110100001001010010000000001111"], dtype=np.int8)

def estimate_tx_seconds(payload: bytes | str, mode_name: str) -> float:
    if isinstance(payload, str):
        payload = payload.encode("utf-8")
    bits = build_frame_bits(payload, mode_name)
    reps = MODES[mode_name]["repetition"]
    return (len(bits) * reps) / SYMBOL_RATE


def hx_encode(payload: bytes, mode_name: str) -> np.ndarray:
    reps = MODES[mode_name]["repetition"]
    bits = build_frame_bits(payload, mode_name)
    coded = fec_encode(bits, reps)
    symbols = (2.0 * coded.astype(np.float32)) - 1.0
    return np.repeat(symbols, SAMPLES_PER_SYMBOL).astype(np.float32)


def bpsk_demodulate(samples: np.ndarray, start_offset: int = 0) -> tuple[np.ndarray, np.ndarray]:
    if start_offset > 0:
        samples = samples[start_offset:]
    n = len(samples) // SAMPLES_PER_SYMBOL
    if n <= 0:
        return np.zeros(0, dtype=np.int8), np.zeros(0, dtype=np.float32)
    vals = samples[: n * SAMPLES_PER_SYMBOL].reshape(n, SAMPLES_PER_SYMBOL).mean(axis=1)
    return (vals > 0).astype(np.int8), vals.astype(np.float32)


def estimate_snr_from_known_symbols(sym_vals: np.ndarray, known_bits: np.ndarray) -> float:
    """Estimate modem-internal SNR at BPSK decision points."""
    if len(sym_vals) == 0 or len(known_bits) == 0:
        return 0.0
    n = min(len(sym_vals), len(known_bits))
    y = sym_vals[:n].astype(np.float64)
    s = (2.0 * known_bits[:n].astype(np.float64)) - 1.0
    amp = float(np.mean(y * s))
    residual = y - (amp * s)
    noise_power = float(np.mean(residual * residual)) + 1e-12
    signal_power = float(amp * amp)
    if signal_power <= 1e-12:
        return 0.0
    snr = 10.0 * np.log10(signal_power / noise_power)
    if not np.isfinite(snr):
        return 0.0
    return float(max(-40.0, min(60.0, snr)))


def _decode_once(samples: np.ndarray, assumed_mode: str, offset: int = 0, invert: bool = False):
    if invert:
        samples = -samples
    reps = MODES[assumed_mode]["repetition"]
    coded_bits, vals = bpsk_demodulate(samples, offset)
    decoded = fec_decode_soft(vals, reps)
    _, hdr, payload_bits = split_frame_bits(decoded)
    mode_hdr, payload = parse_payload_bits(hdr, payload_bits)
    coded_pilot = fec_encode(PILOT_BITS, reps)
    snr_db = estimate_snr_from_known_symbols(vals[:len(coded_pilot)], coded_pilot)
    return snr_db, mode_hdr, payload


def _best_offsets_by_pilot(samples: np.ndarray, mode: str, max_candidates: int = 24):
    reps = MODES[mode]["repetition"]
    coded_pilot = fec_encode(PILOT_BITS, reps)
    pilot_sign = (2.0 * coded_pilot.astype(np.float32)) - 1.0
    n_pilot = len(coded_pilot)
    max_offset = len(samples) - (n_pilot * SAMPLES_PER_SYMBOL)
    if max_offset <= 0:
        return []

    coarse_step = max(1, SAMPLES_PER_SYMBOL // 2)
    scored = []
    for off in range(0, max_offset, coarse_step):
        _, vals = bpsk_demodulate(samples, off)
        if len(vals) < n_pilot:
            continue
        corr = float(np.sum(vals[:n_pilot] * pilot_sign))
        scored.append((corr, off, False))
        scored.append((-corr, off, True))
    scored.sort(reverse=True, key=lambda x: x[0])

    refined = []
    for _score, off, inv in scored[:max_candidates]:
        lo = max(0, off - SAMPLES_PER_SYMBOL)
        hi = min(max_offset, off + SAMPLES_PER_SYMBOL)
        step = max(1, SAMPLES_PER_SYMBOL // 16)
        for roff in range(lo, max(lo + 1, hi), step):
            work = -samples if inv else samples
            _, vals = bpsk_demodulate(work, roff)
            if len(vals) < n_pilot:
                continue
            corr = float(np.sum(vals[:n_pilot] * pilot_sign))
            refined.append((corr, roff, inv))
    refined.sort(reverse=True, key=lambda x: x[0])

    out = []
    seen = set()
    for item in refined:
        key = (item[1], item[2])
        if key not in seen:
            seen.add(key)
            out.append(item)
        if len(out) >= max_candidates:
            break
    return out


def hx_decode_search_timing(samples: np.ndarray, assumed_mode: str, hint_start_sample: int | None = None):
    """Decode by searching for the FEC-coded pilot.

    The hint is intentionally accepted for API compatibility but not forced;
    the v0.1.13 baseline search is more reliable on live VB-CABLE captures.
    """
    last = None
    for _score, off, inv in _best_offsets_by_pilot(samples, assumed_mode, max_candidates=24):
        try:
            return _decode_once(samples, assumed_mode, off, inv)
        except Exception as e:
            last = e
    if last:
        raise last
    raise ValueError("No pilot found")


def hx_decode(samples: np.ndarray, assumed_mode: str):
    return _decode_once(samples, assumed_mode, 0, False)


def choose_mode(snr_db: float) -> str:
    """Choose between the two supported HX modes.

    HX-N is the robust/poor-conditions mode; HX-F is the faster mode.
    """
    if snr_db < 9.0:
        return "HX-N"
    return "HX-F"


def add_awgn(samples: np.ndarray, snr_db: float) -> np.ndarray:
    sig_power = np.mean(samples ** 2)
    noise_power = sig_power / (10 ** (snr_db / 10.0))
    noise = np.sqrt(noise_power) * np.random.randn(*samples.shape)
    return (samples + noise.astype(samples.dtype)).astype(np.float32)
