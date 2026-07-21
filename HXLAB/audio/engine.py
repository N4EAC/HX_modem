from __future__ import annotations
import os
import wave
import json
import numpy as np
import sounddevice as sd
from math import pi

from HXLAB.core.modem import SAMPLE_RATE, TONE_FREQ, HX_R_CARRIERS, HX_R_PAYLOAD_COPIES, HXR_PILOT_BITS, hx_encode, hx_decode_search_timing, estimate_tx_seconds, SAMPLES_PER_SYMBOL, estimate_snr_from_known_symbols
from HXLAB.core.fec import MODES, fec_encode, fec_decode, fec_decode_soft, bits_to_bytes, check_crc
from HXLAB.core.frame import PILOT_BITS, HEADER_LEN_BITS, HEADER_LEN_BYTES, split_frame_bits, parse_payload_bits, parse_header, build_frame_bits


def mix_to_tone(baseband: np.ndarray, level: float = 0.8) -> np.ndarray:
    t = np.arange(len(baseband)) / SAMPLE_RATE
    audio = baseband * np.cos(2.0 * pi * TONE_FREQ * t)
    audio = audio / (np.max(np.abs(audio)) + 1e-9)
    return (audio * float(level)).astype(np.float32)


def mix_down_from_tone(audio: np.ndarray) -> np.ndarray:
    t = np.arange(len(audio)) / SAMPLE_RATE
    return (audio * np.cos(2.0 * pi * TONE_FREQ * t)).astype(np.float32)


def save_wav(path: str, audio: np.ndarray):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    data = np.clip(audio, -1, 1)
    pcm = (data * 32767.0).astype(np.int16)
    with wave.open(path, "wb") as w:
        w.setnchannels(1)
        w.setsampwidth(2)
        w.setframerate(int(SAMPLE_RATE))
        w.writeframes(pcm.tobytes())


def read_wav(path: str) -> np.ndarray:
    with wave.open(path, "rb") as w:
        frames = w.readframes(w.getnframes())
        channels = w.getnchannels()
        sw = w.getsampwidth()
        if sw != 2:
            raise ValueError("Only 16-bit WAV supported")
        data = np.frombuffer(frames, dtype=np.int16).astype(np.float32) / 32768.0
        if channels > 1:
            data = data.reshape(-1, channels).mean(axis=1)
        return data.astype(np.float32)




def _coprime_step(n: int, preferred: int) -> int:
    import math
    if n <= 1:
        return 1
    step = max(1, preferred % n)
    while math.gcd(step, n) != 1:
        step += 1
        if step >= n:
            step = 1
    return step


def _hxr_permutation(n: int, copy_index: int) -> np.ndarray:
    if n <= 0:
        return np.zeros(0, dtype=np.int64)
    preferred = (1, 5, 7, 11, 13)[copy_index % 5]
    step = _coprime_step(n, preferred)
    shift = (copy_index * 17) % n
    return ((np.arange(n, dtype=np.int64) * step + shift) % n).astype(np.int64)


def _hx_r_audio(payload: bytes, level: float = 0.8) -> np.ndarray:
    """New HX-R: 3-carrier BPSK with 5 interleaved payload copies.

    Pilot and header are sent simultaneously on all carriers for frequency
    diversity.  Five independently interleaved payload copies are spread
    over the three carriers in parallel (2/2/1 copies), providing both time
    and frequency diversity against voice bursts and selective fading.
    """
    bits = build_frame_bits(payload, "HX-R")
    # build_frame_bits uses the common single-carrier pilot.  HX-R replaces
    # that pilot with its own longer orthogonal sequence while preserving the
    # complete header and payload bit ranges.
    common_pilot_n = len(PILOT_BITS)
    header_bits = bits[common_pilot_n:common_pilot_n + HEADER_LEN_BITS].astype(np.int8)
    payload_bits = bits[common_pilot_n + HEADER_LEN_BITS:].astype(np.int8)
    prefix = np.concatenate([HXR_PILOT_BITS, header_bits]).astype(np.int8)
    prefix_n = len(prefix)
    p = len(payload_bits)
    carrier_payloads = [[] for _ in HX_R_CARRIERS]
    for r in range(HX_R_PAYLOAD_COPIES):
        perm = _hxr_permutation(p, r)
        carrier_payloads[r % len(HX_R_CARRIERS)].append(payload_bits[perm])
    streams=[]
    for chunks in carrier_payloads:
        tail = np.concatenate(chunks).astype(np.int8) if chunks else np.zeros(0,dtype=np.int8)
        streams.append(np.concatenate([prefix, tail]).astype(np.int8))
    n_symbols=max(len(x) for x in streams)
    n_samples=n_symbols*SAMPLES_PER_SYMBOL
    t=np.arange(n_samples,dtype=np.float64)/SAMPLE_RATE
    audio=np.zeros(n_samples,dtype=np.float64)
    for freq,stream in zip(HX_R_CARRIERS,streams):
        syms=(2.0*stream.astype(np.float64))-1.0
        base=np.zeros(n_symbols,dtype=np.float64)
        base[:len(syms)]=syms
        expanded=np.repeat(base,SAMPLES_PER_SYMBOL)
        audio += expanded*np.cos(2.0*pi*freq*t)
    audio /= (np.max(np.abs(audio))+1e-9)
    return (audio*float(level)).astype(np.float32)


def _mixed_for_freq(audio: np.ndarray, freq: float) -> np.ndarray:
    idx=np.arange(len(audio),dtype=np.float64)
    carrier=np.exp(-1j*2.0*pi*float(freq)*idx/SAMPLE_RATE)
    return (audio.astype(np.float64)*carrier*2.0).astype(np.complex64)


def _hxr_carrier_values(audio: np.ndarray, offset: int = 0):
    out=[]
    for freq in HX_R_CARRIERS:
        mixed=_mixed_for_freq(audio,freq)
        prefix=np.empty(len(mixed)+1,dtype=np.complex128); prefix[0]=0.0
        prefix[1:]=np.cumsum(mixed,dtype=np.complex128)
        out.append(_symbol_values_from_prefix(prefix,offset))
    return out


def _hxr_track_carrier(vals: np.ndarray, pilot_bits: np.ndarray) -> tuple[np.ndarray, float]:
    """Decision-directed BPSK carrier tracker for one HX-R carrier.

    A fixed carrier phase estimate is adequate for short synthetic captures,
    but a small Windows/VB-CABLE sample-clock mismatch causes the phase to
    rotate over a 10+ second HX-R frame.  Track that slow rotation symbol by
    symbol so the payload remains coherent after the pilot/header.
    """
    if len(vals) < len(pilot_bits):
        raise ValueError("Not enough HX-R pilot symbols")
    pilot_sign = (2.0 * pilot_bits.astype(np.float32)) - 1.0
    c = np.sum(vals[:len(pilot_bits)] * pilot_sign)
    phase = float(np.angle(c))
    out = np.empty(len(vals), dtype=np.float32)

    # Conservative loop gain: follows slow sound-card clock drift while
    # resisting voice/noise excursions.  Pilot symbols use their known sign;
    # later symbols use decision-directed signs.
    alpha = 0.035
    for i, z in enumerate(vals):
        rot = z * np.exp(-1j * phase)
        if i < len(pilot_sign):
            decision = float(pilot_sign[i])
        else:
            decision = 1.0 if rot.real >= 0.0 else -1.0
        out[i] = float(rot.real)
        err = float(np.angle(rot * decision))
        # Limit one noisy symbol from pulling the loop far off carrier.
        err = max(-0.35, min(0.35, err))
        phase += alpha * err

    pilot_real = out[:len(pilot_sign)]
    quality = float(abs(np.sum(pilot_real * pilot_sign)) /
                    np.sqrt(max(float(np.sum(pilot_real * pilot_real)) * len(pilot_sign), 1e-12)))
    return out, max(quality, 0.05)


def _hxr_oriented_values(audio: np.ndarray, offset: int = 0):
    vals_list = _hxr_carrier_values(audio, offset)
    oriented = []
    qualities = []
    for vals in vals_list:
        real, quality = _hxr_track_carrier(vals, HXR_PILOT_BITS)
        oriented.append(real)
        qualities.append(quality)
    return oriented, np.asarray(qualities, dtype=np.float32)


def _hxr_decode_payload(audio: np.ndarray, payload_len: int):
    peak=float(np.max(np.abs(audio))+1e-9)
    if peak<1e-6: raise ValueError("Signal too weak")
    work=np.asarray(audio,dtype=np.float32)/peak
    vals,qualities=_hxr_oriented_values(work,0)
    prefix_n=len(HXR_PILOT_BITS)+HEADER_LEN_BITS
    pbits=int(payload_len)*8
    needed=[2*pbits,2*pbits,pbits]
    copies=[]
    copy_map=((0,3),(1,4),(2,))
    for ci,(v,need) in enumerate(zip(vals,needed)):
        tail=v[prefix_n:prefix_n+need]
        if len(tail)<need: raise ValueError("Not enough HX-R payload symbols")
        for seg,copy_index in enumerate(copy_map[ci]):
            seq=tail[seg*pbits:(seg+1)*pbits]
            perm=_hxr_permutation(pbits,copy_index)
            restored=np.zeros(pbits,dtype=np.float32)
            restored[perm]=seq
            copies.append(restored*qualities[ci])
    if len(copies)!=HX_R_PAYLOAD_COPIES: raise ValueError("HX-R copy reconstruction failed")
    combined=np.sum(np.stack(copies,axis=0),axis=0)
    for inv in (False,True):
        bits=(((-combined if inv else combined)>=0.0)).astype(np.int8)
        raw=bits_to_bytes(bits[:pbits])[:payload_len]
        ok,payload=check_crc(raw)
        if ok:
            snr=float(10.0*np.log10((float(np.mean(np.abs(combined)))**2+1e-12)/(float(np.var(combined-np.sign(combined)*np.mean(np.abs(combined))))+1e-12)))
            return {"snr":max(-40.0,min(60.0,snr)),"mode_header":"HX-R","payload":payload,"peak":peak,"decode_mode":"HX-R","payload_decoder":"3-carrier interleaved soft"}
    raise ValueError("Payload CRC error")


def tx_audio_for_payload(payload: bytes, mode: str, level: float = 0.8) -> np.ndarray:
    if mode not in ("HX-F", "HX-N"):
        raise ValueError(f"Unsupported HX mode: {mode}")
    return mix_to_tone(hx_encode(payload, mode), level=level)


def transmit(payload: bytes, mode: str, tx_device: int | None, level: float = 0.8):
    """Transmit one frame.

    Station-to-station testing on Windows/VB-CABLE showed that the last
    fraction of a second can be lost when the stream closes immediately after
    the frame.  Append a short silence drain guard so the actual modem frame
    is never the final samples handed to the audio subsystem.
    """
    frame_audio = tx_audio_for_payload(payload, mode, level)
    guard = np.zeros(int(0.45 * SAMPLE_RATE), dtype=np.float32)
    audio = np.concatenate([frame_audio, guard]).astype(np.float32)
    sd.play(audio, samplerate=int(SAMPLE_RATE), device=tx_device)
    sd.wait()
    return len(frame_audio) / SAMPLE_RATE


def _complex_mixed(audio: np.ndarray) -> np.ndarray:
    idx = np.arange(len(audio), dtype=np.float64)
    carrier = np.exp(-1j * 2.0 * pi * TONE_FREQ * idx / SAMPLE_RATE)
    return (audio.astype(np.float64) * carrier * 2.0).astype(np.complex64)


def _symbol_values_from_prefix(prefix: np.ndarray, offset: int) -> np.ndarray:
    available = len(prefix) - 1 - offset
    n = available // SAMPLES_PER_SYMBOL
    if n <= 0:
        return np.zeros(0, dtype=np.complex64)
    starts = offset + (np.arange(n) * SAMPLES_PER_SYMBOL)
    ends = starts + SAMPLES_PER_SYMBOL
    vals = (prefix[ends] - prefix[starts]) / float(SAMPLES_PER_SYMBOL)
    return vals.astype(np.complex64)


def _decode_audio_capture_quadrature(audio: np.ndarray, mode: str):
    reps = MODES[mode]["repetition"]
    coded_pilot = fec_encode(PILOT_BITS, reps)
    pilot_sign = (2.0 * coded_pilot.astype(np.float32)) - 1.0
    n_pilot = len(coded_pilot)

    max_offset = len(audio) - (n_pilot * SAMPLES_PER_SYMBOL)
    if max_offset <= 0:
        raise ValueError("Recording too short for pilot search")

    mixed = _complex_mixed(audio)
    prefix = np.empty(len(mixed) + 1, dtype=np.complex128)
    prefix[0] = 0.0
    prefix[1:] = np.cumsum(mixed, dtype=np.complex128)

    # Coarse then fine search. Correlation magnitude is phase independent.
    coarse_step = max(1, SAMPLES_PER_SYMBOL // 2)
    coarse = []
    for off in range(0, max_offset, coarse_step):
        vals = _symbol_values_from_prefix(prefix, off)
        if len(vals) < n_pilot:
            continue
        c = np.sum(vals[:n_pilot] * pilot_sign)
        coarse.append((float(abs(c)), off, c))
    coarse.sort(reverse=True, key=lambda x: x[0])

    candidates = []
    fine_step = max(1, SAMPLES_PER_SYMBOL // 24)
    for _score, off, _c in coarse[:18]:
        lo = max(0, off - SAMPLES_PER_SYMBOL)
        hi = min(max_offset, off + SAMPLES_PER_SYMBOL)
        for roff in range(lo, max(lo + 1, hi), fine_step):
            vals = _symbol_values_from_prefix(prefix, roff)
            if len(vals) < n_pilot:
                continue
            c = np.sum(vals[:n_pilot] * pilot_sign)
            candidates.append((float(abs(c)), roff, c))
    candidates.sort(reverse=True, key=lambda x: x[0])

    last = None
    tried = set()
    for _score, off, c in candidates[:48]:
        if off in tried:
            continue
        tried.add(off)
        vals = _symbol_values_from_prefix(prefix, off)
        if len(vals) < n_pilot:
            continue
        phase = np.angle(c)
        real_vals = (vals * np.exp(-1j * phase)).real.astype(np.float32)
        coded_bits = (real_vals > 0).astype(np.int8)
        for inv in (False, True):
            work_vals = -real_vals if inv else real_vals
            try:
                decoded = fec_decode_soft(work_vals, reps)
                _pilot, hdr, payload_bits = split_frame_bits(decoded)
                mode_hdr, payload = parse_payload_bits(hdr, payload_bits)
                snr = estimate_snr_from_known_symbols(real_vals[:n_pilot], coded_pilot)
                return {"snr": snr, "mode_header": mode_hdr, "payload": payload}
            except Exception as e:
                last = e
                continue
    if last:
        raise last
    raise ValueError("No pilot found")


def _decode_audio_capture_locked(audio: np.ndarray, mode: str, locked_start_sample: int, strict_start: bool = False):
    """Decode a frame only around a previously validated pilot position.

    Unlike the generic capture decoder, this function never searches the
    entire recording for a new pilot.  That is important for long HX-N/HX-R
    frames mixed with speech, where a later voice peak can otherwise become
    the strongest correlation candidate and invalidate a header that already
    passed CRC during the live header stage.
    """
    if audio is None or len(audio) < SAMPLES_PER_SYMBOL * 16:
        raise ValueError("Frame too short")

    peak = float(np.max(np.abs(audio)) + 1e-9)
    if peak < 1e-6:
        raise ValueError("Signal too weak")
    work = np.asarray(audio, dtype=np.float32) / peak

    reps = MODES[mode]["repetition"]
    coded_pilot = fec_encode(PILOT_BITS, reps)
    pilot_sign = (2.0 * coded_pilot.astype(np.float32)) - 1.0
    n_pilot = len(coded_pilot)

    mixed = _complex_mixed(work)
    prefix = np.empty(len(mixed) + 1, dtype=np.complex128)
    prefix[0] = 0.0
    prefix[1:] = np.cumsum(mixed, dtype=np.complex128)

    # v0.4.25 strict mode is used after a header has already passed CRC.
    # In that path sample zero is the validated pilot start, so do not search
    # around it again.  Non-strict callers retain the small refinement window.
    center = int(max(0, min(len(work) - 1, locked_start_sample)))
    if strict_start:
        lo = hi = center
    else:
        lo = max(0, center - SAMPLES_PER_SYMBOL)
        hi = min(len(work) - (n_pilot * SAMPLES_PER_SYMBOL), center + SAMPLES_PER_SYMBOL)
    if hi < lo:
        raise ValueError("Not enough samples around locked pilot")

    fine_step = max(1, SAMPLES_PER_SYMBOL // 24)
    candidates = []
    for off in range(lo, hi + 1, fine_step):
        vals = _symbol_values_from_prefix(prefix, off)
        if len(vals) < n_pilot:
            continue
        c = np.sum(vals[:n_pilot] * pilot_sign)
        candidates.append((float(abs(c)), off, c))
    candidates.sort(reverse=True, key=lambda x: x[0])

    last = None
    for _score, off, c in candidates:
        vals = _symbol_values_from_prefix(prefix, off)
        phase = np.angle(c)
        real_vals = (vals * np.exp(-1j * phase)).real.astype(np.float32)
        coded_bits = (real_vals > 0).astype(np.int8)
        for inv in (False, True):
            work_vals = -real_vals if inv else real_vals
            try:
                decoded = fec_decode_soft(work_vals, reps)
                _pilot, hdr, payload_bits = split_frame_bits(decoded)
                mode_hdr, payload = parse_payload_bits(hdr, payload_bits)
                snr = estimate_snr_from_known_symbols(real_vals[:n_pilot], coded_pilot)
                return {
                    "snr": snr,
                    "mode_header": mode_hdr,
                    "payload": payload,
                    "peak": peak,
                    "decode_mode": mode,
                    "locked_start_sample": int(off),
                }
            except Exception as e:
                last = e

    if last:
        raise last
    raise ValueError("No valid decode at locked pilot")



def _decode_locked_payload_only(audio: np.ndarray, mode: str, payload_len: int, use_soft: bool = True):
    if mode == "HX-R":
        return _hxr_decode_payload(audio, payload_len)
    """Decode only the payload using a previously CRC-validated header.

    The frame must begin exactly at the validated pilot.  This function uses
    the pilot only to estimate carrier phase, skips the already-validated
    header, combines the repeated payload symbols, and validates the payload
    CRC.  It never reparses or re-searches the header.
    """
    if audio is None or len(audio) < SAMPLES_PER_SYMBOL * 16:
        raise ValueError("Frame too short")
    payload_len = int(payload_len)
    if payload_len < 2:
        raise ValueError("Invalid payload length")

    peak = float(np.max(np.abs(audio)) + 1e-9)
    if peak < 1e-6:
        raise ValueError("Signal too weak")
    work = np.asarray(audio, dtype=np.float32) / peak
    reps = MODES[mode]["repetition"]
    coded_pilot = fec_encode(PILOT_BITS, reps)
    pilot_sign = (2.0 * coded_pilot.astype(np.float32)) - 1.0
    n_pilot_coded = len(coded_pilot)
    header_coded_symbols = HEADER_LEN_BITS * reps
    payload_coded_symbols = payload_len * 8 * reps
    needed_symbols = n_pilot_coded + header_coded_symbols + payload_coded_symbols

    mixed = _complex_mixed(work)
    prefix = np.empty(len(mixed) + 1, dtype=np.complex128)
    prefix[0] = 0.0
    prefix[1:] = np.cumsum(mixed, dtype=np.complex128)
    vals = _symbol_values_from_prefix(prefix, 0)
    if len(vals) < needed_symbols:
        raise ValueError("Not enough symbols for payload")

    c = np.sum(vals[:n_pilot_coded] * pilot_sign)
    phase = np.angle(c)
    real_vals = (vals * np.exp(-1j * phase)).real.astype(np.float32)
    payload_vals = real_vals[n_pilot_coded + header_coded_symbols:needed_symbols]

    last_error = None
    for inverted in (False, True):
        oriented = -payload_vals if inverted else payload_vals
        try:
            if use_soft:
                payload_bits = fec_decode_soft(oriented, reps)
            else:
                payload_bits = fec_decode((oriented > 0.0).astype(np.int8), reps)
            raw = bits_to_bytes(payload_bits[:payload_len * 8])[:payload_len]
            ok, payload = check_crc(raw)
            if not ok:
                raise ValueError("Payload CRC error")
            snr = estimate_snr_from_known_symbols(real_vals[:n_pilot_coded], coded_pilot)
            return {
                "snr": snr, "mode_header": mode, "payload": payload,
                "peak": peak, "decode_mode": mode,
                "payload_decoder": "soft" if use_soft else "hard",
                "polarity_inverted": bool(inverted),
            }
        except Exception as exc:
            last_error = exc
    if last_error:
        raise last_error
    raise ValueError("Payload CRC error")

def _decode_mode_candidates(mode: str) -> list[str]:
    """Return decode modes to try. AUTO really means try every current HX mode."""
    if mode == "AUTO":
        # Fast first keeps successful HX-F decodes quick; robust last avoids
        # spending time on long FEC paths unless needed.
        return ["HX-F", "HX-N"]
    return [mode]

def decode_audio_capture(audio: np.ndarray, mode: str, hint_start_sample: int | None = None):
    peak = float(np.max(np.abs(audio)) + 1e-9)
    norm = audio / peak

    last_error = None
    for try_mode in _decode_mode_candidates(mode):
        if try_mode == "HX-R":
            try:
                info=probe_frame_header(norm,"HX-R")
                if len(norm)<info["frame_end_sample"]:
                    raise ValueError("Frame too short")
                frame=norm[info["start_sample"]:info["frame_end_sample"]]
                result=_hxr_decode_payload(frame,info["payload_len"])
                result["peak"]=peak
                return result
            except Exception as hxr_error:
                last_error=hxr_error
                continue
        # Preferred for independent TX/RX instances: robust to arbitrary carrier phase.
        try:
            result = _decode_audio_capture_quadrature(norm, try_mode)
            result["peak"] = peak
            result["decode_mode"] = try_mode
            return result
        except Exception as quad_error:
            last_error = quad_error
            # Fallback to the original v0.1.13 real-mixer path for compatibility.
            try:
                baseband = mix_down_from_tone(norm)
                snr, hdr, payload = hx_decode_search_timing(baseband, try_mode, hint_start_sample=hint_start_sample)
                return {"peak": peak, "snr": snr, "mode_header": hdr, "payload": payload, "decode_mode": try_mode}
            except Exception as e:
                last_error = e
                continue

    if last_error:
        raise last_error
    raise ValueError("No decode modes available")


def receive_once(duration: float, mode: str, rx_device: int | None):
    n = int(duration * SAMPLE_RATE)
    audio = sd.rec(n, samplerate=int(SAMPLE_RATE), channels=1, dtype="float32", device=rx_device)
    sd.wait()
    return decode_audio_capture(audio[:, 0], mode)


def live_loopback(payload: bytes, mode: str, tx_device: int | None, rx_device: int | None, capture_path: str, level: float = 0.8):
    """Known-good v0.1.13 style loopback: independent RX thread + TX stream.

    This avoids the earlier sd.rec/sd.play interaction and keeps the stable
    v0.1.13 behavior while the v0.2 UI evolves.
    """
    import threading
    import time

    frame_audio = tx_audio_for_payload(payload, mode, level)
    tx_len = len(frame_audio)
    tx_time = tx_len / SAMPLE_RATE
    tx_audio = np.concatenate([frame_audio, np.zeros(int(0.45 * SAMPLE_RATE), dtype=np.float32)]).astype(np.float32)
    pre_s = 0.50
    post_s = 1.25
    pre = int(pre_s * SAMPLE_RATE)
    post = int(post_s * SAMPLE_RATE)
    total = pre + tx_len + post
    captured = np.zeros(total, dtype=np.float32)

    def rx_worker():
        with sd.InputStream(samplerate=int(SAMPLE_RATE), channels=1, dtype="float32", device=rx_device) as istream:
            got = 0
            while got < total:
                block, _overflowed = istream.read(min(2048, total - got))
                mono = block[:, 0]
                captured[got: got + len(mono)] = mono
                got += len(mono)

    th = threading.Thread(target=rx_worker, daemon=True)
    th.start()
    time.sleep(0.25)

    with sd.OutputStream(samplerate=int(SAMPLE_RATE), channels=1, dtype="float32", device=tx_device) as ostream:
        ostream.write(tx_audio.reshape(-1, 1))

    th.join(timeout=(total / SAMPLE_RATE) + 3.0)
    save_wav(capture_path, captured)

    peak = float(np.max(np.abs(captured)) + 1e-9)

    # Decode only around the expected TX window. This avoids false locks in
    # pre/post silence but still leaves enough margin for VB-CABLE latency.
    start = max(0, pre - int(0.20 * SAMPLE_RATE))
    end = min(len(captured), pre + tx_len + int(0.75 * SAMPLE_RATE))
    result = decode_audio_capture(captured[start:end], mode)
    result["peak"] = peak
    result["tx_time"] = tx_time
    result["capture_time"] = total / SAMPLE_RATE
    result["capture_path"] = capture_path
    return result

def suggested_capture_time(payload: bytes, mode: str) -> float:
    return estimate_tx_seconds(payload, mode) + 2.0



def _stream_window_seconds(mode: str) -> float:
    """Maximum RX Monitor burst window for the current mode.

    v0.2.14 extends these limits for very long station messages, especially
    HX-R.  The modem frame already carries a payload length and CRC, but the
    station RX monitor does not know the final payload length until after it
    has captured enough audio to decode the frame.  Therefore the monitor uses
    audio energy as a physical end-of-message signal and keeps a generous
    safety maximum only to avoid infinite captures if a device sticks open.
    
    These limits do not change the modem format; they only control how long
    the RX monitor is willing to keep recording a detected burst.
    """
    if mode == "AUTO":
        return 100.0
    if mode == "HX-N":
        return 100.0
    return 40.0


def _expected_tx_seconds_for_short_frame(mode: str) -> float:
    # RX Monitor uses this only to choose a maximum burst window.
    # Station identity makes payloads variable length, so use conservative
    # fixed windows rather than estimating from the old HELLO HX test frame.
    return _stream_window_seconds(mode) - 2.4




def detect_hx_preamble(audio: np.ndarray, mode: str) -> dict:
    """Return the strongest normalized HX pilot correlation in *audio*.

    This detector is intentionally independent of raw audio level.  It looks
    for the known HX pilot bit pattern at the HX carrier and symbol timing, so
    voice, CW, FT8, static, and steady tones do not make the channel busy.
    """
    if audio is None or len(audio) < SAMPLES_PER_SYMBOL * 8:
        return {"score": 0.0, "mode": None}

    # Limit work to the most recent four seconds; this is enough for the
    # longest current repeated pilot (HX-R is about 2.6 seconds).
    max_n = int(4.0 * SAMPLE_RATE)
    work = np.asarray(audio[-max_n:], dtype=np.float32)
    peak = float(np.max(np.abs(work)) + 1e-12)
    if peak < 1e-5:
        return {"score": 0.0, "mode": None}
    work = work / peak

    mixed = _complex_mixed(work)
    prefix = np.empty(len(mixed) + 1, dtype=np.complex128)
    prefix[0] = 0.0
    prefix[1:] = np.cumsum(mixed, dtype=np.complex128)

    best_score = 0.0
    best_mode = None
    best_start_sample = None
    work_base_sample = max(0, len(audio) - len(work))
    modes = _decode_mode_candidates(mode)
    # Twelve timing phases is a good compromise between acquisition accuracy
    # and continuous real-time CPU cost.
    phase_step = max(1, SAMPLES_PER_SYMBOL // 12)

    for try_mode in modes:
        if try_mode == "HX-R":
            # Multicarrier pilot: precompute each mixed stream once.  The
            # earlier implementation repeated three full mixes for every
            # timing phase, starving the live audio reader.
            carrier_prefixes = []
            for freq in HX_R_CARRIERS:
                m = _mixed_for_freq(work, freq)
                pf = np.empty(len(m) + 1, dtype=np.complex128)
                pf[0] = 0.0
                pf[1:] = np.cumsum(m, dtype=np.complex128)
                carrier_prefixes.append(pf)
            ps = (2.0 * HXR_PILOT_BITS.astype(np.float32)) - 1.0
            for phase in range(0, SAMPLES_PER_SYMBOL, phase_step):
                carrier_scores=[]
                for pf in carrier_prefixes:
                    vals=_symbol_values_from_prefix(pf,phase)
                    if len(vals)<len(HXR_PILOT_BITS): continue
                    corr=np.correlate(vals,ps.astype(np.complex64),mode="valid")
                    power=np.abs(vals)**2
                    cs=np.empty(len(power)+1,dtype=np.float64); cs[0]=0.0; cs[1:]=np.cumsum(power,dtype=np.float64)
                    wp=cs[len(HXR_PILOT_BITS):]-cs[:-len(HXR_PILOT_BITS)]
                    scores=np.abs(corr)/np.sqrt(np.maximum(wp*float(len(HXR_PILOT_BITS)),1e-12))
                    if len(scores):
                        carrier_scores.append(scores)
                if len(carrier_scores) == len(HX_R_CARRIERS):
                    n=min(len(x) for x in carrier_scores)
                    stack=np.stack([x[:n] for x in carrier_scores],axis=0)
                    # All three carriers must agree at the same symbol index.
                    combo=np.prod(np.maximum(stack, 1e-6), axis=0) ** (1.0 / len(HX_R_CARRIERS))
                    bi=int(np.argmax(combo)); score=float(combo[bi])
                    carrier_at_best=stack[:,bi]
                    if float(np.min(carrier_at_best)) >= 0.58 and score>best_score:
                        best_score=score; best_mode="HX-R"
                        best_start_sample=int(work_base_sample+phase+bi*SAMPLES_PER_SYMBOL)
            continue
        reps = MODES[try_mode]["repetition"]
        coded_pilot = fec_encode(PILOT_BITS, reps)
        pilot_sign = (2.0 * coded_pilot.astype(np.float32)) - 1.0
        n_pilot = len(pilot_sign)
        need = n_pilot * SAMPLES_PER_SYMBOL
        if len(work) < need:
            continue

        for phase in range(0, SAMPLES_PER_SYMBOL, phase_step):
            vals = _symbol_values_from_prefix(prefix, phase)
            if len(vals) < n_pilot:
                continue
            # Sliding complex correlation against the exact coded HX pilot.
            corr = np.correlate(vals, pilot_sign.astype(np.complex64), mode="valid")
            power = np.abs(vals) ** 2
            csum = np.empty(len(power) + 1, dtype=np.float64)
            csum[0] = 0.0
            csum[1:] = np.cumsum(power, dtype=np.float64)
            win_power = csum[n_pilot:] - csum[:-n_pilot]
            denom = np.sqrt(np.maximum(win_power * float(n_pilot), 1e-12))
            scores = np.abs(corr) / denom
            if len(scores):
                best_idx = int(np.argmax(scores))
                score = float(scores[best_idx])
                if score > best_score:
                    best_score = score
                    best_mode = try_mode
                    best_start_sample = int(work_base_sample + phase + best_idx * SAMPLES_PER_SYMBOL)

    return {"score": best_score, "mode": best_mode, "start_sample": best_start_sample}



def probe_frame_header(audio: np.ndarray, mode: str) -> dict:
    """Locate a credible HX pilot and decode only its fixed-size header.

    Returns the pilot start and exact expected frame end in capture samples.
    This is intentionally much cheaper than repeatedly decoding a growing
    capture and lets the live receiver wait for the precise frame length.
    """
    if audio is None or len(audio) < SAMPLES_PER_SYMBOL * 16:
        raise ValueError("Frame too short")

    peak = float(np.max(np.abs(audio)) + 1e-12)
    if peak < 1e-5:
        raise ValueError("Signal too weak")
    work = np.asarray(audio, dtype=np.float32) / peak
    if mode == "HX-R":
        prefix_symbols = len(HXR_PILOT_BITS) + HEADER_LEN_BITS
        max_offset = len(work) - prefix_symbols * SAMPLES_PER_SYMBOL
        if max_offset <= 0:
            raise ValueError("Not enough samples for HX-R header")
        pilot_sign=(2.0*HXR_PILOT_BITS.astype(np.float32))-1.0
        # Fast candidate search on the center carrier, then validate by
        # combining all three carriers at only the strongest offsets.
        mixed_c=_mixed_for_freq(work,HX_R_CARRIERS[1])
        pc=np.empty(len(mixed_c)+1,dtype=np.complex128); pc[0]=0.0; pc[1:]=np.cumsum(mixed_c,dtype=np.complex128)
        coarse=[]
        coarse_step=max(1,SAMPLES_PER_SYMBOL//2)
        for off in range(0,max_offset+1,coarse_step):
            vals=_symbol_values_from_prefix(pc,off)
            if len(vals)<len(HXR_PILOT_BITS): continue
            c=np.sum(vals[:len(HXR_PILOT_BITS)]*pilot_sign)
            power=float(np.sum(np.abs(vals[:len(PILOT_BITS)])**2))
            score=float(abs(c)/np.sqrt(max(power*len(PILOT_BITS),1e-12)))
            coarse.append((score,off))
        coarse.sort(reverse=True)
        candidates=[]
        fine_step=max(1,SAMPLES_PER_SYMBOL//24)
        for _,off in coarse[:16]:
            lo=max(0,off-SAMPLES_PER_SYMBOL); hi=min(max_offset,off+SAMPLES_PER_SYMBOL)
            for roff in range(lo,hi+1,fine_step):
                vals=_symbol_values_from_prefix(pc,roff)
                if len(vals)<len(HXR_PILOT_BITS): continue
                c=np.sum(vals[:len(HXR_PILOT_BITS)]*pilot_sign)
                power=float(np.sum(np.abs(vals[:len(PILOT_BITS)])**2))
                score=float(abs(c)/np.sqrt(max(power*len(PILOT_BITS),1e-12)))
                candidates.append((score,roff))
        candidates.sort(reverse=True)
        last=None; seen=set()
        for _,off in candidates[:48]:
            if off in seen: continue
            seen.add(off)
            # Sample-accurate refinement around the coarse/fine symbol phase.
            refined=[]
            for roff in range(max(0,off-24), min(max_offset,off+24)+1):
                try:
                    rv,rq=_hxr_oriented_values(work,roff)
                    ps=(2.0*HXR_PILOT_BITS.astype(np.float32))-1.0
                    score=float(np.mean([abs(np.sum(v[:len(HXR_PILOT_BITS)]*ps))/np.sqrt(max(float(np.sum(np.abs(v[:len(HXR_PILOT_BITS)])**2))*len(HXR_PILOT_BITS),1e-12)) for v in rv]))
                    refined.append((score,roff,rv,rq))
                except Exception:
                    pass
            refined.sort(reverse=True,key=lambda x:x[0])
            for _rscore,roff,vals,qs in refined[:8]:
              try:
                off=roff
                combined=sum(v[:prefix_symbols]*q for v,q in zip(vals,qs))/float(np.sum(qs))
                bits=(combined>=0.0).astype(np.int8)
                header_bytes=bits_to_bytes(bits[len(HXR_PILOT_BITS):prefix_symbols])[:HEADER_LEN_BYTES]
                mode_hdr,payload_len=parse_header(header_bytes)
                if mode_hdr!="HX-R": continue
                pbits=payload_len*8
                total_symbols=prefix_symbols+2*pbits
                return {"mode":"HX-R","mode_header":"HX-R","score":float(np.mean(qs)),"start_sample":int(off),"frame_end_sample":int(off+total_symbols*SAMPLES_PER_SYMBOL),"payload_len":int(payload_len)}
              except Exception as e:
                last=e
        if last: raise last
        raise ValueError("No valid HX-R header found")
    mixed = _complex_mixed(work)
    prefix = np.empty(len(mixed) + 1, dtype=np.complex128)
    prefix[0] = 0.0
    prefix[1:] = np.cumsum(mixed, dtype=np.complex128)

    last = None
    for try_mode in _decode_mode_candidates(mode):
        reps = MODES[try_mode]["repetition"]
        coded_pilot = fec_encode(PILOT_BITS, reps)
        pilot_sign = (2.0 * coded_pilot.astype(np.float32)) - 1.0
        n_pilot = len(coded_pilot)
        coded_header_symbols = HEADER_LEN_BITS * reps
        need_symbols = n_pilot + coded_header_symbols
        max_offset = len(work) - (need_symbols * SAMPLES_PER_SYMBOL)
        if max_offset <= 0:
            last = ValueError("Not enough samples for header")
            continue

        coarse_step = max(1, SAMPLES_PER_SYMBOL // 2)
        scored = []
        for off in range(0, max_offset, coarse_step):
            vals = _symbol_values_from_prefix(prefix, off)
            if len(vals) < need_symbols:
                continue
            c = np.sum(vals[:n_pilot] * pilot_sign)
            power = float(np.sum(np.abs(vals[:n_pilot]) ** 2))
            score = float(abs(c) / np.sqrt(max(power * n_pilot, 1e-12)))
            scored.append((score, off, c))
        scored.sort(reverse=True, key=lambda x: x[0])

        candidates = []
        fine_step = max(1, SAMPLES_PER_SYMBOL // 24)
        for _score, off, _c in scored[:12]:
            lo = max(0, off - SAMPLES_PER_SYMBOL)
            hi = min(max_offset, off + SAMPLES_PER_SYMBOL)
            for roff in range(lo, max(lo + 1, hi), fine_step):
                vals = _symbol_values_from_prefix(prefix, roff)
                if len(vals) < need_symbols:
                    continue
                c = np.sum(vals[:n_pilot] * pilot_sign)
                power = float(np.sum(np.abs(vals[:n_pilot]) ** 2))
                score = float(abs(c) / np.sqrt(max(power * n_pilot, 1e-12)))
                candidates.append((score, roff, c))
        candidates.sort(reverse=True, key=lambda x: x[0])

        seen = set()
        for score, off, c in candidates[:36]:
            if off in seen:
                continue
            seen.add(off)
            vals = _symbol_values_from_prefix(prefix, off)
            if len(vals) < need_symbols:
                continue
            phase = np.angle(c)
            real_vals = (vals * np.exp(-1j * phase)).real.astype(np.float32)
            coded_bits = (real_vals > 0).astype(np.int8)
            for inv in (False, True):
                work_bits = 1 - coded_bits if inv else coded_bits
                try:
                    decoded = fec_decode(work_bits[:need_symbols], reps)
                    if len(decoded) < len(PILOT_BITS) + HEADER_LEN_BITS:
                        raise ValueError("Not enough decoded header bits")
                    header_bits = decoded[len(PILOT_BITS):len(PILOT_BITS) + HEADER_LEN_BITS]
                    header_bytes = bits_to_bytes(header_bits)[:HEADER_LEN_BYTES]
                    mode_hdr, payload_len = parse_header(header_bytes)
                    total_logical_bits = len(PILOT_BITS) + HEADER_LEN_BITS + (payload_len * 8)
                    total_coded_symbols = total_logical_bits * reps
                    frame_end_sample = off + total_coded_symbols * SAMPLES_PER_SYMBOL
                    return {
                        "mode": try_mode,
                        "mode_header": mode_hdr,
                        "score": score,
                        "start_sample": int(off),
                        "frame_end_sample": int(frame_end_sample),
                        "payload_len": int(payload_len),
                    }
                except Exception as e:
                    last = e
                    continue
    if last:
        raise last
    raise ValueError("No valid HX header found")


def _partial_payload_preview(audio: np.ndarray, mode: str, payload_len: int) -> str:
    """Best-effort human-readable preview; never used for protocol actions."""
    try:
        if audio is None or len(audio) < SAMPLES_PER_SYMBOL * 16:
            return ""
        work = np.asarray(audio, dtype=np.float32)
        peak = float(np.max(np.abs(work)) + 1e-9)
        if peak < 1e-6:
            return ""
        work = work / peak
        reps = MODES[mode]["repetition"]
        coded_pilot = fec_encode(PILOT_BITS, reps)
        pilot_sign = (2.0 * coded_pilot.astype(np.float32)) - 1.0
        n_pilot = len(coded_pilot)
        mixed = _complex_mixed(work)
        prefix = np.empty(len(mixed) + 1, dtype=np.complex128)
        prefix[0] = 0.0
        prefix[1:] = np.cumsum(mixed, dtype=np.complex128)
        vals = _symbol_values_from_prefix(prefix, 0)
        if len(vals) <= n_pilot + HEADER_LEN_BITS * reps:
            return ""
        c = np.sum(vals[:n_pilot] * pilot_sign)
        phase = np.angle(c)
        real_vals = (vals * np.exp(-1j * phase)).real.astype(np.float32)
        payload_vals = real_vals[n_pilot + HEADER_LEN_BITS * reps:]
        preview_payload_len = max(0, int(payload_len) - 2)  # omit trailing frame CRC bytes
        n_bits = min(preview_payload_len * 8, len(payload_vals) // reps)
        n_bytes = n_bits // 8
        if n_bytes <= 0:
            return ""
        grouped = payload_vals[:n_bytes * 8 * reps].reshape(n_bytes * 8, reps)
        combined = grouped.sum(axis=1)
        bits = (combined >= 0.0).astype(np.int8)
        confidence = np.abs(combined) / (np.mean(np.abs(grouped), axis=1) * max(1, reps) + 1e-6)
        raw = bits_to_bytes(bits)[:n_bytes]

        # HXMSG4 begins with a compact binary prefix: b"HX4" + uint16
        # message length.  The operator text follows immediately, allowing a
        # genuine progressive preview after only five payload bytes.  Older
        # wrappers remain supported for received recordings/peers.
        message_start = None
        message_end = len(raw)
        if raw.startswith(b"HX4"):
            if len(raw) < 5:
                return ""
            declared_len = int.from_bytes(raw[3:5], "big")
            message_start = 5
            message_end = min(len(raw), message_start + declared_len)
        elif raw.startswith(b"HXMSG3|"):
            sep_needed = 5
        elif raw.startswith(b"HXMSG2|"):
            sep_needed = 3
        elif raw.startswith(b"HXMSG1|"):
            sep_needed = 2
        else:
            return ""

        if message_start is None:
            seen = 0
            for i, b in enumerate(raw):
                if b == ord("|"):
                    seen += 1
                    if seen == sep_needed:
                        message_start = i + 1
                        break
            if message_start is None:
                return ""
        if message_start >= message_end:
            return ""

        out = []
        gap = False
        for i in range(message_start, message_end):
            b = raw[i]
            bc = float(np.min(confidence[i*8:(i+1)*8])) if (i+1)*8 <= len(confidence) else 0.0
            reliable = bc >= 0.18 and (b in (9, 10, 13) or 32 <= b <= 126)
            if reliable:
                if gap:
                    out.append("(...)")
                    gap = False
                out.append(chr(b))
            else:
                gap = True
        if gap:
            out.append("(...)")
        return ''.join(out).strip()
    except Exception:
        return ""

def receive_stream_until_frame(
    mode: str,
    rx_device: int | None,
    should_continue,
    on_level=None,
    on_samples=None,
    on_debug=None,
    debug_capture_path: str | None = None,
    debug_capture_mode: str = "OFF",
    try_interval_s: float = 0.45,
):
    """Continuously monitor audio and return when one HX frame is decoded.

    v0.2.6 adds explicit station-debug callbacks. Normal idle time is quiet,
    but the caller can see periodic RX peak levels, trigger events, capture
    duration, saved burst WAV path, and decode failure reasons. The modem core
    is unchanged.
    """
    import time

    block_n = 1024
    pre_s = 0.45
    post_s = 0.85
    pre_n = int(pre_s * SAMPLE_RATE)
    post_quiet_blocks_needed = max(3, int(post_s * SAMPLE_RATE / block_n))

    trigger_level = 0.025
    quiet_level = 0.012

    prebuf = np.zeros(pre_n, dtype=np.float32)
    capturing = False
    captured_chunks: list[np.ndarray] = []
    quiet_blocks = 0
    last_decode_try = 0.0
    last_level_report = 0.0
    last_preamble_check = 0.0
    last_diag_report = 0.0
    capture_started_at = 0.0
    decode_attempts = 0
    rx_cycle_id = 0
    rx_state = "MONITORING"
    hx_preamble_confirmed = False
    hx_detected_mode = None
    hx_preamble_threshold = 0.68
    hx_header_info = None
    hx_candidate_start = None
    hx_candidate_confirmed_at = 0.0
    last_header_probe = 0.0
    header_search_window_n = int(12.0 * SAMPLE_RATE)
    last_partial_preview = ""
    last_partial_report = 0.0
    crc_recovery_cooldown_until = 0.0

    expected_tx_s = _expected_tx_seconds_for_short_frame(mode)
    # Close the burst as soon as audio has gone quiet and we have at least
    # one plausible short frame.  This lets AUTO decode HX-F quickly while
    # still allowing HX-N/HX-R to run until their actual quiet tail.
    min_capture_n = int(0.85 * SAMPLE_RATE)
    max_capture_n = int((expected_tx_s + 2.4) * SAMPLE_RATE)

    def debug(msg: str):
        if on_debug:
            try:
                on_debug(msg)
            except Exception:
                pass

    def update_prebuf(mono: np.ndarray):
        nonlocal prebuf
        if len(mono) >= len(prebuf):
            prebuf[:] = mono[-len(prebuf):]
        else:
            prebuf[:-len(mono)] = prebuf[len(mono):]
            prebuf[-len(mono):] = mono

    def set_state(new_state: str, reason: str = ""):
        nonlocal rx_state
        old_state = rx_state
        if old_state != new_state:
            debug(f"RX_STATE cycle={rx_cycle_id} {old_state}->{new_state} reason={reason or '-'}")
            rx_state = new_state

    debug(f"RX_DIAG stream_open mode={mode} device={rx_device} trigger={trigger_level:.3f} quiet={quiet_level:.3f} block={block_n}")

    with sd.InputStream(
        samplerate=int(SAMPLE_RATE),
        channels=1,
        dtype="float32",
        device=rx_device,
        blocksize=block_n,
    ) as stream:
        while should_continue():
            block, _overflowed = stream.read(block_n)
            mono = block[:, 0].astype(np.float32, copy=False)
            peak = float(np.max(np.abs(mono)) + 1e-9)

            if on_level:
                try:
                    on_level(peak)
                except Exception:
                    pass

            if on_samples:
                try:
                    # A copy keeps the sounddevice buffer lifetime independent
                    # from the UI spectrum display.
                    on_samples(mono.copy())
                except Exception:
                    pass

            now = time.time()
            if now - last_level_report >= 1.0 and not capturing:
                debug(f"RX idle level peak={peak:.6f} threshold={trigger_level:.3f}")
                last_level_report = now

            if not capturing:
                # After an unrecoverable CRC failure, immediately return to
                # monitoring and briefly ignore the continuing audio segment.
                # This prevents SSB speech or other continuous energy from
                # relatching the same failed candidate before the operator sees
                # HX return to Listening.
                if now < crc_recovery_cooldown_until:
                    prebuf[:] = 0
                    continue
                update_prebuf(mono)
                if peak >= trigger_level:
                    capturing = True
                    rx_cycle_id += 1
                    capture_started_at = now
                    decode_attempts = 0
                    last_diag_report = now
                    captured_chunks = [prebuf.copy(), mono.copy()]
                    quiet_blocks = 0
                    hx_preamble_confirmed = False
                    hx_detected_mode = None
                    hx_header_info = None
                    hx_candidate_start = None
                    hx_candidate_confirmed_at = 0.0
                    last_header_probe = 0.0
                    last_preamble_check = 0.0
                    set_state("SIGNAL", f"energy peak={peak:.6f}")
                    debug(f"RX_DIAG cycle={rx_cycle_id} energy_start peak={peak:.6f} prebuffer_samples={len(prebuf)}")
                continue

            captured_chunks.append(mono.copy())
            total_n = sum(len(x) for x in captured_chunks)

            # Audio energy alone never marks the channel busy.  Confirm the
            # exact HX pilot first, then notify the UI immediately so queued TX
            # is held only for a credible HX frame.
            if (not hx_preamble_confirmed) and hx_header_info is None and now - last_preamble_check >= 0.30:
                last_preamble_check = now
                try:
                    probe = np.concatenate(captured_chunks).astype(np.float32)
                    det = detect_hx_preamble(probe, mode)
                    debug(f"RX HX pilot score={det['score']:.3f} mode={det['mode'] or '-'} threshold={hx_preamble_threshold:.2f}")
                    if det["score"] >= hx_preamble_threshold:
                        detected_mode = det["mode"] or mode
                        detected_start = det.get("start_sample")
                        newly_confirmed = not hx_preamble_confirmed or hx_detected_mode != detected_mode
                        hx_preamble_confirmed = True
                        hx_detected_mode = detected_mode
                        # Lock the first strong pilot to an absolute sample position.
                        # Do not let later rolling-window correlations move the candidate.
                        if newly_confirmed or hx_candidate_start is None:
                            hx_candidate_start = int(detected_start) if detected_start is not None else None
                            hx_candidate_confirmed_at = now
                            debug(
                                f"RX HX preamble confirmed score={det['score']:.3f} mode={hx_detected_mode} "
                                f"candidate_start={hx_candidate_start if hx_candidate_start is not None else '-'}"
                            )
                except Exception as de:
                    debug(f"RX HX pilot check error: {de}")

            if peak < quiet_level:
                quiet_blocks += 1
            else:
                quiet_blocks = 0

            # v0.4.19: do not repeatedly run the complete decoder inside the
            # live capture loop. First decode only the fixed header, then wait
            # for the exact frame length declared by that valid header.
            if hx_preamble_confirmed and hx_header_info is None and (now - last_header_probe >= 0.55):
                last_header_probe = now
                try:
                    full_audio = np.concatenate(captured_chunks).astype(np.float32)
                    decode_mode = hx_detected_mode or mode

                    # v0.4.21: probe only around the exact pilot location
                    # reported by the detector. A generic newest-12-second search
                    # can repeatedly choose a false alignment in static after a
                    # previously decoded frame.
                    if hx_candidate_start is not None:
                        reps = MODES[decode_mode]["repetition"]
                        pilot_len = len(HXR_PILOT_BITS) if decode_mode == "HX-R" else len(PILOT_BITS)
                        header_need = (pilot_len + HEADER_LEN_BITS) * reps * SAMPLES_PER_SYMBOL
                        margin = 2 * SAMPLES_PER_SYMBOL
                        probe_base = max(0, int(hx_candidate_start) - margin)
                        probe_end = min(len(full_audio), int(hx_candidate_start) + header_need + margin)
                        if probe_end - probe_base < header_need:
                            raise ValueError("Not enough samples for locked candidate header")
                        probe_audio = full_audio[probe_base:probe_end]
                        local_info = probe_frame_header(probe_audio, decode_mode)
                        absolute_start = int(local_info["start_sample"] + probe_base)
                    else:
                        window_base = max(0, len(full_audio) - header_search_window_n)
                        probe_audio = full_audio[window_base:]
                        probe_base = window_base
                        local_info = probe_frame_header(probe_audio, decode_mode)
                        absolute_start = int(local_info["start_sample"] + probe_base)

                    hx_header_info = dict(local_info)
                    hx_header_info["start_sample"] = absolute_start
                    hx_header_info["frame_end_sample"] = int(local_info["frame_end_sample"] + probe_base)
                    debug(
                        f"RX_DIAG cycle={rx_cycle_id} header_valid mode={hx_header_info['mode']} "
                        f"payload_len={hx_header_info['payload_len']} start={hx_header_info['start_sample']} "
                        f"expected_end={hx_header_info['frame_end_sample']} score={hx_header_info['score']:.3f} "
                        f"candidate_start={hx_candidate_start if hx_candidate_start is not None else '-'} "
                        f"probe_base={probe_base} probe_samples={len(probe_audio)}"
                    )
                    set_state("DECODING", "valid HX header")
                except Exception as header_error:
                    debug(
                        f"RX_DIAG cycle={rx_cycle_id} header_wait error={type(header_error).__name__}:{header_error} "
                        f"candidate_start={hx_candidate_start if hx_candidate_start is not None else '-'}"
                    )
                    # Once the complete repeated pilot+header should be present,
                    # a persistent header CRC failure means this alignment is bad.
                    # Release it promptly instead of remaining in SIGNAL forever.
                    if hx_candidate_start is not None:
                        reps = MODES[decode_mode]["repetition"]
                        pilot_len = len(HXR_PILOT_BITS) if decode_mode == "HX-R" else len(PILOT_BITS)
                        required_end = int(hx_candidate_start) + (pilot_len + HEADER_LEN_BITS) * reps * SAMPLES_PER_SYMBOL
                        if total_n >= required_end + int(1.0 * SAMPLE_RATE):
                            debug(
                                f"RX_DIAG cycle={rx_cycle_id} candidate_rejected mode={decode_mode} "
                                f"start={hx_candidate_start} total={total_n} reason=header_not_valid_after_complete_header"
                            )
                            hx_preamble_confirmed = False
                            hx_detected_mode = None
                            hx_candidate_start = None
                            hx_candidate_confirmed_at = 0.0
                            last_preamble_check = 0.0
                            set_state("SIGNAL", "candidate rejected; searching next pilot")

            # v0.5.4.3: operator text is delivered only after the complete frame
            # passes CRC. Progressive/provisional RX presentation is disabled.

            if hx_header_info is not None and total_n >= hx_header_info["frame_end_sample"]:
                decode_attempts += 1
                try:
                    live_audio = np.concatenate(captured_chunks).astype(np.float32)
                    # v0.4.25: The header probe has already established the exact
                    # pilot start and exact frame end.  Do not add a symbol of
                    # padding around the final frame: on long HX-R captures that
                    # padding let the full decoder reinterpret alignment and could
                    # turn a previously valid header into a false Header CRC error.
                    start = int(hx_header_info["start_sample"])
                    end = int(hx_header_info["frame_end_sample"])
                    if start < 0 or end <= start or end > len(live_audio):
                        raise ValueError(
                            f"Invalid locked frame bounds start={start} end={end} available={len(live_audio)}"
                        )
                    frame_audio = live_audio[start:end]
                    decode_mode = hx_header_info["mode"]
                    debug(
                        f"RX_DIAG cycle={rx_cycle_id} exact_decode attempt={decode_attempts} "
                        f"mode={decode_mode} slice={start}:{end} samples={len(frame_audio)} strict_start=0"
                    )
                    locked_local_start = 0
                    debug(f"RX_DIAG cycle={rx_cycle_id} payload_soft_decode mode={decode_mode} payload_len={hx_header_info['payload_len']}")
                    try:
                        result = _decode_locked_payload_only(
                            frame_audio, decode_mode, hx_header_info["payload_len"], use_soft=True
                        )
                        debug(f"RX_DIAG cycle={rx_cycle_id} payload_soft_success mode={decode_mode}")
                    except Exception as soft_error:
                        debug(
                            f"RX_DIAG cycle={rx_cycle_id} payload_soft_miss mode={decode_mode} "
                            f"error={type(soft_error).__name__}:{soft_error}"
                        )
                        debug(f"RX_DIAG cycle={rx_cycle_id} payload_hard_fallback mode={decode_mode}")
                        result = _decode_locked_payload_only(
                            frame_audio, decode_mode, hx_header_info["payload_len"], use_soft=False
                        )
                        debug(f"RX_DIAG cycle={rx_cycle_id} payload_hard_success mode={decode_mode}")
                    result["capture_audio"] = frame_audio
                    result["stream_window_seconds"] = len(frame_audio) / SAMPLE_RATE
                    result["trigger_peak"] = float(np.max(np.abs(frame_audio)) + 1e-9)
                    debug(
                        f"RX frame completed before silence: {len(frame_audio) / SAMPLE_RATE:.2f}s; "
                        f"CRC valid; delivering immediately"
                    )
                    debug(f"RX_DIAG cycle={rx_cycle_id} decode_success attempt={decode_attempts} header_mode={result.get('mode_header', '-')} snr={result.get('snr', 0.0):.2f}")
                    set_state("COMPLETE", "valid frame")
                    debug("RX decode success")
                    return result
                except Exception as live_error:
                    debug(f"RX_DIAG cycle={rx_cycle_id} exact_decode_failed error={type(live_error).__name__}:{live_error}")

                    # v0.4.22: Long HX-N/HX-R frames can accumulate a small
                    # sample-clock mismatch when replayed through Windows audio
                    # paths (Audacity/VB-CABLE, USB codecs, etc.).  HX-F is short
                    # enough to tolerate it, while the same fractional error can
                    # shift the final payload symbols in HX-N/HX-R and cause a
                    # payload CRC failure.  On CRC failure only, try a tightly
                    # bounded timing-recovery search by resampling the locked
                    # frame a few tenths of a percent around nominal length.
                    recovered = None
                    if "Payload CRC error" in str(live_error) and decode_mode in ("HX-N", "HX-R"):
                        nominal_n = len(frame_audio)
                        # v0.4.28: use the live capture, including any samples
                        # already collected after the nominal frame end, as the
                        # timing-recovery source.  Each candidate source window
                        # is then resampled back to the exact nominal frame
                        # length.  This guarantees the payload decoder always
                        # receives a complete symbol count, including for scales
                        # below 1.0, while preserving the locked pilot position.
                        live_source = live_audio[start:].astype(np.float32, copy=False)
                        scale_candidates = (0.9995, 1.0005, 0.9990, 1.0010, 0.9985, 1.0015, 0.9980, 1.0020, 0.9975, 1.0025)
                        for scale in scale_candidates:
                            try:
                                source_n = max(1, int(round(nominal_n * scale)))
                                if len(live_source) < source_n:
                                    raise ValueError(
                                        f"Insufficient tail margin need={source_n} available={len(live_source)}"
                                    )
                                source = live_source[:source_n]
                                x_old = np.linspace(0.0, 1.0, num=len(source), endpoint=False, dtype=np.float64)
                                x_new = np.linspace(0.0, 1.0, num=nominal_n, endpoint=False, dtype=np.float64)
                                adjusted = np.interp(x_new, x_old, source).astype(np.float32)
                                debug(
                                    f"RX_DIAG cycle={rx_cycle_id} timing_recovery_try mode={decode_mode} "
                                    f"scale={scale:.4f} samples={len(adjusted)}"
                                )
                                debug(
                                    f"RX_DIAG cycle={rx_cycle_id} payload_soft_timing_try mode={decode_mode} "
                                    f"scale={scale:.4f}"
                                )
                                try:
                                    trial = _decode_locked_payload_only(
                                        adjusted, decode_mode, hx_header_info["payload_len"], use_soft=True
                                    )
                                except Exception as soft_timing_error:
                                    debug(
                                        f"RX_DIAG cycle={rx_cycle_id} payload_soft_timing_miss mode={decode_mode} "
                                        f"scale={scale:.4f} error={type(soft_timing_error).__name__}:{soft_timing_error}"
                                    )
                                    trial = _decode_locked_payload_only(
                                        adjusted, decode_mode, hx_header_info["payload_len"], use_soft=False
                                    )
                                trial["capture_audio"] = adjusted
                                trial["stream_window_seconds"] = len(adjusted) / SAMPLE_RATE
                                trial["trigger_peak"] = float(np.max(np.abs(adjusted)) + 1e-9)
                                trial["timing_recovery_scale"] = float(scale)
                                recovered = trial
                                debug(
                                    f"RX_DIAG cycle={rx_cycle_id} timing_recovery_success mode={decode_mode} "
                                    f"scale={scale:.4f} snr={trial.get('snr', 0.0):.2f}"
                                )
                                break
                            except Exception as recovery_error:
                                debug(
                                    f"RX_DIAG cycle={rx_cycle_id} timing_recovery_miss mode={decode_mode} "
                                    f"scale={scale:.4f} error={type(recovery_error).__name__}:{recovery_error}"
                                )

                    if recovered is not None:
                        set_state("COMPLETE", "valid frame after timing recovery")
                        debug("RX_DIAG frame_final result=CRC_OK path=timing_recovery")
                        debug("RX decode success after bounded timing recovery")
                        return recovered

                    final_reason = "PAYLOAD_CRC" if "Payload CRC error" in str(live_error) else "HEADER_CRC"
                    debug(f"RX_DIAG frame_final result=UNRECOVERABLE reason={final_reason}")
                    debug(f"RX CRC failure reset to monitoring reason={final_reason} cooldown=0.60s")
                    set_state("MONITORING", "CRC failure; candidate cleared")
                    crc_recovery_cooldown_until = time.time() + 0.60
                    capturing = False
                    captured_chunks = []
                    prebuf[:] = 0
                    quiet_blocks = 0
                    hx_preamble_confirmed = False
                    hx_detected_mode = None
                    hx_header_info = None
                    hx_candidate_start = None
                    hx_candidate_confirmed_at = 0.0
                    continue

            if now - last_diag_report >= 1.0:
                last_diag_report = now
                debug(
                    f"RX_DIAG cycle={rx_cycle_id} state={rx_state} elapsed={now-capture_started_at:.1f}s "
                    f"captured_samples={total_n} captured_seconds={total_n/SAMPLE_RATE:.2f} "
                    f"peak={peak:.6f} quiet_blocks={quiet_blocks} pilot={hx_preamble_confirmed} "
                    f"mode={hx_detected_mode or '-'} decode_attempts={decode_attempts}"
                )

            # Diagnostic safety net only.  This is deliberately longer than a
            # large HX-R file chunk so normal transfers are not truncated.
            if hx_preamble_confirmed and (now - capture_started_at) >= 180.0:
                debug(
                    f"RX_WATCHDOG cycle={rx_cycle_id} elapsed={now-capture_started_at:.1f}s "
                    f"samples={total_n} attempts={decode_attempts}; abandoning candidate"
                )
                set_state("RESET", "180s watchdog")
                capturing = False
                captured_chunks = []
                prebuf[:] = 0
                quiet_blocks = 0
                hx_preamble_confirmed = False
                hx_detected_mode = None
                hx_candidate_start = None
                hx_candidate_confirmed_at = 0.0
                continue

            enough_signal_then_quiet = total_n >= min_capture_n and quiet_blocks >= post_quiet_blocks_needed
            forced_full_window = total_n >= max_capture_n

            # When testing long HX-R messages, keep the operator informed that
            # RX is still collecting the same burst instead of appearing stuck.
            if not forced_full_window and total_n > int(8.0 * SAMPLE_RATE) and total_n % int(4.0 * SAMPLE_RATE) < block_n:
                debug(f"RX signal continues... captured {total_n / SAMPLE_RATE:.1f}s")

            if not (enough_signal_then_quiet or forced_full_window):
                continue

            audio = np.concatenate(captured_chunks).astype(np.float32)
            reason = "quiet/end-of-message" if enough_signal_then_quiet else "max-window/truncated"
            debug(f"RX_DIAG cycle={rx_cycle_id} burst_end reason={reason} state={rx_state} attempts={decode_attempts}")
            debug(f"RX burst captured: {len(audio) / SAMPLE_RATE:.2f}s, peak={float(np.max(np.abs(audio)) + 1e-9):.6f}, reason={reason}")

            set_state("FINAL_DECODE", reason)
            capturing = False
            captured_chunks = []
            prebuf[:] = 0
            quiet_blocks = 0
            hx_preamble_confirmed = False
            hx_detected_mode = None
            hx_header_info = None
            hx_candidate_start = None
            hx_candidate_confirmed_at = 0.0

            # Always perform one final decode of a completed burst.  v0.4.17
            # could discard the entire captured frame when a live decode attempt
            # had occurred less than try_interval_s earlier, leaving RX in an
            # apparent permanent DECODING state.
            last_decode_try = time.time()

            capture_mode = (debug_capture_mode or "OFF").upper()
            if debug_capture_path and capture_mode == "ALL":
                try:
                    save_wav(debug_capture_path, audio)
                    debug(f"RX debug capture saved: {debug_capture_path}")
                except Exception as se:
                    debug(f"RX debug capture save failed: {se}")

            try:
                result = decode_audio_capture(audio, mode)
                result["capture_audio"] = audio
                result["stream_window_seconds"] = len(audio) / SAMPLE_RATE
                result["trigger_peak"] = float(np.max(np.abs(audio)) + 1e-9)
                debug(f"RX_DIAG cycle={rx_cycle_id} final_decode_success header_mode={result.get('mode_header', '-')} snr={result.get('snr', 0.0):.2f}")
                set_state("COMPLETE", "final decode valid")
                debug("RX decode success")
                return result
            except Exception as e:
                debug(f"RX_DIAG cycle={rx_cycle_id} final_decode_failed error={type(e).__name__}:{e}")
                set_state("MONITORING", "candidate rejected")
                debug(f"RX decode miss: {e}")
                if debug_capture_path and capture_mode == "ERRORS ONLY":
                    try:
                        save_wav(debug_capture_path, audio)
                        debug(f"RX error debug capture saved: {debug_capture_path}")
                    except Exception as se:
                        debug(f"RX debug capture save failed: {se}")
                continue
