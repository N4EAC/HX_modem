import numpy as np
from .fec import bytes_to_bits, bits_to_bytes, append_crc, check_crc, crc16_ccitt

PILOT_BITS = np.array([int(b) for b in "11001001011101000101001100110110011100010101100010110011"], dtype=np.int8)[:64]
HEADER_LEN_BYTES = 7
HEADER_LEN_BITS = HEADER_LEN_BYTES * 8
MODE_ID_MAP = {"HX-N": 1, "HX-F": 2}
ID_MODE_MAP = {v: k for k, v in MODE_ID_MAP.items()}


def build_header(payload_len_bytes: int, mode_name: str) -> bytes:
    raw = bytearray([MODE_ID_MAP[mode_name] & 0xFF])
    raw += payload_len_bytes.to_bytes(4, "big")
    raw += crc16_ccitt(bytes(raw)).to_bytes(2, "big")
    return bytes(raw)


def parse_header(header_bytes: bytes) -> tuple[str, int]:
    if len(header_bytes) < HEADER_LEN_BYTES:
        raise ValueError("Header too short")
    mode_id = header_bytes[0]
    payload_len = int.from_bytes(header_bytes[1:5], "big")
    hdr_crc = int.from_bytes(header_bytes[5:7], "big")
    if crc16_ccitt(header_bytes[:5]) != hdr_crc:
        raise ValueError("Header CRC error")
    if mode_id not in ID_MODE_MAP:
        raise ValueError("Unsupported HX mode id")
    return ID_MODE_MAP[mode_id], payload_len


def build_frame_bits(payload: bytes, mode_name: str) -> np.ndarray:
    payload_crc = append_crc(payload)
    header = build_header(len(payload_crc), mode_name)
    return np.concatenate([PILOT_BITS, bytes_to_bits(header), bytes_to_bits(payload_crc)]).astype(np.int8)


def split_frame_bits(bits: np.ndarray):
    n_pilot = len(PILOT_BITS)
    if len(bits) < n_pilot + HEADER_LEN_BITS + 16:
        raise ValueError("Frame too short")
    return bits[:n_pilot], bits[n_pilot:n_pilot + HEADER_LEN_BITS], bits[n_pilot + HEADER_LEN_BITS:]


def parse_payload_bits(header_bits: np.ndarray, payload_bits: np.ndarray):
    mode_name, payload_len = parse_header(bits_to_bytes(header_bits)[:HEADER_LEN_BYTES])
    need = payload_len * 8
    if len(payload_bits) < need:
        raise ValueError("Not enough bits for payload")
    ok, payload = check_crc(bits_to_bytes(payload_bits[:need]))
    if not ok:
        raise ValueError("Payload CRC error")
    return mode_name, payload
