import numpy as np

MODES = {
    "HX-N": {"repetition": 3},
    "HX-F": {"repetition": 1},
}


def bytes_to_bits(data: bytes) -> np.ndarray:
    return np.unpackbits(np.frombuffer(data, dtype=np.uint8)).astype(np.int8)


def bits_to_bytes(bits: np.ndarray) -> bytes:
    if len(bits) % 8 != 0:
        pad = 8 - (len(bits) % 8)
        bits = np.concatenate([bits, np.zeros(pad, dtype=np.int8)])
    return np.packbits(bits.astype(np.uint8)).tobytes()


def crc16_ccitt(data: bytes, poly=0x1021, init=0xFFFF) -> int:
    crc = init
    for b in data:
        crc ^= b << 8
        for _ in range(8):
            if crc & 0x8000:
                crc = ((crc << 1) & 0xFFFF) ^ poly
            else:
                crc = (crc << 1) & 0xFFFF
    return crc & 0xFFFF


def append_crc(data: bytes) -> bytes:
    return data + crc16_ccitt(data).to_bytes(2, "big")


def check_crc(data_with_crc: bytes) -> tuple[bool, bytes]:
    if len(data_with_crc) < 2:
        return False, b""
    data = data_with_crc[:-2]
    expected = int.from_bytes(data_with_crc[-2:], "big")
    return crc16_ccitt(data) == expected, data


def fec_encode(bits: np.ndarray, repetition: int) -> np.ndarray:
    if repetition <= 1:
        return bits.copy()
    return np.repeat(bits, repetition).astype(np.int8)


def fec_decode(bits: np.ndarray, repetition: int) -> np.ndarray:
    if repetition <= 1:
        return bits.copy()
    n = len(bits) // repetition
    if n <= 0:
        return np.zeros(0, dtype=np.int8)
    groups = bits[: n * repetition].reshape(n, repetition)
    votes = groups.sum(axis=1)
    return (votes >= (repetition // 2 + 1)).astype(np.int8)


def fec_decode_soft(symbol_values: np.ndarray, repetition: int) -> np.ndarray:
    """Soft-decision repetition decoder.

    ``symbol_values`` are signed confidence values (positive=1, negative=0).
    Repeated symbols are summed before the final hard decision, so weakly
    corrupted copies have less influence than strong reliable copies.
    """
    vals = np.asarray(symbol_values, dtype=np.float32)
    if repetition <= 1:
        return (vals > 0.0).astype(np.int8)
    n = len(vals) // repetition
    if n <= 0:
        return np.zeros(0, dtype=np.int8)
    groups = vals[: n * repetition].reshape(n, repetition)
    confidence = groups.sum(axis=1)
    return (confidence >= 0.0).astype(np.int8)
