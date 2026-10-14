"""Bitcoin serialization extracted from MINER-MAY-2026 (GPL-3.0)."""
import hashlib
import struct
from typing import Optional

def _uint32_le(n: int) -> bytes:
    return struct.pack("<I", n & 0xFFFFFFFF)


def _varint(n: int) -> bytes:
    if n < 0xFD:
        return bytes([n])
    if n <= 0xFFFF:
        return bytes([0xFD]) + struct.pack("<H", n)
    if n <= 0xFFFFFFFF:
        return bytes([0xFE]) + struct.pack("<I", n)
    return bytes([0xFF]) + struct.pack("<Q", n)


def _double_sha256(data: bytes) -> bytes:
    """Bitcoin consensus hash: SHA256(SHA256(data)). Kept minimal for inner-loop speed."""
    return hashlib.sha256(hashlib.sha256(data).digest()).digest()


def _bits_to_target(bits) -> int:
    """Decode a positive uint256 compact target, with Bitcoin Core's sign/range rules.

    Network powLimit and required nBits are contextual checks made by Core.
    """
    if isinstance(bits, str):
        if len(bits) != 8 or any(c not in "0123456789abcdefABCDEF" for c in bits):
            raise ValueError("bits must be exactly 8 hexadecimal digits")
        bits = int(bits, 16)
    if type(bits) is not int or not 0 <= bits <= 0xffffffff:
        raise ValueError("bits must be a uint32")
    exponent, mantissa = bits >> 24, bits & 0x7fffff
    if bits & 0x800000 or not mantissa:
        raise ValueError("Negative or zero compact target")
    target = mantissa >> (8 * (3 - exponent)) if exponent <= 3 else mantissa << (8 * (exponent - 3))
    if not 0 < target < 1 << 256:
        raise ValueError("Zero or overflowing compact target")
    return target


def _hash_meets_target(hash_bytes: bytes, target: int) -> bool:
    """Check if double-SHA256 hash (32 bytes LE) is <= target (valid block)."""
    return int.from_bytes(hash_bytes, "little") <= target


def _height_to_script_push(height: int) -> bytes:
    """BIP34: minimal encoding of block height for scriptSig."""
    if type(height) is not int or not 0 <= height <= 0x7fffffff:
        raise ValueError("Block height must be a nonnegative signed 32-bit integer")
    if height == 0:
        return bytes([0x00])  # OP_0
    if 1 <= height <= 16:
        return bytes([0x50 + height])  # OP_1 .. OP_16
    # Push as little-endian bytes (minimal CScriptNum encoding)
    n = height
    buf = []
    while n:
        buf.append(n & 0xFF)
        n >>= 8
    # Sign-bit padding: CScriptNum is signed; if MSB has bit 7 set, append 0x00
    # to keep the value positive (matches Bitcoin Core CScriptNum::serialize).
    if buf and (buf[-1] & 0x80):
        buf.append(0x00)
    return _varint(len(buf)) + bytes(buf)


def _build_coinbase_script_sig(height: int, coinbase_aux: Optional[dict] = None) -> bytes:
    """BIP34: height in scriptSig; optional coinbaseaux data.

    Bitcoin consensus requires coinbase scriptSig to be 2-100 bytes.
    We pad with a 0x00 byte if the result would be too short.
    """
    out = _height_to_script_push(height)
    if coinbase_aux:
        for k, v in coinbase_aux.items():
            raw = bytes.fromhex(v) if isinstance(v, str) else v
            # Script push opcodes differ from CompactSize starting at 76 bytes.
            if len(raw) > 100:
                raise ValueError("Coinbase auxiliary data exceeds scriptSig limit")
            out += (bytes([len(raw)]) if len(raw) < 76 else b"\x4c" + bytes([len(raw)])) + raw
    # Ensure minimum 2 bytes (consensus rule for coinbase scriptSig length)
    if len(out) < 2:
        out += b"\x00"
    return out


def _build_coinbase(
    height: int,
    coinbase_value: int,
    script_pubkey: bytes,
    coinbase_aux: Optional[dict] = None,
    witness_commitment_hex: Optional[str] = None,
    extra_nonce: Optional[bytes] = None,
) -> bytes:
    """Serialize coinbase transaction in non-witness (stripped) format.

    This serialization is used to compute the txid for the merkle root.
    For block submission when segwit is active, wrap the result with
    _coinbase_add_witness() to produce the full segwit serialization
    that includes the BIP141 witness reserved value.
    """
    script_sig = _build_coinbase_script_sig(height, coinbase_aux)
    if extra_nonce:
        script_sig += extra_nonce
    if not 2 <= len(script_sig) <= 100:
        raise ValueError("Coinbase scriptSig must contain 2–100 bytes")
    vin = (
        bytes(32)
        + struct.pack("<I", 0xFFFFFFFF)
        + _varint(len(script_sig))
        + script_sig
        + struct.pack("<I", 0xFFFFFFFF)
    )
    out1 = struct.pack("<Q", coinbase_value) + _varint(len(script_pubkey)) + script_pubkey
    if witness_commitment_hex:
        script_commit = bytes.fromhex(witness_commitment_hex)
        out2 = struct.pack("<Q", 0) + _varint(len(script_commit)) + script_commit
        vouts = bytes([2]) + out1 + out2
    else:
        vouts = bytes([1]) + out1
    return (
        struct.pack("<I", 2)
        + bytes([1])
        + vin
        + vouts
        + struct.pack("<I", 0)
    )


def _coinbase_add_witness(stripped_coinbase: bytes) -> bytes:
    """Convert non-segwit (stripped) coinbase to segwit format with witness reserved value.

    Segwit format: version + marker(0x00) + flag(0x01) + inputs + outputs + witness + locktime.
    BIP141 witness for coinbase: 1 stack item of 32 zero bytes (witness reserved value).
    """
    version = stripped_coinbase[:4]
    locktime = stripped_coinbase[-4:]
    middle = stripped_coinbase[4:-4]
    witness = bytes([1, 32]) + bytes(32)
    return version + bytes([0x00, 0x01]) + middle + witness + locktime


def _merkle_root(hashes: list[bytes]) -> bytes:
    """Compute merkle root from list of tx hashes (32 bytes each)."""
    if not hashes:
        return bytes(32)
    while len(hashes) > 1:
        if len(hashes) % 2:
            hashes.append(hashes[-1])
        next_level = []
        for i in range(0, len(hashes), 2):
            next_level.append(_double_sha256(hashes[i] + hashes[i + 1]))
        hashes = next_level
    return hashes[0]


def _build_block_header(
    version: int,
    prev_block_hash_hex: str,
    merkle_root: bytes,
    time_val: int,
    bits_hex: str,
    nonce: int,
) -> bytes:
    """Build 80-byte block header (all LE)."""
    prev = bytes.fromhex(prev_block_hash_hex)
    if len(prev) == 32:
        prev = prev[::-1]  # to internal order
    bits_le = struct.pack("<I", int(bits_hex, 16))
    return (
        struct.pack("<I", version)
        + prev
        + merkle_root
        + struct.pack("<I", time_val)
        + bits_le
        + _uint32_le(nonce)
    )


def _build_header_template(
    version: int,
    prev_block_hash_hex: str,
    merkle_root: bytes,
    time_val: int,
    bits_hex: str,
) -> bytes:
    """Build 80-byte header template with nonce=0 for C batch scanner."""
    return _build_block_header(version, prev_block_hash_hex, merkle_root, time_val, bits_hex, 0)


C_SCAN_CHUNK = 1_000_000


def _build_block(
    template: dict,
    script_pubkey: bytes,
    header: bytes,
    coinbase_raw: bytes,
    tx_list: list[dict],
) -> bytes:
    """Full block: header + varint(n_tx) + coinbase + transactions."""
    coinbase_txid = _double_sha256(coinbase_raw)  # raw hash for merkle tree (internal byte order)
    tx_hashes = [coinbase_txid]
    tx_raws = [coinbase_raw]
    for tx in tx_list:
        data_hex = tx.get("data")
        if data_hex:
            tx_raws.append(bytes.fromhex(data_hex))
            tx_hashes.append(_double_sha256(tx_raws[-1]))
        else:
            txid_hex = tx.get("hash") or tx.get("txid")
            if txid_hex:
                tx_hashes.append(bytes.fromhex(txid_hex)[::-1])  # RPC txids are display order; reverse to internal
            tx_raws.append(bytes.fromhex(tx.get("data", "")))
    # Merkle uses txids; we already built header with correct merkle, so block body is header + txs
    n_tx = len(tx_raws)
    return header + _varint(n_tx) + b"".join(tx_raws)
