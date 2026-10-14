"""Bitcoin job construction and strict payout validation."""
from dataclasses import dataclass, field
from decimal import Decimal, InvalidOperation
import struct
import time
from .native import hash256
from .serialization import _build_coinbase, _coinbase_add_witness, _merkle_root, _varint, _bits_to_target

DIFF1 = 0x00000000FFFF0000000000000000000000000000000000000000000000000000

def target_from_difficulty(value):
    """Convert a Stratum difficulty without rounding a 256-bit target."""
    try:
        difficulty = Decimal(str(value))
    except InvalidOperation:
        raise ValueError("Pool supplied invalid share difficulty") from None
    if not difficulty.is_finite() or difficulty <= 0:
        raise ValueError("Pool supplied invalid share difficulty")
    # Bound extreme exponents before constructing their integer ratios.
    if difficulty > DIFF1:
        return 0
    if difficulty < Decimal("1e-100"):
        return (1 << 256) - 1
    numerator, denominator = difficulty.as_integer_ratio()
    return min((1 << 256) - 1, DIFF1 * denominator // numerator)

def target_from_bits(bits):
    return _bits_to_target(bits)

def script_for_address(address, network):
    if not address or address != address.strip() or any(c.isspace() for c in address):
        raise ValueError("Enter a complete payout address without spaces")
    if address.lower().startswith(("bc1", "tb1", "bcrt1")):
        if address != address.lower() and address != address.upper():
            raise ValueError("Mixed-case Bech32 address")
        a = address.lower()
        if len(a) > 90:
            raise ValueError("Address too long")
        pos = a.rfind("1"); hrp = a[:pos]
        expected = "bc" if network == "mainnet" else "bcrt" if network == "regtest" else "tb"
        if hrp != expected:
            raise ValueError(f"Payout address is for another network (expected {expected}1)")
        charset = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
        try:
            values = [charset.index(c) for c in a[pos+1:]]
        except ValueError:
            raise ValueError("Invalid Bech32 character") from None
        if len(values) < 7 or values[0] > 16:
            raise ValueError("Invalid witness version")
        chk = 1
        expanded = [ord(c) >> 5 for c in hrp] + [0] + [ord(c) & 31 for c in hrp]
        for v in expanded + values:
            top = chk >> 25; chk = ((chk & 0x1ffffff) << 5) ^ v
            for i, gen in enumerate((0x3b6a57b2,0x26508e6d,0x1ea119fa,0x3d4233dd,0x2a1462b3)):
                if top >> i & 1:
                    chk ^= gen
        version = values[0]
        if chk != (1 if version == 0 else 0x2bc830a3):
            raise ValueError("Invalid address checksum")
        acc = bits = 0; program = bytearray()
        for v in values[1:-6]:
            acc = (acc << 5) | v; bits += 5
            while bits >= 8:
                bits -= 8; program.append((acc >> bits) & 255)
        if bits >= 5 or ((acc << (8 - bits)) & 255):
            raise ValueError("Invalid witness padding")
        if not 2 <= len(program) <= 40 or (version == 0 and len(program) not in (20,32)):
            raise ValueError("Invalid witness program length")
        return bytes([0 if version == 0 else 0x50 + version, len(program)]) + program
    alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
    n = 0
    try:
        for char in address:
            n = n * 58 + alphabet.index(char)
    except ValueError:
        raise ValueError("Invalid Base58 character") from None
    raw = b"\0" * (len(address) - len(address.lstrip("1"))) + n.to_bytes((n.bit_length()+7)//8, "big")
    if len(raw) != 25 or hash256(raw[:-4])[:4] != raw[-4:]:
        raise ValueError("Invalid Base58 address checksum")
    pkh, sh = (0,5) if network == "mainnet" else (111,196)
    if raw[0] == pkh:
        return b"\x76\xa9\x14" + raw[1:21] + b"\x88\xac"
    if raw[0] == sh:
        return b"\xa9\x14" + raw[1:21] + b"\x87"
    raise ValueError("Payout address is for another network")

@dataclass
class Work:
    header: bytes
    target: int
    network_target: int
    height: int
    bits: str
    key: str
    generation: int
    data: dict = field(default_factory=dict)

def core_work(template, address, network, extra, generation):
    bits = template["bits"]; target = target_from_bits(bits)
    if "target" in template and int(template["target"], 16) != target:
        raise ValueError("Template target disagrees with compact bits")
    prev = bytes.fromhex(template["previousblockhash"])
    if len(prev) != 32:
        raise ValueError("Invalid previous block hash")
    coinbase = _build_coinbase(template["height"], template["coinbasevalue"],
                               script_for_address(address, network), template.get("coinbaseaux"),
                               template.get("default_witness_commitment"), extra)
    txs = template.get("transactions", [])
    hashes = [hash256(coinbase)] + [bytes.fromhex(tx["txid"])[::-1] for tx in txs]
    root = _merkle_root(hashes)
    timestamp = max(template["curtime"], template.get("mintime", 0))
    header = struct.pack("<I", template["version"]) + prev[::-1] + root + struct.pack("<III", timestamp, int(bits,16), 0)
    body_coinbase = _coinbase_add_witness(coinbase) if template.get("default_witness_commitment") else coinbase
    body = _varint(1 + len(txs)) + body_coinbase + b"".join(bytes.fromhex(tx["data"]) for tx in txs)
    return Work(header, target, target, int(template["height"]), bits,
                template["previousblockhash"] + ":" + extra.hex(), generation, {"body": body})

def pool_height(coinbase):
    # BIP34 height is the first item of coinbase input scriptSig.
    def varint(at):
        tag = coinbase[at]; at += 1
        size = {253:2,254:4,255:8}.get(tag,0)
        return (int.from_bytes(coinbase[at:at+size],"little"), at+size) if size else (tag,at)
    at = 4
    if coinbase[at:at+2] == b"\0\1":
        at += 2
    count, at = varint(at)
    if count != 1:
        raise ValueError("Pool coinbase must have one input")
    at += 36
    length, at = varint(at)
    op = coinbase[at]
    if 0x51 <= op <= 0x60:
        return op - 0x50
    if not 1 <= op <= 5 or op + 1 > length:
        raise ValueError("Pool coinbase does not contain a readable BIP34 height")
    return int.from_bytes(coinbase[at+1:at+1+op],"little")

def pool_work(params, extranonce1, extranonce2, target, generation):
    job_id, prevhash, cb1, cb2, branches, version, bits, ntime, clean = params[:9]
    coinbase = bytes.fromhex(cb1 + extranonce1 + extranonce2 + cb2)
    merkle = hash256(coinbase)
    for branch in branches:
        b = bytes.fromhex(branch)
        if len(b) != 32:
            raise ValueError("Invalid Stratum Merkle branch")
        merkle = hash256(merkle + b)
    prev = bytes.fromhex(prevhash)
    if len(prev) != 32:
        raise ValueError("Invalid Stratum previous hash")
    # Stratum V1 previous hash is transmitted as eight big-endian words.
    prev = b"".join(prev[i:i+4][::-1] for i in range(0,32,4))
    header = struct.pack("<I",int(version,16)) + prev + merkle + struct.pack("<III",int(ntime,16),int(bits,16),0)
    return Work(header, target, target_from_bits(bits), pool_height(coinbase), bits,
                str(job_id)+":"+extranonce2, generation,
                {"job_id": job_id, "extranonce2": extranonce2, "ntime": ntime})
