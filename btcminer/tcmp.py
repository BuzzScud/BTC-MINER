"""Bounded TCMP v1 transport codec, independently implemented in Python.

Wire reference: provider /tcmp.js captured 2026-10-12. Supports current CRT
rod frames and legacy stored/RLE/LZ77/blocked-LZ77/delta frames. FNV uses the
provider's nonstandard seed. This is transport integrity, not authentication.
"""
import math
import struct

HEADER = struct.Struct('<4sBBBBQQ')
PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
MODES = {'network': 1, 'file': 2, 'progressive': 3, 'constellation': 4,
         'auto': 5, 'fhc': 1, 'hdc': 2, 'lbc': 3, 'sic': 4, 'otc': 5}
MAX_BYTES = 8 * 1024 * 1024


class CodecError(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise CodecError(message)


def checksum(data):
    value = 1469598103934665603
    for byte in data:
        value = ((value ^ byte) * 1099511628211) & ((1 << 64) - 1)
    return value


class Reader:
    def __init__(self, data):
        self.data, self.offset = memoryview(data), 0

    def take(self, count):
        require(0 <= count <= len(self.data) - self.offset, 'Truncated TCMP payload')
        result = self.data[self.offset:self.offset + count]
        self.offset += count
        return result

    def uint(self, count):
        return int.from_bytes(self.take(count), 'little')

    def done(self):
        require(self.offset == len(self.data), 'Trailing TCMP payload')


def parameters(algorithm):
    primes = PRIMES[:algorithm + 7]
    block_bytes = (math.prod(primes).bit_length() - 1) // 8
    return primes, block_bytes, [(p - 1).bit_length() for p in primes]


def encode(data, mode='auto', max_input=MAX_BYTES):
    """Encode the provider's exact CRT format, including strict adaptive choice.

    This can expand data. Callers choose raw transport when the frame is larger.
    """
    require(mode in MODES, 'Unknown TCMP mode')
    require(len(data) <= max_input, 'TCMP input exceeds limit')
    algorithm = MODES[mode]
    primes, block_bytes, widths = parameters(algorithm)
    prefixes = [math.prod(primes[:i]) for i in range(1, len(primes) + 1)]
    blocks = []
    fixed_size = adaptive_size = 16
    for start in range(0, len(data), block_bytes):
        value = int.from_bytes(data[start:start + block_bytes], 'little')
        used = next(i + 1 for i, capacity in enumerate(prefixes) if value < capacity)
        blocks.append((value, used))
        fixed_size += (sum(widths) + 7) // 8
        adaptive_size += 1 + (sum(widths[:used]) + 7) // 8
    adaptive = adaptive_size < fixed_size
    payload = bytearray(struct.pack('<IIII', len(blocks), block_bytes, len(primes), 15 if adaptive else 13))
    for value, used in blocks:
        used = used if adaptive else len(primes)
        if adaptive:
            payload.append(used)
        packed = bits = 0
        for p, width in zip(primes[:used], widths):
            packed |= (value % p) << bits
            bits += width
        payload.extend(packed.to_bytes((bits + 7) // 8, 'little'))
    return HEADER.pack(b'TCMP', 1, algorithm, 0, algorithm, len(data), checksum(data)) + payload


def _crt(payload, algorithm, length):
    r = Reader(payload)
    blocks, block_bytes, count, flags = (r.uint(4) for _ in range(4))
    primes, expected_bytes, widths = parameters(algorithm)
    require(block_bytes == expected_bytes and count == len(primes), 'Invalid CRT parameters')
    require(flags & ~15 == 0 and (not flags & 2 or flags & 1), 'Invalid CRT flags')
    require(blocks == (length + block_bytes - 1) // block_bytes, 'Invalid CRT block count')
    if not flags & 4:
        require([r.uint(4) for _ in primes] == list(primes), 'Invalid CRT moduli')
    out = bytearray()
    for _ in range(blocks):
        expected = min(block_bytes, length - len(out))
        size = expected if flags & 8 else r.uint(4)
        require(size == expected, 'Invalid CRT block length')
        used = r.uint(1) if flags & 2 else count
        require(1 <= used <= count, 'Invalid CRT residue count')
        if flags & 1:
            bits = sum(widths[:used])
            packed = r.uint((bits + 7) // 8)
            require(packed >> bits == 0, 'Nonzero CRT padding')
            residues = []
            for width in widths[:used]:
                residues.append(packed & ((1 << width) - 1))
                packed >>= width
        else:
            residues = [r.uint(4) for _ in primes]
        value, product = 0, 1
        for residue, p in zip(residues, primes):
            require(residue < p, 'CRT residue out of range')
            value += product * (((residue - value) * pow(product, -1, p)) % p)
            product *= p
        require(value < 256 ** size, 'CRT value exceeds block length')
        out.extend(value.to_bytes(size, 'little'))
    r.done()
    return out


def _tokens(payload, length, lz=False):
    r, out = Reader(payload), bytearray()
    while r.offset < len(r.data):
        token = r.uint(1)
        count = token + 1 if token < 128 else (token & 127) + (4 if lz else 3)
        require(count <= length - len(out), 'TCMP token exceeds output')
        if token < 128:
            out.extend(r.take(count))
        elif lz:
            distance = r.uint(2) + 1
            require(distance <= len(out), 'Invalid TCMP back reference')
            for _ in range(count):
                out.append(out[-distance])
        else:
            out.extend(bytes([r.uint(1)]) * count)
    require(len(out) == length, 'TCMP output length mismatch')
    return out


def decode(frame, max_output=MAX_BYTES):
    """Validate size before allocation, consume exactly one frame, verify checksum."""
    require(len(frame) >= HEADER.size, 'Truncated TCMP header')
    magic, version, variant, transform, algorithm, length, expected_hash = HEADER.unpack_from(frame)
    require(magic == b'TCMP' and version == 1, 'Unsupported TCMP frame')
    require(1 <= variant <= 5 and 0 <= transform <= 4 and 0 <= algorithm <= 5,
            'Invalid TCMP frame markers')
    require(variant == 5 or transform in (0, variant), 'Invalid TCMP transform variant')
    require(not algorithm or transform == 0, 'Invalid CRT transform')
    require(length <= min(max_output, 1 << 30), 'TCMP output exceeds limit')
    payload = memoryview(frame)[HEADER.size:]
    if algorithm:
        out = _crt(payload, algorithm, length)
    elif transform == 0:
        require(len(payload) == length, 'Stored TCMP length mismatch')
        out = payload
    else:
        require(length >= 2 and len(payload) < length, 'Invalid compressed TCMP length')
        if transform in (1, 2, 4):
            out = _tokens(payload, length, lz=transform == 2)
            if transform == 4:
                for i in range(1, length):
                    out[i] = (out[i] + out[i - 1]) & 255
        else:
            r, out = Reader(payload), bytearray()
            while len(out) < length:
                size = min(65536, length - len(out))
                mode, count = r.uint(1), r.uint(4)
                block = r.take(count)
                require(mode in (0, 1), 'Invalid LZ block mode')
                if mode == 0:
                    require(count == size, 'Invalid stored LZ block length')
                    out.extend(block)
                else:
                    out.extend(_tokens(block, size, lz=True))
            r.done()
    require(checksum(out) == expected_hash, 'TCMP checksum mismatch')
    return bytes(out)
