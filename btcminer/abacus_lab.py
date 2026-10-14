"""Miner-integrated, model-scoped experiments using the live constraint engine."""
import hashlib
import json
import struct
import time
from .adaptive import retain_candidates
from .constraintmodel import Arithmetic, IV, compress, execute, z3
from .scaled_abacus import PrecisionAbacus, SCALES, q_codec


def precision_check(bits):
    if type(bits) is not int or not 1 <= bits <= 1048576:
        raise ValueError('Bounded check requires 1..1048576 bits; the arithmetic class has no fixed ceiling')
    started = time.monotonic(); workspace = PrecisionAbacus(bits)
    a = (1 << bits)-19; b = (1 << max(1, bits//2))-11
    inputs = (0, 1, -1, a, -a, b, -b)
    roundtrips = all(workspace.load(n).value() == n for n in inputs)
    addition = workspace.calculate('add', a, b) == a+b
    product = workspace.calculate('multiply', a, b) == a*b
    subtraction = workspace.calculate('add', -a, b) == -a+b
    identity = id(workspace.model); buffer_id = id(workspace.readings)
    workspace.clear()
    cleared = workspace.value() == 0
    workspace.load(a)
    reused = id(workspace.model) == identity and id(workspace.readings) == buffer_id
    return {'ok': roundtrips and addition and product and subtraction and cleared and reused,
            'input_bits': bits, 'product_bits': abs(a*b).bit_length(),
            'roundtrips': len(inputs), 'addition': addition, 'multiplication': product,
            'signed_addition': subtraction, 'clear_and_reuse': cleared and reused,
            'seconds': time.monotonic()-started, **workspace.description(),
            'scope': 'Exact integer/CRT operations; not factoring, primality, or Bitcoin hash prediction'}


def compression_check():
    rows = []
    for M in SCALES:
        codec = q_codec(M); values = list(codec.values)
        packed, count = codec.pack(values)
        roundtrip = codec.unpack(packed, count) == values
        coordinates = all(codec.from_coordinates(**{k: v for k, v in codec.coordinates(n).items()
                                                    if k in ('k', 'index')}) == n for n in values)
        rows.append({**codec.description(), 'ok': roundtrip and coordinates,
                     'packed_sequence_bytes': len(packed), 'roundtrips': count})
    from .geometry_codec import transport_check
    transport = transport_check()
    return {'ok': all(row['ok'] for row in rows) and transport['ok'], 'scales': rows,
            'miner_geometry_transport': transport}


def toy_check(width=32, rounds=32, nonce_bits=10, difficulty=10, budget_ms=2000, seed=30, scale=0):
    if z3 is None:
        raise RuntimeError('Toy constraints need the installed abacus-solver Python environment')
    if width not in (8, 16, 32, 64) or not 1 <= rounds <= 64 or not 1 <= nonce_bits <= min(width, 16):
        raise ValueError('Use width 8/16/32/64, rounds 1..64, nonce-bits 1..16 within width')
    if not 1 <= difficulty <= width or not 1 <= budget_ms <= 30000:
        raise ValueError('Invalid difficulty or pruning budget')
    prefix = (struct.pack('<I', 0x20000000)
              +hashlib.sha256(('lossless-parent-%d' % seed).encode()).digest()
              +hashlib.sha256(('lossless-root-%d' % seed).encode()).digest()
              +struct.pack('<II', 1700000000+seed, 0x2000ffff))
    initial = compress(list(struct.unpack('>16I', prefix[:64])), IV)[0]
    tail = prefix[64:]+bytes(4)+b'\x80'+bytes(39)+struct.pack('>Q', 640)
    mask = (1 << width)-1
    words = [v & mask for v in struct.unpack('>16I', tail)]
    initial = [v & mask for v in initial]
    values = list(q_codec(scale).values) if scale else list(range(1 << nonce_bits))
    if max(values) > mask:
        raise ValueError('Q family exceeds the toy word width; increase width')
    started = time.monotonic(); deadline = started+budget_ms/1000
    solver = z3.Then('simplify', 'propagate-values', 'solve-eqs', 'simplify', 'smt').solver()
    solver.set(max_memory=256)
    ops = Arithmetic(width, solver); nonce = z3.BitVec('nonce', width)
    symbolic = [ops.constant(v) for v in words]; symbolic[3] = nonce
    result = execute(symbolic, [ops.constant(v) for v in initial], rounds, ops)
    filter_bits = max(1, difficulty-2)
    solver.add(z3.Extract(width-1, width-filter_bits, result[0]) == 0)
    filtered = retain_candidates(solver, nonce, values, deadline)
    frozen = filtered['keep'][:]
    filter_seconds = time.monotonic()-started
    # Only now may a concrete scan run. Its full computation is counted.
    def value(n):
        data = words[:]; data[3] = n
        return compress(data, initial, width, rounds)[0][0]
    trials = 0; first = None; started = time.monotonic()
    for n in frozen:
        trials += 1
        if value(n) >> (width-difficulty) == 0:
            first = n; break
    scan_seconds = time.monotonic()-started
    started = time.monotonic(); baseline_attempts = 0; baseline_first = None
    for n in values:
        baseline_attempts += 1
        if value(n) >> (width-difficulty) == 0:
            baseline_first = n; break
    baseline_seconds = time.monotonic()-started
    started = time.monotonic()
    oracle = {n: value(n) for n in values}
    winners = [n for n in values if oracle[n] >> (width-difficulty) == 0]
    necessary = {n for n in values if oracle[n] >> (width-filter_bits) == 0}
    lost = sorted(set(winners)-set(frozen))
    return {'ok': not lost and necessary <= set(frozen), 'model': 'toy-sha-compression-v1',
            'width': width, 'rounds': rounds, 'difficulty_zero_bits': difficulty,
            'filter_zero_bits': filter_bits, 'scale': scale, 'seed': seed,
            'original_candidates': len(values), 'retained_candidates': len(frozen),
            'excluded': filtered['excluded'], 'adaptive_splits': filtered['adaptive_splits'],
            'unknown': filtered['unknown'], 'solver_checks': filtered['solver_checks'],
            'carry_constraints': ops.count, 'filter_seconds': filter_seconds,
            'concrete_hashes_during_pruning': 0, 'reduced_hashes_attempted': trials,
            'reduced_hashes_to_success': trials if first is not None else None,
            'baseline_hashes_to_success': values.index(winners[0])+1 if winners else None,
            'baseline_scan_seconds': baseline_seconds,
            'baseline_hashes_attempted': baseline_attempts,
            'same_first_winner': baseline_first == first,
            'filter_plus_reduced_scan_seconds': filter_seconds+scan_seconds,
            'full_scan_seconds': scan_seconds, 'exhaustive_validation_hashes': len(values),
            'exhaustive_validation_seconds': time.monotonic()-started,
            'winning_nonces': len(winners), 'lost_winners': lost,
            'retained_set_sha256': hashlib.sha256(json.dumps(frozen).encode()).hexdigest(),
            'scope': 'Integrated toy model; its exclusions never enter a Bitcoin job'}
