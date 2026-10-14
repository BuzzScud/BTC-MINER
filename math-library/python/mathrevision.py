"""Identify the local math implementation loaded by a miner process."""
import hashlib
from . import ROOT

FILES = ('btcminer/pqmath.py', 'btcminer/thesis2.py', 'btcminer/coreprimes.py', 'btcminer/rodmath.py',
         'btcminer/abacus.py', 'btcminer/pruning.py', 'btcminer/pruning_worker.py',
         'btcminer/constraintmodel.py', 'btcminer/scaled_abacus.py',
         'btcminer/adaptive.py', 'btcminer/priority.py', 'btcminer/recurrence.py',
         'btcminer/abacus_lab.py', 'btcminer/shared_abacus.py', 'btcminer/research_system.py',
         'btcminer/claim_calculus.py', 'btcminer/archive_math.py', 'btcminer/theorem_calculations.py', 'research/claims.json', 'research/executable-theorems.json', 'btcminer/engine.py', 'btcminer/protocol.py',
         'btcminer/connections.py', 'btcminer/native.py', 'native/hasher_fast.c',
         'native/latcalc/src/abacus.c', 'native/latcalc/include/latcalc/abacus.h',
         'native/latcalc/src/rodsieve.c', 'native/latcalc/src/bigint.c',
         'native/latcalc/src/rns.c', 'native/latcalc/src/common.c',
         'native/latcalc/include/latcalc/rodsieve.h', 'native/latcalc/include/latcalc/bigint.h',
         'native/latcalc/include/latcalc/rns.h', 'native/latcalc/include/latcalc/common.h')

# Include every compiled arithmetic unit and header in update detection.
FILES = tuple(dict.fromkeys((*FILES, *(p.relative_to(ROOT).as_posix() for p in
    sorted((ROOT/'native/latcalc').rglob('*')) if p.suffix in ('.c', '.h')),
    # Target decoding, local difficulty controls and imported legacy modules
    # are part of the loaded implementation too. Track the built libraries so
    # a binary-only replacement cannot appear to be the same implementation.
    *(p.relative_to(ROOT).as_posix() for p in sorted((ROOT/'btcminer').rglob('*.py'))),
    *(p.relative_to(ROOT).as_posix() for folder in ('src', 'math-library')
      for p in sorted((ROOT/folder).rglob('*')) if p.suffix in ('.py', '.c', '.h')),
    *(p.relative_to(ROOT).as_posix() for p in sorted((ROOT/'native').iterdir())
      if p.is_file() and p.suffix in ('.so', '.dylib', '.dll')))))


def fingerprint():
    return {name: hashlib.sha256((ROOT/name).read_bytes()).hexdigest() for name in FILES}
