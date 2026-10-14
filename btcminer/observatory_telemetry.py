"""META_CONTRACT: MINER-01 DATA-01 RATE-01

The calculator research observatory needs actual miner work, attempted nonces and
outcomes with replayable provenance. This producer MUST NOT select, exclude,
submit or change mining work. It SHALL enqueue a bounded sample after completed
native work; a background writer computes diagnostic SHA256d values and records
their extra cost separately from the miner's attempted-hash counter. Queue loss,
I/O failure and journal rotation MUST remain explicit. This is sampled telemetry,
not a complete hash journal or a Lean refinement proof. No credentials, wallet
addresses, connection URLs or submission bodies may enter these records.

Read ../README.md and ../../bitcoin-algorithm-observatory-2026-10-07/MASTER_PLAN.md
and CONTRACTS.md. Consumers: live_miner_bridge.py and observatory_server.py.
Engine.round owns mining; this module MAY observe immutable completed results.
"""
import hashlib
import json
import queue
import struct
import threading
import time
from pathlib import Path


class Telemetry:
    """Bounded nonblocking producer; at most four replay hashes per batch."""
    def __init__(self, folder, network, enabled=True, capacity=64, max_bytes=1024*1024, minimum_interval=.25):
        if not 1 <= capacity <= 256 or minimum_interval < 0:
            raise ValueError('Telemetry requires bounded capacity and a nonnegative interval')
        self.path = Path(folder) / 'model-events.jsonl'
        self.network = str(network)
        self.enabled = bool(enabled)
        self.queue = queue.Queue(maxsize=capacity)
        self.max_bytes = max_bytes
        self.stop = threading.Event()
        self.thread = None
        self.sequence = 0
        self.minimum_interval = minimum_interval
        self.last_batch = -float('inf')
        self.session = str(time.time_ns())
        self.counters = dict(enqueued=0, written=0, dropped=0, errors=0,
                             extra_sha256d=0, rotations=0, batches_observed=0,
                             batches_throttled=0, attempts_observed=0,
                             shutdown_timeouts=0)
        self.producer_sha256 = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
        self.engine_sha256 = hashlib.sha256(Path(__file__).with_name('engine.py').read_bytes()).hexdigest()

    def snapshot(self):
        return dict(self.counters, attempts_observed=str(self.counters['attempts_observed']),
                    enabled=self.enabled, session_id=self.session,
                    queue_capacity=self.queue.maxsize, queued=self.queue.qsize(),
                    sampled_replay_only=True, maximum_samples_per_batch=4,
                    minimum_batch_interval_seconds=self.minimum_interval,
                    writer_alive=bool(self.thread and self.thread.is_alive()))

    def _enqueue(self, row):
        if not self.enabled or self.stop.is_set():
            return
        self.sequence += 1
        row.update(schema='miner-observation-v1', sequence=self.sequence,
                   session_id=self.session, timestamp=time.time(), network=self.network,
                   producer_sha256=self.producer_sha256, engine_sha256=self.engine_sha256)
        try:
            self.queue.put_nowait(row)
            self.counters['enqueued'] += 1
        except queue.Full:
            self.counters['dropped'] += 1
            return
        if self.thread is None:
            self.thread = threading.Thread(target=self._write, daemon=True, name='model-telemetry')
            try:
                self.thread.start()
            except RuntimeError:
                self.counters['errors'] += 1
                self.enabled = False
                self.thread = None

    def batch(self, work, task, tried, round_id, hits=()):
        if not self.enabled or self.stop.is_set() or tried <= 0:
            return
        self.counters['batches_observed'] += 1
        self.counters['attempts_observed'] += tried
        stamp = time.monotonic()
        if stamp-self.last_batch < self.minimum_interval:
            self.counters['batches_throttled'] += 1
            return
        self.last_batch = stamp
        # Constant-size selection observes only the actually attempted task prefix.
        positions = sorted(set([0, (tried-1)//3, 2*(tried-1)//3, tried-1]))
        nonces = [int(task['nonces'][i]) if 'nonces' in task else (task['start']+i) & 0xffffffff
                  for i in positions]
        self._enqueue(dict(kind='batch', round_id=str(round_id), height=int(work.height),
                           header_hex=bytes(work.header).hex(), target_hex=f'{work.target:064x}',
                           network_target_hex=f'{work.network_target:064x}',
                           attempted=str(tried), sampled_positions=positions, nonces=nonces,
                           native_winner_nonces=[int(n) for n in hits[:64]],
                           native_winner_count=len(hits)))

    def outcome(self, work, nonce, accepted, block, round_id):
        self._enqueue(dict(kind='outcome', round_id=str(round_id), height=int(work.height),
                           header_hex=bytes(work.header).hex(), nonce=int(nonce),
                           accepted=accepted if accepted in (True, False, None) else None,
                           block=bool(block)))

    def _write(self):
        while not self.stop.is_set() or not self.queue.empty():
            try:
                row = self.queue.get(timeout=.1)
            except queue.Empty:
                continue
            try:
                header = bytes.fromhex(row['header_hex'])
                row['job_id'] = hashlib.sha256(header[:76]).hexdigest()
                if row['kind'] == 'batch':
                    points = []
                    for nonce in row.pop('nonces'):
                        actual = header[:76] + struct.pack('<I', nonce)
                        digest = hashlib.sha256(hashlib.sha256(actual).digest()).digest()
                        self.counters['extra_sha256d'] += 1
                        points.append(dict(nonce=nonce, hash=digest[::-1].hex()))
                    row['samples'] = points
                    row['sample_semantics'] = 'Background SHA256d replay of four selected attempted nonce positions; extra computations excluded from mining counters.'
                row['telemetry'] = self.snapshot()
                self.path.parent.mkdir(parents=True, exist_ok=True)
                if self.path.exists() and self.path.stat().st_size >= self.max_bytes:
                    older = self.path.with_suffix('.jsonl.2')
                    previous = self.path.with_suffix('.jsonl.1')
                    if previous.exists():
                        previous.replace(older)
                    self.path.replace(previous)
                    self.counters['rotations'] += 1
                with self.path.open('a') as stream:
                    stream.write(json.dumps(row, separators=(',', ':'), allow_nan=False)+'\n')
                self.counters['written'] += 1
            except Exception:
                # Diagnostic I/O must not change consensus work or crash the miner.
                self.counters['errors'] += 1
            finally:
                self.queue.task_done()

    def close(self, timeout=2.0):
        """Stop admission and drain the finite queue within the shutdown budget.

        Engine.run owns this call; direct-round harnesses MUST register cleanup.
        A stalled OS write cannot safely be killed in Python. A False result and
        explicit timeout counter distinguish that case; the daemon thread MUST
        NOT keep the process alive. Callers needing a drained directory SHALL
        check the result before removing it.
        """
        self.stop.set()
        if self.thread:
            self.thread.join(timeout=timeout)
            if self.thread.is_alive():
                self.counters['shutdown_timeouts'] += 1
                return False
        return True
