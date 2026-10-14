"""Copper input, bounded read-only observations, and incremental terminal output.

LIVE-01: journal samples are diagnostic replay, never the full nonce stream.
Reading or freezing a view cannot control the miner. See MASTER_PLAN.md and
observatory_telemetry.py; tui.py owns presentation and lifecycle shortcuts.
"""
import codecs
import json
import re
import time
from pathlib import Path


class Keys:
    """Retain split UTF-8 and escape sequences; distinguish a lone Escape."""
    def __init__(self):
        self.decoder = codecs.getincrementaldecoder('utf-8')(errors='replace')
        self.pending = ''
        self.since = 0
        self.pasting = False

    def feed(self, data=b'', now=None):
        now = time.monotonic() if now is None else now
        if data:
            if not self.pending:
                self.since = now
            self.pending += self.decoder.decode(data)
        keys = []
        while self.pending:
            if self.pending.startswith('\x1b'):
                match = re.match(r'\x1b(?:\[[0-9;?]*[A-Za-z~]|O[A-Za-z])', self.pending)
                if match:
                    token = match.group(); self.pending = self.pending[len(token):]
                    if token == '\x1b[200~':
                        self.pasting = True
                    elif token == '\x1b[201~':
                        self.pasting = False
                    elif not self.pasting:
                        keys.append(token.replace('\x1bO', '\x1b['))
                    continue
                if now-self.since < .05 and len(self.pending) < 32:
                    break
            token, self.pending = self.pending[0], self.pending[1:]
            # Pasted text is inserted by App, never interpreted as shortcuts.
            keys.append(('paste', token) if self.pasting else token)
        if not self.pending:
            self.since = now
        return keys


class Observations:
    """Read at most 128 KiB; only retain a complete batch from this session."""
    def __init__(self, logs):
        self.path = Path(logs)/'model-events.jsonl'
        self.identity = None
        self.sample = None

    def read(self, status):
        session = status.get('model_telemetry', {}).get('session_id')
        if not session or not status.get('running'):
            self.sample = None; self.identity = None
            return None
        try:
            with self.path.open('rb') as stream:
                stat = __import__('os').fstat(stream.fileno())
                identity = (session, stat.st_ino, stat.st_size, stat.st_mtime_ns)
                if identity == self.identity:
                    return self.sample
                start = max(0, stat.st_size-131072)
                stream.seek(start); raw = stream.read(131072)
            if start:
                raw = raw.partition(b'\n')[2]
            raw = raw[:raw.rfind(b'\n')+1]
            sample = None
            for line in reversed(raw.splitlines()):
                try:
                    row = json.loads(line)
                    if row.get('session_id') != session or row.get('kind') != 'batch':
                        continue
                    point = row['samples'][-1]
                    nonce, digest = point['nonce'], point['hash']
                    if not re.fullmatch('[0-9a-fA-F]{64}', str(row.get('job_id',''))):
                        continue
                    if type(nonce) is not int or not 0 <= nonce < 2**32:
                        continue
                    if not isinstance(digest, str) or not re.fullmatch('[0-9a-fA-F]{64}', digest):
                        continue
                    stamp = row['timestamp']
                    if not isinstance(stamp, (float, int)) or not 0 < stamp <= time.time()+5:
                        continue
                    if int(row['attempted']) <= 0:
                        continue
                    sample = dict(nonce=nonce, hash=digest, timestamp=stamp,
                                  job=str(row['job_id']), round=str(row['round_id']),
                                  height=row.get('height'), session=session,
                                  attempted=int(row['attempted']), sequence=row.get('sequence'))
                    break
                except (ValueError, TypeError, KeyError, IndexError, AttributeError):
                    continue
            self.identity, self.sample = identity, sample
            return sample
        except OSError:
            self.identity = None; self.sample = None
            return None


class Painter:
    """Write changed rows only; fully invalidate after a terminal resize."""
    def __init__(self):
        self.lines = []; self.size = None

    def render(self, frame, size):
        lines = frame.removeprefix('\x1b[0m\x1b[H').split('\r\n')
        if size != self.size:
            self.size = size; self.lines = lines
            return '\x1b[2J'+frame
        output = []
        for index, line in enumerate(lines):
            if index >= len(self.lines) or line != self.lines[index]:
                output.append(f'\x1b[{index+1};1H'+line+'\x1b[0m\x1b[K')
        self.lines = lines
        return ''.join(output)
