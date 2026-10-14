"""Serialized durable leases, exact progress, proof gates and result outbox.

Workers are authenticated, trusted participants. A progress acknowledgment is
their assertion of completed hashing, not a cryptographic proof of negative work.
Every winning candidate and every pruning exclusion is independently checked.
"""
from contextlib import contextmanager
import hashlib
import math
from pathlib import Path
import sqlite3
import threading
import time

from ..native import hash256
from .geometry import Geometry, END, canonical, children, integer, implementation


class Rejected(ValueError):
    pass


class Store:
    def __init__(self, path, *, lease_seconds=15, target_seconds=.25,
                 max_region=1000000, initial_region=16384, clock=time.time):
        if not 2 <= lease_seconds <= 300 or not .01 <= target_seconds <= 10:
            raise ValueError('Invalid lease or scheduling duration')
        integer(max_region, 1, 1000000); integer(initial_region, 1, max_region)
        self.lease_seconds, self.target_seconds = lease_seconds, target_seconds
        self.max_region, self.initial_region = max_region, initial_region
        self.clock = clock; self.lock = threading.RLock(); self.geometries = {}
        Path(path).parent.mkdir(parents=True, exist_ok=True)
        self.db = sqlite3.connect(str(path), timeout=5, isolation_level=None, check_same_thread=False)
        self.db.row_factory = sqlite3.Row
        self.db.execute('PRAGMA journal_mode=DELETE')
        self.db.execute('PRAGMA synchronous=EXTRA')
        self.db.execute('PRAGMA fullfsync=ON')
        self.db.executescript('''
          CREATE TABLE IF NOT EXISTS jobs(id TEXT PRIMARY KEY,spec TEXT NOT NULL,
            active INTEGER NOT NULL,until REAL NOT NULL,root_end INTEGER NOT NULL,
            hashed INTEGER NOT NULL DEFAULT 0,excluded INTEGER NOT NULL DEFAULT 0);
          CREATE TABLE IF NOT EXISTS regions(id INTEGER PRIMARY KEY,job TEXT NOT NULL,
            parent INTEGER,start INTEGER NOT NULL,stop INTEGER NOT NULL,cursor INTEGER NOT NULL,
            total INTEGER NOT NULL,done INTEGER NOT NULL DEFAULT 0,state TEXT NOT NULL,
            owner TEXT,epoch INTEGER NOT NULL DEFAULT 0,expires REAL NOT NULL DEFAULT 0);
          CREATE INDEX IF NOT EXISTS ready_regions ON regions(job,state,start);
          CREATE INDEX IF NOT EXISTS sized_regions ON regions(job,state,total);
          CREATE TABLE IF NOT EXISTS receipts(peer TEXT,op TEXT,intent TEXT,response TEXT,
            PRIMARY KEY(peer,op));
          CREATE TABLE IF NOT EXISTS nodes(peer TEXT PRIMARY KEY,rate REAL NOT NULL);
          CREATE TABLE IF NOT EXISTS hits(job TEXT,nonce INTEGER,value TEXT,status TEXT NOT NULL,
            outcome TEXT,PRIMARY KEY(job,nonce));
          CREATE TABLE IF NOT EXISTS exclusions(job TEXT,raw INTEGER,nonce INTEGER,value TEXT,
            PRIMARY KEY(job,raw));
          CREATE TABLE IF NOT EXISTS progress(id INTEGER PRIMARY KEY,job TEXT,peer TEXT,
            start INTEGER,stop INTEGER,hashes INTEGER,hits TEXT);
          CREATE INDEX IF NOT EXISTS job_progress ON progress(job,id);
        ''')
        from .buffers import initialize
        initialize(self.db)

    @contextmanager
    def transaction(self):
        with self.lock:
            self.db.execute('BEGIN IMMEDIATE')
            try:
                yield
                self.db.execute('COMMIT')
            except BaseException:
                self.db.execute('ROLLBACK'); raise

    def close(self):
        with self.lock: self.db.close()

    def geometry(self, job):
        if job not in self.geometries:
            row = self.db.execute('SELECT spec FROM jobs WHERE id=?', (job,)).fetchone()
            if row is None: raise Rejected('unknown_job')
            import json
            self.geometries[job] = Geometry.from_spec(json.loads(row['spec']))
        return self.geometries[job]

    def add_region(self, job, parent, start, stop, state='pending', done=0):
        total = self.geometry(job).count(start, stop)
        if total == 0: state = 'padding'
        return self.db.execute('''INSERT INTO regions(job,parent,start,stop,cursor,total,done,state)
            VALUES(?,?,?,?,?,?,?,?)''', (job,parent,start,stop,start,total,done,state)).lastrowid

    def activate(self, spec, *, root_end=END):
        """Coordinator only. A bounded root is available to isolated tests."""
        integer(root_end, 1, END)
        geometry = Geometry.from_spec(spec)
        job = spec['id']
        with self.transaction():
            existing = self.db.execute('SELECT * FROM jobs WHERE id=?', (job,)).fetchone()
            if existing and (existing['spec'] != canonical(spec) or existing['root_end'] != root_end):
                raise Rejected('job_conflict')
            self.db.execute('UPDATE jobs SET active=0')
            self.db.execute("UPDATE regions SET state='pending',owner=NULL,epoch=epoch+1,expires=0 WHERE state='leased'")
            # An interrupted external submission is ambiguous, never silently retried.
            self.db.execute("UPDATE hits SET status='unknown' WHERE status='sending'")
            self.geometries = {job: geometry}
            if not existing:
                self.db.execute('INSERT INTO jobs(id,spec,active,until,root_end) VALUES(?,?,1,?,?)',
                                (job,canonical(spec),self.clock()+3,root_end))
                self.add_region(job, None, 0, root_end)
            else:
                self.db.execute('UPDATE jobs SET active=1,until=? WHERE id=?', (self.clock()+3,job))
        return job

    def pulse(self, job):
        with self.transaction():
            self.db.execute('UPDATE jobs SET until=? WHERE id=? AND active=1', (self.clock()+3,job))

    def deactivate(self, job):
        with self.transaction():
            self.db.execute('UPDATE jobs SET active=0 WHERE id=?', (job,))
            self.db.execute("UPDATE regions SET state='pending',owner=NULL,epoch=epoch+1,expires=0 WHERE job=? AND state='leased'", (job,))

    def active(self, job=None):
        row = self.db.execute('SELECT * FROM jobs WHERE active=1 AND until>?', (self.clock(),)).fetchone()
        if row is None or (job is not None and row['id'] != job): raise Rejected('stale_job')
        return row

    def split(self, row, cuts=None):
        if row['state'] != 'pending': raise Rejected('region_not_pending')
        start, stop = row['cursor'], row['stop']
        parts = children(start, stop) if cuts is None else cuts
        if not parts: return []
        if parts[0][0] != start or parts[-1][1] != stop or any(a>=b for a,b in parts) or any(x[1]!=y[0] for x,y in zip(parts,parts[1:])):
            raise Rejected('invalid_partition')
        self.db.execute("UPDATE regions SET state='split' WHERE id=?", (row['id'],))
        if row['cursor'] > row['start']:
            self.add_region(row['job'],row['id'],row['start'],row['cursor'],'done',row['done'])
        return [self.add_region(row['job'],row['id'],a,b) for a,b in parts]

    def expire(self, job):
        self.db.execute("UPDATE regions SET state='pending',owner=NULL,epoch=epoch+1 WHERE job=? AND state='leased' AND expires<=?", (job,self.clock()))

    def _lease(self, peer, request):
        self.active(request['job'])
        row = self.db.execute('SELECT * FROM regions WHERE id=? AND job=?',
                              (request['region'],request['job'])).fetchone()
        if row is None or row['state'] != 'leased' or row['owner'] != peer or row['epoch'] != request['epoch'] or row['expires'] <= self.clock():
            raise Rejected('stale_lease')
        return row

    def envelope(self, row):
        import json
        spec = json.loads(self.db.execute('SELECT spec FROM jobs WHERE id=?', (row['job'],)).fetchone()[0])
        return dict(job=row['job'],region=row['id'],epoch=row['epoch'],start=row['cursor'],
                    stop=row['stop'],expires=row['expires'],lease_seconds=self.lease_seconds,spec=spec)

    def claim(self, peer):
        try: job = self.active()['id']
        except Rejected: return {'assignment': None, 'reason': 'idle'}
        self.expire(job)
        own = self.db.execute("SELECT * FROM regions WHERE job=? AND state='leased' AND owner=?", (job,peer)).fetchone()
        if own: return {'assignment': self.envelope(own)}
        rate = self.db.execute('SELECT rate FROM nodes WHERE peer=?', (peer,)).fetchone()
        capacity = self.initial_region if rate is None else max(1,min(self.max_region,int(rate[0]*self.target_seconds)))
        while True:
            row = self.db.execute("SELECT * FROM regions WHERE job=? AND state='pending' AND total<=? ORDER BY total DESC,start LIMIT 1", (job,capacity)).fetchone()
            if row is None:
                row = self.db.execute("SELECT * FROM regions WHERE job=? AND state='pending' AND total>? ORDER BY total,start LIMIT 1", (job,capacity)).fetchone()
            if row is None: return {'assignment': None, 'reason': 'waiting_or_complete'}
            remaining = self.geometry(job).count(row['cursor'],row['stop'])
            if remaining == 0:
                self.db.execute("UPDATE regions SET state='done',cursor=stop WHERE id=?", (row['id'],)); continue
            if remaining > capacity:
                self.split(row); continue
            self.db.execute("UPDATE regions SET state='leased',owner=?,epoch=epoch+1,expires=? WHERE id=?",
                            (peer,self.clock()+self.lease_seconds,row['id']))
            return {'assignment': self.envelope(self.db.execute('SELECT * FROM regions WHERE id=?',(row['id'],)).fetchone())}

    def commit(self, peer, request):
        row = self._lease(peer, request)
        if request['start'] != row['cursor']: raise Rejected('progress_conflict')
        end = integer(request['cursor'], row['cursor']+1, row['stop'])
        seconds = request['seconds']
        if type(seconds) not in (int,float) or not math.isfinite(seconds) or not 0 <= seconds <= 3600:
            raise Rejected('invalid_duration')
        geometry = self.geometry(row['job'])
        count = geometry.count(row['cursor'],end)
        if request['hashes'] != count or type(request['hashes']) is not int: raise Rejected('invalid_count')
        hits = request['hits']
        if not isinstance(hits,list) or len(hits)>1: raise Rejected('invalid_hits')
        import json
        spec = json.loads(self.db.execute('SELECT spec FROM jobs WHERE id=?',(row['job'],)).fetchone()[0])
        for nonce in hits:
            raw = geometry.raw_index(nonce)
            if not row['cursor'] <= raw < end: raise Rejected('hit_outside_progress')
            value = int.from_bytes(hash256(bytes.fromhex(spec['header'])[:76]+nonce.to_bytes(4,'little')), 'little')
            if value > int(spec['target']): raise Rejected('invalid_hash')
            self.db.execute("INSERT OR IGNORE INTO hits VALUES(?,?,?,'pending',NULL)",(row['job'],nonce,str(value)))
        state = 'done' if end == row['stop'] else 'leased'
        self.db.execute('UPDATE regions SET cursor=?,done=done+?,state=?,expires=? WHERE id=?',
                        (end,count,state,self.clock()+self.lease_seconds,row['id']))
        self.db.execute('UPDATE jobs SET hashed=hashed+? WHERE id=?',(count,row['job']))
        self.db.execute('INSERT INTO progress(job,peer,start,stop,hashes,hits) VALUES(?,?,?,?,?,?)',
                        (row['job'],peer,row['cursor'],end,count,canonical(hits)))
        if seconds > 0 and count:
            old = self.db.execute('SELECT rate FROM nodes WHERE peer=?',(peer,)).fetchone()
            rate = min(1e12,count/seconds)
            rate = rate if old is None else .75*old[0]+.25*rate
            self.db.execute('INSERT OR REPLACE INTO nodes VALUES(?,?)',(peer,rate))
        return dict(cursor=end,hashes=count,complete=state=='done')

    def operation(self, peer, request):
        """Atomic idempotent mutations; peer identity comes from authentication."""
        if not isinstance(peer,str) or not 1<=len(peer)<=128: raise Rejected('invalid_peer')
        if not isinstance(request,dict): raise Rejected('invalid_request')
        schemas = {'claim': {'implementation'}, 'heartbeat': {'job','region','epoch'},
                   'commit': {'job','region','epoch','start','cursor','hashes','hits','seconds'},
                   'release': {'job','region','epoch'}, 'status': set()}
        from .buffers import SCHEMAS, operation as buffer_operation
        schemas.update(SCHEMAS)
        action = request.get('action')
        if action not in schemas or set(request) != schemas[action]|{'action','op'}:
            raise Rejected('invalid_request')
        op = request['op']
        if not isinstance(op,str) or not 1<=len(op)<=128 or not op.isascii(): raise Rejected('invalid_operation')
        if action == 'claim' and request['implementation'] != implementation(): raise Rejected('implementation_mismatch')
        for name in ('region','epoch','start','cursor','hashes'):
            if name in request: integer(request[name],0,END)
        intent = canonical(request)
        import json
        with self.transaction():
            recorded = self.db.execute('SELECT * FROM receipts WHERE peer=? AND op=?',(peer,op)).fetchone()
            if recorded:
                if recorded['intent'] != intent: raise Rejected('operation_conflict')
                return json.loads(recorded['response'])
            if action == 'claim': response = self.claim(peer)
            elif action == 'commit': response = self.commit(peer,request)
            elif action in ('heartbeat','release'):
                row = self._lease(peer,request)
                if action == 'heartbeat':
                    self.db.execute('UPDATE regions SET expires=? WHERE id=?',(self.clock()+self.lease_seconds,row['id']))
                else:
                    self.db.execute("UPDATE regions SET state='pending',owner=NULL,epoch=epoch+1 WHERE id=?",(row['id'],))
                response = {'ok':True}
            elif action == 'status': response = self._stats()
            else: response = buffer_operation(self.db,peer,request)
            self.db.execute('INSERT INTO receipts VALUES(?,?,?,?)',(peer,op,intent,canonical(response)))
            return response

    def _stats(self, job=None):
        if job is None:
            current = self.db.execute('SELECT id FROM jobs WHERE active=1').fetchone()
            if current is None: return {'active':False}
            job = current[0]
        record=self.db.execute('SELECT * FROM jobs WHERE id=?',(job,)).fetchone()
        if record is None: raise Rejected('unknown_job')
        rows = self.db.execute("SELECT state,sum(total) total,sum(done) done,count(*) regions FROM regions WHERE job=? AND state IN ('pending','leased') GROUP BY state",(job,)).fetchall()
        totals = {r['state']:dict(r) for r in rows}
        total = self.geometry(job).count(0,record['root_end'])
        hashed = record['hashed']
        excluded = record['excluded']
        leased = self.db.execute("SELECT sum(total-done) FROM regions WHERE job=? AND state='leased'",(job,)).fetchone()[0] or 0
        return dict(job=job,total=total,hashed=hashed,excluded=excluded,
                    verification_hashes=excluded,
                    remaining=total-hashed-excluded,leased=leased,states=totals,
                    complete=total==hashed+excluded)

    def stats(self, job=None):
        with self.lock: return self._stats(job)

    def baseline(self,job):
        with self.lock:
            row=self.db.execute('SELECT hashed FROM jobs WHERE id=?',(job,)).fetchone()
            cursor=self.db.execute('SELECT max(id) FROM progress WHERE job=?',(job,)).fetchone()[0] or 0
            return (row[0] if row else 0),cursor

    def progress(self,job,after):
        with self.lock:
            return [dict(row) for row in self.db.execute('SELECT * FROM progress WHERE job=? AND id>? ORDER BY id LIMIT 128',(job,after))]

    def proof_region(self, job, maximum):
        integer(maximum,1,64)
        with self.transaction():
            self.active(job)
            while True:
                row = self.db.execute("SELECT * FROM regions WHERE job=? AND state='pending' ORDER BY start LIMIT 1",(job,)).fetchone()
                if row is None: return None
                if self.geometry(job).count(row['cursor'],row['stop']) <= maximum: return dict(row)
                self.split(row)

    def exclude(self, job, region, proposed):
        """Only coordinator-local evidence enters this gate; no remote prune API.

        Each removal is bound to the header/target and independently hashed.
        Partial proposals split out singleton positions; unresolved work remains.
        """
        if not isinstance(proposed,list) or len(proposed)>64: raise Rejected('invalid_exclusions')
        with self.transaction():
            self.active(job)
            row = self.db.execute('SELECT * FROM regions WHERE id=? AND job=?',(region,job)).fetchone()
            if row is None or row['state']!='pending': raise Rejected('region_not_pending')
            geometry = self.geometry(job)
            import json
            spec = json.loads(self.db.execute('SELECT spec FROM jobs WHERE id=?',(job,)).fetchone()[0])
            accepted = {}
            for nonce in proposed:
                raw = geometry.raw_index(nonce)
                if not row['cursor'] <= raw < row['stop']: raise Rejected('exclusion_outside_region')
                value = int.from_bytes(hash256(bytes.fromhex(spec['header'])[:76]+nonce.to_bytes(4,'little')),'little')
                if value <= int(spec['target']): raise Rejected('exclusion_contains_winner')
                accepted[raw] = (nonce,value)
            if not accepted: return 0
            cuts = sorted({row['cursor'],row['stop']}|set(accepted)|{n+1 for n in accepted})
            ids = self.split(row,list(zip(cuts,cuts[1:])))
            for child in ids:
                part = self.db.execute('SELECT * FROM regions WHERE id=?',(child,)).fetchone()
                if part['start'] in accepted and part['stop']==part['start']+1:
                    nonce,value = accepted[part['start']]
                    self.db.execute("UPDATE regions SET state='excluded' WHERE id=?",(child,))
                    self.db.execute('INSERT INTO exclusions VALUES(?,?,?,?)',(job,part['start'],nonce,str(value)))
            self.db.execute('UPDATE jobs SET excluded=excluded+? WHERE id=?',(len(accepted),job))
            return len(accepted)

    def take_hit(self, job):
        with self.transaction():
            self.active(job)
            row = self.db.execute("SELECT nonce FROM hits WHERE job=? AND status='pending' ORDER BY nonce LIMIT 1",(job,)).fetchone()
            if row is None: return None
            self.db.execute("UPDATE hits SET status='sending' WHERE job=? AND nonce=?",(job,row[0]))
            return row[0]

    def finish_hit(self, job, nonce, outcome):
        with self.transaction():
            self.db.execute("UPDATE hits SET status=?,outcome=? WHERE job=? AND nonce=? AND status='sending'",
                            ('unknown' if outcome.get('accepted') is None else 'submitted',canonical(outcome),job,nonce))
