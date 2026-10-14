"""Bounded host resource observation and batch-boundary mining admission.

Only local OS measurements control mining. Provider-reported calculation cost
never grants work or CPU capacity. Limits are sampled guards, not OS quotas.
"""
from collections import deque
from dataclasses import dataclass
import ctypes
import json
import math
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time
import uuid

from .settings import atomic_json

MIB = 1024 * 1024


@dataclass(frozen=True)
class Policy:
    enabled: bool = False
    minimum: int = 2
    maximum: int = 6
    target: float = 85
    backoff: float = 90
    rss_mib: float = 4096
    peer_rss_mib: float = 256
    swap_growth_mib: float = 128
    sample_seconds: float = 2
    increase_seconds: float = 60
    settle_seconds: float = 30

    @classmethod
    def from_config(cls, c):
        p = cls(enabled=c.get('resource_control', False),
                minimum=c.get('resource_min_workers', 2), maximum=c.get('resource_max_workers', 6),
                target=c.get('resource_cpu_target', 85), backoff=c.get('resource_cpu_backoff', 90),
                rss_mib=c.get('resource_rss_mib', 4096), peer_rss_mib=c.get('resource_peer_rss_mib', 256),
                swap_growth_mib=c.get('resource_swap_growth_mib', 128))
        if not 1 <= p.minimum <= p.maximum <= (os.cpu_count() or 8):
            raise ValueError('Invalid resource worker range')
        if not 1 <= p.target < p.backoff <= 100:
            raise ValueError('CPU target must be below backoff')
        if min(p.rss_mib, p.peer_rss_mib, p.swap_growth_mib) <= 0 or p.peer_rss_mib > p.rss_mib:
            raise ValueError('Invalid resource memory limits')
        return p


def command(args):
    return subprocess.check_output(args, text=True, timeout=2, stderr=subprocess.DEVNULL)


class HostSampler:
    """Host CPU deltas and owned descendants, never command lines or credentials."""
    def __init__(self, root_pid=None):
        self.root_pid = os.getpid() if root_pid is None else root_pid
        self.previous = None
        self.root_identity = None
        self.peers = {}  # PID -> observed start identity; protected against reuse.
        self.peer_lock = threading.Lock()
        self.thermal_checked=-float('inf');self.thermal_warning=None

    def cpu_ticks(self):
        if sys.platform == 'win32':
            import psutil
            ticks = psutil.cpu_times()
            return (int(ticks.user*100), int(ticks.system*100), int(ticks.idle*100), 0), 2
        if sys.platform == 'darwin':
            lib = ctypes.CDLL('/usr/lib/libSystem.B.dylib')
            lib.mach_host_self.restype = ctypes.c_uint
            lib.host_statistics.argtypes = [ctypes.c_uint, ctypes.c_int,
                ctypes.POINTER(ctypes.c_uint), ctypes.POINTER(ctypes.c_uint)]
            ticks = (ctypes.c_uint * 4)(); count = ctypes.c_uint(4)
            port = lib.mach_host_self()
            try:
                if lib.host_statistics(port, 3, ticks, ctypes.byref(count)) != 0:
                    raise OSError('host_statistics failed')
            finally:
                task = ctypes.c_uint.in_dll(lib, 'mach_task_self_').value
                lib.mach_port_deallocate(task, port)
            return tuple(ticks), 2
        if sys.platform.startswith('linux'):
            values = tuple(map(int, Path('/proc/stat').read_text().splitlines()[0].split()[1:9]))
            return (sum(values)-values[3]-values[4], 0, values[3]+values[4], 0), 2
        raise OSError('Host resource sampling unsupported on this OS')

    def processes(self):
        rows = {}
        if sys.platform == 'win32':
            import psutil
            for process in psutil.process_iter(['pid','ppid','memory_info','create_time']):
                try:
                    i=process.info
                    rows[i['pid']]=dict(parent=i['ppid'], rss_mib=i['memory_info'].rss/MIB,
                        cpu_percent=0, identity=str(i['create_time']))
                except (psutil.Error, TypeError, AttributeError): continue
            return rows
        for line in command(['ps', '-axo', 'pid=,ppid=,rss=,pcpu=,lstart=']).splitlines():
            parts = line.split()
            if len(parts) != 9:
                continue
            pid, parent, rss = map(int, parts[:3])
            rows[pid] = dict(parent=parent, rss_mib=rss/1024, cpu_percent=float(parts[3]), identity=' '.join(parts[4:]))
        return rows

    def register_peer(self, pid):
        rows = self.processes()
        if pid not in rows: raise ValueError('Peer is not running')
        ancestor = pid; seen = set()
        while ancestor in rows and ancestor not in seen and ancestor != self.root_pid:
            seen.add(ancestor); ancestor = rows[ancestor]['parent']
        if ancestor != self.root_pid: raise ValueError('Peer is not owned by this miner')
        with self.peer_lock: self.peers[pid] = rows[pid]['identity']

    def sample(self):
        ticks, idle_index = self.cpu_ticks()
        cpu = None
        if self.previous is not None:
            delta = [a-b for a,b in zip(ticks,self.previous)]
            if sys.platform == 'darwin': delta = [d % (1 << 32) for d in delta]
            if min(delta) >= 0 and 0 < sum(delta) < (1 << 31):
                cpu = 100*(1-delta[idle_index]/sum(delta))
        self.previous = ticks
        if sys.platform == 'darwin':
            pressure = int(command(['sysctl', '-n', 'kern.memorystatus_vm_pressure_level']).strip())
            swap = float(re.search(r'used = ([\d.]+)M', command(['sysctl', '-n', 'vm.swapusage'])).group(1))
            vm = command(['vm_stat']); page = int(re.search(r'page size of (\d+)', vm).group(1))
            compressed = re.search(r'Pages occupied by compressor:\s+(\d+)', vm)
            compressed_mib = int(compressed.group(1))*page/MIB if compressed else None
            total = int(command(['sysctl', '-n', 'hw.memsize']))
            if time.monotonic()-self.thermal_checked>30:
                self.thermal_checked=time.monotonic()
                try:
                    thermal=command(['pmset','-g','therm'])
                    limits=re.findall(r'(?:CPU_Speed_Limit|CPU_Scheduler_Limit)\s*=\s*(\d+)',thermal)
                    levels=re.findall(r'Thermal_Level\s*=\s*(\d+)',thermal)
                    self.thermal_warning=(any(int(x)<100 for x in limits) or any(int(x)>0 for x in levels)) if limits or levels else None
                except (OSError,subprocess.SubprocessError):self.thermal_warning=None
        elif sys.platform == 'win32':
            import psutil
            memory=psutil.virtual_memory(); total=memory.total
            swap=psutil.swap_memory().used/MIB
            pressure=1 if memory.available>total*.1 else 2
            compressed_mib=None
        else:
            info = {k:int(v.split()[0])*1024 for k,v in (line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())}
            total=info['MemTotal']; swap=(info['SwapTotal']-info['SwapFree'])/MIB
            pressure=1 if info.get('MemAvailable',0)>total*.1 else 2
            compressed_mib=None
        rows=self.processes()
        if self.root_pid not in rows: raise OSError('Owned root disappeared')
        identity=rows[self.root_pid]['identity']
        if self.root_identity is not None and identity!=self.root_identity: raise OSError('Root PID reused')
        self.root_identity=identity
        owned={self.root_pid}
        while True:
            expanded=owned | {pid for pid,row in rows.items() if row['parent'] in owned}
            if expanded==owned: break
            owned=expanded
        with self.peer_lock:
            peer_roots={pid for pid,ident in self.peers.items() if pid in owned and rows[pid]['identity']==ident}
        peer_pids=set(peer_roots)
        while True:
            expanded=peer_pids | {pid for pid in owned if rows[pid]['parent'] in peer_pids}
            if expanded==peer_pids:break
            peer_pids=expanded
        return dict(schema='miner-host-sample/v1', source='local-os', scope='host-and-owned-descendants',
            observed_at=time.time(), monotonic=time.monotonic(), host_cpu_percent=cpu,
            cpu_cores=os.cpu_count() or 1, load_average=list(os.getloadavg()) if hasattr(os, 'getloadavg') else None, memory_total_mib=total/MIB,
            pressure=pressure, swap_mib=swap, compressed_mib=compressed_mib,
            owned_rss_mib=sum(rows[p]['rss_mib'] for p in owned), peer_rss_mib=sum(rows[p]['rss_mib'] for p in peer_pids),
            owned_processes=len(owned), process_rss_mib={str(p):rows[p]['rss_mib'] for p in owned},
            owned_cpu_percent_lifetime=sum(rows[p]['cpu_percent'] for p in owned)/(os.cpu_count() or 1),
            process_cpu_scope='ps lifetime percentage normalized by host cores; not controller input',
            thermal_state='warning' if self.thermal_warning is True else 'normal' if self.thermal_warning is False else 'unavailable')


class History:
    def __init__(self, path, max_bytes=5*MIB, backups=3):
        self.path=Path(path); self.max_bytes=max_bytes; self.backups=backups
        self.errors=0; self.written=0

    def append(self, value):
        raw=json.dumps(value,allow_nan=False,separators=(',',':'))+'\n'
        if len(raw.encode())>65536: self.errors+=1; return
        try:
            self.path.parent.mkdir(parents=True,exist_ok=True)
            if self.path.exists() and self.path.stat().st_size+len(raw.encode())>self.max_bytes:
                for n in range(self.backups,0,-1):
                    src=self.path if n==1 else Path(str(self.path)+'.'+str(n-1))
                    dst=Path(str(self.path)+'.'+str(n))
                    if src.exists():os.replace(src,dst)
            with self.path.open('a') as handle:handle.write(raw)
            self.written+=1
        except OSError:self.errors+=1


class Governor:
    """Pure decisions; hard stops latch, and no remote metric enters this class."""
    def __init__(self, policy, now=None):
        self.policy=policy; self.workers=policy.minimum; self.duty=100
        self.halt=False; self.reason='warming up local measurements'; self.available=False
        self.baseline_swap=None; self.last_change=time.monotonic() if now is None else now
        self.cpu=deque(maxlen=5); self.rate_window=deque(maxlen=32)
        self.last_valid=None; self.probe=None; self.ceiling=policy.maximum

    def update(self, sample, hashes, now):
        if self.halt:return
        p=self.policy
        if self.last_valid is not None and now-self.last_valid>max(10,3*p.sample_seconds):
            self.rate_window.clear();self.cpu.clear();self.probe=None;self.last_change=now
        required=('pressure','swap_mib','owned_rss_mib','peer_rss_mib')
        if not sample or any(type(sample.get(k)) not in (int,float) or not math.isfinite(sample[k]) for k in required):
            self.available=False;self.reason='local safety measurements unavailable';return
        if self.baseline_swap is None:self.baseline_swap=sample['swap_mib']
        sample['swap_growth_mib']=max(0,sample['swap_mib']-self.baseline_swap)
        reason=('thermal warning' if sample.get('thermal_state')=='warning' else
                'memory pressure' if sample['pressure']>1 else
                'owned RAM ceiling' if sample['owned_rss_mib']>p.rss_mib else
                'peer RAM ceiling' if sample['peer_rss_mib']>p.peer_rss_mib else
                'swap growth' if sample['swap_growth_mib']>p.swap_growth_mib else '')
        if reason:self.halt=True;self.available=False;self.reason=reason;return
        cpu=sample.get('host_cpu_percent')
        if type(cpu) not in (float,int) or not math.isfinite(cpu) or not 0<=cpu<=100:
            self.available=False;self.reason='waiting for valid CPU interval';return
        self.available=True;self.last_valid=now;self.cpu.append(cpu)
        self.rate_window.append((now,hashes));average=sum(self.cpu)/len(self.cpu)
        if cpu>p.backoff:
            self.duty=max(10,self.duty-15)
            if average>p.backoff and now-self.last_change>=p.settle_seconds:
                self.workers=max(1,self.workers-1);self.last_change=now
            if self.workers==1 and self.duty==10:
                self.available=False;self.reason='CPU budget exhausted; mining paused';return
            self.reason='CPU above backoff; reducing mining';return
        if average>p.target+2:
            self.duty=max(10,self.duty-5);self.reason='CPU above target; reducing duty';return
        if now-self.last_change<p.settle_seconds:
            self.reason='settling after worker change';return
        rate=0
        if len(self.rate_window)>1:
            a,b=self.rate_window[0],self.rate_window[-1];rate=max(0,b[1]-a[1])/max(.001,b[0]-a[0])
        if self.probe and now-self.last_change>=p.increase_seconds:
            old_workers,old_rate=self.probe;self.probe=None
            if old_rate>0 and rate<old_rate*1.02:
                self.ceiling=max(p.minimum,self.workers-1);self.workers=old_workers
                self.last_change=now;self.rate_window.clear();self.reason='worker increase did not improve committed throughput';return
        if average<p.target-5:
            if self.duty<100:
                self.duty=min(100,self.duty+5);self.reason='CPU headroom; restoring duty';return
            if now-self.last_change>=p.increase_seconds and self.workers<self.ceiling:
                self.probe=(self.workers,rate);self.workers+=1;self.last_change=now
                self.rate_window.clear();self.reason='CPU headroom; adding one worker';return
        self.reason='within resource budget'


class ResourceController:
    def __init__(self, config, logs, stop, hashes):
        self.policy=Policy.from_config(config);self.enabled=self.policy.enabled
        self.stop=stop;self.hashes=hashes;self.session=uuid.uuid4().hex
        self.sampler=HostSampler();self.governor=Governor(self.policy)
        self.folder=Path(logs);self.control_path=self.folder/'resource-control.json'
        self.history=History(self.folder/'resources.jsonl');self.samples=deque(maxlen=128)
        self.lock=threading.RLock();self.closed=threading.Event();self.thread=None;self.watchdog=None
        self.last_tick=time.monotonic();self.last_sample=None
        self.external=config.get('resource_external_workers',0)
        self.local_capacity=(min(config['workers'],self.policy.maximum-self.external)
                             if self.external else self.policy.maximum) if self.enabled else config['workers']
        if self.local_capacity<1:raise ValueError('Resource budget needs at least one local worker')
        self.peer_slots={};self.errors=0;self.peak_rss=0

    @property
    def capacity(self):return self.local_capacity

    def register_peer(self, name, pid, slot):
        if not self.enabled or not self.local_capacity<=slot<self.policy.maximum:raise ValueError('Invalid peer resource slot')
        self.sampler.register_peer(pid)
        with self.lock:
            if slot in self.peer_slots.values():raise ValueError('Resource slot already assigned')
            self.peer_slots[name]=slot

    def set_worker_ceiling(self, count):
        if not self.enabled:raise ValueError('Automatic resource control is disabled')
        if type(count) is not int or not 1<=count<=self.policy.maximum:raise ValueError('Worker ceiling exceeds configured resource budget')
        with self.lock:
            self.governor.ceiling=count
            self.governor.workers=min(self.governor.workers,count)
            self.governor.probe=None
            self.governor.last_change=time.monotonic()
            self.governor.reason='User changed session worker ceiling'
        return self.snapshot()

    def admission(self, slot):
        if not self.enabled:return True,100
        with self.lock:
            g=self.governor
            live=not self.stop.is_set() and not self.closed.is_set() and not g.halt and g.available and time.monotonic()-self.last_tick<10
            return live and slot<g.workers,g.duty

    def local_workers(self):
        if not self.enabled:return self.local_capacity
        return sum(self.admission(i)[0] for i in range(self.local_capacity))

    def snapshot(self):
        if not self.enabled:return {'enabled':False,'state':'disabled'}
        with self.lock:
            g=self.governor
            return dict(enabled=True,schema='miner-resource-control/v1',session=self.session,
                state='stopped' if self.stop.is_set() or self.closed.is_set() else 'halted' if g.halt else 'active' if g.available else 'waiting',
                active_workers=g.workers if g.available and not self.stop.is_set() and not self.closed.is_set() and not g.halt else 0,
                local_capacity=self.local_capacity,maximum_workers=self.policy.maximum,duty_percent=g.duty,
                cpu_target=self.policy.target,cpu_backoff=self.policy.backoff,rss_limit_mib=self.policy.rss_mib,
                peer_rss_limit_mib=self.policy.peer_rss_mib,swap_growth_limit_mib=self.policy.swap_growth_mib,
                last_reason=g.reason,sample=self.last_sample,peak_rss_mib=self.peak_rss,
                errors=self.errors,history_errors=self.history.errors,history_samples=self.history.written,
                guard_scope='sampled local guards, not OS hard quotas')

    def publish(self):
        row=self.snapshot()
        atomic_json(self.folder/'resources-status.json',row)
        with self.lock:
            slots={name:dict(active=self.admission(slot)[0],duty=self.governor.duty) for name,slot in self.peer_slots.items()}
        atomic_json(self.control_path,dict(schema=1,session=self.session,updated_at=time.time(),
            halt=self.stop.is_set() or self.closed.is_set() or self.governor.halt,slots=slots))
        self.history.append(row)

    def start(self):
        if not self.enabled or self.thread:return
        self.publish()
        self.thread=threading.Thread(target=self.run,daemon=True,name='resource-sampler')
        self.watchdog=threading.Thread(target=self.watch,daemon=True,name='resource-watchdog')
        self.thread.start();self.watchdog.start()

    def watch(self):
        while not self.closed.wait(1) and not self.stop.is_set():
            if time.monotonic()-self.last_tick>12:
                with self.lock:self.governor.halt=True;self.governor.reason='local resource sampler stalled'
                self.stop.set();break

    def run(self):
        try:
            while not self.stop.is_set() and not self.closed.is_set():
                try:sample=self.sampler.sample()
                except (OSError,ValueError,AttributeError,subprocess.SubprocessError):sample=None;self.errors+=1
                now=time.monotonic()
                with self.lock:
                    self.governor.update(sample,self.hashes(),now);self.last_tick=now
                    self.last_sample=sample
                    if sample:
                        self.peak_rss=max(self.peak_rss,sample['owned_rss_mib']);self.samples.append(sample)
                    if self.governor.halt:self.stop.set()
                self.publish()
                if self.closed.wait(self.policy.sample_seconds):break
        except Exception:
            with self.lock:self.errors+=1;self.governor.halt=True;self.governor.reason='resource monitor failed'
            self.stop.set()
        finally:
            try:self.publish()
            except OSError:pass

    def close(self):
        self.closed.set()
        for thread in (self.thread,self.watchdog):
            if thread and thread is not threading.current_thread():thread.join(10)
        if self.enabled:
            try:self.publish()
            except OSError:self.errors+=1


class PeerGate:
    """A missing/stale local control record denies work; never restarts a process."""
    def __init__(self,path,session,node):
        self.path=Path(path);self.session=session;self.node=node

    def __call__(self):
        try:
            with self.path.open('rb') as handle:raw=handle.read(65537)
            if len(raw)>65536:raise ValueError('Oversize control')
            row=json.loads(raw)
            age=time.time()-row['updated_at']
            if row.get('schema')!=1 or row.get('session')!=self.session or row.get('halt') or not 0<=age<=8:return False,10
            slot=row.get('slots',{}).get(self.node,{})
            duty=slot.get('duty')
            if type(duty) is not int or not 1<=duty<=100:return False,10
            return slot.get('active') is True,duty
        except (OSError,ValueError,KeyError,TypeError):return False,10
