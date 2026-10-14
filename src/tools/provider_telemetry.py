"""Typed, bounded provider observations. Calculation costs are not host load."""
from collections import deque
from datetime import datetime
import hashlib
import math
import time


def number(value, minimum=0, maximum=1e18):
    return value if type(value) in (int,float) and math.isfinite(value) and minimum<=value<=maximum else None


def calculation(value, *, source, generation=0, ordinal=0, now=None):
    if not isinstance(value,dict):raise ValueError('Calculation telemetry must be an object')
    now=time.time() if now is None else now
    cost=value.get('cost',{});metrics=value.get('metrics',{});progress=value.get('progress',{})
    if not all(isinstance(x,dict) for x in (cost,metrics,progress)):raise ValueError('Invalid telemetry fields')
    identity=value.get('requestId','')
    # WS request IDs can contain the authentication token: never retain raw IDs.
    identity=hashlib.sha256(str(identity).encode()).hexdigest()
    stamp=value.get('timestamp')
    if stamp is not None:
        if not isinstance(stamp,str) or len(stamp)>64:raise ValueError('Invalid server timestamp')
        try:datetime.fromisoformat(stamp.replace('Z','+00:00'))
        except ValueError:raise ValueError('Invalid server timestamp') from None
    return dict(schema='provider-calculation-observation/v1',source=source,scope='calculation',
        measurement_semantics='provider-reported cost; instrumentation unverified',
        observed_at=now,server_timestamp=stamp,connection_generation=generation,observation=ordinal,
        request_fingerprint=identity,sequence=number(value.get('sequence'),0,2**53),
        phase=value.get('phase') if value.get('phase') in ('parse','analyze','synthesize','evaluate') else 'unknown',
        cpu_ms=number(cost.get('cpuMs')),cpu_share=number(cost.get('cpuShare'),0,1),samples=number(cost.get('samples')),
        progress_percent=number(progress.get('percent'),0,100),
        metrics={k:number(metrics.get(k)) for k in ('tokenCount','operatorCount','maxDepth','complexityScore','nodeCount','edgeCount','faceCount','timeIndex')})


def server_metrics(value, now=None):
    """Contract-v1 whitelist. No inference from calculationTelemetry or latency."""
    now=time.time() if now is None else now
    if not isinstance(value,dict) or value.get('schema')!='provider-system-metrics/v1':raise ValueError('Unsupported server metrics schema')
    if value.get('scope') not in ('host','container','process'):raise ValueError('Server metrics require explicit scope')
    if value.get('measurement')!='os-sampled':raise ValueError('Server metrics must identify OS sampling')
    identifier=value.get('sample_id');host=value.get('instance_id')
    if not all(isinstance(x,str) and 0<len(x)<=128 for x in (identifier,host)):raise ValueError('Server sample/instance identity required')
    stamp=number(value.get('sampled_at'),0,1e12)
    if stamp is None:raise ValueError('Server sample time required')
    cpu=value.get('cpu',{});memory=value.get('memory',{});process=value.get('process',{})
    if not all(isinstance(x,dict) for x in (cpu,memory,process)):raise ValueError('Invalid server metrics objects')
    return dict(schema=value['schema'],source='provider-system-metrics',scope=value['scope'],measurement='os-sampled',
        instance_id=hashlib.sha256(host.encode()).hexdigest(),sample_id=hashlib.sha256(identifier.encode()).hexdigest(),sampled_at=stamp,observed_at=now,
        cpu_percent=number(cpu.get('percent'),0,100),cpu_cores=number(cpu.get('cores'),1,65536),
        cpu_window_seconds=number(cpu.get('window_seconds'),.001,3600),
        memory_used_bytes=number(memory.get('used_bytes')),memory_total_bytes=number(memory.get('total_bytes')),
        memory_available_bytes=number(memory.get('available_bytes')),swap_used_bytes=number(memory.get('swap_used_bytes')),
        process_rss_bytes=number(process.get('rss_bytes')),uptime_seconds=number(value.get('uptime_seconds')),
        load_average=[number(x) for x in value.get('load_average',[])[:3]] if isinstance(value.get('load_average'),list) else [],
        active_requests=number(value.get('active_requests')),queue_depth=number(value.get('queue_depth')),
        provenance='authenticated provider report; not independently attested host identity')


class TelemetryState:
    def __init__(self):
        self.latest={};self.server=None;self.generation=0;self.ordinal=0
        self.seen=deque(maxlen=128);self.errors=0;self.duplicates=0;self.out_of_order=0
        self.last_sequence={};self.latencies=deque(maxlen=128);self.reconnects=0

    def connected(self):
        self.generation+=1;self.last_sequence.clear();self.reconnects=max(0,self.generation-1)

    def observe_calculation(self,value,source,now=None):
        self.ordinal+=1
        row=calculation(value,source=source,generation=self.generation,ordinal=self.ordinal,now=now)
        # REST IDs repeat across calls. Only de-duplicate within a WS connection.
        key=(self.generation,row['request_fingerprint'],row['sequence'],row['server_timestamp'])
        if source=='websocket':
            if key in self.seen:self.duplicates+=1;return None
            self.seen.append(key)
            prior=self.last_sequence.get(row['request_fingerprint'])
            seq=row['sequence']
            if prior is not None and seq is not None and seq<prior:self.out_of_order+=1;return None
            if seq is not None:
                if len(self.last_sequence)>=128:self.last_sequence.pop(next(iter(self.last_sequence)))
                self.last_sequence[row['request_fingerprint']]=seq
        self.latest[source]=row;return row

    def observe_server(self,value,now=None):
        row=server_metrics(value,now)
        if self.server and row['instance_id']==self.server['instance_id']:
            if row['sample_id']==self.server['sample_id']:self.duplicates+=1;return None
            if row['sampled_at']<self.server['sampled_at']:self.out_of_order+=1;return None
        self.server=row;return row

    def snapshot(self,now=None):
        now=time.time() if now is None else now
        def fresh(row):
            age=max(0,now-row['observed_at']);availability='current' if age<=30 else 'stale'
            remote=row.get('sampled_at')
            if remote is not None and availability=='current':
                if now-remote>30:availability='stale'
                elif remote-now>30:availability='clock-uncertain'
            return dict(row,age_seconds=age,availability=availability)
        return dict(calculations={k:fresh(v) for k,v in self.latest.items()},
            server=fresh(self.server) if self.server else dict(availability='unavailable',scope='server resources'),
            errors=self.errors,duplicates=self.duplicates,out_of_order=self.out_of_order,reconnects=self.reconnects,
            latency_seconds=list(self.latencies),observation_count=self.ordinal)
