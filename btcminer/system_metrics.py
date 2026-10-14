"""OS-sampled provider metrics adapter; install only at the actual service host.

The service is not started by importing this module. Its default listener is
loopback. Integrate behind the provider's authentication/reverse proxy or use
the required dedicated token. A relay's measurements are not backend metrics.
"""
import argparse
import asyncio
import hashlib
import hmac
import os
from pathlib import Path
import sys
import time
import uuid

from .resources import HostSampler, command, MIB


class Collector:
    def __init__(self, sampler=None):
        self.sampler=sampler or HostSampler();self.instance=uuid.uuid4().hex
        self.sequence=0;self.previous_time=None;self.latest=None

    def sample(self):
        row=self.sampler.sample();now=time.monotonic();self.sequence+=1
        used=available=None;uptime=None
        if sys.platform.startswith('linux'):
            info={k:int(v.split()[0])*1024 for k,v in (line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())}
            available=info.get('MemAvailable');used=info['MemTotal']-available if available is not None else None
            uptime=float(Path('/proc/uptime').read_text().split()[0])
        elif sys.platform=='darwin':
            import re
            vm=command(['vm_stat']);page=int(re.search(r'page size of (\d+)',vm).group(1))
            # Only report the explicit free page count, not a guessed reclaimable total.
            free=re.search(r'Pages free:\s+(\d+)',vm)
            used=int(row['memory_total_mib']*MIB)-int(free.group(1))*page if free else None
        self.latest=dict(schema='provider-system-metrics/v1',measurement='os-sampled',scope='host',
            instance_id=self.instance,sample_id=f'{self.instance}:{self.sequence}',sampled_at=time.time(),
            cpu=dict(percent=row['host_cpu_percent'],cores=row['cpu_cores'],
                window_seconds=None if self.previous_time is None else now-self.previous_time,
                denominator='all host logical CPUs; container quotas are not inferred'),
            memory=dict(total_bytes=int(row['memory_total_mib']*MIB),used_bytes=used,
                available_bytes=available,swap_used_bytes=int(row['swap_mib']*MIB),
                accounting='Linux MemAvailable; macOS used excludes only free pages, available unknown'),
            process=dict(rss_bytes=int(row['owned_rss_mib']*MIB),scope='metrics-service process tree'),
            load_average=row['load_average'],uptime_seconds=uptime,
            active_requests=None,queue_depth=None,
            limitations=['Request/queue instrumentation must come from the calculator application',
                        'Host counters do not establish container CPU quotas',
                        'The installer must bind this instance to the true calculator host'])
        self.previous_time=now;return self.latest


def create_app(token,collector=None):
    from aiohttp import web, WSMsgType
    if not isinstance(token,str) or len(token)<32:raise ValueError('A dedicated metrics token of at least 32 characters is required')
    collector=collector or Collector()
    async def authorize(request):
        supplied=request.headers.get('Authorization','')
        if not hmac.compare_digest(supplied,'Bearer '+token):raise web.HTTPUnauthorized()
    async def snapshot(request):
        await authorize(request)
        if collector.latest is None:raise web.HTTPServiceUnavailable()
        return web.json_response({'ok':True,'metrics':collector.latest})
    async def stream(request):
        await authorize(request)
        ws=web.WebSocketResponse(heartbeat=15,max_msg_size=1024)
        await ws.prepare(request)
        try:
            while not ws.closed:
                if collector.latest is not None:
                    await ws.send_json({'type':'systemTelemetry','metrics':collector.latest})
                try:
                    message=await asyncio.wait_for(ws.receive(),2)
                    if message.type in (WSMsgType.CLOSE,WSMsgType.CLOSED,WSMsgType.ERROR):break
                except asyncio.TimeoutError:pass
        finally:await ws.close()
        return ws
    async def lifecycle(app):
        async def run():
            while True:
                try:await asyncio.to_thread(collector.sample)
                except (OSError,ValueError):collector.latest=None
                await asyncio.sleep(2)
        task=asyncio.create_task(run())
        yield
        task.cancel();await asyncio.gather(task,return_exceptions=True)
    app=web.Application(client_max_size=1024)
    app.router.add_get('/api/system/metrics',snapshot)
    app.router.add_get('/ws/system-metrics',stream)
    app.cleanup_ctx.append(lifecycle)
    return app


def main():
    from aiohttp import web
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--host',default='127.0.0.1');p.add_argument('--port',type=int,default=60112)
    args=p.parse_args();token=os.environ.get('BTC_METRICS_TOKEN','')
    # No token in argv, URL or access logs. Binding outside loopback is explicit.
    web.run_app(create_app(token),host=args.host,port=args.port,access_log=None)


if __name__=='__main__':main()
