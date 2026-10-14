"""Session-owned provider process: live discovery, model stream and job math checks.

The engine hands off fixed-size scalar descriptors; it never waits for the API.
This process cannot alter nonce coverage, proof admission or block submission.
Remote arithmetic is compared with exact local arithmetic for each sampled job.
"""
import argparse
import asyncio
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time
import uuid
from fractions import Fraction

from . import ROOT
from .provider import ProviderClient, ProviderError, save_snapshot, evaluation_number, keychain, PASSWORD_SERVICE
from .provider_telemetry import TelemetryState, calculation
from .resources import History


def read_json(path, limit=65536):
    with Path(path).open('rb') as handle:
        raw = handle.read(limit + 1)
    if len(raw) > limit:
        raise ValueError('Provider runtime record exceeds limit')
    value = json.loads(raw)
    if not isinstance(value, dict):
        raise ValueError('Provider runtime record must be an object')
    return value


def job_descriptor(work, plan, session):
    trace = plan.scale_trace
    inputs = trace['inputs']
    return {'schema': 1, 'session': session, 'job_id': hashlib.sha256(work.header[:76]).hexdigest(),
            'created_at': time.time(), 'height': work.height, 'order': plan.order,
            'cell': inputs['cell'], 'phase': inputs['phase'], 'label': inputs['label'],
            'offset': trace['offset'], 'first_tile': plan.first_tile}


def check_job(client, job):
    """Check actual traversal scalars, with no executable provider formula text."""
    for key, bound in [('cell', 400), ('phase', 144000), ('label', 360),
                       ('offset', 144000), ('first_tile', 29827)]:
        if type(job.get(key)) is not int or not 0 <= job[key] < bound:
            raise ValueError('Invalid traversal descriptor: ' + key)
    unwrapped = 360 * job['cell'] + job['phase'] + job['label']
    expected = unwrapped % 144000
    if job['offset'] != expected:
        raise ValueError('Local traversal descriptor mismatch')
    expression = f'{unwrapped}-144000*floor({unwrapped}/144000)'
    result = client.calculate(expression)
    evaluation = result['evaluation']
    actual = evaluation_number(evaluation)
    matched = actual == expected
    telemetry = result.get('telemetry', {})
    return {'job_id': job['job_id'], 'height': job['height'], 'expression': expression,
            'expected': expected, 'actual': str(actual), 'matched': matched,
            'sampled_offset_only': True,
            'calculation': calculation(telemetry,source='rest'),
            'model_fingerprint': result.get('modelPreview', {}).get('frameFingerprint'),
            'checked_at': time.time()}


class ProviderRuntime:
    def __init__(self, config, logs):
        self.enabled = config.get('provider_enabled', False)
        self.user = config.get('provider_user', '')
        self.base_url = config.get('provider_url', '')
        self.metrics_path = config.get('provider_metrics_path','')
        self.metrics_ws_path = config.get('provider_metrics_ws_path','')
        self.folder = Path(logs) / 'provider-runtime'
        self.session = uuid.uuid4().hex
        self.process = None
        self.current_job = None
        self.error = ''
        self.cached, self.last_read = {}, -float("inf")

    def start(self):
        if not self.enabled or self.process is not None:
            return
        try:
            self.folder.mkdir(parents=True, exist_ok=True)
            environment = dict(os.environ)
            if not environment.get('BTC_PROVIDER_URL') and self.base_url:
                environment['BTC_PROVIDER_URL'] = self.base_url
            self.process = subprocess.Popen([sys.executable, '-B', '-m', 'btcminer.provider_runtime',
                '--folder', str(self.folder), '--session', self.session, '--user', self.user,
                '--parent', str(os.getpid()), '--metrics-path', self.metrics_path,
                '--metrics-ws-path',self.metrics_ws_path], cwd=ROOT, stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, env=environment)
        except OSError as error:
            self.error = type(error).__name__

    def observe(self, work, plan):
        if not self.enabled or self.process is None:
            return
        try:
            row = job_descriptor(work, plan, self.session)
            if row['job_id'] != self.current_job:
                self.current_job = row['job_id']
                save_snapshot(self.folder / 'job.json', row)
        except (OSError, ValueError, KeyError) as error:
            self.error = type(error).__name__

    def snapshot(self):
        if not self.enabled:
            return {'enabled': False, 'state': 'disabled'}
        if time.monotonic() - self.last_read >= 1:
            self.last_read = time.monotonic()
            try:
                value = read_json(self.folder / 'status.json')
                self.cached = value if value.get('session') == self.session else {}
            except (OSError, ValueError):
                self.cached = {}
        result = dict(self.cached, enabled=True, current_job=self.current_job)
        alive = self.process is not None and self.process.poll() is None
        if not alive:
            result.update(state='stopped' if self.process else 'ready', stream='stopped')
        elif not self.cached:
            result['state'] = 'connecting'
        elif time.time() - self.cached.get('updated_at', 0) > 30:
            result.update(state='stale', stream='stale')
        check = result.get('last_check', {})
        result['math_check'] = ('pending' if not self.current_job or check.get('job_id') != self.current_job
                                else 'matched' if check.get('matched') else 'mismatch')
        if self.error:
            result['error'] = self.error
        return result

    def close(self):
        if self.process is not None and self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=2)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=2)


async def worker(folder, session, user, parent, metrics_path='',metrics_ws_path=''):
    folder = Path(folder)
    client = ProviderClient(user=user, timeout=3,limit=1024*1024)
    authenticated = asyncio.Event()
    state = {'schema': 1, 'session': session, 'state': 'connecting', 'stream': 'connecting',
             'checks_passed': 0, 'checks_failed': 0, 'events': 0, 'binary_events': 0,
             'wire_bytes': 0, 'decoded_bytes': 0, 'formula_count': 0}
    last_write = 0
    observations=TelemetryState()
    history=History(folder/'telemetry.jsonl')

    def publish(force=False):
        nonlocal last_write
        if not force and time.monotonic() - last_write < .5:
            return
        state['updated_at'] = time.time()
        state['telemetry']=observations.snapshot()
        state['telemetry_history_errors']=history.errors
        save_snapshot(folder / 'status.json', state)
        last_write = time.monotonic()

    def transport():
        for row in client.metrics:
            state['wire_bytes'] += row.get('wire_bytes', 0)
            state['decoded_bytes'] += row.get('decoded_bytes', row.get('wire_bytes', 0))
            observations.latencies.append(row.get('seconds',0))
        client.metrics.clear()

    async def rest():
        next_refresh, next_check, next_metrics, last_job = 0, 0, 0, None
        while os.getppid() == parent:
            try:
                if not authenticated.is_set():
                    # Own the socket lifetime: closing this runtime must not
                    # invalidate another consumer of a saved shared-session token.
                    supplied=os.environ.get('BTC_PROVIDER_SESSION')
                    if supplied:
                        client.token=supplied
                        await asyncio.to_thread(client.authenticate)
                        state['dedicated_session']=False
                        state['session_source']='caller-supplied token; use a dedicated session'
                    else:
                        password=os.environ.get('BTC_PROVIDER_PASSWORD')
                        if not password:password=await asyncio.to_thread(keychain,user,PASSWORD_SERVICE+':'+hashlib.sha256(client.base_url.encode()).hexdigest()[:16])
                        try:
                            await asyncio.to_thread(client.login, password)
                        finally:
                            del password
                        state['dedicated_session']=True
                    authenticated.set()
                if time.monotonic() >= next_refresh:
                    discovery = await asyncio.to_thread(client.discover)
                    save_snapshot(folder / 'catalogue.json', discovery)
                    state.update(state='online', formula_count=discovery['formula_count'],
                                 catalogue_at=discovery['observed_at'], error='')
                    next_refresh = time.monotonic() + 300
                if time.monotonic() >= next_check:
                    try:
                        job = read_json(folder / 'job.json')
                    except FileNotFoundError:
                        job = {}
                    if job.get('session') == session and job.get('job_id') != last_job:
                        check = await asyncio.to_thread(check_job, client, job)
                        state['last_check'] = check
                        observations.ordinal+=1
                        row=dict(check['calculation'],observation=observations.ordinal)
                        observations.latest['rest']=row
                        history.append(row)
                        state['checks_passed' if check['matched'] else 'checks_failed'] += 1
                        state['state'] = 'online' if check['matched'] else 'math mismatch'
                        last_job = job['job_id']
                    next_check = time.monotonic() + 10
                if metrics_path and time.monotonic()>=next_metrics:
                    next_metrics=time.monotonic()+10
                    try:
                        result=await asyncio.to_thread(client.json,'GET',metrics_path)
                        row=observations.observe_server(result.get('metrics',result))
                        if row:history.append(row)
                        state.pop('server_metrics_error',None)
                    except (ProviderError,ValueError) as error:
                        observations.errors+=1
                        state['server_metrics_error']=type(error).__name__
                transport()
                publish()
                await asyncio.sleep(1)
            except Exception as error:
                transport()
                state.update(state='offline', error=type(error).__name__)
                if isinstance(error, ProviderError) and error.status == 401:
                    client.token = None
                    authenticated.clear()
                publish(True)
                await asyncio.sleep(10)

    async def stream():
        while os.getppid() == parent:
            await authenticated.wait()
            try:
                state['stream'] = 'connecting'
                observations.connected()
                async for event in client.updates(seconds=60, max_events=1000,persistent=True):
                    state['events'] += 1
                    state['binary_events'] += event['encoding'] == 'tcmp'
                    state['wire_bytes'] += event['wire_bytes']
                    state['decoded_bytes'] += event['decoded_bytes']
                    state['stream'] = 'connected'
                    state['last_event_at'] = time.time()
                    state['last_event_type'] = event['message']['type'][:80]
                    try:
                        body=event['message'];row=None
                        if body['type']=='calculationTelemetry':
                            row=observations.observe_calculation(body.get('telemetry'),source='websocket')
                        elif body['type']=='systemTelemetry':
                            row=observations.observe_server(body.get('metrics'))
                        if row:history.append(row)
                    except (ValueError,TypeError):observations.errors+=1
                    publish()
                state['stream'] = 'reconnecting'
            except Exception as error:
                state.update(stream='offline', stream_error=type(error).__name__)
                publish(True)
                await asyncio.sleep(10)

    async def system_stream():
        import aiohttp
        while os.getppid()==parent:
            await authenticated.wait()
            try:
                async def refuse_redirect(*args):raise ProviderError('Metrics redirect refused')
                trace=aiohttp.TraceConfig();trace.on_request_redirect.append(refuse_redirect)
                async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=None,connect=5),trace_configs=[trace]) as http:
                    url=client.base_url.replace('http','ws',1)+metrics_ws_path
                    async with http.ws_connect(url,headers={'Authorization':'Bearer '+client.token},max_msg_size=65536,heartbeat=10) as ws:
                        async for message in ws:
                            if message.type!=aiohttp.WSMsgType.TEXT:continue
                            body=json.loads(message.data)
                            if isinstance(body,dict) and body.get('type')=='systemTelemetry':
                                row=observations.observe_server(body.get('metrics'))
                                if row:history.append(row)
                                publish()
            except Exception as error:
                observations.errors+=1;state['server_metrics_stream_error']=type(error).__name__;publish(True)
                await asyncio.sleep(10)

    publish(True)
    tasks = [asyncio.create_task(rest()), asyncio.create_task(stream())]
    if metrics_ws_path:tasks.append(asyncio.create_task(system_stream()))
    try:
        while os.getppid() == parent:
            await asyncio.sleep(1)
            for task in tasks:
                if task.done():
                    task.result()
    finally:
        for task in tasks:
            task.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--folder', required=True)
    parser.add_argument('--session', required=True)
    parser.add_argument('--user', required=True)
    parser.add_argument('--parent', type=int, required=True)
    parser.add_argument('--metrics-path',default='')
    parser.add_argument('--metrics-ws-path',default='')
    args = parser.parse_args()
    asyncio.run(worker(args.folder, args.session, args.user, args.parent,args.metrics_path,args.metrics_ws_path))


if __name__ == '__main__':
    main()
