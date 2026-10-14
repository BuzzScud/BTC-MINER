"""Thesis API client for explicit tools and the session-owned provider process.

Discovery and wire measurements are observations, not mathematical admission.
No provider prose is executed, no requests/files are published, and no mining
settings, candidate order, native library or live process is changed here.
"""
import asyncio
from collections import Counter
import ctypes
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request

from . import ROOT
from . import tcmp

BASE_URL = os.environ.get('BTC_PROVIDER_URL', '')
SESSION_SERVICE = 'btc-research-calculator-rewrite-session'
PASSWORD_SERVICE = 'btc-research-calculator-provider'
LIMIT = 8 * 1024 * 1024
SENSITIVE = {'sessionid', 'password', 'token', 'apikey', 'authorization', 'email'}


def scrub(value, secrets=()):
    if isinstance(value, dict):
        return {scrub(str(k), secrets): '[redacted]' if str(k).lower() in SENSITIVE else scrub(v, secrets)
                for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return [scrub(v, secrets) for v in value]
    if isinstance(value, str):
        for secret in secrets:
            if secret:
                value = value.replace(secret, '[redacted]').replace(urllib.parse.quote(secret, safe=''), '[redacted]')
    return value


def keychain(user, service):
    """Read only the designated account/service; never invoke an interactive prompt."""
    if sys.platform != 'darwin':
        raise RuntimeError('Set BTC_PROVIDER_SESSION in the environment for this platform')
    sec = ctypes.CDLL('/System/Library/Frameworks/Security.framework/Security')
    sec.SecKeychainSetUserInteractionAllowed.argtypes = [ctypes.c_ubyte]
    sec.SecKeychainSetUserInteractionAllowed(False)
    sec.SecKeychainFindGenericPassword.argtypes = [ctypes.c_void_p, ctypes.c_uint32, ctypes.c_char_p,
        ctypes.c_uint32, ctypes.c_char_p, ctypes.POINTER(ctypes.c_uint32), ctypes.POINTER(ctypes.c_void_p), ctypes.c_void_p]
    sec.SecKeychainFindGenericPassword.restype = ctypes.c_int32
    sec.SecKeychainItemFreeContent.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
    length, value = ctypes.c_uint32(), ctypes.c_void_p()
    service_bytes, user_bytes = service.encode(), user.encode()
    code = sec.SecKeychainFindGenericPassword(None, len(service_bytes), service_bytes,
        len(user_bytes), user_bytes, ctypes.byref(length), ctypes.byref(value), None)
    try:
        if code:
            raise RuntimeError('Provider Keychain access failed (status %s); set BTC_PROVIDER_SESSION or use the saved account' % code)
        return ctypes.string_at(value, length.value).decode()
    finally:
        if value:
            sec.SecKeychainItemFreeContent(None, value)


class ProviderError(RuntimeError):
    def __init__(self, message, status=None):
        super().__init__(message)
        self.status = status


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *args, **kwargs):
        raise ProviderError('Provider redirect refused')


class ProviderClient:
    def __init__(self, base_url=None, token=None, user='', timeout=15, limit=LIMIT):
        base_url = BASE_URL if base_url is None else base_url
        parsed = urllib.parse.urlsplit(base_url)
        if (parsed.scheme not in ('http', 'https') or not parsed.hostname or parsed.username or parsed.password
                or parsed.query or parsed.fragment or parsed.path not in ('', '/')):
            raise ValueError('Set BTC_PROVIDER_URL to your provider HTTP(S) origin without credentials')
        if not 0 < timeout <= 60 or not 0 < limit <= LIMIT:
            raise ValueError('Invalid provider timeout or response limit')
        self.base_url, self.token, self.user = base_url.rstrip('/'), token, user
        self.timeout, self.limit = timeout, limit
        self.metrics = []
        self.opener = urllib.request.build_opener(NoRedirect)

    def authenticate(self):
        supplied = bool(self.token)
        environment_token = os.environ.get('BTC_PROVIDER_SESSION')
        if not self.token:
            if environment_token:
                self.token = environment_token
            elif self.base_url == BASE_URL:
                self.token = keychain(self.user, SESSION_SERVICE+':'+hashlib.sha256(self.base_url.encode()).hexdigest()[:16])
            else:
                raise ProviderError('Custom providers require BTC_PROVIDER_SESSION; saved credentials are bound to the default origin')
        try:
            self.formulas(limit=1)
        except ProviderError as error:
            if error.status != 401 or supplied or environment_token or self.base_url != BASE_URL:
                raise
            password = keychain(self.user, PASSWORD_SERVICE+':'+hashlib.sha256(self.base_url.encode()).hexdigest()[:16])
            result = self.json('POST', '/api/login', {'userName': self.user, 'password': password}, authenticated=False)
            if result.get('ok') is not True or not result.get('sessionId'):
                raise ProviderError('Provider login failed')
            self.token = result['sessionId']  # Retained only in memory.
            self.formulas(limit=1)

    def request(self, method, path, *, data=None, authenticated=True, headers=None):
        if not path.startswith('/') or path.startswith('//') or '#' in path:
            raise ValueError('Provider request requires an origin-relative path')
        head = {'Accept': 'application/json', **(headers or {})}
        if authenticated:
            if not self.token:
                raise ProviderError('Provider authentication required')
            head['Authorization'] = 'Bearer ' + self.token
        req = urllib.request.Request(self.base_url + path, data=data, headers=head, method=method)
        start = time.perf_counter()
        try:
            try:
                response = self.opener.open(req, timeout=self.timeout)
            except urllib.error.HTTPError as error:
                response = error
            with response:
                raw = response.read(self.limit + 1)
                status = response.code
                response_headers = {k.lower(): v for k, v in response.headers.items()}
            if len(raw) > self.limit:
                raise ProviderError('Provider response exceeds limit')
        except (OSError, ValueError) as error:
            raise ProviderError('Provider transport failed: ' + type(error).__name__) from None
        elapsed = time.perf_counter() - start
        if status != 200:
            raise ProviderError('Provider HTTP ' + str(status), status)
        self.metrics.append({'path': path, 'status': status, 'request_bytes': len(data or b''),
                             'wire_bytes': len(raw), 'seconds': elapsed})
        return response_headers, raw

    def json(self, method, path, payload=None, *, authenticated=True):
        raw = None if payload is None else json.dumps(payload, allow_nan=False, separators=(',', ':')).encode()
        headers = {'x-app-accept-encoding': 'tcmp'}
        if raw is not None:
            if len(raw) > 1024 * 1024:
                raise ValueError('Provider JSON request exceeds 1 MiB')
            headers['Content-Type'] = 'application/json'
            if len(raw) >= 256:
                encoded = tcmp.encode(raw)
                if len(encoded) < len(raw):
                    raw = encoded
                    headers['x-app-encoding'] = 'tcmp'
        response_headers, wire = self.request(method, path, data=raw, authenticated=authenticated, headers=headers)
        encoding = response_headers.get('x-app-encoding', '')
        if encoding not in ('', 'tcmp'):
            raise ProviderError('Unknown provider application encoding')
        decoded = tcmp.decode(wire, self.limit) if encoding == 'tcmp' else wire
        if encoding == 'tcmp':
            declared = response_headers.get('x-app-original-size')
            if declared is None or not declared.isdecimal() or int(declared) != len(decoded):
                raise ProviderError('Provider decoded length header mismatch')
        self.metrics[-1].update(encoding=encoding or 'json', decoded_bytes=len(decoded),
                                decoded_sha256=hashlib.sha256(decoded).hexdigest())
        try:
            result = json.loads(decoded)
        except (ValueError, UnicodeError):
            raise ProviderError('Provider returned invalid JSON') from None
        if not isinstance(result, dict) or result.get('ok') is False:
            raise ProviderError('Provider returned an unsuccessful or invalid response')
        return result

    def formulas(self, query=None, limit=200):
        if not 1 <= limit <= 200:
            raise ValueError('Formula limit must be 1–200')
        params = {'limit': limit}
        if query:
            params['q'] = query
        result = self.json('GET', '/api/formulas?' + urllib.parse.urlencode(params))
        if result.get('userName') != self.user or not isinstance(result.get('formulas'), list):
            raise ProviderError('Provider formula account or schema mismatch')
        return result

    def calculate(self, expression, variables=None):
        if not isinstance(expression, str) or not expression.strip():
            raise ValueError('An expression is required')
        if variables is not None and not isinstance(variables, dict):
            raise ValueError('Variables must be a JSON object')
        result = self.json('POST', '/api/calculate', {'expression': expression, 'variables': variables or {}})
        evaluation = result.get('evaluation', {})
        if not isinstance(evaluation, dict) or evaluation.get('ok') is not True:
            raise ProviderError('Provider could not evaluate this expression')
        return result

    def discover(self, query=None):
        endpoints = {'capabilities': '/api/calculate/capabilities', 'app_codec': '/api/app-codec',
                     'compression': '/api/compression/capabilities', 'openapi': '/api/docs/living_openapi.json',
                     'asyncapi': '/api/docs/living_asyncapi.json'}
        documents = {key: self.json('GET', path, authenticated=False) for key, path in endpoints.items()}
        if self.token:
            documents['catalogue'] = self.formulas(query)
        catalogue = documents.get('catalogue', {})
        return {'schema': 'btc-provider-discovery/v1', 'observed_at': datetime.now(timezone.utc).isoformat(),
                'base_url': self.base_url, 'account': self.user if self.token else None,
                'formula_count': len(catalogue.get('formulas', [])),
                'total_available': catalogue.get('totalAvailable'), 'filtered_count': catalogue.get('filteredCount'),
                'catalogue_complete': len(catalogue.get('formulas', [])) == catalogue.get('filteredCount'),
                'documents': scrub(documents, (self.token,)), 'transport': list(self.metrics),
                'proof_status': 'provider_observations_only', 'mining_process_changed': False}

    async def updates(self, seconds=10, max_events=200, persistent=False):
        """Bounded async stream; server bootstrap supplies sessionReady.

        No expression replay, clone/merge or formula writes. Reconnection is an
        explicit new observation so a broken session cannot silently look live.
        """
        if not 0 < seconds <= 60 or not 1 <= max_events <= 1000:
            raise ValueError('Watch requires 0 < seconds <= 60 and 1–1000 events')
        if not self.token:
            raise ProviderError('Provider authentication required')
        try:
            import aiohttp
        except ImportError:
            raise ProviderError('Provider watch requires the optional aiohttp package') from None
        async def refuse_redirect(*args):
            raise ProviderError('Provider WebSocket redirect refused')
        trace = aiohttp.TraceConfig()
        trace.on_request_redirect.append(refuse_redirect)
        url = self.base_url.replace('http', 'ws', 1) + '/ws?' + urllib.parse.urlencode(
            {'sessionId': self.token, 'userName': self.user, 'enc': 'tcmp'})
        deadline = time.monotonic() + seconds
        ready = False
        try:
            async with aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=min(self.timeout, seconds)), trace_configs=[trace]) as session:
                async with session.ws_connect(url, max_msg_size=self.limit, heartbeat=10) as ws:
                    count = 0
                    while persistent or count < max_events:
                        remaining = deadline - time.monotonic()
                        if remaining <= 0 and not persistent:
                            break
                        try:
                            message = await asyncio.wait_for(ws.receive(), 15 if persistent else remaining)
                        except asyncio.TimeoutError:
                            if persistent: continue
                            break
                        count += 1
                        if message.type == aiohttp.WSMsgType.TEXT:
                            raw = message.data.encode()
                            encoding = 'json'
                        elif message.type == aiohttp.WSMsgType.BINARY:
                            raw = tcmp.decode(message.data, self.limit)
                            encoding = 'tcmp'
                        else:
                            raise ProviderError('Provider WebSocket closed before observation completed')
                        body = json.loads(raw)
                        if not isinstance(body, dict) or not isinstance(body.get('type'), str):
                            raise ProviderError('Invalid provider WebSocket message')
                        if body['type'] == 'error':
                            raise ProviderError('Provider WebSocket reported an error')
                        ready = ready or body['type'] == 'sessionReady'
                        yield {'received_at': datetime.now(timezone.utc).isoformat(), 'encoding': encoding,
                               'wire_bytes': len(message.data.encode() if isinstance(message.data, str) else message.data),
                               'decoded_bytes': len(raw), 'message': scrub(body, (self.token,)),
                               'proof_status': 'provider_observation_only'}
            if not ready:
                raise ProviderError('Provider stream ended without sessionReady')
        except ProviderError:
            raise
        except Exception as error:
            raise ProviderError('Provider WebSocket failed: ' + type(error).__name__) from None


def save_snapshot(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    name = None
    try:
        with tempfile.NamedTemporaryFile(mode='w', dir=path.parent, prefix='.provider-', delete=False) as handle:
            name = handle.name
            json.dump(value, handle, indent=2, allow_nan=False)
            handle.write('\n')
        os.replace(name, path)
    finally:
        if name and os.path.exists(name):
            os.unlink(name)


def codec_check(client):
    """Remote round trips use synthetic bytes, never miner logs or user files."""
    rows = []
    samples = {'zeros': bytes(1024), 'sequence': bytes(range(256)) * 4,
               'synthetic_json': json.dumps({'nonces': list(range(128)), 'source': 'synthetic'}).encode()}
    for name, data in samples.items():
        for mode in ('network', 'file', 'progressive', 'constellation', 'auto'):
            started = time.perf_counter()
            local = tcmp.encode(data, mode)
            encode_seconds = time.perf_counter() - started
            started = time.perf_counter()
            if tcmp.decode(local) != data:
                raise ProviderError('Local codec round trip mismatch')
            decode_seconds = time.perf_counter() - started
            query = urllib.parse.urlencode({'codec': 'coprime', 'mode': mode})
            headers, remote = client.request('POST', '/api/compression/compress?' + query, data=data,
                                             headers={'Content-Type': 'application/octet-stream'})
            if tcmp.decode(remote) != data or local != remote:
                raise ProviderError('Provider TCMP encoding changed or returned mismatched data')
            if headers.get('x-original-sha256') != hashlib.sha256(data).hexdigest():
                raise ProviderError('Provider compression digest mismatch')
            _, restored = client.request('POST', '/api/compression/decompress?' + query, data=local,
                                         headers={'Content-Type': 'application/octet-stream'})
            if restored != data:
                raise ProviderError('Provider decompression round trip mismatch')
            rows.append({'sample': name, 'mode': mode, 'input_bytes': len(data), 'frame_bytes': len(local),
                         'saved_bytes': len(data) - len(local), 'encode_seconds': encode_seconds,
                         'decode_seconds': decode_seconds, 'frame_sha256': hashlib.sha256(local).hexdigest(),
                         'byte_identical_to_provider': True})
    return {'ok': True, 'scope': 'Synthetic codec interoperability; no mining throughput claim', 'cases': rows}


def evaluation_number(evaluation):
    """Parse a returned numeric value without treating 'none' as a fraction.

    An exact fraction takes precedence over rounded display text. The daemon
    uses the literal string 'none' for non-rational results. Malformed fractions
    and failed evaluations must remain failures rather than be masked.
    """
    if not isinstance(evaluation, dict) or evaluation.get('ok') is not True:
        raise ProviderError('Provider evaluation was not successful')
    daemon = evaluation.get('daemon', {})
    if not isinstance(daemon, dict):
        raise ProviderError('Invalid provider numeric metadata')
    fraction = daemon.get('fraction')
    value = evaluation.get('value') if fraction in (None, '', 'none') else fraction
    if type(value) not in (str, int):
        raise ProviderError('Provider numeric value must be an exact string or integer')
    try:
        return Fraction(value)
    except (ValueError, ZeroDivisionError, OverflowError):
        raise ProviderError('Invalid provider numeric value') from None


def calculation_check(client):
    """Finite exact arithmetic comparisons against independent Python references."""
    cases = [('11*15*17', 11 * 15 * 17), ('pow(2,32)-1', 2**32 - 1),
             ('pow(2,64)+1', 2**64 + 1), ('pow(3,2)-3*(-2)+pow(-2,2)', 19),
             ('3*pow(6,2)+3*6+1', 127), ('71*83', 5893), ('72*84', 6048),
             ('floor(-7/3)', -3), ('sqrt(15241578750190521)', 123456789),
             ('1/3+1/6', Fraction(1, 2))]
    rows = []
    for expression, expected in cases:
        start = time.perf_counter()
        try:
            result = client.calculate(expression)
            evaluation = result['evaluation']
            value = evaluation_number(evaluation)
            passed = value == expected
            row = {'expression': expression, 'expected': str(expected), 'actual': str(value), 'passed': passed,
                   'provider_exact': evaluation.get('exact'), 'provider_certified': evaluation.get('certified'),
                   'telemetry': result.get('telemetry', {})}
        except (ProviderError, ValueError, ZeroDivisionError) as error:
            row = {'expression': expression, 'expected': str(expected), 'passed': False, 'error': str(error)}
        row['elapsed_seconds'] = time.perf_counter() - start
        rows.append(row)
    return {'ok': all(row['passed'] for row in rows), 'cases': rows,
            'scope': 'Ten finite arithmetic comparisons; provider certification is recorded, not admitted as a Lean proof'}


def remote_sha256(client, data):
    """Use the documented compression integrity digest as a remote SHA256 oracle.

    This bounded adapter accepts one SHA input (up to an 80-byte header), checks
    the returned frame binds to those exact bytes, and never computes a local
    SHA digest. The provider digest remains an externally supplied result.
    """
    if not isinstance(data, bytes) or len(data) > 80:
        raise ValueError('Remote hash input must be bytes, at most 80 bytes')
    path = '/api/compression/compress?codec=coprime&mode=auto'
    headers, frame = client.request('POST', path, data=data,
                                    headers={'Content-Type': 'application/octet-stream'})
    digest = headers.get('x-original-sha256', '')
    if (headers.get('x-compression-codec') != 'coprime'
            or headers.get('x-original-size') != str(len(data))
            or headers.get('x-compressed-size') != str(len(frame))
            or not isinstance(digest, str) or re.fullmatch(r'[0-9a-fA-F]{64}', digest) is None):
        raise ProviderError('Invalid provider hash or input binding metadata')
    try:
        restored = tcmp.decode(frame, max_output=80)
    except tcmp.CodecError:
        raise ProviderError('Invalid provider hash response frame') from None
    if restored != data:
        raise ProviderError('Provider hash response is bound to different input bytes')
    return bytes.fromhex(digest)


def hash_header(client, header, mode='compare'):
    """Hash an exact Bitcoin header remotely; optionally compare independently.

    Two requests: 80 raw header bytes, then 32 raw first-digest bytes. This
    command neither scans nonces nor changes the running miner's backend.
    """
    if not isinstance(header, bytes) or len(header) != 80:
        raise ValueError('A Bitcoin header must contain exactly 80 bytes')
    if mode not in ('compare', 'remote'):
        raise ValueError('Hash mode must be compare or remote')
    started = time.perf_counter()
    first = remote_sha256(client, header)
    digest = remote_sha256(client, first)
    elapsed = time.perf_counter() - started
    result = {'ok': True, 'mode': mode, 'header_hex': header.hex(),
              'first_digest_hex': first.hex(), 'digest_hex': digest.hex(),
              'hash_hex': digest[::-1].hex(), 'remote_seconds': elapsed,
              'remote_requests': 2, 'local_verification': 'not_performed',
              'backend': 'provider compression integrity SHA256',
              'mining_process_changed': False, 'block_submitted': False,
              'scope': 'Exact supplied header only; no evidence that the geometric calculator implements SHA256, and no mining acceptance claim'}
    if mode == 'compare':
        local_first = hashlib.sha256(header).digest()
        local = hashlib.sha256(local_first).digest()
        result.update(ok=(first == local_first and digest == local),
                      first_digest_matches=(first == local_first),
                      final_digest_matches=(digest == local),
                      local_hash_hex=local[::-1].hex(),
                      local_verification='matched' if first == local_first and digest == local else 'mismatch')
    return result


def run_command(args):
    header = None
    if args.action == 'hash':
        text = args.header_hex
        if not isinstance(text, str) or re.fullmatch(r'[0-9a-fA-F]{160}', text) is None:
            raise ValueError('--header-hex requires exactly 160 hexadecimal characters')
        header = bytes.fromhex(text)
    client = ProviderClient(args.base_url, user=args.user)
    if args.action != 'capabilities':
        client.authenticate()
    if args.action in ('capabilities', 'refresh'):
        result = client.discover(args.query)
    elif args.action == 'formulas':
        result = client.formulas(args.query)
    elif args.action == 'calculate':
        result = client.calculate(args.expression, json.loads(args.variables))
    elif args.action == 'hash':
        result = hash_header(client, header, args.hash_mode)
        result['transport'] = client.metrics
    elif args.action == 'check':
        result = {'codec': codec_check(client), 'calculations': calculation_check(client)}
        result['ok'] = result['codec']['ok'] and result['calculations']['ok']
        result['transport'] = client.metrics
    else:
        async def collect():
            events, size = [], 0
            async for event in client.updates(args.seconds):
                size += event['decoded_bytes']
                if size > 2 * LIMIT:
                    raise ProviderError('Provider observation exceeds aggregate output limit')
                events.append(event)
            return events
        events = asyncio.run(collect())
        result = {'ok': True, 'events': events, 'counts': dict(Counter(e['message']['type'] for e in events)),
                  'scope': 'Bounded provider observation; event labels do not certify expressions'}
    result = scrub(result, (client.token,))
    destination = args.output
    if not destination and args.action == 'refresh':
        destination = ROOT / 'logs/provider/latest.json'
    if destination:
        save_snapshot(destination, result)
    if args.action in ('capabilities', 'refresh'):
        documents = result['documents']
        channel = documents['asyncapi'].get('channels', {}).get('ws', {})
        return {'ok': True, 'observed_at': result['observed_at'], 'base_url': client.base_url,
                'account': result['account'], 'formula_count': result['formula_count'],
                'total_available': result['total_available'], 'catalogue_complete': result['catalogue_complete'],
                'functions': documents['capabilities'].get('supportedFunctions', []),
                'constants': documents['capabilities'].get('supportedConstants', []),
                'codec': documents['app_codec'].get('codec', {}).get('name'),
                'server_messages': [v.get('name') for v in channel.get('subscribe', {}).get('message', {}).get('oneOf', [])],
                'snapshot': str(destination) if destination else None,
                'proof_status': result['proof_status'], 'mining_process_changed': False}
    return result
