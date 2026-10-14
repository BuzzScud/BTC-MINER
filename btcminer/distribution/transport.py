"""Authenticated bounded HTTP(S) protocol and durable worker request retries."""
import hmac
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import ipaddress
import json
import os
from pathlib import Path
import re
import ssl
import threading
import urllib.error
import urllib.parse
import urllib.request
import uuid

from ..settings import atomic_json
from .geometry import canonical
from .store import Rejected

LIMIT = 262144


def strict_json(raw):
    def pairs(items):
        result = {}
        for key,value in items:
            if key in result: raise ValueError('Duplicate JSON key')
            result[key] = value
        return result
    def constant(_): raise ValueError('Nonfinite JSON')
    try: return json.loads(raw,object_pairs_hook=pairs,parse_constant=constant)
    except RecursionError: raise ValueError('JSON nesting limit') from None


def loopback(host):
    if host == 'localhost': return True
    try: return ipaddress.ip_address(host).is_loopback
    except ValueError: return False


def read_tokens(path):
    path = Path(path)
    if os.name != 'nt' and path.stat().st_mode & 0o077:
        raise ValueError('Worker credentials file must have mode 600')
    tokens = strict_json(path.read_bytes())
    if not isinstance(tokens,dict) or not tokens: raise ValueError('Credentials map required')
    if any(not isinstance(p,str) or not re.fullmatch(r'[A-Za-z0-9_.-]{1,64}',p) or p in ('.','..') or
           not isinstance(t,str) or len(t)<32 or not t.isascii() or not t.isalnum()
           for p,t in tokens.items()) or len(set(tokens.values())) != len(tokens):
        raise ValueError('Use unique 32+ character alphanumeric tokens and node names')
    return tokens


class Server(ThreadingHTTPServer):
    daemon_threads = True
    request_queue_size = 32
    def __init__(self, address, store, tokens):
        self.store,self.tokens = store,tokens
        self.slots = threading.BoundedSemaphore(32)
        super().__init__(address,Handler)

    def process_request(self,request,address):
        if not self.slots.acquire(blocking=False):
            self.shutdown_request(request); return
        try: super().process_request(request,address)
        except BaseException:
            self.slots.release(); raise

    def process_request_thread(self,request,address):
        try: super().process_request_thread(request,address)
        finally: self.slots.release()


class Handler(BaseHTTPRequestHandler):
    protocol_version = 'HTTP/1.1'
    def setup(self):
        super().setup(); self.connection.settimeout(5)

    def log_message(self,*_): pass

    def reply(self,status,data):
        raw = canonical(data).encode()
        self.send_response(status); self.send_header('Content-Type','application/json')
        self.send_header('Content-Length',str(len(raw))); self.send_header('Connection','close')
        self.end_headers(); self.close_connection = True
        try: self.wfile.write(raw)
        except (OSError,ConnectionError): pass

    def do_POST(self):
        if self.path != '/v1/work': return self.reply(404,{'error':'not_found'})
        try:
            auth = self.headers.get_all('Authorization') or []
            if len(auth)!=1: return self.reply(401,{'error':'unauthenticated'})
            peer = next((p for p,t in self.server.tokens.items()
                         if hmac.compare_digest(auth[0].encode(),('Bearer '+t).encode())),None)
            if peer is None: return self.reply(401,{'error':'unauthenticated'})
            lengths = self.headers.get_all('Content-Length') or []
            if self.headers.get_all('Transfer-Encoding') is not None or len(lengths)!=1 or not lengths[0].isascii() or not lengths[0].isdecimal():
                raise ValueError('Invalid framing')
            length = int(lengths[0])
            if not 0 < length <= LIMIT: return self.reply(413,{'error':'body_limit'})
            raw = self.rfile.read(length)
            if len(raw)!=length: raise ValueError('Truncated request')
            result = self.server.store.operation(peer,strict_json(raw))
            self.reply(200, result)
        except Rejected as error: self.reply(409,{'error':str(error)})
        except (ValueError,TypeError,KeyError,OverflowError,UnicodeError): self.reply(400,{'error':'invalid_request'})
        except Exception: self.reply(503,{'error':'service_unavailable'})


def serve(store,host,port,tokens,cert='',key=''):
    if not loopback(host) and not (cert and key):
        raise ValueError('Remote listener requires a TLS certificate and key')
    server = Server((host,port),store,tokens)
    try:
        if cert or key:
            if not cert or not key: raise ValueError('Both TLS certificate and key required')
            context = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            context.minimum_version = ssl.TLSVersion.TLSv1_2
            context.load_cert_chain(cert,key)
            server.socket = context.wrap_socket(server.socket,server_side=True)
        thread = threading.Thread(target=server.serve_forever,name='partition-coordinator',daemon=True)
        thread.start()
        return server,thread
    except BaseException:
        server.server_close(); raise


class LocalClient:
    def __init__(self,store,peer): self.store,self.peer = store,peer
    def call(self,action,**fields):
        return self.store.operation(self.peer,dict(action=action,op=uuid.uuid4().hex,**fields))


class TransportError(RuntimeError): pass


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*args,**kwargs): raise TransportError('Redirect refused')


class Client:
    def __init__(self,url,token,journal,ca=None,timeout=5):
        parsed = urllib.parse.urlsplit(url)
        if parsed.scheme not in ('http','https') or not parsed.hostname or parsed.username or parsed.password or parsed.path not in ('','/') or parsed.query or parsed.fragment:
            raise ValueError('Coordinator URL must be an HTTP(S) origin')
        if parsed.scheme=='http' and not loopback(parsed.hostname):
            raise ValueError('Remote workers require HTTPS')
        if not isinstance(token,str) or len(token)<32 or not token.isalnum() or not token.isascii():
            raise ValueError('Invalid worker token')
        self.url,self.token,self.journal,self.timeout = url.rstrip('/'),token,Path(journal),timeout
        self.binding = hashlib_binding(self.url,token)
        context = ssl.create_default_context(cafile=ca)
        self.opener = urllib.request.build_opener(NoRedirect(),urllib.request.HTTPSHandler(context=context))

    def recover(self):
        if not self.journal.exists(): return None
        saved = strict_json(self.journal.read_bytes())
        if saved.get('binding')!=self.binding: raise ValueError('Journal belongs to another coordinator or credential')
        return self._send(saved['request'])

    def _send(self,request):
        raw = canonical(request).encode()
        req = urllib.request.Request(self.url+'/v1/work',data=raw,method='POST',headers={
            'Content-Type':'application/json','Authorization':'Bearer '+self.token})
        for attempt in range(3):
            try:
                with self.opener.open(req,timeout=self.timeout) as response:
                    body = response.read(LIMIT+1)
                if len(body)>LIMIT: raise TransportError('Response too large')
                result = strict_json(body)
                if not isinstance(result,dict): raise TransportError('Invalid response')
                self.journal.unlink(missing_ok=True)
                return result
            except urllib.error.HTTPError as error:
                if error.code in (400,401,403,404,409,413):
                    try: message = strict_json(error.read(LIMIT)).get('error','request_rejected')
                    except ValueError: message = 'request_rejected'
                    self.journal.unlink(missing_ok=True)
                    raise Rejected(message) from None
            except (OSError,ValueError,urllib.error.URLError): pass
        raise TransportError('Coordinator unavailable; pending request retained for exact retry')

    def call(self,action,**fields):
        if self.journal.exists(): raise TransportError('Recover the outstanding request before new work')
        request = dict(action=action,op=uuid.uuid4().hex,**fields)
        atomic_json(self.journal,dict(binding=self.binding,request=request))
        # atomic_json uses a mode-600 temporary file; fsync before sending so a
        # worker process crash cannot discard its operation identity.
        with self.journal.open('rb') as handle: os.fsync(handle.fileno())
        return self._send(request)


def hashlib_binding(url,token):
    import hashlib
    return hashlib.sha256((url+'\0'+token).encode()).hexdigest()
