"""Local process control: Unix socket, or authenticated loopback TCP on Windows."""
import hmac
import json
import secrets
import socket
from .platform_support import WINDOWS, private_file


def connect(address):
    if not WINDOWS:
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        target, token = str(address), None
    else:
        # The endpoint record is ACL-restricted before publication.
        with address.open('rb') as stream:
            value = json.loads(stream.read(4097))
        if type(value.get('port')) is not int or not 1 <= value['port'] <= 65535:
            raise ValueError('Invalid local control endpoint')
        token = value.get('token')
        if not isinstance(token, str) or len(token) != 64:
            raise ValueError('Invalid local control credential')
        sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        target = ('127.0.0.1', value['port'])
    try:
        sock.settimeout(3)
        sock.connect(target)
    except BaseException:
        sock.close()
        raise
    return sock, token


def listen(address):
    from .settings import atomic_json
    address.unlink(missing_ok=True)
    server = socket.socket(socket.AF_INET if WINDOWS else socket.AF_UNIX, socket.SOCK_STREAM)
    try:
        token = secrets.token_hex(32) if WINDOWS else None
        server.bind(('127.0.0.1', 0) if WINDOWS else str(address))
        if not WINDOWS: private_file(address)
        server.listen(4)
        server.settimeout(.3)
        if WINDOWS:
            atomic_json(address, {'port': server.getsockname()[1], 'token': token})
        return server, token
    except BaseException:
        server.close()
        address.unlink(missing_ok=True)
        raise


def authorize(command, token):
    if token is not None:
        supplied = command.pop('_auth', '')
        if not isinstance(supplied, str) or not hmac.compare_digest(token, supplied):
            raise ValueError('Local control authentication failed')
