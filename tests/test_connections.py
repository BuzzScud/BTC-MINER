import json
import unittest
from unittest.mock import Mock

from btcminer.connections import PoolConnection, endpoint
from btcminer.protocol import DIFF1
from btcminer.service import parse_control
from btcminer.settings import DEFAULTS


class ConnectionTests(unittest.TestCase):
    def setUp(self):
        self.pool = PoolConnection(dict(DEFAULTS, pool="stratum+tcp://localhost:3333",
                                        pool_user="test.worker"), Mock())
        self.pool.socket = Mock()

    def test_subscribe_authorize_and_invalid_authorization(self):
        self.pool.send("mining.subscribe", [], "subscribe")
        self.pool.receive({"id":1,"result":[[],"abcd",4],"error":None})
        request = json.loads(self.pool.socket.sendall.call_args[0][0])
        self.assertEqual(request["method"], "mining.authorize")
        self.assertEqual(request["params"], ["test.worker","x"])
        self.pool.receive({"id":2,"result":True,"error":None})
        self.assertTrue(self.pool.connected)
        self.pool.send("mining.authorize", [], "authorize")
        with self.assertRaisesRegex(ValueError, "authorization failed"):
            self.pool.receive({"id":3,"result":False,"error":None})

    def test_difficulty_applies_to_next_job(self):
        self.pool.receive({"method":"mining.set_difficulty","params":[2]})
        self.assertEqual(self.pool.target, DIFF1)
        self.pool.receive({"method":"mining.notify","params":["job"]+[""]*7+[True]})
        self.assertEqual(self.pool.target, DIFF1//2)

    def test_reused_job_id_does_not_reset_extranonce(self):
        self.pool.counter = 42
        params = ["reused"]+[""]*7+[True]
        self.pool.receive({"method":"mining.notify","params":params})
        generation = self.pool.generation
        self.pool.receive({"method":"mining.notify","params":params})
        self.assertGreater(self.pool.generation, generation)
        self.assertEqual(self.pool.counter, 42)

    def test_unconfigured_pool_redirect_is_not_followed(self):
        with self.assertRaises(ConnectionError):
            self.pool.receive({"method":"client.reconnect","params":["other.example",1234]})

    def test_endpoint_validation_and_tls(self):
        self.assertEqual(endpoint("stratum+ssl://example.com:3333"), ("example.com",3333,True))
        self.assertEqual(endpoint("stratum+tcp://[::1]:3333"), ("::1",3333,False))
        for value in ("", "example.com", "https://example.com:443", "user:pass@example.com:3333",
                      "stratum+ssl://example.com:3333/path", "example.com:65536"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                endpoint(value)

    def test_control_requests_reject_non_objects_and_invalid_fields(self):
        for request in ([], None, 1, "status", {}, {"command":[]},
                        {"command":"stop","summary":"false"}):
            with self.subTest(request=request), self.assertRaises(ValueError):
                parse_control(json.dumps(request))
        self.assertEqual(parse_control(b'{"command":"stop","summary":false}'),
                         {"command":"stop","summary":False})
