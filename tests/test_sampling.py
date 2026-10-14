from array import array
import csv
import json
import os
from pathlib import Path
import struct
import tempfile
import unittest
from unittest.mock import patch

from btcminer.diagnostics import GENESIS
from btcminer.engine import Engine
from btcminer.native import Hasher, hash256
from btcminer.protocol import Work
from btcminer.settings import DEFAULTS


class SamplingTests(unittest.TestCase):
    def test_native_selection_matches_python_and_excludes_unattempted_tail(self):
        h = Hasher()
        reference = Hasher(False)
        for nonces in (list(range(10000,15000)), array("I",range(10000,15000))):
            for step in (1,3,64,1000000):
                task = {"nonces":nonces}
                self.assertEqual(list(h.sampled_nonces(task,2345,step)),
                                 list(reference.sampled_nonces(task,2345,step)))
        self.assertEqual(list(h.sampled_nonces({"start":62,"count":100},70,64)),[64,128])

    def test_batch_diagnostics_preserve_rows_hashes_and_round_counts(self):
        import supt_streams as ss
        with tempfile.TemporaryDirectory() as folder, patch.dict(os.environ):
            c = dict(DEFAULTS,supt_log=True,supt_sample_every=64)
            engine = Engine(c,logs=folder)
            round_id = ss.begin_round(900000,search_mode="thesis2")
            self.addCleanup(ss.shutdown_writer)
            work = Work(GENESIS,1,1,900000,"1d00ffff","test",1)
            task = {"nonces":array("I",[128,129,64,192,256])}
            engine.sample_batch(work,task,4,round_id)
            ss.end_round(round_id,-1,4,.1)
            with (Path(folder)/"math/nonce_hash_stream.csv").open() as f:
                rows = list(csv.DictReader(f))
            self.assertEqual([int(row["nonce"]) for row in rows],[128,64,192])
            for row in rows:
                digest = hash256(GENESIS[:76]+struct.pack("<I",int(row["nonce"])))
                self.assertEqual(int(row["hash_int"]),int.from_bytes(digest,"little"))
            record = json.loads((Path(folder)/"math/search_mode.jsonl").read_text())
            self.assertEqual(record["stream_a_samples"],3)
            self.assertEqual(record["hashes_tried"],4)
