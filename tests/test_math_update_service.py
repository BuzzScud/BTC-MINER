from contextlib import nullcontext
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
from btcminer import service


class MathUpdateServiceTests(unittest.TestCase):
    def run_update(self, before=None, final=None, hashes=None, started=None):
        implementation={'math.py':'new'}
        before = dict({'pid':123,'running':True,'state':'MINING','blocks_accepted':0}, **(before or {}))
        final = dict({'pid':123,'blocks_accepted':0}, **(final or {}))
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            (root/'last-session.json').write_text(json.dumps(final))
            with patch.object(service,'LOGS',root), patch.object(service,'lifecycle_lock',return_value=nullcontext()), \
                 patch.object(service,'request',return_value=before), \
                 patch('btcminer.mathrevision.fingerprint',side_effect=hashes or [implementation,implementation]), \
                 patch.object(service,'_stop') as stop, \
                 patch.object(service,'_start',return_value=started or {'running':True,'pid':456,'math_implementation':implementation}) as start:
                result=service.restart_for_math(123,implementation)
                return result,stop.call_count,start.call_count

    def test_same_session_reloads_once(self):
        result,stops,starts=self.run_update()
        self.assertTrue(result['applied'])
        self.assertEqual((stops,starts),(1,1))

    def test_stopped_paused_changed_session_or_found_block_is_untouched(self):
        for change in ({'running':False},{'state':'PAUSED'},{'pid':999},{'blocks_accepted':1}):
            result,stops,starts=self.run_update(before=change)
            self.assertFalse(result['applied'])
            self.assertEqual((stops,starts),(0,0))

    def test_block_accepted_while_stopping_prevents_restart(self):
        result,stops,starts=self.run_update(final={'blocks_accepted':1})
        self.assertFalse(result['applied'])
        self.assertEqual((stops,starts),(1,0))

    def test_final_session_mismatch_prevents_restart(self):
        result,stops,starts=self.run_update(final={'pid':999})
        self.assertFalse(result['applied'])
        self.assertEqual((stops,starts),(1,0))

    def test_already_loaded_or_changed_files_do_not_restart(self):
        for kwargs in ({'before':{'math_implementation':{'math.py':'new'}}}, {'hashes':[{'math.py':'changed'}]}):
            result,stops,starts=self.run_update(**kwargs)
            self.assertFalse(result['applied'])
            self.assertEqual((stops,starts),(0,0))
        result,stops,starts=self.run_update(hashes=[{'math.py':'new'},{'math.py':'changed'}])
        self.assertEqual((stops,starts),(1,0))

    def test_failed_reload_is_stopped(self):
        with self.assertRaisesRegex(RuntimeError,'left stopped'):
            self.run_update(started={'running':True,'math_implementation':{'wrong':'hash'}})
