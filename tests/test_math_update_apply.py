import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

SCRIPTS=Path(__file__).resolve().parents[1]/'scripts'
sys.path.insert(0,str(SCRIPTS))
SPEC=importlib.util.spec_from_file_location('apply_math_update',SCRIPTS/'apply_math_update.py')
updater=importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(updater)


class ApplyMathTests(unittest.TestCase):
    def run_apply(self, valid=True, reviewed=True, mining=True, test_code=0):
        implementation={'math.py':'digest'}
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            report={'ok':valid,'task_status':'COMPLETE','task_id':'task',
                    'targets':updater.LATEST_TARGETS,'sources':{'proof':'digest'}}
            manifest={'task_id':'task','sources':report['sources'],
                      'implementation':implementation if reviewed else {}}
            path=root/'reference/aristotle-rods-towers/reviewed-sources.json'
            path.parent.mkdir(parents=True);path.write_text(json.dumps(manifest))
            (root/'report.json').write_text(json.dumps(report))
            with patch.object(updater,'ROOT',root),patch.object(updater,'OUT',root), \
                 patch.object(updater,'validation_path',return_value=root/'report.json'), \
                 patch.object(updater,'fingerprint',return_value=implementation), \
                 patch.object(updater.service,'status',return_value={'running':mining,'state':'MINING','pid':5}), \
                 patch.object(updater.subprocess,'run') as tests, \
                 patch.object(updater.service,'restart_for_math',return_value={'applied':True}) as restart:
                tests.return_value.returncode=test_code
                result=updater.apply('task')
                return result,tests.call_count,restart.call_count

    def test_only_validated_reviewed_and_tested_revision_restarts(self):
        result,tests,restarts=self.run_apply()
        self.assertTrue(result['applied'])
        self.assertEqual((tests,restarts),(1,1))
        for kwargs in ({'valid':False},{'reviewed':False},{'mining':False}):
            result,tests,restarts=self.run_apply(**kwargs)
            self.assertFalse(result['applied'])
            self.assertEqual((tests,restarts),(0,0))
        result,tests,restarts=self.run_apply(test_code=1)
        self.assertFalse(result['applied'])
        self.assertEqual((tests,restarts),(1,0))
