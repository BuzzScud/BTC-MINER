"""PROOF-01/PUBLISH-01 negative controls; see ../MASTER_PLAN.md.

MUST mutate only disposable copies. SHALL reject stale, incomplete or semantically
changed evidence; no mining, network, provider API or Lean process is started.
"""
import copy
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock
from btcminer import ROOT
from btcminer.proof_evidence import EvidenceError, parse_axioms, verify, verify_catalogue
from btcminer import theorem_calculations


class EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.accepted = verify(ROOT)
        cls.catalogue = json.loads((ROOT/'research/executable-theorems.json').read_text())

    def capsule(self):
        folder = tempfile.TemporaryDirectory(prefix='miner-proof-test-')
        self.addCleanup(folder.cleanup)
        root = Path(folder.name)
        shutil.copytree(ROOT/'research/proof-evidence', root/'research/proof-evidence')
        for relative in self.accepted['manifest']['workspace_sources']:
            target = root/relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(ROOT/relative, target)
        return root

    def test_portable_current_sources_and_objects(self):
        result = verify(self.capsule())
        self.assertEqual(result['manifest_sha256'], self.accepted['manifest_sha256'])
        self.assertEqual(result['theorem_roots'], self.accepted['theorem_roots'])

    def test_current_source_change_rejected(self):
        root = self.capsule()
        relative = next(iter(self.accepted['manifest']['workspace_sources']))
        with (root/relative).open('a') as output:
            output.write('\n-- Changed after acceptance\n')
        with self.assertRaisesRegex(EvidenceError, 'Stale proof source'):
            verify(root)

    def test_missing_compiled_object_rejected(self):
        root = self.capsule()
        build = self.accepted['raw_receipt']['builds'][0]
        path = PurePosixPath(self.accepted['raw_receipt']['object_directory'])/next(iter(build['artifacts']))
        relative = self.accepted['original_files'][str(path)]
        (root/'research/proof-evidence'/relative).unlink()
        with self.assertRaises(EvidenceError):
            verify(root)

    def test_corrupt_object_rejected(self):
        root = self.capsule()
        relative = next(iter(self.accepted['manifest']['objects']))
        (root/'research/proof-evidence'/relative).write_bytes(b'corrupt')
        with self.assertRaisesRegex(EvidenceError, 'Changed evidence object'):
            verify(root)

    def test_unreferenced_old_cache_objects_are_not_admitted(self):
        root = self.capsule()
        (root/'research/proof-evidence/objects/old-unreferenced').write_bytes(b'old')
        result = verify(root)
        self.assertEqual(result['objects_checked'], self.accepted['objects_checked'])

    def test_omitted_local_binding_rejected(self):
        root = self.capsule()
        path = root/'research/proof-evidence/manifest.json'
        data = json.loads(path.read_text())
        del data['original_files'][next(p for p in data['original_files'] if p.endswith('/run_retry.py'))]
        path.write_text(json.dumps(data))
        with self.assertRaises(EvidenceError):
            verify(root)

    def test_symlink_object_rejected(self):
        root = self.capsule()
        relative = next(iter(self.accepted['manifest']['objects']))
        path = root/'research/proof-evidence'/relative
        original = path.read_bytes()
        path.unlink()
        target = root/'outside-object'
        target.write_bytes(original)
        path.symlink_to(target)
        with self.assertRaisesRegex(EvidenceError, 'Invalid evidence object path'):
            verify(root)

    def test_unknown_custom_sorry_and_native_assumptions_rejected(self):
        required = {'Module':['theorem1']}
        for assumption in ('custom_axiom', 'sorryAx', 'Lean.ofReduceBool'):
            with self.subTest(assumption=assumption), self.assertRaises(EvidenceError):
                parse_axioms('ROOT\tModule\ttheorem1\t'+assumption+'\nTOTAL\t1\n', required)

    def test_incomplete_duplicate_and_missing_roots_rejected(self):
        required = {'Module':['theorem1']}
        good = 'ROOT\tModule\ttheorem1\tpropext\n'
        for text in (good, good+'TOTAL\t2\n', good+good+'TOTAL\t2\n', good.replace('theorem1','wrong')+'TOTAL\t1\n'):
            with self.subTest(text=text), self.assertRaises(EvidenceError):
                parse_axioms(text, required)

    def test_allowed_assumptions_are_parsed(self):
        roots, counts = parse_axioms('ROOT\tModule\ttheorem1\tQuot.sound,propext\nTOTAL\t1\n', {'Module':['theorem1']})
        self.assertEqual(roots['theorem1']['axioms'], ['Quot.sound','propext'])
        self.assertEqual(counts, {'Module':1})

    def test_current_catalogue_is_admitted(self):
        self.assertEqual(verify_catalogue(ROOT, self.catalogue)['count'], 5)

    def test_legacy_or_stale_catalogue_rejected(self):
        for field,value in [('schema',1), ('proof_manifest_sha256','0'*64)]:
            altered = copy.deepcopy(self.catalogue)
            altered[field] = value
            with self.subTest(field=field), self.assertRaises(EvidenceError):
                verify_catalogue(ROOT, altered, self.accepted)

    def test_statement_premise_type_and_result_mutations_rejected(self):
        mutations = {'statement':'theorem returned_1 : False', 'premises':[['eq',0,1]],
                     'variables':[{'name':'n','domain':'Nat'}], 'conclusion':['eq',11,12],
                     'bitcoin_exclusion_authority':True, 'instance_check_passed':False}
        for key,value in mutations.items():
            altered = copy.deepcopy(self.catalogue)
            altered['theorems'][0][key] = value
            with self.subTest(key=key), self.assertRaises(EvidenceError):
                verify_catalogue(ROOT, altered, self.accepted)

    def test_public_catalogue_has_no_stale_success_cache(self):
        root = self.capsule()
        (root/'research/executable-theorems.json').write_text(json.dumps(self.catalogue))
        with mock.patch.object(theorem_calculations,'ROOT',root):
            self.assertEqual(theorem_calculations.catalogue()['count'],5)
            relative = next(iter(self.accepted['manifest']['workspace_sources']))
            (root/relative).write_text('changed')
            with self.assertRaises(EvidenceError):
                theorem_calculations.catalogue()

    def test_failed_publication_preserves_catalogue(self):
        root = self.capsule()
        path = root/'research/executable-theorems.json'
        previous = json.dumps(self.catalogue).encode()
        path.write_bytes(previous)
        relative = next(iter(self.accepted['manifest']['workspace_sources']))
        (root/relative).write_text('unproved modified source')
        result = subprocess.run([sys.executable, '-B', str(ROOT/'scripts/publish_archive_calculations.py'),
                                 '--root', str(root)], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
        self.assertNotEqual(result.returncode,0)
        self.assertIn('Stale proof source',result.stderr)
        self.assertEqual(path.read_bytes(),previous)
