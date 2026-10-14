import json
from pathlib import Path
import shutil
import tempfile
import unittest
from btcminer import ROOT
from btcminer.math_catalogue import catalogue


class MathCatalogueTests(unittest.TestCase):
    def test_full_snapshot_and_source_search_keep_proof_scope(self):
        summary=catalogue()
        self.assertEqual(summary['formula_count'],1302)
        self.assertFalse(summary['proof_acceptance_from_provider_records'])
        found=catalogue(query='fractal_arbitrary_precision')
        self.assertTrue(any(f['name']=='fractal_arbitrary_precision' for f in found['formulas']))
        self.assertFalse(found['proof_acceptance_from_provider_records'])
        self.assertEqual(catalogue(query='not-a-real-formula-09ef')['matched_count'],0)

    def test_changed_catalogue_is_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder); (root/'research').mkdir()
            for name in ('formula-catalogue.json','math-catalogue-reference.json'):
                shutil.copyfile(ROOT/'research'/name,root/'research'/name)
            self.assertFalse(catalogue(root)['workspace_cards_available'])
            p=root/'research/formula-catalogue.json';data=json.loads(p.read_text())
            data['formulas'][0]['status']='verified'
            data['formulas'][0]['expression']='arbitrary false promoted expression'
            p.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError,'differs'):catalogue(root)

    def test_changed_consumer_map_is_rejected(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder); (root/'research').mkdir()
            for name in ('formula-catalogue.json','math-catalogue-reference.json','math-consumers.json'):
                shutil.copyfile(ROOT/'research'/name,root/'research'/name)
            self.assertIn('consumer_map',catalogue(root))
            path=root/'research/math-consumers.json'
            path.write_bytes(path.read_bytes()+b' ')
            with self.assertRaisesRegex(ValueError,'Consumer map differs'):catalogue(root)


if __name__=='__main__':unittest.main()
