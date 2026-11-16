import contextlib
import io
import json
from pathlib import Path
import runpy
import unittest
import os
from unittest.mock import patch

W = Path(os.environ.get('CAMPAIGN_WORK', Path(__file__).resolve().parent)).resolve()
R = W/'replay432/Common'
VALIDATOR = W/'accept_common432.py'
READ = Path.read_text

class CommonAcceptanceControls(unittest.TestCase):
    def refused(self, file, mutate):
        p = R/file
        value = json.loads(READ(p, encoding='utf-8'))
        mutate(value)
        changed = json.dumps(value)
        def read(path, *args, **kwargs):
            return changed if path.resolve() == p.resolve() else READ(path,*args,**kwargs)
        with patch.object(Path, 'read_text', read), patch.object(Path, 'write_text',
                side_effect=RuntimeError('Invalid corpus reached acceptance output')):
            with contextlib.redirect_stdout(io.StringIO()), self.assertRaises(AssertionError):
                runpy.run_path(str(VALIDATOR),run_name='__main__')

    def test_unsupported_dependency_despite_successful_exit(self):
        self.refused('verdicts.json', lambda v: v['decls'][0].update(verdict='unsupported'))

    def test_missing_per_declaration_verdict(self):
        self.refused('verdicts.json', lambda v: v['decls'].pop())

    def test_wrong_input_hash(self):
        self.refused('verdicts.json', lambda v: v['input'].update(sha256='0'*64))

    def test_wrong_toolchain_pin(self):
        self.refused('verdicts.json', lambda v: v['pins'].update(file_lean_version='4.35.0'))

    def test_missing_new_lemma_in_manifest(self):
        self.refused('manifest.json', lambda v: v['theorems'].pop())

    def test_changed_exported_proof(self):
        self.refused('source_export_comparison.json', lambda v:
            v['records'][-1].update(value_equal_after_metadata_normalization=False))

    def test_changed_exported_statement(self):
        self.refused('source_export_comparison.json', lambda v:
            v['records'][-1].update(type_equal=False))

    def test_open_dependency_graph(self):
        self.refused('axiom-graph.json', lambda v: v.update(structurally_closed=False))

if __name__ == '__main__':
    unittest.main(verbosity=2)
