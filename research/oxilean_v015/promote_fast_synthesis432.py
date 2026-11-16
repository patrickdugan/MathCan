from pathlib import Path
import hashlib
import json
import os
import shutil

assert os.name == 'posix'
W = Path(__file__).resolve().parent
R = W/'replay432/Synthesis'
F = Path('/dev/shm/oxilean-synthesis432-20261116/replay')
def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024*1024), b''):
            digest.update(data)
    return digest.hexdigest()
v = json.loads((F/'verdicts.json').read_text())
a = json.loads((F/'axiom-graph.json').read_text())
c = json.loads((F/'source_export_comparison.json').read_text())
assert all(row['verdict'] == 'verified' for row in v['decls'])
assert v['totals']['unsupported'] == v['totals']['rejected'] == 0
assert sha(F/'Lemmas.ndjson') == v['input']['sha256'] == a['sha256']
assert a['structurally_closed'] and a['unambiguous_names'] and not a['unsafe_records']
assert c['status'] == 'matched'
assert all(row['type_equal'] and row['value_equal_after_metadata_normalization']
           and row['level_parameters_equal'] for row in c['records'])
for proc in Path('/proc').iterdir():
    if not proc.name.isdigit():
        continue
    try:
        if os.readlink(proc/'fd/1') == str(R/'Lemmas.ndjson'):
            raise RuntimeError('The interrupted exporter still holds the canonical output')
    except (FileNotFoundError, PermissionError):
        pass
partial = R/'Lemmas.ntfs-interrupted.partial'
if (R/'Lemmas.ndjson').exists() and not partial.exists():
    (R/'Lemmas.ndjson').rename(partial)
interrupted_path=R/'slow_export_interruption.json'
if interrupted_path.exists() and partial.exists():
    interrupted=json.loads(interrupted_path.read_text())
    interrupted['partial_file']=str(partial)
    interrupted['partial_sha256']=sha(partial)
    interrupted_path.write_text(json.dumps(interrupted,indent=2)+'\n')
names = ['Lemmas.ndjson', 'verdicts.json', 'axiom-graph.json', 'source_export_comparison.json',
         'source_export_comparison.log', 'axioms.log', 'oxilean.stdout.log', 'oxilean.stderr.log',
         'audit_status.log']
for name in names:
    with (F/name).open('rb') as src, (R/name).open('wb') as out:
        shutil.copyfileobj(src, out, length=1024*1024)
    assert sha(F/name) == sha(R/name), name
result = {'status': 'matched', 'method': 'Linux-local output, then byte-checked bulk copy',
          'export_sha256': v['input']['sha256'], 'verdicts': v['totals'],
          'constants_compared': c['constants_compared'],
          'partial_export_counted': False, 'partial_file': str(partial),
          'files_sha256': {name: sha(R/name) for name in names}}
(R/'fast_output_promotion.json').write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({key: value for key, value in result.items() if key != 'files_sha256'}, indent=2), flush=True)
