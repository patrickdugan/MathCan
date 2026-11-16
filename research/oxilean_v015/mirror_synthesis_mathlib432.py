from pathlib import Path
import hashlib
import json
import os
import shutil
import time
import argparse

W = Path(os.environ.get('CAMPAIGN_WORK', Path(__file__).resolve().parent)).resolve()
assert os.name == 'posix', 'Run this helper in WSL'
source_root = W/'mathlib432-local'
R = W/'replay432/Synthesis'
receipt_file = W/'MATHLIB_ARTIFACT_RECEIPT.json'
receipt = json.loads(receipt_file.read_text())
assert receipt['mathlib_revision'] == '360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56'
assert receipt['status'] == 'complete'
records = {}
def file_sha256(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024*1024), b''):
            digest.update(data)
    return digest.hexdigest()

for module in receipt['modules']:
    for rel, expected in module['retained_files'].items():
        if any(rel.endswith(ext) for ext in ['.olean', '.olean.server', '.olean.private',
                                            '.ir', '.ir.server', '.ir.private']):
            records[rel] = expected
assert len(records) >= 2*2145
parser = argparse.ArgumentParser()
parser.add_argument('--verify-only', action='store_true')
options = parser.parse_args()
if options.verify_only:
    previous = json.loads((R/'mathlib_mirror.json').read_text())
    assert previous['status'] == 'matched' and previous['files'] == records
    target_root = Path(previous['target'])
else:
    print(f'Checking mirror capacity for {len(records)} runtime artifacts', flush=True)
    total_bytes = sum((source_root/rel).stat().st_size for rel in records)
    memory_available = next(int(line.split()[1])*1024
        for line in Path('/proc/meminfo').read_text().splitlines() if line.startswith('MemAvailable:'))
    ram_free = shutil.disk_usage('/dev/shm').free
    in_ram = total_bytes + 512*1024**2 < ram_free and total_bytes + 2*1024**3 < memory_available
    target_root = Path('/dev/shm' if in_ram else '/tmp')/'oxilean-synthesis432-20261116/mathlib432-local'
    assert shutil.disk_usage(target_root.parents[1]).free > total_bytes + 512*1024**2
    print(f'Mirror size {total_bytes} bytes; target {target_root}', flush=True)
assert target_root.is_absolute() and any(target_root.is_relative_to(prefix) for prefix in [
    '/tmp/oxilean-synthesis432-20261116', '/dev/shm/oxilean-synthesis432-20261116'])
started = time.monotonic()
copied_bytes = 0
for index, (rel, expected) in enumerate(sorted(records.items()), 1):
    relative = Path(rel)
    assert not relative.is_absolute() and '..' not in relative.parts
    source = source_root/relative
    dest = target_root/relative
    assert dest.is_relative_to(target_root)
    if not options.verify_only:
        dest.parent.mkdir(parents=True, exist_ok=True)
    if dest.exists():
        assert file_sha256(dest) == expected, rel
    else:
        assert not options.verify_only, ('missing mirror file', rel)
        digest = hashlib.sha256()
        with source.open('rb') as src, dest.open('xb') as out:
            while data := src.read(1024*1024):
                digest.update(data)
                out.write(data)
                copied_bytes += len(data)
        assert digest.hexdigest() == expected, ('source hash mismatch', rel)
        assert file_sha256(dest) == expected, ('copy hash mismatch', rel)
    if index % 500 == 0:
        print(f'Validated mirror {index}/{len(records)} runtime artifacts', flush=True)
result = {'status': 'matched', 'purpose': 'Byte-identical Linux-local runtime artifact mirror',
          'mathlib_revision': receipt['mathlib_revision'], 'source': str(source_root),
          'target': str(target_root), 'runtime_artifact_files': len(records),
          'copied_bytes': copied_bytes, 'elapsed_seconds': time.monotonic()-started,
          'artifact_receipt_sha256': hashlib.sha256(receipt_file.read_bytes()).hexdigest(),
          'files': records}
(R/('mathlib_mirror_after.json' if options.verify_only else 'mathlib_mirror.json')).write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps({key: value for key, value in result.items() if key != 'files'}, indent=2), flush=True)
