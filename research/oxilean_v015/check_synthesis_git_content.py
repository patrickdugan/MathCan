from pathlib import Path
import argparse
import gzip
import hashlib
import json
import subprocess

args = argparse.ArgumentParser()
args.add_argument('--index', action='store_true')
options = args.parse_args()
W = Path(__file__).resolve().parent
O = W.parent/'outputs'
A = json.loads((W/'replay432/Synthesis/ACCEPTANCE.json').read_text(encoding='utf-8'))
assert A['status'] == 'accepted' and len(A['theorems']) == 47
assert A['verdicts']['unsupported'] == A['verdicts']['rejected'] == 0
sha = lambda data: hashlib.sha256(data).hexdigest()
def git(repo, *params):
    return subprocess.check_output(['git', '-C', str(repo), *params])
def text(repo, *params):
    return git(repo, *params).decode('utf-8').strip()
def blob(repo, path):
    return git(repo, 'show', (':' if options.index else 'HEAD:')+path)

M = W/'MathCan'
C = W/'Compactification-Theory'
for repo, branch, base in [
    (M, 'research/quantized-jet-replay-20261115', '819c061893c250ef208ce63cdf3f967b64439f0f'),
    (C, 'research/quantization-d-audit-20261115', 'b8dc406e7457be5eef859a2cd1c0bd49eb8a3e68'),
]:
    assert text(repo, 'branch', '--show-current') == branch
    assert text(repo, 'rev-parse', 'HEAD' if options.index else 'HEAD^') == base
    if not options.index:
        assert not text(repo, 'status', '--porcelain')
for rel, expected in A['source_sha256'].items():
    assert sha(blob(M, rel)) == expected, rel
assert sha(blob(M, 'MathCan/Hodge.lean')) == '6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5'
assert blob(M, 'research/approximation_mathlib432/ApproximationMathlib.lean') == b'import ApproximationMathlib.MultivariateCapture\n'
prefix = 'research/oxilean_v015/'
compressed = blob(M, prefix+'pinned432_synthesis/Lemmas.ndjson.gz')
assert sha(gzip.decompress(compressed)) == A['export_sha256']
stored = json.loads(blob(M, prefix+'pinned432_synthesis/ACCEPTANCE.json'))
assert stored == A
main_report = blob(M, prefix+'MULTIVARIATE_SYNTHESIS_REPORT.md')
assert main_report == blob(C, 'research/quantization/MULTIVARIATE_SYNTHESIS_REPORT.md')
for repo, path in [(M, prefix+'FINAL_VALIDATION.json'),
                   (C, 'research/quantization/FINAL_VALIDATION.json')]:
    assert json.loads(blob(repo, path))['formal_theorems'] == 257
result = {'status': 'matched', 'location': 'Git index' if options.index else 'Git HEAD',
          'proof_source_sha256': A['source_sha256'], 'new_authored_roots': 47,
          'export_sha256': A['export_sha256'], 'gzip_blob_sha256': sha(compressed),
          'report_sha256': sha(main_report),
          'repository_heads': {repo.name: text(repo, 'rev-parse', 'HEAD') for repo in [M,C]}}
name = 'SYNTHESIS_GIT_INDEX_VERIFICATION.json' if options.index else 'SYNTHESIS_GIT_CONTENT_VERIFICATION.json'
(O/name).write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps({key: value for key, value in result.items() if key != 'proof_source_sha256'}, indent=2))
