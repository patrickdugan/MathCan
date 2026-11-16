from pathlib import Path
import hashlib
import json
import subprocess
import zipfile

W = Path(__file__).resolve().parent
O = W.parent/'outputs'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], encoding='utf-8').strip()

push = json.loads((O/'PUSH_RECEIPT.json').read_text(encoding='utf-8'))
assert push['status'] == 'verified'
commits = []
for name, base, bundle in [
    ('MathCan', '819c061893c250ef208ce63cdf3f967b64439f0f', 'MathCan_synthesis.bundle'),
    ('Compactification-Theory', 'b8dc406e7457be5eef859a2cd1c0bd49eb8a3e68', 'Compactification_Theory_synthesis.bundle'),
]:
    repo = W/name
    assert not git(repo, 'status', '--porcelain')
    head = git(repo, 'rev-parse', 'HEAD')
    branch = git(repo, 'branch', '--show-current')
    remote = next(row for row in push['repositories'] if row['repository'] == name)
    assert head == remote['local_commit'] == remote['remote_commit']
    assert head != base
    subprocess.run(['git', '-C', str(repo), 'bundle', 'create', str(O/bundle), base+'..'+branch],
                   check=True, capture_output=True)
    subprocess.run(['git', '-C', str(repo), 'bundle', 'verify', str(O/bundle)],
                   check=True, capture_output=True)
    commits.append({'repository': name, 'branch': branch, 'base': base, 'commit': head,
                    'bundle': bundle, 'bundle_sha256': sha(O/bundle),
                    'worktree_clean': True, 'remote_verified': True})
(O/'SYNTHESIS_COMMITS.json').write_text(json.dumps(commits, indent=2)+'\n', encoding='utf-8', newline='\n')
members = {}
for name in ['MULTIVARIATE_SYNTHESIS_REPORT.md', 'SYNTHESIS_ACCEPTANCE.json',
             'SYNTHESIS_BUILD_RECEIPT.json', 'SYNTHESIS_VERIFICATION_SUMMARY.json',
             'SYNTHESIS_COMMITS.json', 'PUSH_RECEIPT.json', 'FINAL_VALIDATION.json',
             'SYNTHESIS_GIT_INDEX_VERIFICATION.json', 'SYNTHESIS_GIT_CONTENT_VERIFICATION.json',
             'MathCan_synthesis.bundle', 'Compactification_Theory_synthesis.bundle']:
    members[name] = O/name
manifest = json.loads((W/'replay432/Synthesis/manifest.json').read_text(encoding='utf-8'))
for rel in manifest['sources'].values():
    members['MathCan/'+rel] = W/'MathCan'/rel
for rel in ['research/approximation_mathlib432/ApproximationMathlib.lean',
            'research/approximation_mathlib432/README.md',
            'research/approximation_mathlib432/lakefile.toml',
            'research/approximation_mathlib432/lean-toolchain']:
    members['MathCan/'+rel] = W/'MathCan'/rel
proof_dir = W/'MathCan/research/oxilean_v015'
for p in (proof_dir/'pinned432_synthesis').iterdir():
    if p.is_file():
        members['MathCan/research/oxilean_v015/pinned432_synthesis/'+p.name] = p
for name in ['synthesis_env432.sh', 'freeze_synthesis432.sh', 'build_synthesis432.sh',
             'kernel_synthesis432.sh', 'export_synthesis432.sh', 'compare_synthesis432.sh',
             'prepare_synthesis_replay.py', 'accept_synthesis432.py',
             'test_synthesis_acceptance.py', 'check_synthesis_source.py',
             'finalize_synthesis_phase.py', 'record_push_receipt.py',
             'package_synthesis_results.py', 'check_synthesis_git_content.py',
             'fast_synthesis_replay432.sh', 'promote_fast_synthesis432.py',
             'mirror_synthesis_mathlib432.py', 'stop_slow_synthesis_export.py',
             'probe_stock_synthesis432.sh',
             'finish_fast_synthesis432.sh', 'audit_export_fast.py',
             'test_audit_export_fast.py', 'prepare_fast_auditor.py',
             'check_mirror_native432.py',
             'validate_mathlib432.py', 'audit_export.py',
             'CompareLemmas.lean']:
    members['MathCan/research/oxilean_v015/'+name] = proof_dir/name
readme = '''# Verified multivariate synthesis phase packet

All 47 new authored theorem roots passed frozen-source Lean compilation,
native kernel replay and independent OxiLean verification. Read
MULTIVARIATE_SYNTHESIS_REPORT.md for the mathematical scope and remaining
network theorem obligations. The research total is 257 roots; Hodge is separate.
No new email, direct message or repository comment was sent.

This is an incremental packet. Its two Git bundles require the preceding
MathCan 819c061893c250ef208ce63cdf3f967b64439f0f and Compactification-Theory
b8dc406e7457be5eef859a2cd1c0bd49eb8a3e68 commits, respectively. The previous
full campaign packet retains the earlier proof sources, dependency receipts
and reproduction prerequisites. Pinned tool binaries, Mathlib artifacts and
compiled oleans are not bundled here. The accepted raw NDJSON is stored as
deterministic gzip; its uncompressed hash is recorded by acceptance.

PUSH_RECEIPT.json and SYNTHESIS_COMMITS.json bind the clean local commits to
the verified remote research branches. DELIVERABLE_HASHES.json binds every
other packet member. Historical pending-runtime checkpoints remain outside
this verified packet.
'''
(O/'SYNTHESIS_PACKET_README.md').write_text(readme, encoding='utf-8', newline='\n')
members['README.md'] = O/'SYNTHESIS_PACKET_README.md'
hashes = {name: {'sha256': sha(p), 'size_bytes': p.stat().st_size}
          for name, p in sorted(members.items())}
(O/'SYNTHESIS_DELIVERABLE_HASHES.json').write_text(json.dumps(hashes, indent=2)+'\n', encoding='utf-8', newline='\n')
members['DELIVERABLE_HASHES.json'] = O/'SYNTHESIS_DELIVERABLE_HASHES.json'
archive = O/'oxilean_multivariate_synthesis_20261116.zip'
with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
    for name, p in sorted(members.items()):
        z.write(p, name)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for name, row in hashes.items():
        assert hashlib.sha256(z.read(name)).hexdigest() == row['sha256']
receipt = {'status': 'verified_phase_packet', 'archive': str(archive),
           'archive_sha256': sha(archive), 'bytes': archive.stat().st_size,
           'files': len(members), 'commits': commits}
(O/'SYNTHESIS_PACKAGE_RECEIPT.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8', newline='\n')
print(json.dumps(receipt, indent=2))
