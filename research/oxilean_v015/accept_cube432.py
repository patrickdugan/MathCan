from collections import Counter
import hashlib
sha_file=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
from pathlib import Path
import hashlib
import json
import re
import os

W = Path(os.environ.get('CAMPAIGN_WORK', Path(__file__).resolve().parent)).resolve()
R = W/'replay432/Cube'
manifest = json.loads((R/'manifest.json').read_text(encoding='utf-8'))
assert manifest['mathlib_revision'] == '360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56'
for phase in ['before','after']:
    binding=json.loads((R/f'mathlib_{phase}.json').read_text(encoding='utf-8'))
    assert binding['status']=='matched' and binding['mathlib_revision']==manifest['mathlib_revision']
    assert binding['artifact_modules']==2145 and binding['packages']==8
    assert binding['artifact_receipt_sha256']==hashlib.sha256((W/'MATHLIB_ARTIFACT_RECEIPT.json').read_bytes()).hexdigest()
mirror_used=json.loads((R/'mirror_used.json').read_text(encoding='utf-8'))
artifacts=json.loads((W/'MATHLIB_ARTIFACT_RECEIPT.json').read_text(encoding='utf-8'))
expected_runtime={rel:digest for module in artifacts['modules'] for rel,digest in module['retained_files'].items()
    if any(rel.endswith(ext) for ext in ['.olean','.olean.server','.olean.private','.ir','.ir.server','.ir.private'])}
for name in ['mathlib_mirror.json','mathlib_mirror_after.json']:
    mirror=json.loads((R/name).read_text(encoding='utf-8'))
    assert mirror['status']=='matched' and mirror['files']==expected_runtime
    assert mirror['target']==mirror_used['target']
    assert mirror['mathlib_revision']==manifest['mathlib_revision']
    assert mirror['artifact_receipt_sha256']==mirror_used['artifact_receipt_sha256']==hashlib.sha256((W/'MATHLIB_ARTIFACT_RECEIPT.json').read_bytes()).hexdigest()
runtime=json.loads((R/'runtime_mirror.json').read_text(encoding='utf-8'))
assert runtime['status']=='matched'
assert runtime['target_linux']=='/dev/shm/oxilean-sharp432-20261117'
runtime_after=json.loads((R/'runtime_mirror_after.json').read_text(encoding='utf-8'))
assert runtime_after['status']=='matched' and runtime_after['files']==runtime['files']
executable=json.loads((R/'executable_mirror.json').read_text(encoding='utf-8'))
executable_after=json.loads((R/'executable_mirror_after.json').read_text(encoding='utf-8'))
assert executable['status']==executable_after['status']=='matched'
assert executable['files']==executable_after['files']
parser=json.loads((R/'exporter_library_mirror.json').read_text(encoding='utf-8'))
parser_after=json.loads((R/'exporter_library_mirror_after.json').read_text(encoding='utf-8'))
assert parser['status']==parser_after['status']=='matched' and parser['files']==parser_after['files']
for name in ['extra_executable_mirror','previous_module_mirror']:
    before=json.loads((R/(name+'.json')).read_text())
    after=json.loads((R/(name+'_after.json')).read_text())
    assert before['status']==after['status']=='matched' and before['files']==after['files']
    for row in before['files']:
        assert sha_file(W/row['source'])==row['sha256']
frozen=json.loads((R/'source_mirror.json').read_text())
spatial=json.loads((R/'SPATIAL_SOURCE_REBUILD.json').read_text())
assert spatial['status']=='byte_identical' and spatial['lean']=='4.32.0-rc1'
assert spatial['source']=='MathCan/SpatialInterface.lean'
assert sha_file(W/'MathCan'/spatial['source'])==spatial['source_sha256']
assert sha_file(W/spatial['reference_olean'])==spatial['rebuilt_olean_sha256']==spatial['reference_olean_sha256']
prior_mirrors=json.loads((R/'previous_module_mirror.json').read_text())['files']
assert any(p['source']==spatial['reference_olean'] and p['sha256']==spatial['rebuilt_olean_sha256'] for p in prior_mirrors)
assert frozen['status']=='matched' and set(frozen['source_sha256'])==set(manifest['sources'].values())
for rel,digest in frozen['source_sha256'].items():assert sha_file(W/'MathCan'/rel)==digest
v = json.loads((R/'verdicts.json').read_text(encoding='utf-8'))
a = json.loads((R/'axiom-graph.json').read_text(encoding='utf-8'))
c = json.loads((R/'source_export_comparison.json').read_text(encoding='utf-8'))
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert v['input']['sha256'] == a['sha256'] == sha(R/'Lemmas.ndjson')
assert v['pins']['file_lean_version'] == '4.32.0-rc1'
assert v['pins']['file_lean_githash'] == 'b4812ae53eea93439ad5dce5a5c26591c31cb697'
assert a['structurally_closed'] and a['unambiguous_names'] and not a['unsafe_records']
assert len(v['decls']) == a['record_count'] == a['closure_record_count']
assert all(x['verdict'] == 'verified' for x in v['decls'])
assert v['totals']['verified'] == len(v['decls'])
assert v['totals']['unsupported'] == v['totals']['rejected'] == 0
assert c['status'] == 'matched'
assert c['constants_compared'] == sum(len(x['names']) for x in a['records'])
assert all(x['type_equal'] and x['value_equal_after_metadata_normalization']
           and x['level_parameters_equal'] for x in c['records'])
native = {}
log = (R/'axioms.log').read_text(encoding='utf-8')
assert 'error:' not in log and 'sorryAx' not in log
for name, axes in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.M):
    native[name] = sorted(x.strip() for x in axes.split(',') if x.strip())
for name in re.findall(r"^'([^']+)' does not depend on any axioms", log, re.M):
    native[name] = []
assert set(native) == set(manifest['theorems'])
nodes = {r['id']:r for r in a['records']}
owners = {name:r['id'] for r in a['records'] for name in r['display_names']}
byname = {r['name']:r for r in v['decls']}
roots = []
for name, axes in sorted(native.items()):
    assert byname[name]['verdict'] == 'verified'
    assert nodes[owners[name]]['kind'] == 'thm'
    todo = [owners[name]]
    seen = set()
    while todo:
        i = todo.pop()
        if i in seen: continue
        seen.add(i)
        todo.extend(nodes[i]['dependencies'])
    exported = sorted(n for i in seen if nodes[i]['kind']=='axiom' for n in nodes[i]['display_names'])
    assert exported == axes, (name, exported, axes)
    assert set(axes) <= {'propext', 'Quot.sound', 'Classical.choice'}
    roots.append({'name':name, 'verdict':'verified', 'native_lean':'accepted',
        'leanchecker':'accepted', 'axioms':axes, 'dependency_record_ids':sorted(seen),
        'dependency_records':len(seen), 'statement_and_proof_match':True})
source_hashes = {}
for module in manifest['modules']:
    name=module.rsplit('.',1)[-1]
    rel=manifest['sources'][name]
    p=W/'MathCan'/rel
    source=p.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b',source)
    blocks=re.findall(r'^namespace (MathCan\.\w+)\n(.*?)^end \1\s*$',source,re.M|re.S)
    assert len(blocks)==5
    declared={ns+'.'+n for ns,body in blocks for n in re.findall(r'^(?:theorem|lemma) (\w+)',body,re.M)}
    assert declared==set(native)
    assert (R/(name+'.compiled.sha256')).read_text(encoding='ascii').strip()==sha(p)
    assert (R/(name+'.checked.sha256')).read_text(encoding='ascii').strip()==sha(p)
    source_hashes[rel]=sha(p)
    for suffix in ['native.log','leanchecker.log']:
        assert 'error:' not in (R/(name+'_'+suffix)).read_text(encoding='utf-8')
    assert (R/(name+'_leanchecker.log')).read_text(encoding='utf-8').strip() == 'Accepted ApproximationMathlib.'+name
    assert ('Accepted ApproximationMathlib.'+name) in (R/'direct_kernel.log').read_text(encoding='utf-8')
for previous in ['Lemmas','Decoder','SpatialScalar','Transport','Common','Analytic','Synthesis','Sharp','Matrix']:
    prior=json.loads((W/'replay432'/previous/'ACCEPTANCE.json').read_text(encoding='utf-8'))
    assert prior['status']=='accepted'
    for rel,digest in prior['source_sha256'].items():
        source = W/'MathCan'/rel
        if not source.exists(): source = W/'MathCan/MathCan'/rel
        assert sha(source)==digest

result = {'status':'accepted', 'scope':'Intrinsic closed-cube Taylor jets, exact clipped-anchor serpentine schedule, bounded motion tags and decoded spatial approximation. Safe-phase aggregation and dense ReLU resource realization remain separate.',
    'export_sha256':sha(R/'Lemmas.ndjson'),
    'verdicts':{k:v['totals'][k] for k in ['verified','unsupported','rejected']},
    'constants_compared':c['constants_compared'], 'theorems':roots,
    'source_sha256':source_hashes,
    'mathlib_revision':manifest['mathlib_revision'],
    'runtime_artifact_source':'Hash-checked Linux-local mirror of the pinned cache',
    'native_kernel_method':'Unmodified pinned LeanChecker.replayFromImports API; stock CLI path scan omitted',
    'vendor_roots':[],
    'standard_axioms':sorted({ax for axes in native.values() for ax in axes})}
(R/'ACCEPTANCE.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
for rel, digest in source_hashes.items():
    (R/(Path(rel).stem+'.checked.sha256')).write_text(digest+'\n',encoding='ascii',newline='\n')
print(json.dumps({k:len(x) if k=='theorems' else x for k,x in result.items() if k!='source_sha256'},indent=2))
