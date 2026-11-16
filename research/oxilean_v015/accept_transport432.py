from collections import Counter
from pathlib import Path
import hashlib
import json
import re
import os

W = Path(os.environ.get('CAMPAIGN_WORK', Path(__file__).resolve().parent)).resolve()
R = W/'replay432/Transport'
manifest = json.loads((R/'manifest.json').read_text(encoding='utf-8'))
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
    p = W/'MathCan'/Path(*module.split('.')).with_suffix('.lean')
    source = p.read_text(encoding='utf-8')
    assert not re.search(r'\b(sorry|admit|axiom|unsafe)\b', source)
    declared = {module+'.'+n for n in re.findall(r'^theorem (\w+)', source, re.M)}
    assert declared == {n for n in native if n.startswith(module+'.')}
    assert (R/(p.stem+'.checked.sha256')).read_text(encoding='ascii').strip() == sha(p)
    source_hashes[str(p.relative_to(W/'MathCan')).replace('\\','/')] = sha(p)
for module in manifest['modules']:
    name=module.rsplit('.',1)[-1]
    for suffix in ['native.log','leanchecker.log']:
        assert 'error:' not in (R/(name+'_'+suffix)).read_text(encoding='utf-8')
for previous in ['Decoder','SpatialScalar']:
    prior=json.loads((W/'replay432'/previous/'ACCEPTANCE.json').read_text(encoding='utf-8'))
    assert prior['status']=='accepted'
    for rel,digest in prior['source_sha256'].items(): assert sha(W/'MathCan'/rel)==digest

result = {'status':'accepted', 'scope':'Hamming amplitude selector, finite polynomial Taylor transport and concrete scheduled spatial capture; analytic remainder and dense compiler remain open',
    'export_sha256':sha(R/'Lemmas.ndjson'),
    'verdicts':{k:v['totals'][k] for k in ['verified','unsupported','rejected']},
    'constants_compared':c['constants_compared'], 'theorems':roots,
    'source_sha256':source_hashes,
    'standard_axioms':sorted({ax for axes in native.values() for ax in axes})}
(R/'ACCEPTANCE.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
for rel, digest in source_hashes.items():
    (R/(Path(rel).stem+'.checked.sha256')).write_text(digest+'\n',encoding='ascii',newline='\n')
print(json.dumps({k:len(x) if k=='theorems' else x for k,x in result.items() if k!='source_sha256'},indent=2))
