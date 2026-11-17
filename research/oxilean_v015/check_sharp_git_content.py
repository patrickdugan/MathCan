from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
options=argparse.ArgumentParser();options.add_argument('--index',action='store_true');options=options.parse_args()
W=Path(__file__).resolve().parent;O=W.parent/'outputs'
A=json.loads((W/'replay432/Sharp/ACCEPTANCE.json').read_text());assert A['status']=='accepted'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(repo,*a):return subprocess.check_output(['git','-C',str(repo),*a])
def text(repo,*a):return git(repo,*a).decode().strip()
def blob(repo,path):return git(repo,'show',(':' if options.index else 'HEAD:')+path)
M=W/'MathCan';C=W/'Compactification-Theory'
for repo,branch,base in [(M,'research/quantized-jet-replay-20261115','1068f4f62f9b020353a2110e734f0dd680ff6754'),
 (C,'research/quantization-d-audit-20261115','e64226250f1e3ac181a619f3f1a367dac20b7c3a')]:
 assert text(repo,'branch','--show-current')==branch
 assert text(repo,'rev-parse','HEAD' if options.index else 'HEAD^')==base
 if not options.index:assert not text(repo,'status','--porcelain')
for rel,expected in A['source_sha256'].items():assert sha(blob(M,rel))==expected,rel
assert sha(blob(M,'MathCan/Hodge.lean'))=='6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5'
assert blob(M,'research/approximation_mathlib432/ApproximationMathlib.lean')==b'import ApproximationMathlib.MultivariateCapture\nimport ApproximationMathlib.SharpTransport\n'
prefix='research/oxilean_v015/';compressed=blob(M,prefix+'pinned432_sharp/Lemmas.ndjson.gz')
assert sha(gzip.decompress(compressed))==A['export_sha256']
assert json.loads(blob(M,prefix+'pinned432_sharp/ACCEPTANCE.json'))==A
report=blob(M,prefix+'SHARP_TRANSPORT_REPORT.md');assert report==blob(C,'research/quantization/SHARP_TRANSPORT_REPORT.md')
total=257+len(A['theorems'])
for repo,p in [(M,prefix+'FINAL_VALIDATION.json'),(C,'research/quantization/FINAL_VALIDATION.json')]:
 assert json.loads(blob(repo,p))['formal_theorems']==total
for prior in ['Lemmas','Decoder','SpatialScalar','Transport','Common','Analytic','Synthesis']:
 previous=json.loads((W/'replay432'/prior/'ACCEPTANCE.json').read_text())
 for rel,digest in previous['source_sha256'].items():
  actual=rel if (M/rel).exists() else 'MathCan/'+rel
  assert sha(blob(M,actual))==digest,actual
result={'status':'matched','location':'Git index' if options.index else 'Git HEAD','new_authored_roots':len(A['theorems']),
 'proof_source_sha256':A['source_sha256'],'export_sha256':A['export_sha256'],'gzip_blob_sha256':sha(compressed),
 'report_sha256':sha(report),'repository_heads':{p.name:text(p,'rev-parse','HEAD') for p in [M,C]}}
name='SHARP_GIT_INDEX_VERIFICATION.json' if options.index else 'SHARP_GIT_CONTENT_VERIFICATION.json'
(O/name).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in result.items() if k!='proof_source_sha256'},indent=2))
