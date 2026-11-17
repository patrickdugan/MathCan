from pathlib import Path
import argparse,gzip,hashlib,json,subprocess
options=argparse.ArgumentParser();options.add_argument('--index',action='store_true');options=options.parse_args()
W=Path(__file__).resolve().parent;O=W.parent/'outputs'
A=json.loads((W/'replay432/Cube/ACCEPTANCE.json').read_text());assert A['status']=='accepted'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(repo,*a):return subprocess.check_output(['git','-C',str(repo),*a])
def text(repo,*a):return git(repo,*a).decode().strip()
def blob(repo,path):return git(repo,'show',(':' if options.index else 'HEAD:')+path)
M=W/'MathCan';C=W/'Compactification-Theory'
for repo,branch,base in [(M,'research/quantized-jet-replay-20261115','3f99a6e90a2fbb5f5889998c48b1fe7d9a10660a'),
 (C,'research/quantization-d-audit-20261115','41829db0ae124516992e8ce9aa79707565e9b080')]:
 assert text(repo,'branch','--show-current')==branch
 assert text(repo,'rev-parse','HEAD' if options.index else 'HEAD^')==base
 if not options.index:assert not text(repo,'status','--porcelain')
for rel,expected in A['source_sha256'].items():assert sha(blob(M,rel))==expected,rel
assert sha(blob(M,'MathCan/Hodge.lean'))=='6874f33895ead142e867b331ec16730e8f827d521f17aa260850207de68332f5'
assert blob(M,'research/approximation_mathlib432/ApproximationMathlib.lean')==b'import ApproximationMathlib.MultivariateCapture\nimport ApproximationMathlib.SharpTransport\nimport ApproximationMathlib.WordTransport\nimport ApproximationMathlib.CubeApproximation\n'
prefix='research/oxilean_v015/';compressed=blob(M,prefix+'pinned432_cube/Lemmas.ndjson.gz')
assert sha(gzip.decompress(compressed))==A['export_sha256']
assert json.loads(blob(M,prefix+'pinned432_cube/ACCEPTANCE.json'))==A
report=blob(M,prefix+'CUBE_APPROXIMATION_REPORT.md');assert report==blob(C,'research/quantization/CUBE_APPROXIMATION_REPORT.md')
total=316+len(A['theorems'])
for repo,p in [(M,prefix+'FINAL_VALIDATION.json'),(C,'research/quantization/FINAL_VALIDATION.json')]:
 assert json.loads(blob(repo,p))['formal_theorems']==total
for prior in ['Lemmas','Decoder','SpatialScalar','Transport','Common','Analytic','Synthesis','Sharp','Matrix']:
 previous=json.loads((W/'replay432'/prior/'ACCEPTANCE.json').read_text())
 for rel,digest in previous['source_sha256'].items():
  actual=rel if (M/rel).exists() else 'MathCan/'+rel
  assert sha(blob(M,actual))==digest,actual
result={'status':'matched','location':'Git index' if options.index else 'Git HEAD','new_authored_roots':len(A['theorems']),
 'proof_source_sha256':A['source_sha256'],'export_sha256':A['export_sha256'],'gzip_blob_sha256':sha(compressed),
 'report_sha256':sha(report),'repository_heads':{p.name:text(p,'rev-parse','HEAD') for p in [M,C]}}
name='CUBE_GIT_INDEX_VERIFICATION.json' if options.index else 'CUBE_GIT_CONTENT_VERIFICATION.json'
(O/name).write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({k:v for k,v in result.items() if k!='proof_source_sha256'},indent=2))
