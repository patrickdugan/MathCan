"""DETFACT-10: measured scheduling on synthetic exponent execution workloads."""
import hashlib,json,math,pathlib,random,statistics,subprocess
from collections import defaultdict
import numpy as np
from sklearn.linear_model import Ridge
H=pathlib.Path(__file__).resolve().parent
A=[('explicit',8192,256),('stream',128,64),('stream',512,64),('stream',512,256),('stream',2048,256),('stream',2048,1024),('stream',8192,256),('stream',8192,1024)]
CAPS=[1024,2048,4096,16384,65536,262144]

def make(split,ks,ns,bs,ms,count,seed):
    rng=random.Random(seed);out=[]
    def odd(b):return rng.getrandbits(b-1)|(1<<(b-1))|1
    for i in range(count):
        k=ks[i%3];n=ns[(i//3+i)%3];b=bs[(i//2+i)%3];m=ms[(i//3+i//2)%3]
        N=odd(n//2)*odd(n-n//2);M=odd(m-3)<<3
        out.append(dict(id=f'{split}-{i:02}',split=split,k=k,n=str(N),m=str(M),nbits=N.bit_length(),mbits=M.bit_length(),batch=b))
    return out

def call(w,a,cap=0):
    mode,s,c=A[a];p=subprocess.run([str(H/'native_audit'),mode,*map(str,[w['k'],s,c,w['batch'],cap,w['n'],w['m']])],capture_output=True,text=True)
    if p.returncode==3:
        assert 'workspace budget exhausted' in p.stderr;return None
    if p.returncode:raise RuntimeError(p.stderr)
    r=json.loads(p.stdout);assert r['live_after_clear_bytes']==0;return r

def sig(r):return hashlib.sha256(json.dumps([r['s'],r['residues'],r['splits']],separators=(',',':')).encode()).hexdigest()

def ref(w):
    k=w['k'];n=int(w['n']);m=int(w['m']);f=bytearray(b'\1')*(k+1);f[:2]=b'\0\0'
    for p in range(2,math.isqrt(k)+1):
        if f[p]:f[p*p:k+1:p]=b'\0'*((k-p*p)//p+1)
    qs=[]
    for p in range(2,k+1):
        if f[p]:
            q=p
            while q<=k//p:q*=p
            qs.append(q)
    E=2*m*math.prod(qs);s=(E&-E).bit_length()-1;u=E>>s;rs=[];ss=[]
    for a in range(2,w['batch']+2):
        x=pow(a,u,n);rs.append(str(x));g=math.gcd(a,n);out=None
        if 1<g<n:out=[-1,str(g)]
        else:
            for j in range(s+1):
                g=math.gcd(x-1,n)
                if 1<g<n:out=[j,str(g)];break
                x=x*x%n
        ss.append(out)
    return sig(dict(s=s,residues=rs,splits=ss))

def sweep(ws):
    rows=[];checks=0
    for w in ws:
        samples=defaultdict(list);rng=random.Random(w['id']);expected=ref(w)
        for _ in range(3):
            order=list(range(len(A)));rng.shuffle(order)
            for a in order:
                r=call(w,a);assert sig(r)==expected,(w['id'],a);checks+=w['batch'];samples[a].append(r)
        for a,rs in sorted(samples.items()):
            rows.append(dict(id=w['id'],action=a,seconds=[r['seconds'] for r in rs],median=statistics.median(r['seconds'] for r in rs),payload=max(r['peak_payload_full_run_bytes'] for r in rs),payload_runs=[r['peak_payload_full_run_bytes'] for r in rs],rss=[r['peak_rss_kib'] for r in rs],hash=expected))
        print('measured',w['id'],flush=True)
    return rows,checks

def feat(w):return [math.log2(w[k]) for k in ('k','nbits','batch','mbits')]

def fit(train,cal,ws):
    models=[];margin=[]
    for a in range(len(A)):
        t=[r for r in train if r['action']==a];c=[r for r in cal if r['action']==a]
        m=Ridge(alpha=.5).fit([feat(ws[r['id']]) for r in t],[[math.log(r['median']),math.log(r['payload'])] for r in t]);models.append(m)
        ratios=[r['payload']/math.exp(m.predict([feat(ws[r['id']])])[0][1]) for r in c];margin.append(max(1.,max(ratios))*1.05)
    return models,margin

def choose(w,cap,models,margin):
    pred=[np.exp(m.predict([feat(w)])[0]).tolist() for m in models];ok=[a for a,(t,p) in enumerate(pred) if p*margin[a]<=cap]
    return min(ok,key=lambda a:(pred[a][0],a)) if ok else min(range(len(A)),key=lambda a:(pred[a][1]*margin[a],a))

def fixed(train,cap):
    d=defaultdict(dict)
    for r in train:d[r['id']][r['action']]=r
    def key(a):
        fail=0;reg=[]
        for rr in d.values():
            f=[r for r in rr.values() if r['payload']<=cap]
            if not f:continue
            if rr[a]['payload']>cap:fail+=1;continue
            reg.append(math.log(rr[a]['median']/min(r['median'] for r in f)))
        return fail,statistics.mean(reg) if reg else math.inf,a
    return min(range(len(A)),key=key)

def summary(rows):
    d={}
    for p in ['learned','fixed','smallest']:
        rr=[r for r in rows if r['policy']==p];f=[r for r in rr if r['oracle'] is not None];ok=[r for r in f if r['status']=='ok'];reg=[r['regret'] for r in ok]
        d[p]=dict(feasible_cases=len(f),success=len(ok),budget_aborts=sum(r['status']=='budget' for r in rr),unavoidable_aborts=sum(r['oracle'] is None and r['status']=='budget' for r in rr),median_regret=statistics.median(reg) if reg else None,geomean_regret=math.exp(statistics.mean(map(math.log,reg))) if reg else None,max_regret=max(reg) if reg else None,grid_best_hits=sum(r['action']==r['oracle'] for r in ok))
    return d

def main():
    subprocess.run(['gcc','-O3','-std=c11','-Wall','-Wextra','-Werror',str(H/'native_audit.c'),'-lgmp','-o',str(H/'native_audit')],check=True)
    tr=make('train',[8192,32768,98304],[60,96,160],[1,4,8],[32,96,256],18,410)
    ca=make('cal',[12288,49152,114688],[72,112,192],[3,5,10],[48,128,384],6,411)
    te=make('test',[16384,65536,131072],[80,128,224],[2,6,12],[64,160,512],12,412)
    ws={w['id']:w for w in tr+ca+te};train,n1=sweep(tr);cal,n2=sweep(ca);models,margin=fit(train,cal,ws);baseline={c:fixed(train,c) for c in CAPS}
    decisions=[dict(id=w['id'],cap=c,policy=p,action=a) for w in te for c in CAPS for p,a in [('learned',choose(w,c,models,margin)),('fixed',baseline[c]),('smallest',1)]]
    frozen=dict(configs=A,budgets=CAPS,models=[{'coef':m.coef_.tolist(),'intercept':m.intercept_.tolist(),'margin':g} for m,g in zip(models,margin)],fixed=baseline,decisions=decisions,train_ids=[w['id'] for w in tr],cal_ids=[w['id'] for w in ca],test_ids=[w['id'] for w in te])
    (H/'frozen_policy.json').write_text(json.dumps(frozen,indent=2)+'\n');print('frozen',flush=True)
    test,n3=sweep(te);lookup={(r['id'],r['action']):r for r in test};evals=[];executed={}
    for q in decisions:
        w=ws[q['id']];c=q['cap'];a=q['action'];row=lookup[(q['id'],a)];f=[r for r in test if r['id']==q['id'] and r['payload']<=c];best=min(f,key=lambda r:(r['median'],r['action'])) if f else None
        key=(w['id'],c,a)
        if key not in executed:executed[key]=call(w,a,c)
        r=executed[key];assert (r is not None)==(row['payload']<=c),(q,row,r)
        if r is not None:assert r['peak_payload_full_run_bytes']<=c and sig(r)==row['hash']
        evals.append({**q,'status':'ok' if r is not None else 'budget','oracle':best['action'] if best else None,'regret':row['median']/best['median'] if r is not None and best else None,'payload':r['peak_payload_full_run_bytes'] if r is not None else None})
    result=dict(schema='MATHCAN-DETFACT-10',repeats=3,workloads=tr+ca+te,train=train,calibration=cal,test=test,frozen_sha256=hashlib.sha256((H/'frozen_policy.json').read_bytes()).hexdigest(),native_residue_and_split_comparisons=n1+n2+n3,independent_python_bases=sum(w['batch'] for w in tr+ca+te),actual_capped_runs=len(executed),summary=summary(evals),evaluations=evals)
    (H/'policy_receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result['summary'],indent=2),flush=True)
if __name__=='__main__':main()
