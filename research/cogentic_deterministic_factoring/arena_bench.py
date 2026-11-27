"""DETFACT-12: exact workspace preflight and frozen-policy audit."""
import hashlib,json,math,pathlib,random,statistics,subprocess,time,sys
from collections import defaultdict
H=pathlib.Path(__file__).resolve().parent
A=[(32,16),(32,64),(128,64),(512,32),(512,64),(2048,64)]
CAPS=[256,512,768,1024,1536,3072,8192]
SPECS={'train':([256,1024,4096],[64,128,256],[1,4,8],[32,128,256],12,1201),'test':([768,3072,8192],[96,224,448],[2,6,12],[64,192,512],15,1202)}
def save(name,obj): (H/name).write_text(json.dumps(obj,indent=2,sort_keys=True)+'\n')
def load(name):return json.loads((H/name).read_text())
def sha(name):return hashlib.sha256((H/name).read_bytes()).hexdigest()
def make(split,spec):
    ks,ns,bs,es,n,seed=spec;rng=random.Random(seed);ls=[]
    for values in (ks,ns,bs,es):
        v=(values*((n+2)//3))[:n];rng.shuffle(v);ls.append(v)
    def odd(b):return rng.getrandbits(b-1)|(1<<(b-1))|1
    out=[]
    for i,(k,nb,b,eb) in enumerate(zip(*ls)):
        p=nb//3 if split=='test' and i%2 else nb//2
        N=odd(p)*odd(nb-p);M=odd(eb-4)<<4
        out.append(dict(id=f'{split}-{i:02}',k=k,n=format(N,'x'),m=format(M,'x'),nbits=N.bit_length(),target_nbits=nb,ebits=M.bit_length(),batch=b))
    for key,values in [('k',ks),('target_nbits',ns),('batch',bs),('ebits',es)]:assert {w[key] for w in out}==set(values)
    return out

def need(w,a):
    s,_=A[a];L=(len(w['n'])+7)//8;E=(len(w['m'])+7)//8;k=w['k']
    return 4*((w['batch']+8)*L+E+2)+math.isqrt(k)+1+min(s,(k-1)//2)
def run(w,a,cap=0):
    S,W=A[a];t=time.perf_counter_ns();p=subprocess.run([str(H/'arena_audit'),*map(str,[w['k'],S,W,w['batch'],cap,w['n'],w['m']])],capture_output=True,text=True);wall=(time.perf_counter_ns()-t)/1e9
    assert p.returncode in (0,3),(p.returncode,p.stderr,p.stdout,w,a)
    r=json.loads(p.stdout);q=need(w,a);assert r['required_bytes']==q
    if cap and q>cap:assert p.returncode==3 and r['allocated_bytes']==0 and r['status']=='unresolved'
    else:assert p.returncode==0 and r['allocated_bytes']==q and r['status']=='ok'
    return r,wall

def ref(w):
    N=int(w['n'],16);M=2*int(w['m'],16)*math.lcm(*range(1,w['k']+1));s=(M&-M).bit_length()-1;u=M>>s;rs=[];splits=[]
    for a in range(2,2+w['batch']):
        x=pow(a,u,N);rs.append(format(x,'x'));d=math.gcd(a,N);out=None
        if 1<d<N:out=[-1,format(d,'x')]
        else:
            for j in range(s+1):
                d=math.gcd(x-1,N)
                if 1<d<N:out=[j,format(d,'x')];break
                x=x*x%N
        splits.append(out)
    return [s,rs,splits]
def signature(r):return [r['s'],r['residues'],r['splits']]
def validate(r,expected):assert signature(r)==expected,(signature(r),expected)
def hash_sig(v):return hashlib.sha256(json.dumps(v,separators=(',',':')).encode()).hexdigest()
def edges():
    count=0;boundary=0
    for n in [3,15,45,2**32-5,2**64-59,2**96-17,2**127+123,2**128-159]:
        for k in [1,2,3,7,8,9,31,32,33,257]:
            m=(1 if k%3==0 else (2**130+15)<<5);w=dict(n=format(n,'x'),m=format(m,'x'),batch=5,k=k);v=ref(w)
            for a in [0,1,2,5]:
                r,_=run(w,a,need(w,a));validate(r,v);count+=w['batch'];boundary+=1
                bad,_=run(w,a,need(w,a)-1);assert bad['status']=='unresolved' and bad['allocated_bytes']==0;boundary+=1
    cases=[['9','32','64','1','0','f','0'],['9','32','64','1','0','10','1'],['9','32','65','1','0','f','1'],['9','32','64','1','0','0f','1'],['0','32','64','1','0','f','1']]
    for c in cases:
        p=subprocess.run([str(H/'arena_audit'),*c],capture_output=True);assert p.returncode==2
    return dict(residue_checks=count,split_checks=count,exact_cap_and_cap_minus_one_checks=boundary,invalid_input_checks=len(cases))
def sweep(ws):
    rows=[];checks=0
    for w in ws:
        v=ref(w);sig=hash_sig(v);rr=defaultdict(list);rng=random.Random(w['id'])
        for _ in range(3):
            order=list(range(len(A)));rng.shuffle(order)
            for a in order:
                r,wall=run(w,a);validate(r,v);checks+=w['batch'];rr[a].append((r,wall))
        for a,rs in sorted(rr.items()):
            r=rs[0][0];rows.append(dict(id=w['id'],action=a,bytes=need(w,a),kernel=[x['seconds'] for x,_ in rs],wall=[y for _,y in rs],median=statistics.median(y for _,y in rs),montgomery_multiplications=r['montgomery_multiplications'],pow_calls=r['pow_calls'],rss_kib=[x['peak_rss_kib'] for x,_ in rs],hash=sig))
        print('grid',w['id'],flush=True)
    return rows,checks
def rank(train,c):
    d=defaultdict(dict)
    for r in train:d[r['id']][r['action']]=r
    def key(a):
        fail=0;reg=[]
        for v in d.values():
            ok=[r for r in v.values() if r['bytes']<=c]
            if not ok:continue
            if v[a]['bytes']>c:fail+=1
            else:reg.append(math.log(v[a]['median']/min(r['median'] for r in ok)))
        return fail,statistics.mean(reg) if reg else math.inf,a
    return sorted(range(len(A)),key=key)
def choices(w,c,ranks):
    rr=ranks[str(c)];ok=[a for a in rr if need(w,a)<=c]
    smallest=min(ok,key=lambda a:(need(w,a),-A[a][1],a)) if ok else None
    return {'fixed':rr[0],'certified_rank':ok[0] if ok else None,'certified_minimum':smallest}
def main():
    phase=sys.argv[1]
    if phase=='train':
        subprocess.run(['gcc','-O3','-std=c11','-Wall','-Wextra','-Werror','-Wvla',str(H/'arena_audit.c'),'-o',str(H/'arena_audit')],check=True)
        train=make('train',SPECS['train']);test=make('test',SPECS['test'])
        protocol=dict(schema='DETFACT-12-protocol',actions=A,caps=CAPS,workloads={'train':train,'test':test},primary='certified_rank completes all grid-feasible cases, preflight abstains on all grid-infeasible, zero over-cap allocations, and exact output matches; compare fixed descriptively',timing='3 shuffled uncapped wall samples; 1 capped validation per unique selected action; no learning on test',seed=1203)
        save('protocol.json',protocol);print('protocol',sha('protocol.json'),flush=True)
        edge=edges();save('edges.json',edge);print('edges',edge,flush=True)
        t,n1=sweep(train);save('train.json',dict(rows=t,checks=n1))
        ranks={str(c):rank(t,c) for c in CAPS};decisions=[dict(id=w['id'],cap=c,choices=choices(w,c,ranks)) for w in test for c in CAPS]
        save('frozen.json',dict(ranks=ranks,decisions=decisions,protocol_sha256=sha('protocol.json')));print('frozen',sha('frozen.json'),flush=True)
    elif phase=='test':
        p=load('protocol.json');test=p['workloads']['test'];f=load('frozen.json');assert f['protocol_sha256']==sha('protocol.json')
        v,n2=sweep(test);save('test.json',dict(rows=v,checks=n2))
    elif phase=='finish':
        p=load('protocol.json');test=p['workloads']['test'];ws={w['id']:w for w in test};f=load('frozen.json');decisions=f['decisions'];tr=load('train.json');te=load('test.json');lookup={(r['id'],r['action']):r for r in te['rows']};evaluations=[];calls=0
        for d in decisions:
            w=ws[d['id']];c=d['cap'];ok=[lookup[w['id'],a] for a in range(len(A)) if need(w,a)<=c];best=min(ok,key=lambda r:(r['median'],r['action'])) if ok else None;done={}
            for policy,a in d['choices'].items():
                if a is None:status='preflight_unresolved';r=None;wall=None;reg=None
                else:
                    if a not in done:done[a]=run(w,a,c);calls+=1
                    r,wall=done[a];status=r['status'];reg=lookup[w['id'],a]['median']/best['median'] if status=='ok' and best else None
                    if status=='ok':assert hash_sig(signature(r))==lookup[w['id'],a]['hash']
                evaluations.append(dict(id=w['id'],cap=c,policy=policy,action=a,status=status,oracle=best['action'] if best else None,allocated=r['allocated_bytes'] if r else 0,regret=reg,capped_wall=wall))
        summary={}
        for policy in decisions[0]['choices']:
            rr=[r for r in evaluations if r['policy']==policy];feas=[r for r in rr if r['oracle'] is not None];good=[r for r in feas if r['status']=='ok'];reg=[r['regret'] for r in good]
            summary[policy]=dict(feasible=len(feas),completed=len(good),avoidable_failures=len(feas)-len(good),grid_infeasible=len(rr)-len(feas),preflight_abstentions=sum(r['status']=='preflight_unresolved' for r in rr),worker_budget_rejections=sum(r['status']=='unresolved' for r in rr),overcap_allocations=sum(r['allocated']>r['cap'] for r in rr),geomean_regret=math.exp(statistics.mean(map(math.log,reg))),max_regret=max(reg),grid_best_hits=sum(r['action']==r['oracle'] for r in good))
        q=summary['certified_rank'];passed=q['completed']==q['feasible'] and q['preflight_abstentions']==q['grid_infeasible'] and q['overcap_allocations']==0
        receipt=dict(schema='DETFACT-12',protocol_sha256=sha('protocol.json'),frozen_sha256=sha('frozen.json'),edges=load('edges.json'),grid_runs=(len(p['workloads']['train'])+len(test))*len(A)*3,grid_residue_checks=tr['checks']+te['checks'],grid_split_checks=tr['checks']+te['checks'],capped_runs=calls,summary=summary,primary_pass=passed,rank=f['ranks'],evaluations=evaluations)
        save('arena_receipt.json',receipt);print(json.dumps({k:receipt[k] for k in ['edges','grid_runs','grid_residue_checks','capped_runs','summary','primary_pass','rank']},indent=2),flush=True)
if __name__=='__main__':main()
