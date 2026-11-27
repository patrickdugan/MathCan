"""Calibrate on one K; evaluate frozen policies on disjoint K and batches."""
import hashlib, json, math, pathlib, platform, statistics, subprocess
HERE=pathlib.Path(__file__).resolve().parent
BIN=HERE/'native_audit'
N=1000000007*1000000009
M=2**9*3**5*5*7*11
CONFIGS=[('explicit',8192,256),('stream',512,64),('stream',512,256),('stream',2048,256),('stream',8192,256),('stream',8192,1024)]
BUDGETS=[4096,16384]
def cmd(mode,k,s,w,b,budget=0,n=N,m=M):
    return [str(BIN),mode,*map(str,[k,s,w,b,budget,n,m])]
def run(*a,**kw):
    return json.loads(subprocess.check_output(cmd(*a,**kw),text=True))
def reference(n,m,k,b):
    e=2*m*math.lcm(*range(1,k+1));s=(e&-e).bit_length()-1;u=e>>s
    rs=[pow(a,u,n) for a in range(2,b+2)];ss=[]
    for a,x in zip(range(2,b+2),rs):
        g=math.gcd(a,n);out=None
        if 1<g<n:out=[-1,str(g)]
        else:
            for j in range(s+1):
                g=math.gcd(x-1,n)
                if 1<g<n:out=[j,str(g)];break
                x=x*x%n
        ss.append(out)
    return s,list(map(str,rs)),ss
def check():
    fixtures=0
    for n,m in [(15,1),(45,12),(77,60),(211*251,math.lcm(210,250)),(41*41*43,math.lcm(40,42)),(3,1)]:
        for k in [1,2,3,7,8,9,31,32,33,127,128,129,257]:
            ref=reference(n,m,k,8)
            for mode,s,w in [('explicit',32,64),('stream',1,1),('stream',7,16),('stream',64,256)]:
                r=run(mode,k,s,w,8,n=n,m=m)
                assert (r['s'],r['residues'],r['splits'])==ref,(n,m,k,mode,s,w,r,ref)
                assert r['live_after_clear_bytes']==0
                fixtures+=1
    for args,code in [(cmd('stream',0,512,64,4),2),(cmd('stream',32,512,64,4,m=0),2),(cmd('stream',65536,512,64,4,budget=128),3)]:
        r=subprocess.run(args,capture_output=True,text=True);assert r.returncode==code,(r.returncode,r.stderr)
    return {'native_fixtures':fixtures,'independent_python_residue_checks':8*fixtures,'split_result_checks':8*fixtures,'invalid_domain_checks':2,'budget_rejection_checks':1}
def sweep(k,b,configs=CONFIGS,repeats=3):
    rows=[];ref=None
    for mode,s,w in configs:
        rr=[run(mode,k,s,w,b) for _ in range(repeats)]
        for r in rr:
            out=(r['s'],r['residues'],r['splits'])
            if ref is None:ref=out
            assert out==ref and r['live_after_clear_bytes']==0
        row={key:rr[0][key] for key in ('max_exponent_bits','pow_calls','prime_powers','mark_writes','segments','s','allocation_events')}
        row.update(mode=mode,k=k,batch=b,span=s,width=w,seconds_runs=[r['seconds'] for r in rr],median_seconds=statistics.median(r['seconds'] for r in rr),peak_payload_bytes=max(r['peak_payload_full_run_bytes'] for r in rr),gmp_peak_bytes=max(r['gmp_peak_bytes'] for r in rr),own_peak_bytes=max(r['own_peak_bytes'] for r in rr),rss_kib_runs=[r['peak_rss_kib'] for r in rr],output_sha256=hashlib.sha256(json.dumps(ref,separators=(',',':')).encode()).hexdigest())
        rows.append(row)
    return rows
def select(rows,budget):
    viable=[r for r in rows if r['peak_payload_bytes']<=budget]
    return min(viable,key=lambda r:(r['median_seconds'],r['peak_payload_bytes'],r['mode'],r['span'],r['width'])) if viable else None
def main():
    subprocess.run(['gcc','-O3','-std=c11','-Wall','-Wextra','-Werror',str(HERE/'native_audit.c'),'-lgmp','-o',str(BIN)],check=True)
    r={'schema':'MATHCAN-DETFACT-AUDIT-09','environment':{'platform':platform.platform(),'python':platform.python_version(),'compiler':subprocess.check_output(['gcc','--version'],text=True).splitlines()[0],'gmp':subprocess.check_output(['pkg-config','--modversion','gmp'],text=True).strip()},'policy':'lowest calibration median time within full-run tracked live payload cap; tie by payload, mode, span, width; freeze before held-out K','checks':check(),'calibration':sweep(65536,4),'holdout':[],'batch_sweep':[],'policy_evaluations':[]}
    chosen={budget:select(r['calibration'],budget) for budget in BUDGETS}
    r['chosen']={str(b):{k:c[k] for k in ('mode','span','width')} if c else None for b,c in chosen.items()}
    (HERE/'calibration_receipt.json').write_text(json.dumps({'calibration':r['calibration'],'chosen':r['chosen'],'policy':r['policy']},indent=2)+'\n')
    for k in [262144,1048576]:
        rows=sweep(k,4);r['holdout']+=rows
        for budget,c in chosen.items():
            if c is None:continue
            args=(c['mode'],k,c['span'],c['width'],4)
            x=subprocess.run(cmd(*args,budget=budget),capture_output=True,text=True)
            assert x.returncode in (0,3),x.stderr
            best=select(rows,budget);row=next(z for z in rows if (z['mode'],z['span'],z['width'])==(c['mode'],c['span'],c['width']))
            assert (x.returncode==0)==(row['peak_payload_bytes']<=budget)
            r['policy_evaluations'].append({'k':k,'budget':budget,'status':'within cap' if x.returncode==0 else 'budget exhausted','selected_median_seconds':row['median_seconds'],'selected_peak_payload_bytes':row['peak_payload_bytes'],'best_feasible_median_seconds':best['median_seconds'] if best else None,'selected_to_best_ratio':row['median_seconds']/best['median_seconds'] if best and x.returncode==0 else None})
    for b in [1,16]:r['batch_sweep']+=sweep(262144,b,[CONFIGS[0],CONFIGS[2],CONFIGS[4]])
    (HERE/'native_receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r['checks']));print(json.dumps(r['chosen']));print(json.dumps(r['policy_evaluations']))
    for row in r['calibration']+r['holdout']+r['batch_sweep']:
        print(row['k'],row['batch'],row['mode'],row['span'],row['width'],round(row['median_seconds']*1000,3),row['peak_payload_bytes'],row['max_exponent_bits'],row['rss_kib_runs'])
if __name__=='__main__':main()
