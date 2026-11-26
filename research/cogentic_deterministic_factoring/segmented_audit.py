"""DETFACT-08: synthetic exponent execution audit."""
import hashlib, json, math, resource, subprocess, sys, time
from array import array


def odd(m):
    if m < 1: raise ValueError('exponent')
    return m >> ((m & -m).bit_length()-1)


def segments(k, s, start=3):
    root=math.isqrt(k)
    small=bytearray([1])*(root+1)
    small[0]=0
    if root>=1: small[1]=0
    for p in range(2,math.isqrt(root)+1):
        if small[p]:
            for j in range(p*p,root+1,p): small[j]=0
    ps=array('Q',(p for p in range(3,root+1,2) if small[p]))
    base=len(ps)*ps.itemsize
    setup=len(small)+base
    del small
    for lo in range(start,k+1,2*s):
        count=min(s,(k-lo)//2+1); hi=lo+2*(count-1)
        mark=bytearray([1])*count; strikes=0
        for p in ps:
            if p*p>hi: break
            first=max(p*p,((lo+p-1)//p)*p)
            if first%2==0: first+=p
            for j in range((first-lo)//2,count,p):
                mark[j]=0; strikes+=1
        yield lo+2*s,lo,mark,max(setup,base+count),strikes
        del mark


def powers(k,lo,mark):
    for i,v in enumerate(mark):
        if v:
            p=lo+2*i; q=p
            while q<=k//p: q*=p
            yield q


def digest(x):
    return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()


def checkpoint(params,lo,xs):
    body={'params':params,'next_lo':lo,'residues':xs}
    return {'body':body,'sha256':digest(body)}


def execute(n,m,k,s,w,bases,mode='stream',resume=None,stop=None):
    if n<2 or m<1 or k<1 or s<1 or w<1 or not bases: raise ValueError('domain')
    params=[n,m,k,s,w,list(bases)]; lo=3
    xs=[pow(a,odd(m),n) for a in bases] if mode=='stream' else []
    if resume is not None:
        b=resume['body']
        if mode!='stream' or digest(b)!=resume['sha256'] or b['params']!=params: raise ValueError('checkpoint')
        lo,xs=b['next_lo'],list(b['residues'])
        if lo<3 or (lo-3)%(2*s) or lo>max(3,k+2*s) or len(xs)!=len(bases) or any(not 0<=x<n for x in xs): raise ValueError('shape')
    st={'sieve_payload_bytes':0,'max_exponent_bits':odd(m).bit_length(),'prime_powers':0,'mark_writes':0,'segments':0,'pow_calls':len(bases) if mode=='stream' else 0}
    slots=[]
    for nxt,begin,mark,space,strikes in segments(k,s,lo):
        st['sieve_payload_bytes']=max(st['sieve_payload_bytes'],space);st['mark_writes']+=strikes;st['segments']+=1
        chunk=1
        def flush(q):
            nonlocal xs
            if q!=1:
                xs=[pow(x,q,n) for x in xs];st['pow_calls']+=len(xs);st['max_exponent_bits']=max(st['max_exponent_bits'],q.bit_length())
        for q in powers(k,begin,mark):
            st['prime_powers']+=1
            if mode=='explicit':
                i=0
                while i<len(slots) and slots[i] is not None:
                    q*=slots[i];slots[i]=None;i+=1
                if i==len(slots):slots.append(q)
                else:slots[i]=q
            else:
                if q.bit_length()>w:flush(chunk);chunk=1;flush(q);continue
                if chunk!=1 and chunk.bit_length()+q.bit_length()>w:flush(chunk);chunk=1
                chunk*=q
        if mode=='stream':flush(chunk)
        lo=nxt;del mark
        if stop is not None and st['segments']>=stop: return xs,st,checkpoint(params,lo,xs)
    if mode=='explicit':
        u=odd(m)*math.prod(q for q in slots if q is not None)
        xs=[pow(a,u,n) for a in bases];st['max_exponent_bits']=u.bit_length();st['pow_calls']=len(bases)
    return xs,st,checkpoint(params,lo,xs)


def checks():
    count=0
    for k in [1,2,3,7,8,9,31,32,33,63,64,65,127,128,129,257]:
        u=odd(6*math.lcm(*range(1,k+1)))
        for s in [1,3,16,64]:
            for w in [1,16,64]:
                args=[45,6,k,s,w,[0,1,2,3,5,44,45]]
                assert execute(*args)[0]==[pow(a,u,45) for a in args[-1]]==execute(*args,mode='explicit')[0]
                count+=len(args[-1])
    p=[77,10,257,7,64,[0,2,3,7,11]]
    want=execute(*p)[0];_,_,cp=execute(*p,stop=3)
    assert execute(*p,resume=cp)[0]==want
    bad=json.loads(json.dumps(cp));bad['body']['residues'][1]^=1
    try:execute(*p,resume=bad)
    except ValueError:pass
    else:raise AssertionError('corrupt checkpoint accepted')
    bad['sha256']=digest(bad['body']);execute(*p,resume=bad)
    assert execute(*p,stop=3)[2]!=bad
    return {'edge_residue_checks':count,'checkpoint_resume':True,'checksum_mutation_rejected':True,'forged_prefix_replay_rejected':True}


def worker(mode,k,s,w,b):
    n=1000000007*1000000009;m=2**9*3**5*5*7*11;bases=list(range(2,2+b));t=time.perf_counter()
    xs,st,_=execute(n,m,k,s,w,bases,mode=mode)
    return {'mode':mode,'k':k,'span':s,'width':w,'batch':b,'seconds':round(time.perf_counter()-t,6),'peak_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'result_sha256':digest(xs),**st}


def main():
    if len(sys.argv)>1:
        print(json.dumps(worker(sys.argv[1],*map(int,sys.argv[2:]))));return
    r={'schema':'MATHCAN-DETFACT-AUDIT-08','runtime':sys.version.split()[0],'checks':checks(),'benchmarks':[]}
    for k in [16384,65536]:
        for mode,s,w in [('explicit',8192,256),('stream',512,64),('stream',8192,256),('stream',16384,256)]:
            cmd=[sys.executable,__file__,mode,str(k),str(s),str(w),'4']
            rows=[json.loads(subprocess.check_output(cmd,text=True)) for _ in range(3)]
            row=rows[1].copy();row['seconds']=sorted(x['seconds'] for x in rows)[1];row['peak_rss_kib']=max(x['peak_rss_kib'] for x in rows);row['seconds_runs']=[x['seconds'] for x in rows];row['rss_runs']=[x['peak_rss_kib'] for x in rows];r['benchmarks'].append(row)
        assert len({x['result_sha256'] for x in r['benchmarks'] if x['k']==k})==1
    print(json.dumps(r,indent=2))


if __name__=='__main__':main()
