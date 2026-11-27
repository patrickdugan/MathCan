"""DETFACT-13: sanitizer and abstract-layout boundary audit."""
import json, math, pathlib, random, subprocess
from arena_bench import ref, signature
H=pathlib.Path(__file__).resolve().parent

def run():
    flags=['-std=c11','-Wall','-Wextra','-Werror','-Wvla']
    st=subprocess.run(['clang','--analyze',*flags,'-Xanalyzer','-analyzer-output=text',str(H/'arena_audit.c')],capture_output=True,text=True,check=True)
    assert not st.stderr.strip(),st.stderr
    subprocess.run(['clang','-O1','-g',*flags,'-fsanitize=address,undefined','-fno-sanitize-recover=all',str(H/'arena_audit.c'),'-o',str(H/'arena_sanitized')],check=True)
    rng=random.Random(1313);checks=boundaries=0
    def need(n,m,k,s,b):return 4*((b+8)*((n.bit_length()+31)//32)+(m.bit_length()+31)//32+2)+math.isqrt(k)+1+min(s,(k-1)//2)
    def call(n,m,k,s,w,b,c):
        p=subprocess.run([str(H/'arena_sanitized'),*map(str,[k,s,w,b,c]),format(n,'x'),format(m,'x')],capture_output=True,text=True)
        assert not p.stderr.strip(),p.stderr
        assert p.returncode in (0,3),(p.returncode,p.stdout);return json.loads(p.stdout),p.returncode
    for i in range(180):
        # Include exact limb boundaries and moduli near the radix.
        bits=[2,31,32,33,63,64,65,95,96,97,127,128,129,255,256,257,511,512,513,1024,4096][i%21]
        n=(1<<bits)-1 if i%3==0 else (1<<(bits-1))|rng.getrandbits(bits-1)|1
        if n<3:n=3
        eb=[1,31,32,33,63,64,65,129,257,513][i%10];m=(1<<(eb-1))|rng.getrandbits(eb-1)
        if i%7==0:m=1
        k=[1,2,3,7,8,9,31,32,33,63,64,65,127,128,129,257][i%16];s=[1,7,32,128,2048][i%5];w=[1,16,32,63,64][i%5];b=1+i%4
        c=need(n,m,k,s,b);r,code=call(n,m,k,s,w,b,c)
        assert code==0 and r['allocated_bytes']==c and signature(r)==ref(dict(n=format(n,'x'),m=format(m,'x'),k=k,batch=b));checks+=b
        bad,code=call(n,m,k,s,w,b,c-1);assert code==3 and bad['required_bytes']==c and bad['allocated_bytes']==0;boundaries+=2
    # Largest accepted input dimensions: preflight only, never launch huge arithmetic.
    n=m=(1<<4096)-1;k=s=10000000;b=128;c=need(n,m,k,s,b)
    r,code=call(n,m,k,s,64,b,c-1);assert code==3 and r['required_bytes']==c and r['allocated_bytes']==0;boundaries+=1
    receipt=dict(schema='DETFACT-13-safety',fixtures=180,residue_checks=checks,split_checks=checks,allocation_boundary_checks=boundaries,max_domain_preflight_bytes=c,static_analyzer_diagnostics=0,address_sanitizer_errors=0,undefined_behavior_sanitizer_errors=0,compiler=subprocess.check_output(['clang','--version'],text=True).splitlines()[0],seed=1313)
    (H/'safety_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':run()
