"""AHR-COMP-01: compact U(1) fields, spectral counting and CPU dynamics. Offline only."""
import argparse
import itertools as it
import json
import math
import platform
import time
from pathlib import Path
import numpy as np
from scipy.linalg import expm

SEED = 20261124
PRIMES = (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71)

def wrap(x): return (np.asarray(x)+np.pi)%(2*np.pi)-np.pi

def subs(s): return (t for k in range(len(s)+1) for t in it.combinations(s,k))

def supports(d,r): return (s for k in range(1,min(d,r+1)+1) for s in it.combinations(range(d),k))

def rank(d,r): return sum((s-1)*math.comb(d,s) for s in range(2,min(d,r+1)+1))

def full_rank(d): return (d-2)*2**(d-1)+1

def field(d,r,rng,canonical=False):
    a=[{} for _ in range(d)]
    for s in supports(d,r):
        for i in s:
            a[i][tuple(j for j in s if j!=i)]=0. if canonical and i==s[0] else float(rng.uniform(-1,1))
    return a

def face(a,i,j,bg):
    bg=set(bg)
    return sum(v for t,v in a[j].items() if i in t and set(t)-{i}<=bg)-sum(v for t,v in a[i].items() if j in t and set(t)-{j}<=bg)

def gauge_fix(a,r):
    b=[{} for _ in a]
    for s in supports(len(a),r):
        c=a[s[0]].get(s[1:],0.)
        for i in s:
            t=tuple(j for j in s if j!=i)
            b[i][t]=float(wrap(a[i].get(t,0.)-c))
    return b

def reconstruct(a,r):
    b=[{} for _ in a]; samples={}
    for s in supports(len(a),r):
        i=s[0]; b[i][s[1:]]=0.
        for j in s[1:]:
            t=tuple(k for k in s if k not in (i,j))
            samples[i,j,t]=float(wrap(face(a,i,j,t)))
            b[j][tuple(k for k in s if k!=j)]=float(wrap(sum((-1)**(len(t)-len(v))*samples[i,j,v] for v in subs(t))))
    return b,len(samples)

def mean_cos_pair(a,i,j):
    b=a[j].get((i,),0.)-a[i].get((j,),0.); z=np.exp(1j*b)
    for k in range(len(a)):
        if k not in (i,j):
            c=a[j].get(tuple(sorted((i,k))),0.)-a[i].get(tuple(sorted((j,k))),0.)
            z*=(1+np.exp(1j*c))/2
    return float(z.real)

def moment_deficit(a):
    # (Tr H_A^4 - Tr H_0^4)/2^d for J=1 and unchanged onsite energies.
    assert all(len(t)<=2 for aa in a for t in aa)
    return 2*sum(mean_cos_pair(a,i,j)-1 for i,j in it.combinations(range(len(a)),2))

def table(a,i):
    d=len(a); y=np.zeros(1<<(d-1))
    for t,v in a[i].items(): y[sum(1<<(j-(j>i)) for j in t)]+=v
    for k in range(d-1):
        n=1<<k; z=y.reshape(-1,2*n); z[:,n:]+=z[:,:n]
    return np.exp(1j*y).reshape(-1,1<<i)

def edge_tables(a): return [table(a,i) for i in range(len(a))]

def energies(d,detuning=True):
    e=np.zeros(1<<d)
    if detuning:
        for i,p in enumerate(PRIMES[:d]): e.reshape(-1,2,1<<i)[:,1,:]+=math.log(p)
    return e

def dense(a,detuning=True):
    d=len(a); n=1<<d; H=np.diag(energies(d,detuning)).astype(complex)
    for i,ph in enumerate(edge_tables(a)):
        low=np.arange(n).reshape(-1,2,1<<i)[:,0,:].ravel(); high=low+(1<<i)
        H[high,low]=ph.ravel(); H[low,high]=ph.ravel().conj()
    return H

def test_algebra():
    rng=np.random.default_rng(SEED); errors=[]; moment_errors=[]; gauges=[]
    for d,r in ((3,1),(5,2),(8,3),(12,2),(20,2)):
        a=field(d,r,rng); b,n=reconstruct(a,r); target=gauge_fix(a,r)
        err=max(abs(float(wrap(b[i][t]-v))) for i in range(d) for t,v in target[i].items())
        assert n==rank(d,r) and err<1e-10
        errors.append(dict(d=d,degree=r,independent=n,max_wrapped_error=err))
        copy=[x.copy() for x in a]
        for s in supports(d,r):
            c=float(rng.normal())
            for i in s: copy[i][tuple(j for j in s if j!=i)]+=c
        b2,_=reconstruct(copy,r)
        g=max(abs(float(wrap(b2[i][t]-v))) for i in range(d) for t,v in b[i].items())
        assert g<1e-10; gauges.append(g)
    for d in (3,4,5,6):
        a=field(d,2,rng); zero=[{} for _ in range(d)]
        observed=(np.trace(np.linalg.matrix_power(dense(a),4))-np.trace(np.linalg.matrix_power(dense(zero),4))).real/2**d
        err=abs(observed-moment_deficit(a)); assert err<1e-9
        for i,j in it.combinations(range(d),2):
            rem=[k for k in range(d) if k not in (i,j)]
            exhaustive=np.mean([np.cos(face(a,i,j,[k for k,bit in zip(rem,bits) if bit])) for bits in it.product((0,1),repeat=d-2)])
            assert abs(exhaustive-mean_cos_pair(a,i,j))<1e-12
        moment_errors.append(float(err))
    return dict(reconstruction=errors,max_gauge_error=max(gauges),moment_trials=len(moment_errors),max_moment_error=max(moment_errors))

def toggle(poly,t):
    t=frozenset(t)
    if t in poly: poly.remove(t)
    else: poly.add(t)

def count_gap(circuit,n):
    g=len(circuit); constraints=[]
    for j,(op,u,v) in enumerate(circuit):
        q={frozenset([n+j])}
        if op=='AND': toggle(q,[u,v])
        elif op=='XOR': toggle(q,[u]); toggle(q,[v])
        elif op=='NOT': toggle(q,[u]); toggle(q,[])
        else: raise ValueError(op)
        constraints.append(q)
    constraints.append({frozenset([n+g-1]),frozenset()})
    f=set()
    for j,q in enumerate(constraints):
        for term in q: toggle(f,set(term)|{n+g+j})
    assert max(map(len,f))<=3
    total_vars=n+2*g+1
    x=np.arange(1<<total_vars,dtype=np.uint64); parity=np.zeros(len(x),dtype=np.uint8)
    for t in f:
        mask=sum(1<<k for k in t); parity^=((x&mask)==mask).astype(np.uint8)
    gap=int(len(x)-2*int(parity.sum()))
    count=0
    for inp in it.product((0,1),repeat=n):
        wires=list(inp)
        for op,u,v in circuit:
            wires.append(wires[u]&wires[v] if op=='AND' else wires[u]^wires[v] if op=='XOR' else 1-wires[u])
        count+=wires[-1]
    assert gap==count*2**(g+1)
    normalized_gap=gap/2**total_vars
    a=[{} for _ in range(total_vars+2)]
    a[1]={tuple(sorted([0]+[k+2 for k in t])):math.pi for t in f}
    phases=table(a,1).ravel(); cos_mean=float(np.mean(phases[1::2].real))
    assert abs(cos_mean-normalized_gap)<1e-12
    return dict(inputs=n,gates=g,background_bits=total_vars,satisfying=count,integer_gap=gap,mean_cosine=cos_mean,normalized_pair_trace_deficit=2*(cos_mean-1))

def test_counting():
    rng=np.random.default_rng(SEED+1); cases=[]
    for _ in range(24):
        gates=[(str(rng.choice(['AND','XOR','NOT'])),int(rng.integers(0,3+j)),int(rng.integers(0,3+j))) for j in range(4)]
        cases.append(count_gap(gates,3))
    cases.append(count_gap([('AND',0,1),('AND',3,2)],3))
    cases.append(count_gap([('XOR',0,0),('NOT',3,0)],3))
    assert {0,1,8} <= {c['satisfying'] for c in cases}
    return cases

def evolve(tables,e,t,steps):
    d=len(tables); psi=np.zeros(len(e),complex); psi[0]=1
    delta=t/steps; de=np.exp(-.5j*delta*e)
    ch,sh=math.cos(delta/2),-1j*math.sin(delta/2)
    cf,sf=math.cos(delta),-1j*math.sin(delta)
    def hop(i,c,s):
        p=tables[i]; v=psi.reshape(-1,2,1<<i); lo=v[:,0,:].copy(); hi=v[:,1,:].copy()
        v[:,0,:]=c*lo+s*p.conj()*hi; v[:,1,:]=c*hi+s*p*lo
    for _ in range(steps):
        psi*=de
        for i in range(d-1): hop(i,ch,sh)
        hop(d-1,cf,sf)
        for i in range(d-2,-1,-1): hop(i,ch,sh)
        psi*=de
    return psi

def zero_return(d,t):
    a=np.log(PRIMES[:d]); w=np.sqrt(1+a*a/4)
    return float(np.prod(1-(np.sin(w*t)/w)**2))

def clifford(d): return [{(j,):math.pi for j in range(i)} for i in range(d)]

def clifford_gaussian_return(d,t,detuning=True):
    # Auxiliary parity mode: replace each physical Majorana g_a by i*g_aux*g_a.
    m=d+1; K=np.zeros((2*m,2*m)); G=np.zeros_like(K)
    for i in range(m): G[2*i,2*i+1]=-1; G[2*i+1,2*i]=1
    for i,p in enumerate(PRIMES[:d]):
        K[2*i,2*i+1]=math.log(p) if detuning else 0.
        K[2*i+1,2*i]=-K[2*i,2*i+1]
        K[2*d,2*i]=2.; K[2*i,2*d]=-2.
    R=expm(t*K); Gt=R@G@R.T
    sign,logdet=np.linalg.slogdet(np.eye(2*m)-G@Gt)
    return 0. if sign<=0 else float(np.clip(math.exp(.5*logdet-m*math.log(2)),0,1))

def gate_count(a):
    d=len(a); multiplicity=[2]*(d-1)+[1]
    return dict(hopping_factors=2*d-1,rx=2*d-1,diagonal_rz=2*d,
        controlled_rz_by_controls={str(k):sum(2*mult*sum(len(t)==k and abs(v)>1e-14 for t,v in aa.items()) for mult,aa in zip(multiplicity,a)) for k in range(3)})

def test_dynamics():
    rng=np.random.default_rng(SEED+2); out=[]; t=.7
    for d in (3,4,5,6):
        a=field(d,2,rng,True); e=energies(d); tabs=edge_tables(a); exact=expm(-1j*t*dense(a))[:,0]
        errs=[float(np.linalg.norm(evolve(tabs,e,t,s)-exact)) for s in (4,8,16)]
        assert errs[2]<.30*errs[1] and errs[1]<.30*errs[0]
        z=expm(-1j*t*dense([{} for _ in range(d)]))[0,0]
        assert abs(abs(z)**2-zero_return(d,t))<1e-12
        D=dense(clifford(d),False); assert np.max(abs(D@D-d*np.eye(1<<d)))<1e-12
        errors=[]
        for time_point in (.1,.7,1.6,2.):
            true=abs(expm(-1j*time_point*dense(clifford(d)))[0,0])**2
            errors.append(abs(true-clifford_gaussian_return(d,time_point)))
            assert abs(clifford_gaussian_return(d,time_point,False)-math.cos(time_point*math.sqrt(d))**2)<1e-10
        assert max(errors)<1e-10
        out.append(dict(d=d,state_l2_errors_steps_4_8_16=errs,clifford_return_no_detuning=math.cos(t*math.sqrt(d))**2,gaussian_dense_max_error=max(errors)))
    return out

def test_controlled_gates():
    # Assumption: tunable individual hopping generators and switchable/refocused detuning.
    I=np.eye(2); X=np.array([[0.,1.],[1.,0.]]); Z=np.diag([1.,-1.])
    # q0 target (least significant bit), q1 control; A_0=pi*x_1 gives Z_1 X_0.
    # The individual direction generator is obtained by selecting only that direction.
    Hx=np.kron(I,X); Hconditional=np.kron(Z,X)
    p=expm(-1j*np.pi/4*Hx)@expm(+1j*np.pi/4*Hconditional)
    control_phase=np.kron(np.diag([1.,1j]),I)
    cnot=np.eye(4,dtype=complex); cnot[2:,2:]=X
    error=float(np.max(abs(control_phase@p-cnot)))
    assert error<1e-12
    # Direct check of H_i(A)=D_i X_i D_i^dagger.
    a=[{():.3,(1,):.7,(1,2):-.4},{},{}]
    phi=table(a,0).ravel(); ph=np.angle(phi)
    DD=np.diag(np.stack([np.exp(-.5j*ph),np.exp(.5j*ph)],axis=-1).ravel())
    Xi=np.kron(np.eye(4),X)
    expected=np.zeros((8,8),complex)
    expected[np.arange(1,8,2),np.arange(0,8,2)]=phi
    expected[np.arange(0,8,2),np.arange(1,8,2)]=phi.conj()
    err2=float(np.max(abs(DD@Xi@DD.conj().T-expected)))
    assert err2<1e-12
    return dict(cnot_error=error,phase_conjugation_error=err2,scope='switchable generators; not static Hamiltonian universality')

def benchmark(max_d):
    rows=[]; t=.7
    for d in (3,5,8,12,16,20):
        if d>max_d: continue
        rng=np.random.default_rng(SEED+10+d); e=energies(d)
        rows.append(dict(d=d,arm='zero_flux_exact_product',return_p=zero_return(d,t),algorithm='analytic O(d)',steps=0))
        a1=field(d,1,rng,True); a2=field(d,2,rng,True)
        for i in range(d):
            for term in a2[i]:
                if len(term)==2: a2[i][term]/=math.sqrt(max(1,d-2))
        start=time.perf_counter(); pg=clifford_gaussian_return(d,t); sec=time.perf_counter()-start
        rows.append(dict(d=d,arm='pi_flux_detuned_gaussian',algorithm='parity-extended Majorana covariance O(d^3)',return_p=pg,evolve_s=sec,steps=0,covariance_matrix_dimension=2*(d+1)))
        arms=[('affine',a1),('quadratic',a2),('pi_flux_detuned',clifford(d))]
        for name,a in arms:
            start=time.perf_counter(); tabs=edge_tables(a); setup=time.perf_counter()-start
            start=time.perf_counter(); psi=evolve(tabs,e,t,8); elapsed=time.perf_counter()-start
            norm=float(np.vdot(psi,psi).real); assert abs(norm-1)<2e-12
            p=abs(psi)**2
            row=dict(d=d,arm=name,algorithm='CPU statevector Strang product',steps=8,t=t,
                     return_p=float(p[0]),norm=norm,participation=float(1/np.sum(p*p)),
                     state_bytes=psi.nbytes,edge_table_bytes=sum(x.nbytes for x in tabs),setup_s=setup,evolve_s=elapsed,
                     logical_gates_per_step=gate_count(a),closed_form_curvature_density=moment_deficit(a)/(2*math.comb(d,2)))
            if name=='pi_flux_detuned': row['return_error_vs_gaussian']=abs(row['return_p']-pg)
            if d<=12 or (d==20 and name=='quadratic'):
                other=evolve(tabs,e,t,4); row['step_4_to_8_state_l2']=float(np.linalg.norm(psi-other))
                del other
            if d==20 and name=='quadratic':
                other=evolve(tabs,e,t,16); row['step_8_to_16_state_l2']=float(np.linalg.norm(psi-other)); row['return_p_steps16']=float(abs(other[0])**2)
                del other
            rows.append(row)
            if name=='quadratic' and d<=12:
                shuffled=[rng.permutation(x.ravel()).reshape(x.shape) for x in tabs]
                start=time.perf_counter(); q=evolve(shuffled,e,t,8); sec=time.perf_counter()-start
                assert abs(float(np.vdot(q,q).real)-1)<2e-12
                rows.append(dict(d=d,arm='shuffled_edge_matched_marginals',algorithm='CPU statevector Strang product',steps=8,t=t,return_p=float(abs(q[0])**2),evolve_s=sec,state_bytes=q.nbytes,explicit_edge_angles=d*2**(d-1)))
                del q,shuffled
            del psi,p,tabs
    return rows

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--max-qubits',type=int,choices=(8,12,16,20),default=12); p.add_argument('--output',type=Path,default=Path(__file__).with_name('validation.json')); args=p.parse_args()
    report=dict(status='PASS',scope='mathematical checks and approximate CPU circuits only; no hardware or complexity separation',seed=SEED,environment=dict(python=platform.python_version(),numpy=np.__version__),algebra=test_algebra(),counting=test_counting(),dynamics_checks=test_dynamics(),controlled_gate_checks=test_controlled_gates(),scaling=benchmark(args.max_qubits),parameter_table=[dict(d=d,full=full_rank(d),affine=rank(d,1),quadratic=rank(d,2),quartic=rank(d,4)) for d in (3,5,10,15,20)])
    args.output.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n'); print(json.dumps({k:report[k] for k in ('status','algebra','dynamics_checks','parameter_table')},indent=2)); print('scaling rows',len(report['scaling']))

if __name__=='__main__': main()
