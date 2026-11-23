"""Sparse pi-flux defects: exact algebra, Gaussian bounds and a three-qubit witness.
Offline only. No QPU calls. All angles radians, J=1 unless stated.
"""
import itertools as it
import json
import math
from pathlib import Path
import numpy as np
from scipy.linalg import expm

PRIMES=(2,3,5,7,11,13,17,19)
SEED=20261124
I=np.eye(2,dtype=complex)
X=np.array([[0,1],[1,0]],complex)
Y=np.array([[0,-1j],[1j,0]],complex)
Z=np.diag([1,-1]).astype(complex)

def op(d,sites):
    out=np.ones((1,1),complex)
    for k in reversed(range(d)):out=np.kron(out,sites.get(k,I))
    return out

def majoranas(d):
    return [op(d,{**{k:Z for k in range(i)},i:P}) for i in range(d) for P in (X,Y)]

def lift(d):
    E=np.zeros((1<<(d+1),1<<d),complex)
    for x in range(1<<d):
        b=x.bit_count()%2
        E[x|(b<<d),x]=(-1j if b else 1.)
    return E

def pieces(d,defects,detuning=True):
    """At most one extra spectator per hopping direction: i -> (j,theta)."""
    g=majoranas(d); G=np.zeros_like(g[0]); qs=[]
    for i in range(d):
        if detuning:G+=math.log(PRIMES[i])*(np.eye(1<<d)-op(d,{i:Z}))/2
        if i not in defects:G+=g[2*i];continue
        j,t=defects[i]; assert i!=j
        a=(1+math.cos(t))/2; b=math.sin(t)/2
        c=(1-math.cos(t))/2; s=-math.sin(t)/2
        G+=a*g[2*i]+b*g[2*i+1]
        w=math.hypot(c,s)
        if w>1e-15:qs.append((w,op(d,{j:Z})@(c*g[2*i]+s*g[2*i+1])/w))
    return G,qs

def direct(d,defects,detuning=True):
    N=1<<d; H=np.zeros((N,N),complex)
    for x in range(N):
        if detuning:H[x,x]=sum(math.log(PRIMES[i]) for i in range(d) if (x>>i)&1)
        for i in range(d):
            if (x>>i)&1:continue
            phase=math.pi*(x&((1<<i)-1)).bit_count()
            if i in defects:
                j,th=defects[i];phase+=th*((x>>j)&1)
            y=x|(1<<i);H[y,x]=np.exp(1j*phase);H[x,y]=H[y,x].conjugate()
    return H

def audit():
    rng=np.random.default_rng(SEED);err=[];lift_err=[];gate_err=[]
    for d in (3,4,5):
        E=lift(d);g=majoranas(d);h=majoranas(d+1);star=h[2*d]
        for a in range(2*d):
            lift_err.append(float(np.max(abs(E.conj().T@(1j*star@h[a])@E-g[a]))))
        for _ in range(4):
            defects={i:((i+1)%d,float(rng.uniform(-np.pi,np.pi))) for i in rng.choice(d,2,replace=False).tolist()}
            G,qs=pieces(d,defects)
            H=G+sum(w*Q for w,Q in qs)
            err.append(float(np.max(abs(H-direct(d,defects)))))
            for w,Q in qs:
                assert np.max(abs(Q@Q-np.eye(1<<d)))<1e-12
                a=.37*w
                gate_err.append(float(np.max(abs(expm(-1j*a*Q)-(np.cos(a)*np.eye(1<<d)-1j*np.sin(a)*Q)))))
            assert abs(sum(w for w,Q in qs)-sum(abs(np.sin(t/2)) for j,t in defects.values()))<1e-12
    assert max(err+lift_err+gate_err)<1e-12
    return dict(matrix_error=max(err),parity_lift_error=max(lift_err),branch_identity_error=max(gate_err),fixtures=len(err))

# S is the signed complement bilinear, in the *original* logical basis.
S=np.zeros((8,8))
for u,v,s in ((0,7,1),(3,4,-1),(5,2,1),(1,6,-1)):S[u,v]=S[v,u]=s
assert np.array_equal(S@S,np.eye(8))

def concurrence(psi):
    return float(np.clip(abs(psi.T@S@psi),0,1))

def gaussian_fidelity_bound(psi):
    C=concurrence(psi)
    return (1+np.sqrt(max(0,1-C*C)))/2

def state_scan(H,times):
    lam,U=np.linalg.eigh(H)
    return (np.exp(-1j*np.asarray(times)[:,None]*lam)*U[0,:].conj())@U.T

def witness():
    tlist=np.array([.04,.02,.01])
    rows=[]
    for theta in (.4,np.pi/2,np.pi,-np.pi/2):
        psi=state_scan(direct(3,{0:(1,theta)}),tlist)
        # Signed bilinear in logical basis: psi^T S psi/2 = -i*(e^{i theta}-1)*t^3/3 + O(t^4).
        lead=-1j*(np.exp(1j*theta)-1)/3
        # Check the coefficient directly; absolute phase convention is fixed by |000>.
        coeff=np.array([p.T@S@p/2 for p in psi])/tlist**3
        errors=abs(coeff-lead)
        assert errors[-1]<.06 and errors[-1]<errors[0],(theta,coeff,lead)
        rows.append(dict(theta=float(theta),coefficient=[lead.real,lead.imag],relative_error_at_001=float(errors[-1]/abs(lead))))
    times=np.arange(.025,4.001,.025)
    base=state_scan(direct(3,{}),times)
    assert max(map(concurrence,base))<1e-12
    candidates=[]
    for theta in (np.pi/4,np.pi/2,3*np.pi/4,np.pi):
        psi=state_scan(direct(3,{0:(1,theta)}),times)
        cs=np.array(list(map(concurrence,psi))); k=int(np.argmax(cs)); target=psi[k]
        Fg=float(gaussian_fidelity_bound(target))
        # Check maximum is attained among all isotropic vectors using an explicit real structure.
        # Takagi S=Q diag(sign) Q^T; M^T S M=I.
        vals,Q=np.linalg.eigh(S);M=Q@np.diag(np.where(vals>0,1.,1j))
        z=M.conj().T@target; z=z*np.exp(-.5j*np.angle(z.T@z)); a=z.real; b=z.imag
        if np.linalg.norm(b)>1e-10:
            ph=M@(a/np.linalg.norm(a)+1j*b/np.linalg.norm(b))/np.sqrt(2)
            assert concurrence(ph)<1e-10 and abs(abs(np.vdot(ph,target))**2-Fg)<1e-10
        # Global depolarization on the logical eight-dimensional code: rho=(1-p)|psi><psi|+p I/8.
        noise_threshold=(1-Fg)/(1-1/8)
        candidates.append(dict(theta=float(theta),time=float(times[k]),C=float(cs[k]),convex_gaussian_fidelity_bound=Fg,
            global_depolarization_threshold=float(noise_threshold),return_p=float(abs(target[0])**2),
            target_amplitudes=[[float(x.real),float(x.imag)] for x in target]))
    best=max(candidates,key=lambda r:r['C'])
    # Same total depolarization applied to Gaussian control: target-specific fidelity certificate stays valid.
    return dict(short_time=rows,zero_defect_max_C=max(map(concurrence,base)),time_grid=[.025,4.,.025],candidates=candidates,selected=best)

def measurement_design(best):
    """Pauli-projector fidelity witness on 27 product-basis settings."""
    psi=np.array([complex(*a) for a in best['target_amplitudes']]); d=3;N=8
    P={'I':I,'X':X,'Y':Y,'Z':Z}
    rotations={a:np.linalg.eigh(P[a])[1] for a in 'XYZ'}
    axes=list(it.product('XYZ',repeat=d));groups={a:[] for a in axes}
    identity=1/N
    for terms in it.product('IXYZ',repeat=d):
        if terms==('I',)*d:continue
        r=float(np.vdot(psi,op(d,dict(enumerate(P[x] for x in terms)))@psi).real)
        if abs(r)<1e-12:continue
        setting=tuple('Z' if x=='I' else x for x in terms)
        groups[setting].append((terms,r/N))
    w2=0.;dist=[];ideal=identity
    for a in axes:
        if not groups[a]:continue
        V=op(d,{k:rotations[x] for k,x in enumerate(a)})
        p=abs(V.conj().T@psi)**2
        scores=np.zeros(N)
        # eigh orders the eigenvalues as -1,+1 on the local outcome bit.
        for term,coef in groups[a]:
            for y in range(N):
                scores[y]+=coef*math.prod((1 if y>>k&1 else -1) for k,x in enumerate(term) if x!='I')
        weight=sum(abs(c) for _,c in groups[a]);w2+=weight*weight
        ideal+=float(scores@p);dist.append((p,scores))
    assert abs(ideal-1)<1e-12
    rng=np.random.default_rng(SEED+2);F=best['convex_gaussian_fidelity_bound'];out=[]
    for shots in (1024,2048,4096):
        # One-sided Hoeffding interval under independent ideal product-basis measurements.
        radius=float(np.sqrt(2*w2*np.log(20)/shots))
        for depol in (0.,.10,.15,.20):
            samples=np.full(2000,identity)
            for p,scores in dist:
                counts=rng.multinomial(shots,(1-depol)*p+depol/N,size=len(samples))
                samples+=counts@scores/shots
            out.append(dict(shots_per_setting=shots,settings=len(dist),total_shots=shots*len(dist),
               illustrative_global_depolarization=depol,expected_fidelity=1-depol*(1-1/N),
               mean_fidelity=float(samples.mean()),hoeffding_one_sided_95_radius=radius,
               witness_pass_fraction=float(np.mean(samples-radius>F))))
    return dict(ideal_projector_check=ideal,settings=len(dist),group_weight_squared_sum=w2,
        threshold=F,shots_model='independent binomial/multinomial ideal measurements and illustrative global depolarization only; no device calibration',trials=out)

def branch_bound():
    # Trotterize Gaussian G and each quartic Q. Sample Gaussian branches with absolute coefficients.
    rng=np.random.default_rng(SEED+1);d=3;t=1.2;steps=3;G,qs=pieces(d,{0:(1,np.pi/2),1:(2,.6)})
    U=expm(-1j*t*G/steps);alpha=np.array([w*t/steps for w,Q in qs]);L=float(np.prod(abs(np.cos(alpha))+abs(np.sin(alpha)))**steps)
    A=[expm(-1j*a*Q) for a,(_,Q) in zip(alpha,qs)]
    layer=U.copy()
    for gate in A:layer=gate@layer
    exact=np.linalg.matrix_power(layer,steps)[0,0]
    vacuum=np.eye(1<<d,dtype=complex)[:,0]
    choices=np.array([[np.cos(a),-1j*np.sin(a)] for a in alpha]);probs=abs(choices)/abs(choices).sum(axis=1,keepdims=True)
    full=0j
    for bits in it.product((0,1),repeat=len(qs)*steps):
        psi=vacuum.copy();weight=1.+0j
        for l in range(steps):
            psi=U@psi
            for j,(_,Q) in enumerate(qs):
                b=bits[l*len(qs)+j];weight*=choices[j,b]
                if b:psi=Q@psi
        full+=weight*psi[0]
    assert abs(full-exact)<1e-12
    N=20000;states=np.tile(vacuum,(N,1));weights=np.ones(N,complex)
    for _ in range(steps):
        states=states@U.T
        for j,(_,Q) in enumerate(qs):
            b=rng.random(N)<probs[j,1];states[b]=states[b]@Q.T
            weights*=choices[j,b.astype(int)]/probs[j,b.astype(int)]
    samples=weights*states[:,0];estimate=samples.mean();se=float(np.std(samples)/np.sqrt(N))
    assert abs(estimate-exact)<5*se
    strength=t*sum(w for w,Q in qs)
    assert L<=np.exp(strength)+1e-12
    # The branch simulation uses dense matrices for a small cross-check, not a measured scalable FLO algorithm.
    return dict(t=t,steps=steps,defects=len(qs),non_gaussian_strength=float(strength),branch_count=2**(len(qs)*steps),
        l1=L,exp_strength=float(np.exp(strength)),exact_amplitude=[exact.real,exact.imag],
        sampled_amplitude=[estimate.real,estimate.imag],monte_carlo_samples=N,complex_rmse_se=se,absolute_sample_error=float(abs(estimate-exact)),enumeration_error=float(abs(full-exact)))

def main():
    w=witness()
    report=dict(status='PASS',scope='offline finite-dimensional checks; no hardware or complexity separation',seed=SEED,algebra=audit(),witness=w,measurement_design=measurement_design(w['selected']),branch_estimator=branch_bound())
    p=Path(__file__).with_name('validation.json');p.write_text(json.dumps(report,indent=2,allow_nan=False)+'\n');print(json.dumps(report,indent=2,allow_nan=False))
if __name__=='__main__':main()
