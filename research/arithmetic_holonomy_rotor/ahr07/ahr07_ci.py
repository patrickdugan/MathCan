"""AHR-07 compact reproducibility oracle. NumPy/SciPy; no hardware."""
from math import pi, log
from pathlib import Path
import json
import numpy as np
from scipy.linalg import eigh

OFFSETS = np.arange(4)*pi/2

def model(primes, cycle, tree=()):
    n=1<<len(primes)
    V=np.array([sum(log(p) for k,p in enumerate(primes) if x>>k&1) for x in range(n)])
    return V, list(zip(cycle,cycle[1:]+cycle[:1])), tree

def p_return(graph,t,phi,mask=None):
    V,edges,tree=graph
    H=np.diag(V).astype(complex)
    for k,(a,b) in enumerate(edges):
        if mask is not None and not(mask>>k&1):continue
        z=np.exp(1j*phi) if k==len(edges)-1 else 1
        H[a,b]=z; H[b,a]=z.conjugate()
    for a,b,w in tree:H[a,b]=H[b,a]=w
    e,U=eigh(H)
    return float(abs(np.dot(abs(U[0])**2,np.exp(-1j*t*e)))**2)

def p4(graph,t,phi,mask=None):
    return np.array([p_return(graph,t,phi+d,mask) for d in OFFSETS])

def z4(p):
    return complex((p[0]-p[2]+1j*(p[3]-p[1]))/2)

def harmonic(graph,t,k):
    theta=np.arange(64)*2*pi/64
    return float(2*np.mean([p_return(graph,t,q)*np.cos(k*q) for q in theta]))

def masked(graph,t,phi):
    L=len(graph[1]); K=1<<L
    m=np.array([p4(graph,t,phi,mask) for mask in range(K)])
    signs=np.array([(-1)**(L-int(s).bit_count()) for s in range(K)])
    return m,signs

def rms_angle(z,theta):
    err=(np.angle(z)-theta+pi)%(2*pi)-pi
    return float(np.sqrt(np.mean(err*err)))

def main():
    g1=model((2,3),(0,1,3,2))
    g2=model((2,3,5),(0,1,3,7,6,4),((0,2,.7),(1,5,.6)))
    rng=np.random.default_rng(20261123)
    B=8192; R=2500; theta=.73; cases=[]
    for name,g,t in [('square',g1,1.6),('hexagon_with_trees',g2,2.5)]:
        L=len(g[1]); K=1<<L
        for mask in range(K-1):
            assert abs(p_return(g,.91,theta,mask)-p_return(g,.91,theta+.84,mask))<5e-13
        p=p4(g,t,theta)
        m,signs=masked(g,t,theta)
        assert abs(z4(p)-z4(m.T@signs))<5e-13
        harmonics=[harmonic(g,t,k) for k in range(1,5)]
        assert abs(harmonics[2]/harmonics[0])<.005
        c1=harmonics[0]
        z=z4(p)
        bias=rms_angle(np.array([z/c1]),theta)
        y=rng.binomial(B//4,p[None,:],size=(R,4))/(B//4)
        z_est=(y[:,0]-y[:,2]+1j*(y[:,3]-y[:,1]))/(2*c1)
        py=m.T
        ym=rng.binomial(B//(4*K),py[None,:,:],size=(R,4,K))/(B//(4*K))
        D=ym@signs
        zm=(D[:,0]-D[:,2]+1j*(D[:,3]-D[:,1]))/(2*c1)
        rmse=rms_angle(z_est,theta)
        rmse_mask=rms_angle(zm,theta)
        assert rmse<.1 and rmse_mask>3*rmse
        cases.append(dict(name=name,time=t,cycle_edges=L,settings_phase=4,
            settings_masks=4*K,full_probabilities=p.tolist(),
            harmonics=harmonics,noiseless_angle_error_rad=bias,
            angle_rmse_deg=float(rmse*180/pi),
            masked_rmse_deg=float(rmse_mask*180/pi)))
    confound=model((2,3,5),(0,1,3,7,6,4),((0,2,.7),(1,5,.6),(4,5,.8)))
    m,signs=masked(confound,1.3,theta)
    gap=abs(z4(p4(confound,1.3,theta))-z4(m.T@signs))
    assert gap>.01
    result=dict(status='PASS',seed=20261123,shots=B,replicates=R,theta=theta,cases=cases,
                confounder_phase_mask_gap=gap)
    Path(__file__).with_name('ahr07_ci_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
if __name__=='__main__': main()
