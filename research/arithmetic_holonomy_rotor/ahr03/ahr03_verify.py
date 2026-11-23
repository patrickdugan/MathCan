"""AHR-03: finite symmetric-oscillator holonomy and combinatorial face-law checks.

Uses NumPy/SciPy, runs without IBM hardware, Lean or credentials.
"""
from __future__ import annotations

import itertools
import json
from pathlib import Path

import numpy as np
from scipy.integrate import solve_ivp, dblquad


TOL = 2e-9


def base_k(q, omega=1.0, delta=8.0):
    q = np.asarray(q, dtype=float)
    n = np.r_[q, np.sqrt(1.0 - np.dot(q, q))]
    return omega**2 * np.eye(4) + delta * np.outer(n, n)


def transport_segment(T, a, b, *, rtol=1e-11, atol=1e-13):
    a, b = np.asarray(a, dtype=float), np.asarray(b, dtype=float)
    direction = b-a

    def ode(s, x):
        q = a+s*direction
        h = np.sqrt(1.0-float(q@q))
        n = np.r_[q, h]
        ndot = np.r_[direction, -float(q@direction)/h]
        U = x.reshape(4, 3)
        # Levi-Civita transport of tangent vectors on S^3.
        return (-np.outer(n, ndot@U)).ravel()

    sol = solve_ivp(ode, [0, 1], T.ravel(), rtol=rtol, atol=atol, method="DOP853")
    assert sol.success, sol.message
    return sol.y[:, -1].reshape(4, 3)


def transport_rectangle(r, axes):
    assert 0 < r < 1/np.sqrt(2)
    e = np.eye(3)
    u, v = e[axes[0]], e[axes[1]]
    pts = [np.zeros(3), r*u, r*(u+v), r*v, np.zeros(3)]
    T = np.vstack([np.eye(3), np.zeros((1, 3))])
    for a, b in zip(pts[:-1], pts[1:]):
        T = transport_segment(T, a, b)
    assert np.linalg.norm(T[3, :]) < TOL
    W = T[:3, :]
    assert np.linalg.norm(W.T@W-np.eye(3)) < TOL
    return W


def area_of_rectangle(r):
    value, err = dblquad(lambda y, x: 1.0/np.sqrt(1.0-x*x-y*y), 0, r,
                         lambda _: 0, lambda _: r, epsabs=1e-12, epsrel=1e-12)
    return value


def cube_hamiltonian(d, J, phases, eps):
    N = 1 << d
    H = np.diag([float(eps[n]) for n in range(N)]).astype(complex)
    for state in range(N):
        for i in range(d):
            other = state ^ (1 << i)
            if state < other:
                phi = phases[(state, other)]
                H[state, other] = J*np.exp(1j*phi)
                H[other, state] = np.conjugate(H[state, other])
    return H


def face_fluctuation(d, J, phases):
    # For i<j, face corners are s,s^2**i,s^2**j,s^2**i^2**j.
    terms=[]
    for i in range(d):
        for j in range(i+1, d):
            for s in range(1<<d):
                if ((s>>i)&1) or ((s>>j)&1):
                    continue
                si=s^(1<<i); sj=s^(1<<j); sij=si^(1<<j)
                def edge(a,b):
                    if a<b: return phases[(a,b)]
                    return -phases[(b,a)]
                F=edge(s,si)+edge(si,sij)+edge(sij,sj)+edge(sj,s)
                terms.append(float(np.cos(F)-1))
    return 8*J**4*sum(terms), len(terms)


def run():
    res={}
    r=0.55
    Wa=transport_rectangle(r, (0,1)); Wb=transport_rectangle(r, (1,2))
    area=area_of_rectangle(r)
    # A clockwise holonomy may carry the negative orientation: use absolute angle.
    theta=abs(float(np.arctan2(Wa[1,0], Wa[0,0])))
    assert abs(theta-area)<2e-9, (theta,area)
    assert np.linalg.norm(Wa@Wb-Wb@Wa)>0.02
    # Test both loop orders from e1, with return to the same site.
    e1=np.array([1.,0.,0.]); dist=np.linalg.norm(Wa@Wb@e1-Wb@Wa@e1)
    expected=2*abs(np.sin(theta)*np.sin(theta/2))
    assert abs(dist-expected)<2e-9
    K=base_k([0.1,-0.2,0.15]); freqs=np.sqrt(np.linalg.eigvalsh(K))
    assert np.allclose(freqs,[1,1,1,3],atol=2e-14)
    # F12=E12-E21, F23=E23-E32, and [F12,F23]=F13.
    def F(i,j):
        z=np.zeros((3,3));z[i,j]=1;z[j,i]=-1;return z
    assert np.allclose(F(0,1)@F(1,2)-F(1,2)@F(0,1),F(0,2))
    res['symplectic_tangent_model']={
        'stiffness_eigenfrequencies':freqs.tolist(),
        'rectangle_coordinate_size':r,
        'sphere_area':area,
        'abs_holonomy_angle':theta,
        'noncommuting_order_operator_frobenius':float(np.linalg.norm(Wa@Wb-Wb@Wa)),
        'path_order_state_L2_distance':float(dist),
        'analytic_state_L2_distance':float(expected),
        'holonomy_A':Wa.round(12).tolist(),
        'holonomy_B':Wb.round(12).tolist(),
    }
    rng=np.random.default_rng(22631)
    trials=[]
    for d in (2,3,4,5):
        N=1<<d; J=float(rng.uniform(.4,1.1))
        eps=rng.normal(size=N)
        phases={(a,a^(1<<i)):float(rng.uniform(-np.pi,np.pi))
                for a in range(N) for i in range(d)
                if not ((a>>i)&1)}
        zero={x:0.0 for x in phases}
        H=cube_hamiltonian(d,J,phases,eps)
        H0=cube_hamiltonian(d,J,zero,eps)
        def trk(h,k): return float(np.real(np.trace(np.linalg.matrix_power(h,k))))
        for k in (1,2,3):
            assert abs(trk(H,k)-trk(H0,k))<1e-8
        observed=trk(H,4)-trk(H0,4)
        predicted,faces=face_fluctuation(d,J,phases)
        assert abs(observed-predicted)<1e-7,(d,observed,predicted)
        assert faces==d*(d-1)//2*2**(d-2)
        trials.append({'d':d,'vertices':N,'faces':faces,'observed_tr4_diff':observed,'predicted_tr4_diff':predicted,'abs_error':abs(observed-predicted)})
    res['hypercube_face_moment_law']=trials
    Path('ahr03_validation.json').write_text(json.dumps(res,indent=2)+'\n')
    print(json.dumps(res,indent=2))


if __name__=='__main__':
    run()