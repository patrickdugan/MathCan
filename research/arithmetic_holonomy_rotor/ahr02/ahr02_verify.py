#!/usr/bin/env python3
"""AHR-02: stand-alone finite-dimensional checks. Requires NumPy and SciPy.

All bit positions use little-endian integers, x_i = (vertex >> i) & 1.
Geometry is synthetic; no hardware or RH proof is claimed.
"""
import json
from math import comb, cos, log, pi, sin
from pathlib import Path
import numpy as np
from scipy.linalg import expm

OUT = Path(__file__).resolve().parent
I2 = np.eye(2, dtype=complex)
X = np.array([[0, 1], [1, 0]], dtype=complex)
Y = np.array([[0, -1j], [1j, 0]], dtype=complex)
Z = np.diag([1, -1]).astype(complex)


def qubit(op, i, d):
    mats = [op if j == i else I2 for j in reversed(range(d))]
    q = mats[0]
    for mat in mats[1:]:
        q = np.kron(q, mat)
    return q


def gammas(d):
    ret = []
    for i in range(d):
        m = qubit(X, i, d)
        for j in range(i):
            m = m @ qubit(Z, j, d)
        ret.append(m)
    return ret


def build(d, theta=None, energies=None, J=1.0, delta_11=0.0):
    """Hopping on the d-hypercube, Landau gauge A_i(x)=sum_{j<i} theta[j,i] x_j."""
    theta = np.zeros((d, d)) if theta is None else theta
    energies = np.zeros(d) if energies is None else energies
    H = np.zeros((1 << d, 1 << d), dtype=complex)
    for x in range(1 << d):
        H[x, x] = sum(float(energies[i]) * ((x >> i) & 1) for i in range(d))
        if d == 2 and x == 3:
            H[x, x] += delta_11
        for i in range(d):
            if x & (1 << i):
                continue
            y = x | (1 << i)
            A = sum(float(theta[j, i]) * ((x >> j) & 1) for j in range(i))
            H[y, x] = J * np.exp(1j * A)
            H[x, y] = np.conj(H[y, x])
    return H


def tol(actual, expected, t=1e-10, label=''):
    e = float(np.max(np.abs(np.asarray(actual) - np.asarray(expected))))
    assert e < t, f'{label}: max abs difference {e}, tolerance {t}'
    return e


def cplx_2cocycle(a, b, theta):
    d = len(a)
    return np.exp(1j * sum(theta[i, j] * a[i] * b[j]
                            for i in range(d) for j in range(i + 1, d)))


def concurrence(psi):
    # indices 0 = 00, 1 = 10, 2 = 01, 3 = 11
    return 2.0 * abs(psi[0] * psi[3] - psi[1] * psi[2])


def test_cocycle():
    theta = np.array([[0, .71, -.38], [-.71, 0, 1.17], [.38, -1.17, 0]])
    for a in (np.array([1, -1, 2]), np.array([0, 2, 3])):
        b, c = np.array([-2, 1, 3]), np.array([1, 1, -1])
        tol(cplx_2cocycle(a, b, theta) * cplx_2cocycle(a+b, c, theta),
            cplx_2cocycle(b, c, theta) * cplx_2cocycle(a, b+c, theta),
            label='associative 2-cocycle')
    return True


def test_clifford():
    report = {}
    for d in range(2, 7):
        g = gammas(d)
        zero = np.zeros_like(g[0]); eye=np.eye(1 << d, dtype=complex)
        for i in range(d):
            tol(g[i] @ g[i], eye, label='gamma square')
            for j in range(i):
                tol(g[i] @ g[j] + g[j] @ g[i], zero, label='anticommutator')
        D = sum(g)
        theta=np.array([[pi if i<j else (-pi if i>j else 0)
                         for j in range(d)] for i in range(d)], dtype=float)
        H=build(d, theta)
        tol(H,D,1e-12, 'π-flux graph equals Clifford representation')
        tol(D@D, d*eye, 1e-12, 'flat band identity')
        ev=np.linalg.eigvalsh(D)
        tol(ev, np.r_[np.full(1 << (d-1),-np.sqrt(d)),
                             np.full(1 << (d-1),np.sqrt(d))],1e-10,'spectrum')
        t=.53
        v0=np.zeros(1 << d, complex); v0[0]=1
        p_pi = abs(v0.conj() @ expm(-1j*t*D) @ v0)**2
        p_zero = abs(v0.conj() @ expm(-1j*t*build(d)) @ v0)**2
        tol(p_pi, cos(np.sqrt(d)*t)**2, 1e-11, 'π return')
        tol(p_zero, cos(t)**(2*d), 1e-11,'zero return')
        report[d]={'positive_eigenvalue':float(np.sqrt(d)),
                   'multiplicity':1 << (d-1),
                   'pi_return_at_t0.53':float(p_pi),
                   'zero_return_at_t0.53':float(p_zero)}
    return report


def test_trace_face_law():
    d=3; J=.71
    theta=np.array([[0,.71,-.38],[-.71,0,1.17],[.38,-1.17,0]])
    energies=np.array([log(2), log(3),log(5)])
    H=build(d,theta,energies,J)
    H0=build(d,energies=energies,J=J)
    for k in range(1,4):
        tol(np.trace(np.linalg.matrix_power(H,k)),
            np.trace(np.linalg.matrix_power(H0,k)),2e-12, f'trace power {k}')
    measured=(np.trace(np.linalg.matrix_power(H,4))
              -np.trace(np.linalg.matrix_power(H0,4))).real
    # Each i-j pair supports 2^(d-2) square faces.
    predicted=8*J**4*(2**(d-2))*sum(cos(theta[i,j])-1
                       for i in range(d) for j in range(i+1,d))
    tol(measured,predicted,1e-11,'trace fourth-moment face law')
    # Origin sees exactly one face for each pair of coordinate directions.
    t=.014; init=np.zeros(1 << d,complex);init[0]=1
    actual=abs(init@expm(-1j*t*H)@init)**2-abs(init@expm(-1j*t*H0)@init)**2
    lead=J**4*t**4/6*sum(cos(theta[i,j])-1 for i in range(d)
                        for j in range(i+1,d))
    assert abs(actual-lead)<5e-11, (actual,lead)
    return {'d':3,'faces':6,'predicted_delta_trace_H4':predicted,
            'measured_delta_trace_H4':float(measured),
            'origin_prob_short_t':float(actual),
            'leading_t4_prediction':float(lead)}


def test_gauge():
    d=3
    theta=np.array([[0,.71,-.38],[-.71,0,1.17],[.38,-1.17,0]])
    H=build(d,theta,[log(2),log(3),log(5)])
    chi=np.array([.32,-.5,.8,.1,-.2,1.6,-.7,.71])
    U=np.diag(np.exp(1j*chi)); Hp=U@H@U.conj().T
    t=.78
    result=tol(np.abs(expm(-1j*t*H)[:,0])**2,
               np.abs(expm(-1j*t*Hp)[:,0])**2,1e-12,'gauge probabilities')
    return {'max_probability_error':result}


def test_arithmetic_curvature():
    a=np.array([log(2),log(3),log(5)])
    for i in range(3):
        for j in range(i+1,3):
            # f(a+ei+ej)-f(a+ei)-f(a+ej)+f(a) = 0.
            x=np.array([.6,-1.2,.9]); ei=np.eye(3)[i]; ej=np.eye(3)[j]
            f=lambda u:float(a@u)
            tol(f(x+ei+ej)-f(x+ei)-f(x+ej)+f(x),0,1e-14,'exact log phase')
    return True


def test_delta_concurrence():
    a,b=log(2),log(3);J=.9;delta=.41
    H=build(2,energies=[a,b],J=J,delta_11=delta)
    report={}
    for t in (.015,.01,.005):
        v=expm(-1j*t*H)[:,0]; C=concurrence(v)
        leading=2*abs(delta)*J**2*t**3/3
        report[str(t)]={'exact_concurrence':float(C),
                        'cubic_prediction':float(leading),
                        'ratio':float(C/leading)}
    assert abs(report['0.005']['ratio']-1)<.02,report
    return report


def test_squarefree_euler():
    primes=(2,3,5,7);s=2.2 +.35j
    lhs=sum(np.exp(-s*sum(log(primes[i]) *((x>>i)&1)
                           for i in range(len(primes)))) for x in range(1<<len(primes)))
    rhs=np.prod([1+p**(-s) for p in primes])
    return {'error':tol(lhs,rhs,1e-13,'squarefree finite Euler product'),
            'partition_value_real':float(rhs.real)}


def test_su2_order():
    alpha=pi/4;beta=pi/2
    A=expm(1j*alpha*X);B=expm(1j*beta*Z)
    v0=np.array([1,0], complex)
    u=A@B@v0;v=B@A@v0
    dist=np.sqrt(max(0,1-abs(np.vdot(u,v))**2))
    tol(dist,abs(sin(2*alpha)*sin(beta)),1e-12,'SU2 order memory')
    K=A@B@A.conj().T@B.conj().T
    tr=(np.trace(K)/2).real
    tol(tr,1-2*sin(alpha)**2*sin(beta)**2,1e-12,'Wilson commutator trace')
    tol(dist,1,1e-12,'perfect discriminability of loop order')
    return {'alpha':float(alpha),'beta':float(beta),
            'pure_state_trace_distance':float(dist),
            'half_trace_group_commutator':float(tr)}



def test_two_prime_exact_spectrum():
    samples=[]
    for a,b,J in [(log(2),log(3),1.0),(.2,2.8,.7),(0.0,0.0,1.0),(.9,.9,1.0)]:
        for phi in [0,.24,pi/2,2.3,pi]:
            theta=np.array([[0,phi],[-phi,0]])
            H=build(2,theta,[a,b],J)
            center=(a+b)/2
            s=2*J**2+(a*a+b*b)/4
            q=np.sqrt(a*a*b*b/4+J**2*(a*a+b*b)+4*J**4*np.cos(phi/2)**2)
            eps_hi=np.sqrt(s+q)
            k=(a*a-b*b)**2/16+4*J**4*np.sin(phi/2)**2
            eps_lo=np.sqrt(k/(s+q))
            expected=np.sort([center-eps_hi,center-eps_lo,
                              center+eps_lo,center+eps_hi])
            measured=np.linalg.eigvalsh(H)
            tol(measured,expected,2e-8,'exact four-level spectral formula')
            samples.append(float(np.max(np.abs(measured-expected))))
    return {'parameter_combinations':len(samples),'maximum_absolute_error':max(samples)}


def test_flux_interaction_compensation():
    a,b=log(2),log(3);J=.9;delta=.41
    kappa=2*delta/3
    report=[]
    for t in (.12,.06,.03,.015,.0075):
        pure=build(2,energies=[a,b],J=J,delta_11=delta)
        theta=np.array([[0,kappa*t],[-kappa*t,0]])
        comp=build(2,theta,energies=[a,b],J=J,delta_11=delta)
        c0=concurrence(expm(-1j*t*pure)[:,0])
        c1=concurrence(expm(-1j*t*comp)[:,0])
        report.append({'t':t,'uncompensated_C':float(c0),
                       'compensated_C':float(c1),'suppression_factor':float(c0/c1)})
    assert report[-1]['suppression_factor']>300
    return {'kappa':kappa,'results':report,
            'interpretation':'flux phi=kappa*t held fixed within each duration-t experiment'}


def nonbacktracking_cycle_det(s, L, phi):
    # Directed arcs (u,v); one quantum-walk step appends the next directed arc.
    # Assign a 1/4 length and 1/4 phase to each clockwise arc and conjugate phase to reverse.
    cw=[(0,1),(1,2),(2,3),(3,0)]
    arcs=cw+[(v,u) for u,v in cw]
    B=np.zeros((8,8),complex)
    for k,(a,b) in enumerate(arcs):
        for m,(c,d) in enumerate(arcs):
            if b!=c or d==a:continue
            if (c,d) in cw:
                phase=phi/4
            else:
                phase=-phi/4
            B[k,m]=np.exp(-s*L/4+1j*phase)
    return np.linalg.det(np.eye(8)-B)


def test_primitive_loop_euler():
    s=2.1+.6j
    residues={1:1,2:1j,3:-1j,4:-1}
    primes=[2,3,7,11,13]
    graph_det=1+0j;arith_det=1+0j
    for p in primes:
        phase=float(np.angle(residues[p%5])); L=log(p)
        factor=(1-p**(-s)*np.exp(1j*phase))*(1-p**(-s)*np.exp(-1j*phase))
        tol(nonbacktracking_cycle_det(s,L,phase),factor,3e-14,
            f'nonbacktracking cycle p={p}')
        graph_det*=nonbacktracking_cycle_det(s,L,phase)
        arith_det*=factor
    tol(graph_det,arith_det,5e-14,'Dirichlet L function pair partial Euler product')
    return {'prime_cycles':primes,'character':'order-four Dirichlet character mod 5',
            'complex_s':[float(s.real),float(s.imag)],
            'max_error':float(abs(graph_det-arith_det)),
            'graph_zeta_inverse_re':float(graph_det.real),
            'graph_zeta_inverse_im':float(graph_det.imag)}



def test_nonlocal_gauge_entanglement():
    # A zero-flux square may be represented by an entangling vertex phase gauge.
    # This changes computational-qubit concurrence but not any site probability.
    H0=build(2,J=1.0)
    G=np.diag([1,1,1,-1]).astype(complex)   # controlled-Z
    Hg=G@H0@G.conj().T
    t=.4
    u0=expm(-1j*t*H0)[:,0]
    ug=expm(-1j*t*Hg)[:,0]
    tol(np.abs(u0)**2,np.abs(ug)**2,1e-12,'gauge-invariant site probabilities')
    c0=concurrence(u0); cg=concurrence(ug)
    tol(c0,0,1e-12,'zero gauge separability')
    tol(cg,sin(2*t)**2,1e-12,'zero-flux entanglement in CZ gauge')
    return {'t':t,'flux_radians':0.,'untransformed_concurrence':float(c0),
            'CZ_gauge_concurrence':float(cg),
            'return_probability_difference':float(abs(abs(u0[0])**2-abs(ug[0])**2))}


def main():
    results={'cocycle':test_cocycle(),
             'exact_two_prime_spectrum':test_two_prime_exact_spectrum(),
             'flux_interaction_compensation':test_flux_interaction_compensation(),
             'prime_cycle_graph_zeta':test_primitive_loop_euler(),
             'arithmetic_zero_curvature':test_arithmetic_curvature(),
             'clifford_pi_flux':test_clifford(),
             'gauge_invariance':test_gauge(),
             'nonlocal_gauge_entanglement_caveat':test_nonlocal_gauge_entanglement(),
             'fourth_moment_face_law':test_trace_face_law(),
             'energetic_delta_concurrence':test_delta_concurrence(),
             'squarefree_euler':test_squarefree_euler(),
             'nonabelian_order_memory':test_su2_order()}
    (OUT/'ahr02_validation.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':
    main()