"""AHR-04: exact-matrix oracle for fourth/fifth magnetic hypercube moments."""
from itertools import combinations, product
from pathlib import Path
import json
import numpy as np
from scipy.linalg import expm


def graph(d, rng, primes=None):
    v = (np.array([sum(np.log(primes[i]) for i in range(d) if (x >> i) & 1)
                   for x in range(1 << d)]) if primes else rng.normal(size=1 << d))
    j = {(x, x | (1 << i)): float(rng.uniform(.3, 1.5))
         for x in range(1 << d) for i in range(d) if not ((x >> i) & 1)}
    a = {e: float(rng.uniform(-np.pi, np.pi)) for e in j}
    return v, j, a


def phase(a, x, y):
    return a[(x, y)] if x < y else -a[(y, x)]


def faces(d, v, j, a):
    for i, k in combinations(range(d), 2):
        for x in range(1 << d):
            if ((x >> i) & 1) or ((x >> k) & 1):
                continue
            xi, xk = x | (1 << i), x | (1 << k)
            xik = xi | (1 << k)
            path = [(x, xi), (xi, xik), (xik, xk), (xk, x)]
            es = [tuple(sorted(e)) for e in path]
            f = sum(phase(a, y, z) for y, z in path)
            yield es, f, float(np.prod([j[e] for e in es])), float(sum(v[y] for y in (x, xi, xk, xik)))


def hamiltonian(d, v, j, a):
    h = np.diag(v).astype(complex)
    for (x, y), magnitude in j.items():
        h[x, y] = magnitude * np.exp(1j*a[(x, y)])
        h[y, x] = h[x, y].conjugate()
    return h


def tr(h, n):
    return float(np.trace(np.linalg.matrix_power(h, n)).real)


def probe(d, v, j, a, es, eta):
    shifted = dict(a)
    shifted[es[0]] += eta
    total = 0.
    for bits in product((0, 1), repeat=4):
        changed = dict(j)
        for e, bit in zip(es, bits):
            changed[e] *= bit
        total += (-1)**(4-sum(bits)) * tr(hamiltonian(d, v, changed, shifted), 4)
    return total


def canonical_gauge(d, a):
    vals = np.zeros(1 << d)
    for x in range(1 << d):
        s = 0
        for i in range(d):
            if (x >> i) & 1:
                t = s | (1 << i)
                vals[x] += phase(a, s, t)
                s = t
    return np.exp(1j*vals)


def main():
    rng = np.random.default_rng(20261123)
    errors4, errors5 = [], []
    for d in range(2, 6):
        for _ in range(4):
            v, j, a = graph(d, rng)
            h = hamiltonian(d, v, j, a)
            h0 = hamiltonian(d, v, j, {e: 0. for e in j})
            assert all(abs(tr(h, k) - tr(h0, k)) < 1e-8 for k in range(4))
            f = list(faces(d, v, j, a))
            p4 = 8*sum(w*(np.cos(theta)-1) for _, theta, w, _ in f)
            p5 = 10*sum(w*s*(np.cos(theta)-1) for _, theta, w, s in f)
            err4 = abs((tr(h, 4)-tr(h0, 4))-p4)
            err5 = abs((tr(h, 5)-tr(h0, 5))-p5)
            assert err4 < 2e-7 and err5 < 1e-6
            errors4.append(err4); errors5.append(err5)

    v, j, a = graph(2, rng, [2, 3]); a = {e: 0. for e in j}; a[(0, 1)] = .7
    h = hamiltonian(2, v, j, a)
    h0 = hamiltonian(2, v, j, {e: 0. for e in j})
    ratio = (tr(h0, 5)-tr(h, 5))/(tr(h0, 4)-tr(h, 4))
    assert abs(ratio - 2.5*np.log(6)) < 2e-10

    d = 3; v, j, a = graph(d, rng)
    es, f, w, _ = list(faces(d, v, j, a))[2]
    s0, s90 = probe(d, v, j, a, es, 0.), probe(d, v, j, a, es, np.pi/2)
    assert abs(s0-8*w*np.cos(f)) < 2e-10
    assert abs(s90+8*w*np.sin(f)) < 2e-10
    recovered = np.arctan2(-s90, s0)
    phase_error = abs((recovered-f+np.pi)%(2*np.pi)-np.pi)
    assert phase_error < 1e-10

    d = 4; v, j, a = graph(d, rng)
    h0 = hamiltonian(d, v, j, {e: 0. for e in j})
    g = rng.uniform(-np.pi, np.pi, size=1 << d)
    flat = hamiltonian(d, v, j, {(x,y):float(g[x]-g[y]) for x,y in j})
    diagonal = np.diag(np.exp(1j*g))
    assert np.linalg.norm(flat-diagonal@h0@diagonal.conj().T) < 1e-11

    j = {e: .9 for e in j}
    h, h0 = hamiltonian(d,v,j,a),hamiltonian(d,v,j,{e:0. for e in j})
    z = canonical_gauge(d,a)
    fro2 = np.linalg.norm(z[:,None]*h*np.conj(z[None,:])-h0, 'fro')**2
    defect = tr(h0,4)-tr(h,4)
    bound = len(j)*(d-1)*defect/(2*.9**2)
    assert 0 <= fro2 <= bound + 1e-8
    hminus = hamiltonian(d,v,j,{e:-p for e,p in a.items()})
    assert np.allclose(np.linalg.eigvalsh(h),np.linalg.eigvalsh(hminus),atol=1e-12)
    assert np.allclose(np.diag(expm(-.7j*h)),np.diag(expm(-.7j*hminus)),atol=1e-12)

    result = {'status':'PASS','seed':20261123,'dimensions':[2,3,4,5],
              'random_graph_trials':len(errors4),'max_fourth_error':max(errors4),
              'max_fifth_error':max(errors5),
              'prime_ratio_observed':ratio,'prime_ratio_predicted':2.5*np.log(6),
              'signed_flux_error':phase_error,
              'canonical_gauge_frobenius_squared':fro2,'gauge_bound':bound,
              'time_reversal_eigenvalues_returns':'PASS'}
    Path(__file__).with_name('ahr04_validation.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
