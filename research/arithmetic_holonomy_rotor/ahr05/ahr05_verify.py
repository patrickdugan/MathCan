"""AHR-05: six-cycle counts, Wilson-loop mixed derivatives, and lattice Stokes."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json
import math
import numpy as np


def cycles(d, length):
    ans = set()
    for start in range(1 << d):
        def visit(path):
            x = path[-1]
            if len(path) == length:
                if (x ^ start).bit_count() == 1:
                    p = tuple(path)
                    ans.add(min(p, (start,)+tuple(reversed(p[1:]))))
                return
            for i in range(d):
                nxt = x ^ (1 << i)
                if nxt > start and nxt not in path:
                    visit(path+[nxt])
        visit([start])
    return sorted(ans)


def face_vertices(d):
    for i, j in combinations(range(d),2):
        for x in range(1 << d):
            if ((x >> i) & 1) or ((x >> j) & 1):
                continue
            yield (x, x^(1<<i), x^(1<<i)^(1<<j), x^(1<<j))


def oriented_edges(verts):
    return [(x, y) for x, y in zip(verts, verts[1:]+verts[:1])]


def edge_key(x, y):
    return (min(x, y), max(x, y))


def boundary(verts):
    out = {}
    for x, y in oriented_edges(verts):
        e = edge_key(x, y)
        out[e] = out.get(e,0) + (1 if x < y else -1)
    return {k:v for k,v in out.items() if v}


def hamiltonian(d, v, w, a):
    h=np.diag(v).astype(complex)
    for (x,y), j in w.items():
        h[x,y]=j*np.exp(1j*a[(x,y)])
        h[y,x]=h[x,y].conjugate()
    return h


def angle(verts, a):
    return sum((1 if x < y else -1)*a[edge_key(x,y)] for x,y in oriented_edges(verts))


def tr(h, k):
    return float(np.trace(np.linalg.matrix_power(h,k)).real)


def probe(d, v, w, a, oriented_cycle, eta=0.0, order=None):
    es=[edge_key(x,y) for x,y in oriented_edges(oriented_cycle)]
    shifted=dict(a)
    first=oriented_cycle[0],oriented_cycle[1]
    shifted[es[0]] += eta*(1 if first[0] < first[1] else -1)
    n=len(es)
    if order is None: order=n
    total=0.0
    for bits in product([0,1],repeat=n):
        changed=dict(w)
        for e,bit in zip(es,bits):changed[e]=w[e]*bit
        total += (-1)**(n-sum(bits))*tr(hamiltonian(d,v,changed,shifted),order)
    return total


def spanning_faces(face_data, cycle):
    desired=boundary(cycle)
    edge_set=set(desired)
    for n in range(1,len(face_data)+1):
        for indexes in combinations(range(len(face_data)),n):
            toggle=set()
            for idx in indexes: toggle.symmetric_difference_update(set(boundary(face_data[idx])))
            if toggle != edge_set: continue
            for signs in product((-1,1), repeat=n):
                b={}
                for idx,sign in zip(indexes,signs):
                    for e,value in boundary(face_data[idx]).items():
                        b[e]=b.get(e,0)+sign*value
                if {k:v for k,v in b.items() if v}==desired:
                    return indexes, signs
    raise AssertionError('Could not find oriented spanning surface')


def main():
    rng=np.random.default_rng(20261123)
    counts={}
    for d in (3,4,5):
        observed=len(cycles(d,6))
        expected=16*math.comb(d,3)*(1 << (d-3))
        assert observed==expected,(d,observed,expected)
        counts[str(d)]={'observed':observed,'expected':expected}

    d=3
    faces=list(face_vertices(d)); six=cycles(d,6)
    v=rng.normal(size=1<<d)
    w={(x,x|(1<<i)):float(rng.uniform(.35,1.35)) for x in range(1<<d) for i in range(d) if not(x>>i&1)}
    a={e:float(rng.uniform(-np.pi,np.pi)) for e in w}
    patch_counts=Counter()
    representatives={}
    stokes_errors=[]
    signed_correlation_errors=[]
    for c in six:
        indexes,signs=spanning_faces(faces,c)
        patch_counts[len(indexes)]+=1
        representatives.setdefault(len(indexes),c)
        ph=angle(c,a)
        sum_faces=sum(sign*angle(faces[idx],a) for idx,sign in zip(indexes,signs))
        err=abs((ph-sum_faces+np.pi)%(2*np.pi)-np.pi)
        stokes_errors.append(err)
        assert err<1e-11
        if len(indexes)==2:
            p,q=[sign*angle(faces[idx],a) for idx,sign in zip(indexes,signs)]
            signed_correlation_errors.append(abs((np.cos(ph)-np.cos(p)*np.cos(q))+np.sin(p)*np.sin(q)))
    assert dict(patch_counts)=={2:12,3:4}
    assert max(signed_correlation_errors)<1e-12

    mixed_results=[]
    for span,c in sorted(representatives.items()):
        es=[edge_key(x,y) for x,y in oriented_edges(c)]
        magnitude=float(np.prod([w[e] for e in es]))
        phi=angle(c,a)
        s0=probe(d,v,w,a,c)
        s90=probe(d,v,w,a,c,np.pi/2)
        predicted0=12*magnitude*np.cos(phi)
        predicted90=-12*magnitude*np.sin(phi)
        err0=abs(s0-predicted0);err90=abs(s90-predicted90)
        assert err0<1e-9 and err90<1e-9,(span,err0,err90)
        recovered=np.arctan2(-s90,s0)
        errphase=abs((recovered-phi+np.pi)%(2*np.pi)-np.pi)
        assert errphase<1e-9
        mixed_results.append({'min_spanning_faces':span,'cycle':c,
            'flux_mod_2pi':float((phi+np.pi)%(2*np.pi)-np.pi),
            'observed_cos_derivative':s0,'predicted_cos_derivative':predicted0,
            'observed_sin_derivative':s90,'predicted_sin_derivative':predicted90,
            'phase_error':errphase})

    prime_v=np.array([sum(np.log([2,3,5][i]) for i in range(3) if x>>i&1)
                      for x in range(8)])
    c=representatives[3]
    es=[edge_key(x,y) for x,y in oriented_edges(c)]
    magnitude=float(np.prod([w[e] for e in es]))
    hol=angle(c,a)
    m6=probe(3,prime_v,w,a,c,order=6)
    m7=probe(3,prime_v,w,a,c,order=7)
    predicted6=12*magnitude*np.cos(hol)
    predicted7=14*magnitude*sum(prime_v[x] for x in c)*np.cos(hol)
    assert abs(m6-predicted6)<2e-9
    assert abs(m7-predicted7)<1e-8
    ratio=m7/m6
    assert abs(ratio-3.5*np.log(30))<2e-9

    result={'status':'PASS','seed':20261123,'six_cycle_counts':counts,
            'prime_three_face_hexagon':{'mixed_sixth':m6,'mixed_seventh':m7,
                                       'ratio_observed':ratio,'ratio_predicted':3.5*np.log(30)},
            'q3_spanning_surface_distribution':dict(patch_counts),
            'max_stokes_error':max(stokes_errors),
            'max_relative_chirality_error':max(signed_correlation_errors),
            'sixth_derivative_examples':mixed_results,
            'claim':'Exact finite matrices; no hardware or complexity separation'}
    Path(__file__).with_name('ahr05_validation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
