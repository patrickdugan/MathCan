import json, random, time
from fractions import Fraction as F
from itertools import product
from scheduler import Chords,greedy,minimax,readout_lower

def run():
    t=time.perf_counter(); rows=[]
    # Exact analytic cross-polytope gauge; alternating axis, amplitude and scale.
    for d in (3,8,16):
        scales=[120*(i+1) for i in range(d)]
        V=[tuple(sign*scales[i] if j==i else 0 for j in range(d)) for i in range(d) for sign in (-1,1)]
        C=Chords(V,cache_entries=128)
        for seed in (11,23,37):
            rng=random.Random(seed); edges=[]
            for j in range(64):
                i=rng.randrange(d); step=rng.choice([12,24,36,48,60]); sign=rng.choice([-1,1]); edges.append(tuple(sign*step if l==i else 0 for l in range(d)))
            points=[(0,)*d]
            for dx in edges: points.append(tuple(a+b for a,b in zip(points[-1],dx)))
            chords=[C.solve(dx) for dx in edges]; cost=[z[2] for z in chords]
            exact=[sum(F(abs(x),2*s) for x,s in zip(dx,scales)) for dx in edges]
            assert all(x<=y<=x+F(1,10**6) for x,y in zip(exact,cost))
            cuts=greedy(cost,F(1,2)); k=len(cuts)-1
            methods={'gauge':cuts,'euclidean':minimax([sum(abs(x) for x in dx) for dx in edges],k),'fixed':[j*64//k for j in range(k+1)],'gauge_minimax':minimax(cost,k)}
            for name,cut in methods.items():
                mass=[sum(cost[a:b]) for a,b in zip(cut,cut[1:])]; passed=0
                for a,b,m in zip(cut,cut[1:],mass):
                    if m<=F(1,2):
                        v,_=C.chart(points,chords,a,b,F(1,2)); passed+=1
                        direction=tuple(1 if j==0 else -1 if j==1 else 0 for j in range(d)); lower=readout_lower(V,v,F(1,2),direction)
                        assert all(sum(x*y for x,y in zip(direction,p))>=lower for p in points[a:b+1])
                rows.append(dict(d=d,seed=seed,method=name,charts=k,certified=passed,max_mass=float(max(mass))))
        assert C._cached.cache_info().hits>0
    # General asymmetric polytope, including dense chords and LP rejection controls.
    V=[p for p in product((-12,12),repeat=3) if p!=(12,12,12)]+[(0,12,12),(12,0,12),(12,12,0)]
    C=Chords(V); dense=0
    for dx in product(range(-3,4),repeat=3):
        p,q,a=C.solve(dx); assert a<=F(1,2); C.chart([(0,0,0),dx],[(p,q,a)],0,1,F(1,2)); dense+=1
    try: greedy([F(3,4)],F(1,2)); raise AssertionError('oversize accepted')
    except ValueError: pass
    try: Chords([(0,0),(1,1)]); raise AssertionError('degenerate hull accepted')
    except ValueError: pass
    try: C.solve((0.1,0,0)); raise AssertionError('fractional coordinate accepted')
    except TypeError: pass
    try: C.chart([(0,0,0),(1,0,0)],[C.solve((0,0,0))],0,1,F(1,2)); raise AssertionError('corrupt chord accepted')
    except ArithmeticError: pass
    print(json.dumps(dict(rows=rows,dense_asymmetric=dense,negative_controls=4,seconds=round(time.perf_counter()-t,3)),indent=2))
if __name__=='__main__': run()
