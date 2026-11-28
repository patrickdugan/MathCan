"""SPC-06: exact arithmetic checks for future observability and readout fibers."""
from fractions import Fraction as Q
import itertools
import unittest


def shift_register(x, q):
    return x[q:]+x[:q]


def temporal_observation(x, q, T):
    out=[]
    s=list(x)
    for _ in range(T):
        out.extend(s[:q])
        s=shift_register(s,q)
    return tuple(out)


def fraction_rank(rows):
    a=[[Q(v) for v in row] for row in rows]
    if not a:return 0
    ncol=len(a[0]); rank=0
    for c in range(ncol):
        r=next((i for i in range(rank,len(a)) if a[i][c]),None)
        if r is None:continue
        a[rank],a[r]=a[r],a[rank]
        for i in range(rank+1,len(a)):
            factor=a[i][c]/a[rank][c]
            if factor:
                for j in range(c,ncol):a[i][j]-=factor*a[rank][j]
        rank+=1
        if rank==len(a):break
    return rank


class PhaseObservabilityExactTests(unittest.TestCase):
    def test_invisible_now_visible_after_one_step(self):
        visible=lambda x:x[1]
        F=lambda x:(0,x[0]+x[1])
        for a in list(range(-10,0))+list(range(1,11)):
            x=(a,0);y=(0,0)
            self.assertEqual(visible(x),visible(y))
            self.assertNotEqual(visible(F(x)),visible(F(y)))

    def test_sharp_rank_growth_for_cyclic_coordinate_readout(self):
        for d in (4,7,9,12):
            for q in range(1,d+1):
                e=[[int(j==i) for j in range(d)] for i in range(d)]
                for T in range(1, min(5,d)+1):
                    rows=[]
                    for t in range(T):
                        for k in range(q):
                            rows.append(e[(q*t+k)%d])
                    self.assertEqual(fraction_rank(rows),min(d,q*T))

    def test_exact_reconstruction_in_four_loops(self):
        for x in itertools.product((0,1),repeat=4):
            self.assertEqual(temporal_observation(x,1,4),x)
            for y in itertools.product((0,1),repeat=4):
                self.assertEqual(temporal_observation(x,1,4)==temporal_observation(y,1,4),x==y)

    def test_coordinate_freeze_while_context_moves(self):
        def F(s):return (s[0]+1, Q(1,2)*s[1]+Q(3,5)*s[0])
        def controlled(s):return (s[0],F(s)[1])
        for key,context in itertools.product((-2,0,3),(-1,0,2)):
            state=(Q(key),Q(context))
            for _ in range(12):
                self.assertEqual(state[0],Q(key))
                state=controlled(state)

    def test_exact_readout_fiber_linear_algebra(self):
        # Readout sees the sum of coordinates; all vectors on the circle
        # in its orthogonal plane with fixed Euclidean norm have identical
        # readout. This exact-integer witness needs no floating-point SVD.
        readout=lambda x:sum(x)
        x=(3,0,0)
        y=(0,3,0)
        z=(0,0,3)
        self.assertEqual(readout(x),readout(y))
        self.assertEqual(readout(y),readout(z))
        self.assertEqual(sum(t*t for t in x),sum(t*t for t in y))
        self.assertEqual(sum(t*t for t in x),sum(t*t for t in z))
        # Dynamics can promote the readout-invisible distinction.
        F=lambda s:(s[1],s[2],s[0])
        first=lambda s:s[0]
        self.assertEqual(first(x),3)
        self.assertEqual(first(y),0)
        self.assertEqual(first(F(x)),0)
        self.assertEqual(first(F(z)),0)


if __name__=='__main__':unittest.main()
