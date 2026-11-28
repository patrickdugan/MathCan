import unittest
from fractions import Fraction
from itertools import permutations, combinations

def matching_states(v):
    if not v:
        yield ()
        return
    a,*tail=v
    for j,b in enumerate(tail):
        for sub in matching_states(tail[:j]+tail[j+1:]):
            yield tuple(sorted(((a,b),)+sub))

def transform(perm,matching):
    return tuple(sorted(tuple(sorted((perm[a],perm[b]))) for a,b in matching))

def pooled(g,h,k,phi,bias):
    edges=combinations(range(2*k),2)
    return bias+sum((phi[int(e in g),int(e in h)] for e in edges),Fraction(0))

class EdgePoolingTests(unittest.TestCase):
    def test_pooled_readout_exact_affine_overlap(self):
        phi={(0,0):Fraction(2),(0,1):Fraction(-1),
             (1,0):Fraction(3),(1,1):Fraction(11,2)}
        bias=Fraction(2,3)
        for k in (2,3):
            matchings=tuple(matching_states(list(range(2*k))))
            N=k*(2*k-1)
            A=bias+k*(phi[1,0]+phi[0,1])+(N-2*k)*phi[0,0]
            Delta=phi[1,1]-phi[1,0]-phi[0,1]+phi[0,0]
            for g in matchings:
                for h in matchings:
                    c=len(set(g)&set(h))
                    self.assertEqual(pooled(g,h,k,phi,bias),A+Delta*c)
                    if g!=h:
                        self.assertLessEqual(c,k-2)

    def test_relabeling_exact_for_each_edge_pool(self):
        phi={(0,0):Fraction(7,3),(0,1):Fraction(4,7),
             (1,0):Fraction(-2,3),(1,1):Fraction(9,2)}
        for k in (2,3):
            ms=tuple(matching_states(list(range(2*k))))
            perms=list(permutations(range(2*k)))[:24]
            for perm in perms:
                for g in ms:
                    for h in ms:
                        self.assertEqual(pooled(g,h,k,phi,Fraction(0)),
                                         pooled(transform(perm,g),transform(perm,h),k,phi,Fraction(0)))

    def test_gap_to_nearest_nonmatching(self):
        for k in (2,3):
            ms=tuple(matching_states(list(range(2*k))))
            overlaps=[len(set(g)&set(h)) for g in ms for h in ms if g!=h]
            self.assertEqual(max(overlaps),k-2)
            self.assertEqual(min(overlaps),0)

if __name__=='__main__':
    unittest.main()
