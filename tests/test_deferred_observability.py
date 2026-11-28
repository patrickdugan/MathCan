"""SPC-08 exact rational rank decomposition and cyclic observability certificates.

Uses only Python standard library; no approximate numerical rank threshold.
"""
import random
import unittest
from fractions import Fraction as Q


def rank(rows):
    if not rows:
        return 0
    M = [[Q(v) for v in row] for row in rows]
    n = len(M[0])
    if any(len(row) != n for row in M):
        raise ValueError('ragged exact matrix')
    r = 0
    for j in range(n):
        pivot = next((i for i in range(r, len(M)) if M[i][j]), None)
        if pivot is None:
            continue
        M[r], M[pivot] = M[pivot], M[r]
        div = M[r][j]
        M[r] = [v / div for v in M[r]]
        for i in range(len(M)):
            if i != r:
                factor = M[i][j]
                if factor:
                    M[i] = [a - factor*b for a,b in zip(M[i], M[r])]
        r += 1
        if r == len(M):
            break
    return r


def kernel_basis(rows, dim):
    """Free-column rational basis for ker C, returned as column vectors."""
    M = [[Q(v) for v in row] for row in rows]
    if any(len(row) != dim for row in M):
        raise ValueError('row dimension mismatch')
    pivots = []
    for j in range(dim):
        k = len(pivots)
        found = next((i for i in range(k,len(M)) if M[i][j]),None)
        if found is None:
            continue
        M[k],M[found] = M[found],M[k]
        scale = M[k][j]
        M[k] = [x/scale for x in M[k]]
        for i in range(len(M)):
            if i != k:
                coeff=M[i][j]
                if coeff:
                    M[i] = [a-coeff*b for a,b in zip(M[i],M[k])]
        pivots.append(j)
        if len(pivots)==len(M):break
    free = [j for j in range(dim) if j not in pivots]
    basis = []
    for j in free:
        v=[Q(0)]*dim
        v[j]=Q(1)
        for i,p in enumerate(pivots):
            v[p]=-M[i][j]
        basis.append(v)
    return basis


def apply(rows,vector):
    return [sum((Q(a)*b for a,b in zip(row,vector)),Q(0)) for row in rows]


def multiply(a,b):
    if not a or not b:
        return []
    return [[sum((Q(x)*Q(b[k][j]) for k,x in enumerate(row)),Q(0))
             for j in range(len(b[0]))] for row in a]


def shift(dim):
    return [[int(j==(i+1)%dim) for j in range(dim)] for i in range(dim)]


def observable_rows(A, C, horizon):
    rows=list(C)
    b=list(C)
    for _ in range(horizon):
        b=multiply(b,A)
        rows.extend(b)
    return rows


class DeferredObservabilityExactTests(unittest.TestCase):
    def test_rank_quotient_identity_over_rationals(self):
        rng=random.Random(20261115)
        for dim in range(2,8):
            for _ in range(75):
                current=[[rng.randrange(-2,3) for _ in range(dim)]
                         for i in range(rng.randrange(0,dim+1))]
                delayed=[[rng.randrange(-2,3) for _ in range(dim)]
                         for i in range(rng.randrange(0,dim+1))]
                null=kernel_basis(current,dim)
                restricted=[[value for value in apply(delayed,v)] for v in null]
                # Transpose restriction: each column is D v.
                matrix=list(map(list,zip(*restricted))) if delayed and restricted else []
                self.assertEqual(rank(current+delayed),rank(current)+rank(matrix))

    def test_sharp_all_horizon_cyclic_register(self):
        for width in range(2,10):
            A=shift(width)
            C=[[int(i==0) for i in range(width)]]
            for horizon in range(2*width+1):
                obs=observable_rows(A,C,horizon)
                self.assertEqual(rank(obs),min(width,horizon+1))
                delayed=obs[1:]
                null=kernel_basis(C,width)
                restriction=list(map(list,zip(*[apply(delayed,v) for v in null])))
                self.assertEqual(rank(restriction),min(width-1,horizon))

    def test_delayed_hidden_coordinate_is_causally_future_visible(self):
        A=shift(2)
        C=[[1,0]]
        present=[0,1]
        self.assertEqual(apply(C,present),[0])
        self.assertEqual(apply(multiply(C,A),present),[1])
        self.assertEqual(rank(observable_rows(A,C,0)),1)
        self.assertEqual(rank(observable_rows(A,C,1)),2)

    def test_coordinate_permutation_conjugates_observation(self):
        for width in range(2,8):
            A=shift(width)
            C=[[int(j==0) for j in range(width)]]
            perm=list(range(width));perm.reverse()
            Qm=[[int(j==perm[i]) for j in range(width)] for i in range(width)]
            Qt=list(map(list,zip(*Qm)))
            conjugate=multiply(multiply(Qm,A),Qt)
            newreadout=multiply(C,Qt)
            for horizon in range(width+2):
                observed=observable_rows(A,C,horizon)
                transformed=observable_rows(conjugate,newreadout,horizon)
                self.assertEqual(transformed,multiply(observed,Qt))
                self.assertEqual(rank(transformed),rank(observed))

    def test_disjoint_future_and_present_gain_in_two_cell_model(self):
        C=[[1,0]]
        A=shift(2)
        future=multiply(C,A)
        self.assertEqual(apply(C,[0,3]),[0])
        self.assertEqual(apply(future,[0,3]),[3])
        self.assertEqual(apply(C,[4,0]),[4])
        self.assertEqual(apply(future,[4,0]),[0])

if __name__=='__main__':
    unittest.main()
