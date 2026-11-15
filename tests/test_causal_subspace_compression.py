"""Independent exact-rational SPC-09 witnesses and analytical-bound checks."""
from fractions import Fraction as F
import itertools
import random
import unittest


def transpose(A): return list(map(list, zip(*A)))
def multiply(A,B): return [[sum(x*y for x,y in zip(a,b)) for b in transpose(B)] for a in A]
def subtract(A,B): return [[x-y for x,y in zip(a,b)] for a,b in zip(A,B)]
def rank(A):
    A=[list(map(F,row)) for row in A]; row=0
    for col in range(len(A[0])):
        pivot=next((k for k in range(row,len(A)) if A[k][col]),None)
        if pivot is None: continue
        A[row],A[pivot]=A[pivot],A[row]
        v=A[row][col]; A[row]=[x/v for x in A[row]]
        for k in range(len(A)):
            if k!=row:
                v=A[k][col]; A[k]=[x-v*y for x,y in zip(A[k],A[row])]
        row+=1
        if row==len(A): break
    return row


def kernel_basis(A):
    A=[list(map(F,row)) for row in A]; row=0; pivots=[]
    for col in range(len(A[0])):
        pivot=next((k for k in range(row,len(A)) if A[k][col]),None)
        if pivot is None: continue
        A[row],A[pivot]=A[pivot],A[row]; v=A[row][col]; A[row]=[x/v for x in A[row]]
        for k in range(len(A)):
            if k!=row:
                v=A[k][col]; A[k]=[x-v*y for x,y in zip(A[k],A[row])]
        pivots.append(col); row+=1
        if row==len(A): break
    vectors=[]
    for free in set(range(len(A[0])))-set(pivots):
        vector=[F(0)]*len(A[0]); vector[free]=F(1)
        for i,col in enumerate(pivots): vector[col]=-A[i][free]
        vectors.append(vector)
    return vectors


def step(x): return (not x[0],x[2],x[1],0)
def compress(x): return (*x[:3],0)
def erase(x): return (x[0],x[1],0,x[3])


class ExactCompressionTests(unittest.TestCase):
    def test_deferred_quotient_rank_identity(self):
        rng=random.Random(930909)
        for _ in range(300):
            d=rng.randint(1,5)
            J=[[F(rng.randint(-2,2)) for _ in range(d)] for _ in range(rng.randint(1,4))]
            B=[[F(rng.randint(-2,2)) for _ in range(d)] for _ in range(rng.randint(1,5))]
            K=kernel_basis(J)
            restricted=multiply(B,transpose(K)) if K else []
            deferred=rank(restricted) if K else 0
            self.assertEqual(rank(J+B),rank(J)+deferred)
            self.assertLessEqual(deferred,min(d-rank(J),len(B)))

    def test_inert_compression_preserves_arbitrary_horizon(self):
        for x in itertools.product((False,True),range(4),range(4),range(4)):
            a=x; b=compress(x)
            for _ in range(20):
                self.assertEqual(a[0],b[0]); self.assertEqual(a[1],b[1])
                a,b=step(a),step(b)
                self.assertEqual(a,b)

    def test_current_invisibility_does_not_imply_future_inertness(self):
        for b in range(1,20):
            x=(False,3,b,7); y=erase(x)
            self.assertEqual(x[1],y[1]); self.assertNotEqual(step(x)[1],step(y)[1])

    def test_gramian_perturbation_diagonal_exact_norms(self):
        for a,b,e,f in itertools.product(range(-3,4),repeat=4):
            original=max(abs(a),abs(b)); error=max(abs(e),abs(f))
            difference=max(abs((a+e)**2-a*a),abs((b+f)**2-b*b))
            self.assertLessEqual(difference,2*original*error+error*error)
        self.assertEqual(3**2-2**2,2*2*1+1)

    def test_recurrent_omission_bound_exact_one_norm(self):
        A=[[F(1,2),F(1,4)],[F(1,3),F(1,2)]]
        Q=[[F(1),F(0)],[F(0),F(0)]]
        L=max(sum(abs(A[i][j]) for i in range(2)) for j in range(2))
        x=[[F(2)],[F(3)]]; z=[[F(2)],[F(0)]]
        bound=sum(abs(r[0]) for r in subtract(x,z))
        for _ in range(20):
            x=multiply(A,x); z=multiply(Q,multiply(A,z))
            omitted=sum(abs(r[0]) for r in subtract(x,multiply(Q,x)))
            bound=omitted+L*bound
            self.assertLessEqual(sum(abs(r[0]) for r in subtract(x,z)),bound)

    def test_phase_half_gap_strictness(self):
        for delta in (F(-4),F(0),F(4),F(49,10)):
            self.assertLess(abs(delta),abs(10-delta))
        self.assertEqual(abs(F(5)),abs(10-F(5)))
        self.assertGreater(abs(F(6)),abs(10-F(6)))

    def test_taylor_radius_squared_remainder(self):
        for x in (F(-2),F(0),F(3)):
            for delta in (F(-1,10),F(1,100),F(1,2)):
                remainder=(x+delta)**2-x*x-2*x*delta
                self.assertEqual(remainder,delta*delta)

    def test_point_jacobian_is_not_a_tube_bound(self):
        x=F(0); delta=F(1)
        self.assertEqual(2*x,0)
        self.assertNotEqual((x+delta)**2-x*x,0)


if __name__=='__main__': unittest.main()
