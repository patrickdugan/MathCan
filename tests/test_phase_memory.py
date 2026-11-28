"""Exact rational independent checks for SPC-04 Hermite phase memory."""
import unittest
from fractions import Fraction
from itertools import product


def poly_add(a, b):
    out = [Fraction(0)] * max(len(a), len(b))
    for i, x in enumerate(a):out[i] += x
    for i, x in enumerate(b):out[i] += x
    return out


def poly_mul(a, b):
    out = [Fraction(0)] * (len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[i+j] += x*y
    return out


def poly_eval(p,x):
    z=Fraction(0)
    for c in reversed(p):z=z*x+c
    return z


def derivative(p):
    return [i*p[i] for i in range(1,len(p))] or [Fraction(0)]


def hermite_cycle(p):
    if p<2:raise ValueError('p needs at least two nodes')
    coeff=[Fraction(0)]
    for i in range(p):
        L=[Fraction(1)]
        for j in range(p):
            if j!=i:L=poly_mul(L, [-Fraction(j,i-j), Fraction(1,i-j)])
        Ld=poly_eval(derivative(L),i)
        pref=[1+2*Ld*i, -2*Ld]
        H=poly_mul(pref,poly_mul(L,L))
        coeff=poly_add(coeff,[v*Fraction((i+1)%p) for v in H])
    return coeff


def mm(a,b):
    return [[sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)] for i in range(2)]


class PhaseMemoryTests(unittest.TestCase):
    def test_exact_hermite_orbits_and_derivatives(self):
        for p in (2,3,4,5,6):
            f=hermite_cycle(p)
            self.assertLessEqual(len(f)-1,2*p-1)
            for i in range(p):
                self.assertEqual(poly_eval(f,i),(i+1)%p)
                self.assertEqual(poly_eval(derivative(f),i),0)
                current=i
                for _ in range(p):current=int(poly_eval(f,current))
                self.assertEqual(current,i)

    def test_twocycle_cubic(self):
        self.assertEqual(hermite_cycle(2),[1,0,-3,2])

    def test_tensor_power_has_many_exact_phases(self):
        for m in range(1,6):
            phases=list(product(range(3),repeat=m))
            self.assertEqual(len(phases),3**m)
            self.assertEqual(len(set(phases)),3**m)
            for state in phases:
                current=state
                for _ in range(3):current=tuple((x+1)%3 for x in current)
                self.assertEqual(current,state)

    def test_nilpotent_one_step_explosive_product(self):
        for q in (2,3,4,10):
            a=[[0,q],[0,0]];b=[[0,0],[q,0]]
            self.assertEqual(mm(a,a),[[0,0],[0,0]])
            self.assertEqual(mm(b,b),[[0,0],[0,0]])
            self.assertEqual(mm(b,a),[[0,0],[0,q*q]])

if __name__=='__main__':unittest.main()
