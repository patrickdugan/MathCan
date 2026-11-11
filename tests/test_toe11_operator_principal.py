"""Independent six-dimensional curvature/gauge second-variation checks."""
import math
import random
import unittest
from fractions import Fraction as Q
from research.toe.mixed_principal import partial_jet,det
from research.toe.operator_principal import (
    colored_background, electric_flavor_change,build_theta,
    pair_curvature_first, susceptibility, zeros, identity, inverse, mul,
    wave_riemann_pair, wave_field_strength, wave_example, gram, S, PAIR,
    differential,
)


def mk(E=(Q(1,3),Q(1,2)),B=(Q(1,4),Q(1,5)),sig=Q(1,70)):
    return dict(E=E,B=B,A=Q(2,5),Bcurv=1,alpha=Q(1,50),
                beta=Q(1,100),sigma=sig)


def full(E,B,**kw):
    a=mk(E,B);a.update(kw)
    return a


class ExactOperatorTests(unittest.TestCase):
    def test_induced_six_dimensional_orthonormal_block(self):
        x=mk();E,B=x['E'],x['B']
        T=build_theta(colored_background(E,B),x['A'],x['Bcurv'],x['alpha'],x['beta'])
        p=partial_jet(E,B,A=x['A'],Bcurv=x['Bcurv'],alpha=x['alpha'],beta=x['beta'],sigma=x['sigma'])
        for k in range(3):
            self.assertEqual(T[k][k],p.theta_e)
            self.assertEqual(T[k+3][k+3],p.theta_b)
            self.assertEqual(T[k][k+3],x['alpha']*sum((e*b for e,b in zip(E,B)),Q()))
            self.assertEqual(T[k+3][k],-T[k][k+3])

    def test_inverse_exact(self):
        A=build_theta(colored_background((1,2),(Q(1,7),Q(1,11))),Q(1,5),1,Q(1,80),Q(1,120))
        B=inverse(A);C=mul(A,B)
        self.assertEqual(C,identity())

    def test_match_reduced_hessian_two_flavors(self):
        r=random.Random(202611)
        for _ in range(25):
            E=tuple(Q(r.randint(-5,5),10) for i in range(2))
            B=tuple(Q(r.randint(-5,5),10) for i in range(2))
            d=mk(E,B)
            p=partial_jet(E,B,A=d['A'],Bcurv=d['Bcurv'],alpha=d['alpha'],beta=d['beta'],sigma=d['sigma'])
            F=colored_background(E,B)
            for j in (0,1):
                df=electric_flavor_change(2,j)
                s=susceptibility(F,df,pair_curvature_first(1),A=d['A'],B=d['Bcurv'],
                                 alpha=d['alpha'],beta=d['beta'],sigma=d['sigma'])
                self.assertEqual(s['rr'],p.curvature_entry)
                self.assertEqual(s['rf'],p.mixed_entries[j])
                self.assertEqual(s['ff'],p.gauge_hessian[j][j])

    def test_reduced_mixed_gauge_hessian(self):
        x=mk();F=colored_background(x['E'],x['B'])
        df1=electric_flavor_change(2,0)
        df2=electric_flavor_change(2,1)
        def add(a,b):return tuple(tuple(x+y for x,y in zip(u,v)) for u,v in zip(a,b))
        a=susceptibility(F,df1,zeros(),A=x['A'],B=x['Bcurv'],alpha=x['alpha'],beta=x['beta'],sigma=x['sigma'])['ff']
        b=susceptibility(F,df2,zeros(),A=x['A'],B=x['Bcurv'],alpha=x['alpha'],beta=x['beta'],sigma=x['sigma'])['ff']
        c=susceptibility(F,add(df1,df2),zeros(),A=x['A'],B=x['Bcurv'],alpha=x['alpha'],beta=x['beta'],sigma=x['sigma'])['ff']
        k=partial_jet(x['E'],x['B'],A=x['A'],Bcurv=x['Bcurv'],alpha=x['alpha'],beta=x['beta'],sigma=x['sigma'])
        self.assertEqual((c-a-b)/2,k.gauge_hessian[0][1])

    def test_susceptibility_reciprocity(self):
        x=mk();F=colored_background(x['E'],x['B']);d=electric_flavor_change(2,0)
        a=susceptibility(F,d,pair_curvature_first(1),A=x['A'],B=x['Bcurv'],alpha=x['alpha'],beta=x['beta'],sigma=x['sigma'])
        self.assertNotEqual(a['rf'],0)
        # This is the same scalar whether interpreted as d/dA(dL/dE) or d/dE(dL/dA).
        p=partial_jet(x['E'],x['B'],A=x['A'],Bcurv=x['Bcurv'],alpha=x['alpha'],beta=x['beta'],sigma=x['sigma'])
        self.assertEqual(a['rf'],p.mixed_entries[0])

    def test_pure_gauge_field_perturbation_null(self):
        xi=(2,0,1,3)
        da=wave_field_strength(xi,xi)
        self.assertEqual(da,(0,)*6)
        F=colored_background((2,1),(1,0))
        dF=tuple(da for _ in F)
        x=susceptibility(F,dF,zeros(),A=Q(2,5),B=1,
                         alpha=Q(3,500),beta=Q(1,100),sigma=Q(1,100))
        self.assertEqual((x['rr'],x['rf'],x['ff']),(0,0,0))

    def test_pure_diffeomorphism_metric_principal_null(self):
        xi=(3,1,2,0);v=(0,2,0,1)
        h=tuple(tuple(xi[i]*v[j]+xi[j]*v[i] for j in range(4)) for i in range(4))
        R=wave_riemann_pair(xi,h)
        self.assertEqual(R,zeros())

    def test_metric_wave_riemann_pair_exchange_and_bianchi(self):
        xi=(3,-1,2,4)
        h=((1,2,3,4),(2,5,6,7),(3,6,8,9),(4,7,9,10))
        r=wave_riemann_pair(xi,h)
        for i in range(6):
            for j in range(6):self.assertEqual(r[i][j]*S[j],r[j][i]*S[i])

    def test_wave_riemann_is_quadratic_in_covector(self):
        xi=(2,0,0,3)
        h=tuple(tuple(Q(1 if i==j==1 else -1 if i==j==2 else 0) for j in range(4)) for i in range(4))
        a=wave_riemann_pair(xi,h);b=wave_riemann_pair(tuple(3*z for z in xi),h)
        self.assertEqual(b,tuple(tuple(9*z for z in row) for row in a))

    def test_wave_field_is_linear_in_covector(self):
        xi=(2,0,0,3);a=(0,1,0,0)
        self.assertEqual(wave_field_strength(tuple(3*z for z in xi),a),
                         tuple(3*z for z in wave_field_strength(xi,a)))

    def test_wave_susceptibilities_scaling(self):
        F=colored_background((2,1),(1,0));
        dF=tuple(wave_field_strength((1,0,0,1),(0,1,0,0)) for _ in F)
        dR=wave_riemann_pair((1,0,0,1),tuple(tuple(Q(1 if i==j==1 else -1 if i==j==2 else 0) for j in range(4)) for i in range(4)))
        p=dict(A=Q(2,5),B=1,alpha=Q(3,500),beta=Q(1,100),sigma=Q(1,100))
        a=susceptibility(F,dF,dR,**p)
        dF3=tuple(tuple(3*z for z in row) for row in dF)
        dR9=tuple(tuple(9*z for z in row) for row in dR)
        b=susceptibility(F,dF3,dR9,**p)
        self.assertEqual(b['rr'],81*a['rr'])
        self.assertEqual(b['rf'],27*a['rf'])
        self.assertEqual(b['ff'],9*a['ff'])

    def test_nonzero_mixed_third_derivative_projection(self):
        e=wave_example()
        self.assertNotEqual(Q(e['mixed_third_derivative']),0)
        self.assertTrue(Q(e['mixed_third_derivative'])>0)
        self.assertTrue(e['only_declared_two_form_sector'])

    def test_sigma_zero_reduces_to_minimal_yang_mills(self):
        F=colored_background((2,1),(1,0))
        dF=electric_flavor_change(2,0)
        r=susceptibility(F,dF,pair_curvature_first(1),A=Q(2,5),B=1,
                         alpha=Q(3,500),beta=Q(1,100),sigma=0)
        self.assertEqual((r['rr'],r['rf'],r['ff']),(0,0,3))

    def test_bad_dimensions(self):
        with self.assertRaises(ValueError):inverse(((Q(1),),))
        with self.assertRaises(ValueError):wave_field_strength((1,2),(1,2))
        with self.assertRaises(ValueError):wave_riemann_pair((1,2),((1,2),(2,3)))
        with self.assertRaises(ValueError):colored_background((1,2),(3,))
        with self.assertRaises(ValueError):build_theta(colored_background((1,),(0,)),0,0,0,1)

    def test_matrix_full_variation_matches_logdet_finite_differences(self):
        # Unconstrained local source perturbations in the curvature pair matrix.
        # Independent determinant/log evaluation, apart from initial 6x construction.
        F=colored_background((Q(1,3),Q(1,2)),(Q(1,4),Q(1,5)))
        dF=electric_flavor_change(2,0)
        dR=pair_curvature_first(1)
        a=Q(1,50);b=Q(1,100);sigma=Q(1,70);A=Q(2,5);Bc=Q(1)
        q=susceptibility(F,dF,dR,A=A,B=Bc,alpha=a,beta=b,sigma=sigma)
        h=1e-4
        def energy(t):
            tt=Q(str(t))
            FF=tuple(tuple(x+tt*y for x,y in zip(u,v)) for u,v in zip(F,dF))
            T0=build_theta(FF,A,Bc,a,b)
            theta=tuple(tuple(T0[i][j]-b*tt*dR[i][j] for j in range(6)) for i in range(6))
            D=det(theta)
            ym=-sum((S[i]*f[i]*f[i] for f in FF for i in range(6)),Q())/2
            return float(ym)-float(sigma)*math.log(float(D))
        est=(energy(h)-2*energy(0)+energy(-h))/(h*h)
        self.assertAlmostEqual(est,float(q['rr']+2*q['rf']+q['ff']),delta=3e-7)

if __name__=='__main__':unittest.main()
