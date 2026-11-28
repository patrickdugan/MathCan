"""DEL-21B: independent exact Kähler-fiber and square-zero lift oracle.

For affine K[x,y]/(f) at a K-rational point, the fiber of the
Kähler differential module has the presentation K^2/<grad f>.
Its dual consists of the vectors annihilating grad f. The dual
numbers K[ε]/ε² provide the corresponding first-order algebra
lifts, which we enumerate for seven prime fields.
"""
import json
import unittest
from pathlib import Path

PRIMES=(2,3,5,7,11,13,17)
MODES=("parabola","node_origin","double_line",
       "radical_line","repeated_root","smooth_root")


def frozen():
    rows=[]
    for n in range(96):
        p=PRIMES[n%len(PRIMES)]
        mode=MODES[n%len(MODES)]
        a=(3*n+1)%p
        x,y=(7*n+2)%p,(5*n+4)%p
        if mode=="parabola":
            y=x*x%p
        if mode=="node_origin":
            x=y=0
        if mode in ("double_line","radical_line"):
            x=0
        if mode in ("repeated_root","smooth_root"):
            x=a
        if mode=="parabola":
            g=(-2*x%p,1)
        elif mode in ("node_origin","double_line","repeated_root"):
            g=(0,0)
        else:
            g=(1,0)
        rank=int(g!=(0,0))
        rows.append({
            "id":f"DEL21B-{n+1:03d}",
            "field":f"F{p}","mode":mode,
            "x":x,"y":y,"a":a,
            "grad_x":g[0],"grad_y":g[1],
            "cotangent_dim":2-rank,
            "expected_lifts":p**(2-rank),
        })
    return rows


def defining_poly(mode,a):
    if mode=="parabola":
        return {(0,1):1,(2,0):-1}
    if mode=="node_origin":
        return {(1,1):1}
    if mode=="double_line":
        return {(2,0):1}
    if mode=="radical_line":
        return {(1,0):1}
    if mode=="repeated_root":
        return {(2,0):1,(1,0):-2*a,(0,0):a*a}
    if mode=="smooth_root":
        return {(1,0):1,(0,0):-a}
    raise ValueError(mode)


def dual_mul(u,v,p):
    return (u[0]*v[0]%p,(u[0]*v[1]+u[1]*v[0])%p)


def dual_pow(x,n,p):
    z=(1,0)
    for _ in range(n):
        z=dual_mul(z,x,p)
    return z


def polynomial_first_order(poly,x,y,dx,dy,p):
    result=(0,0)
    for (m,n),coef in poly.items():
        z=dual_mul(dual_pow((x,dx),m,p),
                   dual_pow((y,dy),n,p),p)
        z=dual_mul((coef%p,0),z,p)
        result=((result[0]+z[0])%p,(result[1]+z[1])%p)
    return result


def formal_gradient(poly,x,y,p):
    a,b=0,0
    for (m,n),c in poly.items():
        if m:
            a+=m*c*x**(m-1)*y**n
        if n:
            b+=n*c*x**m*y**(n-1)
    return (a%p,b%p)


class KahlerSquareZeroOracle(unittest.TestCase):
    def test_frozen_manifest(self):
        file=(Path(__file__).resolve().parents[1]/
              "research/deligne_sign_audit/del21b_tasks.jsonl")
        loaded=[json.loads(s) for s in file.read_text().splitlines() if s]
        self.assertEqual(loaded,frozen())
        self.assertEqual(len(loaded),96)
        self.assertEqual(len({r["id"] for r in loaded}),96)
        self.assertEqual({m:sum(r["mode"]==m for r in loaded)
                          for m in MODES},{m:16 for m in MODES})

    def test_kahler_conormal_cotangent_rank(self):
        for r in frozen():
            p=int(r["field"][1:])
            f=defining_poly(r["mode"],r["a"])
            self.assertEqual(polynomial_first_order(f,r["x"],r["y"],0,0,p),(0,0))
            gx,gy=formal_gradient(f,r["x"],r["y"],p)
            self.assertEqual((gx,gy),(r["grad_x"],r["grad_y"]))
            rank=int((gx,gy)!=(0,0))
            self.assertEqual(2-rank,r["cotangent_dim"])

    def test_derivations_equal_square_zero_lifts(self):
        for r in frozen():
            p=int(r["field"][1:])
            f=defining_poly(r["mode"],r["a"])
            accepted=0
            for dx in range(p):
                for dy in range(p):
                    from_gradient=(r["grad_x"]*dx+r["grad_y"]*dy)%p==0
                    lifted=polynomial_first_order(
                        f,r["x"],r["y"],dx,dy,p)==(0,0)
                    self.assertEqual(from_gradient,lifted,(r,dx,dy))
                    accepted+=lifted
            self.assertEqual(accepted,r["expected_lifts"])

    def test_nonreduced_double_line_vs_radical(self):
        for p in PRIMES:
            thick={(2,0):1}
            reduced={(1,0):1}
            for y in range(p):
                self.assertEqual(polynomial_first_order(thick,0,y,1,0,p),(0,0))
                self.assertEqual(polynomial_first_order(reduced,0,y,1,0,p),(0,1))

    def test_singular_node_tangent_fiber_dimension(self):
        for p in PRIMES:
            f={(1,1):1}
            at_origin=sum(polynomial_first_order(f,0,0,dx,dy,p)==(0,0)
                          for dx in range(p) for dy in range(p))
            at_smooth=sum(polynomial_first_order(f,1,0,dx,dy,p)==(0,0)
                          for dx in range(p) for dy in range(p))
            self.assertEqual(at_origin,p*p)
            self.assertEqual(at_smooth,p)

    def test_redundant_generators_preserve_conormal_span(self):
        # (x²,x³) has the same ideal as (x²); both derivative rows
        # vanish along x=0. The quotient retains its nilpotents.
        for p in PRIMES:
            for y in range(p):
                for dx in range(p):
                    self.assertEqual(
                        polynomial_first_order({(2,0):1},0,y,dx,1,p),
                        polynomial_first_order({(3,0):1},0,y,dx,1,p))

    def test_p2_repeated_root_is_nonreduced(self):
        p=2
        for a in range(2):
            repeated=defining_poly("repeated_root",a)
            reduced=defining_poly("smooth_root",a)
            self.assertEqual(polynomial_first_order(repeated,a,0,1,0,p),(0,0))
            self.assertEqual(polynomial_first_order(reduced,a,0,1,0,p),(0,1))

    def test_dual_number_square_zero(self):
        for p in PRIMES:
            for a in range(p):
                for b in range(p):
                    self.assertEqual(dual_mul((0,a),(0,b),p),(0,0))


if __name__=="__main__":
    unittest.main()
