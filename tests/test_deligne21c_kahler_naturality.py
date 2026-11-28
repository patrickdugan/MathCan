"""DEL-21C: independent exact Kähler coordinate versus dual-number naturality.

The Kähler basis of K[x,y] is (dx,dy), and the basis coordinates
of d(P) are the actual formal partials. Evaluating those at u and
pairing with a tangent vector v must recover the epsilon coefficient
of P(u+epsilon*v), in all characteristics.

Test cases preserve the full defining ideal: the dual-number
scheme tangent for (x^2) differs from that of the radical (x).
"""
from __future__ import annotations

import json
import unittest
from pathlib import Path

PRIMES=(2,3,5,7,11,13,17)
MODES=("parabola","node","double_line","radical_mutant","redundant","generic_polynomial")


def frozen_rows() -> list[dict]:
    rows=[]
    for n in range(144):
        p=PRIMES[n % len(PRIMES)]
        mode=MODES[n % len(MODES)]
        x,y=(3*n+1)%p,(5*n+2)%p
        dx,dy=(7*n+3)%p,(n*n+4)%p
        if mode=="parabola":
            y=x*x%p
        if mode=="node":
            x=0
        if mode in ("double_line","radical_mutant","redundant"):
            x=0
        if mode=="radical_mutant":
            dx=1
        abc=[(n+1)%p,(2*n+3)%p,(3*n+5)%p,(5*n+7)%p,
             (7*n+11)%p,(11*n+13)%p]
        rows.append({
            "id":f"DEL21C-{n+1:03d}",
            "field":f"F{p}","mode":mode,
            "x":x,"y":y,"dx":dx,"dy":dy,"coefficients":abc
        })
    return rows


def generic_poly(c: list[int]) -> dict[tuple[int,int],int]:
    # Includes nonlinear terms that expose the product rule,
    # with integer coefficients reduced only at evaluation time.
    return {
        (0,0):c[0],(1,0):c[1],(0,1):c[2],
        (2,0):c[3],(1,1):c[4],(0,3):c[5],
        (2,2):c[0]+c[4]
    }


def formal_partial(poly,axis):
    out={}
    for (i,j),a in poly.items():
        exponents=[i,j]
        power=exponents[axis]
        if power:
            exponents[axis]-=1
            k=tuple(exponents)
            out[k]=out.get(k,0)+a*power
    return {k:v for k,v in out.items() if v}


def scalar_eval(poly,x,y,p):
    return sum(a*x**i*y**j for (i,j),a in poly.items())%p


def dual_mul(a,b,p):
    return (a[0]*b[0]%p,(a[0]*b[1]+a[1]*b[0])%p)


def dual_pow(a,n,p):
    v=(1,0)
    for _ in range(n):
        v=dual_mul(v,a,p)
    return v


def dual_eval(poly,x,y,dx,dy,p):
    acc=(0,0)
    for (i,j),coef in poly.items():
        t=dual_mul((coef%p,0),dual_mul(
            dual_pow((x,dx),i,p),dual_pow((y,dy),j,p),p),p)
        acc=((acc[0]+t[0])%p,(acc[1]+t[1])%p)
    return acc


def product_poly(A,B):
    out={}
    for (i,j),a in A.items():
        for (k,l),b in B.items():
            key=(i+k,j+l)
            out[key]=out.get(key,0)+a*b
    return {k:v for k,v in out.items() if v}


def ideal_gen(mode):
    if mode=="parabola":
        return {(0,1):1,(2,0):-1}
    if mode=="node":
        return {(1,1):1}
    if mode in ("double_line","radical_mutant","redundant"):
        return {(2,0):1}
    return {}


class KahlerCoordinateNaturalityOracle(unittest.TestCase):
    def test_frozen_corpus(self):
        path=Path(__file__).resolve().parents[1]/(
            "research/deligne_sign_audit/del21c_tasks.jsonl")
        rows=[json.loads(line) for line in path.read_text().splitlines() if line]
        self.assertEqual(rows,frozen_rows())
        self.assertEqual(len(rows),144)
        self.assertEqual(len({r["id"] for r in rows}),144)
        self.assertEqual(
            {mode:sum(row["mode"]==mode for row in rows) for mode in MODES},
            {mode:24 for mode in MODES})

    def test_kahler_coordinate_pairing_matches_epsilon(self):
        for row in frozen_rows():
            p=int(row["field"][1:])
            x,y,dx,dy=(row[k] for k in ("x","y","dx","dy"))
            poly=generic_poly(row["coefficients"])
            px=formal_partial(poly,0)
            py=formal_partial(poly,1)
            kahler=(scalar_eval(px,x,y,p)*dx+
                    scalar_eval(py,x,y,p)*dy)%p
            first=dual_eval(poly,x,y,dx,dy,p)
            self.assertEqual(first,(scalar_eval(poly,x,y,p),kahler),row)

    def test_coordinate_differentials_are_unit_vectors(self):
        for row in frozen_rows():
            p=int(row["field"][1:])
            x,y,dx,dy=(row[k] for k in ("x","y","dx","dy"))
            self.assertEqual(dual_eval({(1,0):1},x,y,dx,dy,p),(x,dx))
            self.assertEqual(dual_eval({(0,1):1},x,y,dx,dy,p),(y,dy))
            self.assertEqual(formal_partial({(1,0):1},0),{(0,0):1})
            self.assertEqual(formal_partial({(0,1):1},1),{(0,0):1})

    def test_product_rule_global_coefficients(self):
        for row in frozen_rows():
            p=int(row["field"][1:])
            x,y,dx,dy=(row[k] for k in ("x","y","dx","dy"))
            P=generic_poly(row["coefficients"])
            G=ideal_gen(row["mode"])
            lhs=dual_eval(product_poly(P,G),x,y,dx,dy,p)
            rhs=dual_mul(dual_eval(P,x,y,dx,dy,p),
                         dual_eval(G,x,y,dx,dy,p),p)
            self.assertEqual(lhs,rhs,row)

    def test_first_order_quotient_ideal_vanishing(self):
        for row in frozen_rows():
            p=int(row["field"][1:])
            x,y,dx,dy=(row[k] for k in ("x","y","dx","dy"))
            G=ideal_gen(row["mode"])
            if not G:
                continue
            if dual_eval(G,x,y,dx,dy,p)!=(0,0):
                continue
            P=generic_poly(row["coefficients"])
            self.assertEqual(dual_eval(product_poly(G,P),
                x,y,dx,dy,p),(0,0))

    def test_nilpotent_radical_replacement_is_detected(self):
        for row in frozen_rows():
            if row["mode"]!="radical_mutant":
                continue
            p=int(row["field"][1:])
            x,y,dx,dy=(row[k] for k in ("x","y","dx","dy"))
            self.assertEqual(dual_eval({(2,0):1},x,y,dx,dy,p),(0,0))
            self.assertEqual(dual_eval({(1,0):1},x,y,dx,dy,p),(0,1))

    def test_redundant_generators_same_tangent_conditions(self):
        for row in frozen_rows():
            if row["mode"]!="redundant":
                continue
            p=int(row["field"][1:])
            x,y,dx,dy=(row[k] for k in ("x","y","dx","dy"))
            self.assertEqual(dual_eval({(2,0):1},x,y,dx,dy,p),(0,0))
            self.assertEqual(dual_eval({(3,0):1},x,y,dx,dy,p),(0,0))

    def test_characteristic_two_power_rule(self):
        p=2
        for x in range(2):
            for y in range(2):
                for dx in range(2):
                    for dy in range(2):
                        self.assertEqual(dual_eval({(2,0):1},x,y,dx,dy,p),
                                         (x*x%p,0))
                        self.assertEqual(scalar_eval(
                            formal_partial({(2,0):1},0),x,y,p),0)

    def test_node_tangent_coordinate_rank(self):
        for p in PRIMES:
            gen={(1,1):1}
            at_origin=[(dx,dy) for dx in range(p) for dy in range(p)
                       if dual_eval(gen,0,0,dx,dy,p)==(0,0)]
            self.assertEqual(len(at_origin),p*p)
            at_smooth=[(dx,dy) for dx in range(p) for dy in range(p)
                       if dual_eval(gen,1,0,dx,dy,p)==(0,0)]
            self.assertEqual(len(at_smooth),p)


if __name__=="__main__":
    unittest.main()
