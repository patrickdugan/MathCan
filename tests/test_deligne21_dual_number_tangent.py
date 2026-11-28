"""DEL-21A: exact dual-number quotient tangent and nonreduced-scheme oracle.

The target is the actual quotient algebra K[x,y]/I. Every generator
must evaluate to (0,0) in K[ε]/ε², not just vanish at K-rational
points. The ring-hom kernel condition is tested against ideal
multiplication and sparse polynomial formal derivatives.
"""
import json
import unittest
from pathlib import Path

PRIMES = (2, 3, 5, 7, 11, 13, 17)
MODES = ("parabola", "node", "double_line", "redundant", "radical_mutant")


def frozen_rows():
    rows = []
    for n in range(120):
        p = PRIMES[n % 7]
        mode = MODES[n % 5]
        x, y = (n*n+3) % p, (5*n+1) % p
        dx, dy = (7*n+1) % p, (11*n+3) % p
        if mode == "parabola":
            y = x*x % p
        if mode == "node":
            if n % 2 == 0:
                x = 0
            else:
                y = 0
        if mode in ("double_line", "redundant", "radical_mutant"):
            x = 0
        if mode == "radical_mutant":
            dx = 1
        f = ("y-x²" if mode == "parabola" else
             "xy" if mode == "node" else "x²")
        val = ((y-x*x) if mode == "parabola" else
               x*y if mode == "node" else 0) % p
        derivative = ((dy-2*x*dx) if mode == "parabola" else
                      y*dx+x*dy if mode == "node" else 0) % p
        radical = dx % p if mode == "radical_mutant" else None
        rows.append({
            "id": f"DEL21-{n+1:03d}", "field": f"F{p}", "mode": mode,
            "f": f, "x": x, "y": y, "dx": dx, "dy": dy,
            "value": val, "directional": derivative,
            "tangent": val == 0 and derivative == 0,
            "radical_directional": radical,
        })
    return rows


def dual_add(a, b, p):
    return ((a[0]+b[0]) % p, (a[1]+b[1]) % p)


def dual_mul(a, b, p):
    return (a[0]*b[0] % p, (a[0]*b[1]+a[1]*b[0]) % p)


def dual_pow(a, n, p):
    z = (1, 0)
    for _ in range(n):
        z = dual_mul(z, a, p)
    return z


def sparse_eval(poly, x, y, p):
    """Dictionary {(power_x,power_y): coefficient}."""
    return sum(coef*x**i*y**j for (i,j),coef in poly.items()) % p


def sparse_gradient(poly, x, y, dx, dy, p):
    return sum(coef*(i*x**(i-1)*y**j*dx if i else 0) +
               coef*(j*x**i*y**(j-1)*dy if j else 0)
               for (i,j),coef in poly.items()) % p


def sparse_dual_eval(poly, x, y, dx, dy, p):
    X, Y = (x, dx), (y, dy)
    acc = (0,0)
    for (i,j),coef in poly.items():
        term=dual_mul(dual_pow(X,i,p),dual_pow(Y,j,p),p)
        acc=dual_add(acc,dual_mul((coef%p,0),term,p),p)
    return acc


def sparse_mul(a,b):
    res={}
    for (i,j),v in a.items():
        for (k,l),w in b.items():
            key=(i+k,j+l)
            res[key]=res.get(key,0)+v*w
    return {k:v for k,v in res.items() if v}


POLYS={
    "parabola":{(0,1):1,(2,0):-1},
    "node":{(1,1):1},
    "double_line":{(2,0):1},
    "redundant":{(2,0):1},
    "radical_mutant":{(2,0):1},
}
MULTIPLIERS=({(0,0):1}, {(1,0):1}, {(0,1):1}, {(1,0):2,(0,1):1},
             {(2,0):1,(0,0):-3})


class DualNumberTangentOracle(unittest.TestCase):
    def test_frozen_corpus(self):
        path=(Path(__file__).resolve().parents[1]/
              "research/deligne_sign_audit/del21_tasks.jsonl")
        loaded=[json.loads(s) for s in path.read_text().splitlines() if s]
        self.assertEqual(loaded,frozen_rows())
        self.assertEqual(len(loaded),120)
        self.assertEqual(len({r["id"] for r in loaded}),120)
        self.assertEqual({m:sum(r["mode"]==m for r in loaded)
                          for m in MODES},{m:24 for m in MODES})

    def test_actual_first_order_evaluation(self):
        for r in frozen_rows():
            p=int(r["field"][1:])
            poly=POLYS[r["mode"]]
            got=sparse_dual_eval(poly,r["x"],r["y"],r["dx"],r["dy"],p)
            self.assertEqual(got,(r["value"],r["directional"]),r)
            self.assertEqual(got==(0,0),r["tangent"])

    def test_sparse_derivative_equals_dual_number_snd(self):
        for r in frozen_rows():
            p=int(r["field"][1:])
            for poly in (*POLYS.values(),*MULTIPLIERS):
                dual=sparse_dual_eval(poly,r["x"],r["y"],r["dx"],r["dy"],p)
                self.assertEqual(dual,(sparse_eval(poly,r["x"],r["y"],p),
                    sparse_gradient(poly,r["x"],r["y"],r["dx"],r["dy"],p)))

    def test_multiplication_preserves_ideal_kernel(self):
        for r in frozen_rows():
            p=int(r["field"][1:])
            g=POLYS[r["mode"]]
            jet_g=sparse_dual_eval(g,r["x"],r["y"],r["dx"],r["dy"],p)
            for h in MULTIPLIERS:
                jet_product=sparse_dual_eval(sparse_mul(g,h),
                    r["x"],r["y"],r["dx"],r["dy"],p)
                jet_factor=dual_mul(jet_g,sparse_dual_eval(h,
                    r["x"],r["y"],r["dx"],r["dy"],p),p)
                self.assertEqual(jet_product,jet_factor)
                if jet_g==(0,0):
                    self.assertEqual(jet_product,(0,0))

    def test_redundant_generators_do_not_change_tangent(self):
        for r in frozen_rows():
            if r["mode"]!="redundant":
                continue
            p=int(r["field"][1:])
            g=POLYS["redundant"]
            x3={(3,0):1}
            self.assertEqual(sparse_dual_eval(g,r["x"],r["y"],
                r["dx"],r["dy"],p),(0,0))
            self.assertEqual(sparse_dual_eval(x3,r["x"],r["y"],
                r["dx"],r["dy"],p),(0,0))

    def test_nonreduced_radical_mutant_is_detected(self):
        # K[x,y]/(x²) has every tangent direction at x=0, whereas
        # K[x,y]/(x) forces dx=0. Their rational zero sets coincide.
        for r in frozen_rows():
            if r["mode"]!="radical_mutant":
                continue
            p=int(r["field"][1:])
            thick=sparse_dual_eval({(2,0):1},r["x"],r["y"],
                r["dx"],r["dy"],p)
            reduced=sparse_dual_eval({(1,0):1},r["x"],r["y"],
                r["dx"],r["dy"],p)
            self.assertEqual(thick,(0,0))
            self.assertEqual(reduced,(0,1%p))
            self.assertNotEqual(thick,reduced)

    def test_node_tangent_rank_jumps_at_origin(self):
        for p in PRIMES:
            for x,y in ((0,0),(1,0),(0,1)):
                directions=[(dx,dy) for dx in range(p)
                            for dy in range(p)
                            if sparse_dual_eval({(1,1):1},x,y,dx,dy,p)==(0,0)]
                self.assertEqual(len(directions),p*p if x==0 and y==0 else p)

    def test_double_line_tangent_all_directions_all_fields(self):
        for p in PRIMES:
            for y in range(p):
                for dx in range(p):
                    for dy in range(p):
                        self.assertEqual(sparse_dual_eval({(2,0):1},
                            0,y,dx,dy,p),(0,0))

    def test_char_two_nilpotent_and_derivative(self):
        p=2
        self.assertEqual(dual_mul((0,1),(0,1),p),(0,0))
        self.assertEqual(sparse_dual_eval({(2,0):1},
            0,1,1,1,p),(0,0))
        self.assertEqual(sparse_dual_eval({(1,0):1},
            0,1,1,1,p),(0,1))


if __name__=="__main__":
    unittest.main()
