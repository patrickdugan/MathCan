"""COL: cross-check finite enumeration, residue quotients and exact lattices."""
import csv
import io
import json
import shutil
import subprocess
import tempfile
import unittest
from collections import Counter
from math import gcd, prod
from pathlib import Path

from research.collatz_resonance.arithmetic import (
    branch_lattice, combine_congruences, construct_sign_parameters, legendre,
    near_resonances, primitive_prime_lattice,
)
from research.collatz_resonance.collatz_core import (
    analyze, branch_history, full_step, modular_labels, odd_step, readout_ceiling,
)

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "research/collatz_resonance"


class CollatzExactTests(unittest.TestCase):
    def test_finite_core_full_step_replay(self):
        for d in range(1, 514, 4):
            core = analyze(d)
            self.assertEqual(sum(x["basin_size"] for x in core.cycles), (d+1)//2)
            for n in core.states:
                successor, a, u = odd_step(n, d)
                self.assertLessEqual(successor, d)
                self.assertGreaterEqual(a, 2)
                full = full_step(n, d)
                for _ in range(a):
                    self.assertEqual(full % 2, 0)
                    full = full_step(full, d)
                self.assertEqual((full, int(n%4 == 1)), (successor, u))
                self.assertEqual(core.basin[n], core.basin[successor])
            for cycle in core.cycles:
                x = cycle["minimum"]
                seen = set()
                for _ in range(cycle["period"]):
                    self.assertNotIn(x, seen)
                    seen.add(x)
                    x = full_step(x, d)
                self.assertEqual(x, cycle["minimum"])
                self.assertEqual(min(seen), x)

    def test_core_descent_and_invalid_inputs(self):
        for d in range(1, 98, 4):
            for n in range(d+2, d+202, 2):
                self.assertLess(odd_step(n,d)[0],n)
        for d in (-1,0,2,3,True,1.0):
            with self.assertRaises(ValueError): analyze(d)
        for n in (-1,0,2,True,1.0):
            with self.assertRaises(ValueError): odd_step(n,13)
        with self.assertRaises(ValueError): modular_labels(9)
        with self.assertRaises(ValueError): analyze(101,max_parameter=100)

    def test_quotient_and_cycle_congruences(self):
        for d in range(1, 514, 4):
            if gcd(d,6) != 1: continue
            core, labels, lattice = analyze(d), modular_labels(d), branch_lattice(d)
            for n in range(d):
                self.assertEqual(labels[n],labels[2*n%d])
                self.assertEqual(labels[n],labels[3*n%d])
            for n in core.states:
                self.assertEqual(labels[n%d],labels[core.successors[n]%d])
                self.assertEqual(gcd(n,d),gcd(core.successors[n],d))
            for c in core.cycles:
                reduced = d//c["gcd_with_d"]
                self.assertTrue(branch_lattice(reduced).contains(c["triple_branches"],c["halvings"]))
            for u in range(-3,8):
                for A in range(-3,16):
                    self.assertEqual(lattice.contains(u,A),pow(2,A,d)==pow(3,u,d))

    def test_reference_anchors(self):
        for r in json.loads((BASE/'small_reference.json').read_text()):
            core, q = analyze(r['d']), modular_labels(r['d'])
            cycles = [{k:v for k,v in c.items() if k!='nodes'} for c in core.cycles]
            self.assertEqual(cycles,r['cycles'])
            self.assertEqual(len(set(q.values())),r['quotient_count'])
            self.assertEqual(list(readout_ceiling(core,{n:q[n%r['d']] for n in core.states})),r['quotient_ceiling'])
        c,q=analyze(13),modular_labels(13)
        self.assertEqual(q[1],q[5])
        self.assertNotEqual(c.basin[1],c.basin[5])

    def test_large_lattice_and_construction(self):
        lattice,logs=primitive_prime_lattice((29,53,269,389))
        self.assertEqual(logs,(5,17,109,271))
        self.assertEqual((lattice.triple_stride,lattice.halving_residue,lattice.halving_period),(2,885958,2365636))
        self.assertEqual(lattice.index,4731272)
        self.assertEqual(near_resonances(lattice,10000,100),[(3546,21230),(7092,42460)])
        primes=construct_sign_parameters((5,7,11))
        self.assertEqual(primes,(1873,1321,1009))
        for i,p in enumerate(primes):
            self.assertEqual(p%24,1)
            self.assertEqual(legendre(2,p),1)
            self.assertEqual(legendre(3,p),1)
            self.assertEqual([legendre(q,p) for q in (5,7,11)],[1 if j!=i else -1 for j in range(3)])
        labels=set()
        for mask in range(8):
            seed=prod(q for j,q in enumerate((5,7,11)) if mask>>j&1)
            labels.add(tuple(legendre(seed,p) for p in primes))
        self.assertEqual(len(labels),8)
        with self.assertRaises(ValueError): combine_congruences(0,4,1,2)
        with self.assertRaises(ValueError): primitive_prime_lattice((73,))

    def test_prefix_decodes_seed_at_five_steps(self):
        for d in range(1,1026,4):
            if gcd(d,6)!=1: continue
            core=analyze(d)
            words=[]
            for n in core.states:
                word=branch_history(n,d,5)
                words.append(word)
                B,A,u=0,0,0
                for triple,a in word:
                    B=(3 if triple else 1)*B+2**A
                    A+=a
                    u+=triple
                modulus=2**(A+1)
                residue=((2**A-B*d)*pow(3**u,-1,modulus))%modulus
                self.assertEqual(residue,n)
            self.assertEqual(len(set(words)),len(core.states))

    @unittest.skipUnless(shutil.which('g++') or shutil.which('c++'),'C++17 compiler unavailable')
    def test_cpp_algorithms_against_python(self):
        compiler=shutil.which('g++') or shutil.which('c++')
        with tempfile.TemporaryDirectory() as temp:
            exe=str(Path(temp)/'census')
            subprocess.run([compiler,'-O2','-std=c++17',str(BASE/'census.cpp'),'-o',exe],check=True)
            for d in (1,5,9,13,29,73,97,217,313,577,1001):
                expected=sorted((c['minimum'],c['odd_steps'],c['halvings'],c['triple_branches'],c['gcd_with_d']) for c in analyze(d).cycles)
                for method in ('path','peel'):
                    result=subprocess.run([exe,str(d),method],check=True,capture_output=True,text=True)
                    rows=[tuple(int(v) for v in row.values()) for row in csv.DictReader(io.StringIO(result.stdout))]
                    self.assertEqual(rows,expected)
            for args in (['-1'],['2'],['13','bogus'],['13','path','2']):
                r=subprocess.run([exe,*args],capture_output=True,text=True)
                self.assertEqual(r.returncode,2)


if __name__ == '__main__': unittest.main()
