"""DEL-02 exact prime-power Fourier oracles and mutation checks."""
import random
import unittest

from research.deligne_sign_audit.prime_power_fourier import (
 FIELDS, SmallField, identity_matrix, is_nondegenerate,
 orthogonality_fiber_certificate, one, scalar, shift_poly,
 mul_poly, norm_certificate, norm_sq_le_integer, reduced_cyclotomic, path_sum_contract,
 path_sum_direct, verify_path_bound
)

class PrimePowerFourierTests(unittest.TestCase):
 def test_field_axioms_and_traces(self):
    for name,f in FIELDS.items():
        with self.subTest(field=name):
            p,q=f.p,f.q
            for x in range(q):
                self.assertEqual(f.pow(x,q),x)
                self.assertEqual(f.add(x,f.neg(x)),0)
                self.assertEqual(f.mul(x,1),x)
                self.assertTrue(0<=f.trace(x)<p)
                if x: self.assertEqual(f.mul(x,f.inv(x)),1)
                for y in range(q):
                    self.assertEqual(f.add(x,y),f.add(y,x))
                    self.assertEqual(f.mul(x,y),f.mul(y,x))
                    self.assertEqual(f.trace(f.add(x,y)),
                                     (f.trace(x)+f.trace(y))%p)
    with self.assertRaisesRegex(ValueError,"irreducibility"):
        SmallField(2,(0,0,1))

 def test_character_orthogonality_on_extension_fields(self):
    for name,f in FIELDS.items():
        for d in ((1,2) if f.q<=9 else (1,)):
            matrices=[identity_matrix(d)]
            if d==2: matrices.append(((0,1),(1,f.q-1)))
            for b in matrices:
                self.assertTrue(is_nondegenerate(f,b))
                for h in sorted({1,f.q-1}):
                    with self.subTest(field=name,d=d,h=h,b=b):
                        c=orthogonality_fiber_certificate(f,b,h)
                        self.assertTrue(c["balanced"],c)
                        self.assertEqual(c["fiber_size"],f.q**d//f.p)
    with self.assertRaisesRegex(ValueError,"nonzero"):
        orthogonality_fiber_certificate(FIELDS["F4"],((1,),),0)

 def test_exact_cyclotomic_norms(self):
    self.assertEqual(norm_certificate((1,1,0,0,0)),(3,1,2))
    self.assertEqual(norm_certificate((1,0,1,0,0)),(3,-1,2))
    self.assertTrue(norm_sq_le_integer((1,1,0,0,0),3))
    self.assertFalse(norm_sq_le_integer((1,1,0,0,0),2))
    self.assertTrue(norm_sq_le_integer((1,0,1,0,0),1))
    self.assertFalse(norm_sq_le_integer((1,0,1,0,0),0))
    self.assertEqual(norm_certificate((4,1)),(9,0,1))
    self.assertEqual(norm_certificate((1,1,0)),(1,0,1))
    self.assertEqual(mul_poly((1,1,0,0,0),(1,0,1,0,0)),(1,1,1,1,0))

 def test_matrix_contraction_matches_direct_enumeration(self):
    rng=random.Random(261100790)
    for name,d,k in (("F2",2,4),("F4",1,5),("F8",1,3),
                     ("F9",1,3),("F5",1,3),("F25",1,2)):
        f=FIELDS[name]; space=f.vectors(d)
        matrices=tuple(identity_matrix(d) for _ in range(k-1))
        h,c=f.q-1,f.q//2
        weights=tuple({x:shift_poly(scalar(rng.randrange(-2,3),f.p),
                                    rng.randrange(f.p)) for x in space}
                      for _ in range(k))
        with self.subTest(name=name,d=d,k=k):
            self.assertEqual(path_sum_direct(f,d,weights,matrices,h,c),
                             path_sum_contract(f,d,weights,matrices,h,c))
            self.assertTrue(verify_path_bound(f,d,weights,matrices,h,c)["ok"])

 def test_random_varied_bilinear_forms(self):
    rng=random.Random(261100791)
    for name,d,k,trials in (("F4",2,4,8),("F8",1,7,10),
                            ("F9",2,3,6),("F16",1,6,7),
                            ("F27",1,4,4),("F25",1,5,8)):
        f=FIELDS[name]; space=f.vectors(d)
        for _ in range(trials):
            weights=tuple({x:shift_poly(scalar(rng.randrange(-2,3),f.p),
                                        rng.randrange(f.p)) for x in space}
                          for _ in range(k))
            if d==1:
                matrices=tuple(((rng.randrange(1,f.q),),) for _ in range(k-1))
            else:
                matrices=tuple(((0,rng.randrange(1,f.q)),
                                (rng.randrange(1,f.q),rng.randrange(f.q)))
                               for _ in range(k-1))
            receipt=verify_path_bound(f,d,weights,matrices,
                         rng.randrange(1,f.q),rng.randrange(f.q))
            self.assertTrue(receipt["all_forms_nondegenerate"])
            self.assertTrue(receipt["ok"],(name,receipt))

 def test_all_odd_lengths_sharp_with_constant_weights(self):
    # For any nondegenerate pairings and uniform weight 1,
    # S_k=N*S_(k-2), S_1=S_2=N, hence S_k=N^ceil(k/2).
    for name,d,ks in (("F2",1,(3,5,7)),("F4",2,(3,5,7)),
                      ("F8",1,(3,5,7)),("F9",2,(3,5)),
                      ("F16",1,(3,5)),("F25",1,(3,5)),
                      ("F27",1,(3,5))):
        f=FIELDS[name]
        N=f.q**d
        space=f.vectors(d)
        h,c=f.q-1,f.q//2
        for k in ks:
            weights=tuple({x:one(f.p) for x in space} for _ in range(k))
            matrices=tuple(identity_matrix(d) for _ in range(k-1))
            got=path_sum_contract(f,d,weights,matrices,h,c)
            expect=shift_poly(scalar(N**((k+1)//2),f.p),
                              f.trace(f.mul(h,c)))
            with self.subTest(field=name,d=d,k=k):
                self.assertEqual(reduced_cyclotomic(got),
                                 reduced_cyclotomic(expect))
                cert=verify_path_bound(f,d,weights,matrices,h,c,t_bound=1)
                self.assertTrue(cert["ok"])
                self.assertTrue(cert["all_forms_nondegenerate"])
                self.assertEqual(cert["norm_certificate"][1],0)
                self.assertEqual(cert["norm_certificate"][0],
                                 cert["norm_certificate"][2]*cert["ceiling"])

 def test_degenerate_mutants(self):
    for name in ("F4","F9","F25"):
        f=FIELDS[name]; space=f.vectors(1)
        weights=tuple({x:one(f.p) for x in space} for _ in range(3))
        matrices=(((0,),),)*2
        bad=verify_path_bound(f,1,weights,matrices,1,0,t_bound=1)
        self.assertFalse(bad["ok"])
        self.assertFalse(bad["all_forms_nondegenerate"])
        self.assertFalse(orthogonality_fiber_certificate(f,matrices[0],1)["balanced"])

 def test_understated_T_mutation(self):
    f=FIELDS["F25"]
    weights=({(x,):scalar(2,5) for x in range(f.q)},)*2
    with self.assertRaisesRegex(ValueError,"T does not bound"):
        verify_path_bound(f,1,weights,(((1,),),),1,0,t_bound=1)

if __name__=="__main__":
    unittest.main()
