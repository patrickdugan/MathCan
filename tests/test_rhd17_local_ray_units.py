"""RHD-17 exhaustive finite local ray quotient and tamper controls."""
import hashlib
import tempfile
import unittest
from pathlib import Path

from research.rh_proof_distillation.rhd17_local_ray_units import (
    FAMILIES, ORDERS, PROPER_POWER_CHECKS, deterministic_unit_orbits,
    exact_alpha_order, exhaustive_unit_distribution, multiply, norm, power,
    normalized_witness, report, write_report,
)


class LocalRayUnitTests(unittest.TestCase):
    def test_all_primitive_root_orders(self):
        for family in FAMILIES:
            p=family.p
            for j,f in enumerate(family.factors):
                cert=exact_alpha_order(family,j)
                self.assertEqual(cert["root_order"],ORDERS[p])
                self.assertEqual(cert["root_powers"],ORDERS[p])
                self.assertTrue(cert["root_characters_all_zero"])
                for d in PROPER_POWER_CHECKS[p]:
                    self.assertNotEqual(power(f,(0,1),d,p*p),(1,0))
                self.assertEqual(power(f,(0,1),ORDERS[p],p*p),(1,0))

    def test_quadratic_norm_multiplicativity(self):
        for family in FAMILIES:
            p=family.p
            m=p*p
            for j,f in enumerate(family.factors):
                for i in range(60):
                    seed=hashlib.sha256(f"RHD17/mul/{p}/{j}/{i}".encode()).digest()
                    x=(int.from_bytes(seed[:4],"big")%m,
                       int.from_bytes(seed[4:8],"big")%m)
                    y=(int.from_bytes(seed[8:12],"big")%m,
                       int.from_bytes(seed[12:16],"big")%m)
                    z=multiply(f,x,y,m)
                    self.assertEqual(norm(f,z,m),norm(f,x,m)*norm(f,y,m)%m)
                    if norm(f,x,m)%p and norm(f,y,m)%p:
                        self.assertEqual(
                            family.q(norm(f,z,m)),
                            (family.q(norm(f,x,m))+family.q(norm(f,y,m)))%p,
                        )

    def test_all_unit_fibers_exhaustive(self):
        r=report()
        self.assertEqual(r["total_ring_elements_enumerated"],2831624)
        self.assertTrue(r["all_eight_factors_exhaustively_enumerated"])
        self.assertFalse(r["global_norm_one_torus_character_constructed"])
        self.assertFalse(r["upstream_TyEll_proved"])
        for family in r["families"]:
            p=family["p"]
            n=ORDERS[p]
            expected_units=p*p*(p*p-1)
            each=p*(p*p-1)
            quotient=expected_units//n
            kernel=each//n
            for row in family["factors"]:
                self.assertEqual(row["units"],expected_units)
                self.assertEqual(row["nonunits"],p*p)
                self.assertEqual(row["unit_char_histogram"],[each]*p)
                self.assertEqual(row["root_quotient_cardinality"],quotient)
                self.assertEqual(row["root_quotient_kernel_cardinality"],kernel)
                self.assertEqual(row["root_quotient_character_order"],p)
                self.assertEqual(quotient,p*kernel)
                self.assertEqual(row["root_order_certificate"]["root_order"],n)
                self.assertEqual(
                    row["surjectivity_witness"]["character_exponent_mod_p"],1)
            self.assertEqual(quotient,35322 if p==29 else 25)
            self.assertEqual(kernel,1218 if p==29 else 5)

    def test_root_orbit_invariance_and_negative_control(self):
        for family in FAMILIES:
            for j,f in enumerate(family.factors):
                self.assertEqual(deterministic_unit_orbits(family,j,samples=32),32)
                self.assertEqual(normalized_witness(family,j)["character_exponent_mod_p"],1)
                # A mutation of the local root is expected to violate
                # the cyclotomic order or character-kernel gate.
                mutated=(f[0],(f[1]+1)%(family.p**2),1)
                self.assertNotEqual(power(mutated,(0,1),ORDERS[family.p],family.p**2),
                                    (1,0))

    def test_receipt_replay_sha256_and_exact_scope(self):
        with tempfile.TemporaryDirectory() as directory:
            target=Path(directory)/"local_ray_units.json"
            result=write_report(target)
            first=target.read_bytes()
            sha=target.with_suffix(".sha256").read_text().split()[0]
            self.assertEqual(hashlib.sha256(first).hexdigest(),sha)
            second=write_report(target)
            self.assertEqual(result,second)
            self.assertEqual(target.read_bytes(),first)
            self.assertEqual(second["total_ring_elements_enumerated"],2831624)


if __name__=="__main__":
    unittest.main()
