"""CHTR-05: atomic receipt, generalized extraction bound, and debt checks."""
import unittest
from fractions import Fraction as F

from research.chitraverse.amount_aware_hooks import Wallet
from research.chitraverse.settlement_potentials import (
    LedgerState, Transfer, BalanceGuard, Swap, SettlementRule,
    SettlementProgram, AccountRoles, settle, settle_route,
    extraction_certificate, verify_witness, audit_finite_superpotential,
)


def ledger(pools=(("p0", Wallet(100, 100)),), trader=Wallet(20, 0),
           hook=Wallet(0, 0), sponsor=Wallet(0, 0), treasury=Wallet(0, 0),
           phase=0):
    return LedgerState(tuple([("trader", trader), ("hook", hook),
                              ("treasury", treasury), ("sponsor", sponsor)] + list(pools)),
                       tuple(n for n, _ in pools), phase)


ROLES = AccountRoles("trader", ("hook", "treasury"), ("sponsor",))


class SettlementPotentialTests(unittest.TestCase):
    def test_01_swap_matches_cp_and_exact_zero_subsidy_budget(self):
        s = ledger()
        p = SettlementProgram((SettlementRule("swap", 0, 0,
                                              swap=Swap("p0", "A2B", 10, F(9, 10))),))
        t, cert, (r,) = verify_witness(s, p, ("swap",), ROLES)
        y = F(100) * F(9) / F(109)
        self.assertEqual(r.swap_output, y)
        self.assertEqual(t.wallet("trader"), Wallet(10, y))
        self.assertGreater(t.wallet("p0").a * t.wallet("p0").b, 10_000)
        self.assertEqual(s.totals(), t.totals())
        self.assertLess(cert["trader_gain"], 0)
        self.assertLessEqual(cert["trader_gain"], cert["gain_upper_bound"])

    def test_02_custom_pool_drain_detected_by_final_invariant_floor(self):
        s = ledger()
        p = SettlementProgram((SettlementRule("drain", 0, 0,
                                              after=(Transfer("p0", "trader", "A", 10),)),))
        t, cert, receipts = verify_witness(s, p, ("drain",), ROLES)
        self.assertEqual(cert["trader_gain"], 10)
        self.assertEqual(cert["pool_value_loss"], 10)
        self.assertEqual(cert["external_sponsor_drawdown"], 0)
        self.assertEqual(cert["custodian_drawdown"], 0)
        self.assertEqual(receipts[0].products_after, (("p0", F(9_000)),))
        self.assertTrue(cert["gain_upper_bound"] >= 10)
        self.assertTrue(cert["gain_upper_bound"] < 11)
        # Claiming the original invariant was preserved is unsound.
        with self.assertRaisesRegex(ValueError, "below claimed floor"):
            extraction_certificate(s, t, ROLES, ex_ante_pool_floors={"p0": 10_000})

    def test_03_registered_reserve_floor_aborts_entire_transaction(self):
        s = ledger()
        p = SettlementProgram((SettlementRule("drain", 0, 0,
                after=(Transfer("p0", "trader", "A", 10),),
                pool_floors=(("p0", F(10000)),)),))
        with self.assertRaisesRegex(ValueError, "registered floor"):
            settle(s, p, "drain")
        self.assertEqual(s.wallet("p0"), Wallet(100, 100))

    def test_04_sponsor_subsidy_exactly_traced(self):
        s = ledger(sponsor=Wallet(12, 0), trader=Wallet(0, 0))
        p = SettlementProgram((SettlementRule("grant", 0, 1,
                              before=(Transfer("sponsor", "trader", "A", 12),)),))
        t, cert, _ = verify_witness(s, p, ("grant",), ROLES)
        self.assertEqual(cert["trader_gain"], 12)
        self.assertEqual(cert["external_sponsor_drawdown"], 12)
        self.assertEqual(cert["certificate_gap"], 0)
        self.assertEqual(cert["gain_upper_bound"], 12)
        self.assertEqual(t.phase, 1)

    def test_05_treasury_and_hook_budget_are_both_counted(self):
        s = ledger(trader=Wallet(0, 0), hook=Wallet(5, 0), treasury=Wallet(0, 7))
        p = SettlementProgram((SettlementRule("subsidize", 0, 0,
                            before=(Transfer("hook", "trader", "A", 5),),
                            after=(Transfer("treasury", "trader", "B", 7),)),))
        t, cert, _ = verify_witness(s, p, ("subsidize",), ROLES)
        self.assertEqual(cert["trader_gain"], 12)
        self.assertEqual(cert["custodian_drawdown"], 12)
        self.assertEqual(cert["gain_upper_bound"], 12)
        self.assertEqual(t.wallet("trader"), Wallet(5, 7))

    def test_06_unfunded_mint_and_unknown_account_rejected(self):
        s = ledger(trader=Wallet(0,0))
        p = SettlementProgram((SettlementRule("mint", 0, 0,
                             before=(Transfer("unknown", "trader", "A", 100),)),))
        with self.assertRaisesRegex(ValueError, "unregistered transfer"):
            settle(s, p, "mint")
        p2 = SettlementProgram((SettlementRule("overdraft", 0, 0,
                             before=(Transfer("hook", "trader", "A", 1),)),))
        with self.assertRaisesRegex(ValueError, "authorized credit"):
            settle(s, p2, "overdraft")

    def test_07_intrastep_flash_credit_repaid_with_reported_exposure(self):
        s = ledger(trader=Wallet(0,0), hook=Wallet(0,0))
        p = SettlementProgram((SettlementRule("flash", 0, 0,
                             before=(Transfer("trader", "hook", "A", 5),),
                             after=(Transfer("hook", "trader", "A", 5),)),),
                             credit_limits=(("trader", "A", F(5)),))
        t, cert, receipts = verify_witness(s, p, ("flash",), ROLES)
        self.assertEqual(s, t)
        self.assertIn(("trader", "A", F(5)), receipts[0].exposures)
        self.assertEqual(cert["trader_gain"], 0)
        self.assertEqual(cert["certificate_gap"], 0)

    def test_08_intrastep_credit_cap_enforced(self):
        s = ledger(trader=Wallet(0,0))
        p = SettlementProgram((SettlementRule("over", 0, 0,
                             before=(Transfer("trader", "hook", "A", 6),),
                             after=(Transfer("hook", "trader", "A", 6),)),),
                             credit_limits=(("trader", "A", F(5)),))
        with self.assertRaisesRegex(ValueError, "authorized credit"):
            settle(s, p, "over")

    def test_09_unsettled_overdraft_aborts(self):
        s = ledger(trader=Wallet(0,0))
        p = SettlementProgram((SettlementRule("unsettled", 0, 0,
                             before=(Transfer("trader", "hook", "A", 4),)),),
                             credit_limits=(("trader", "A", F(10)),))
        with self.assertRaisesRegex(ValueError, "unsettled account deficit"):
            settle(s, p, "unsettled")

    def test_10_phase_guard_and_noncommutation(self):
        s = ledger(pools=(("p0", Wallet(100,100)),("p1",Wallet(200,200))),
                   trader=Wallet(30,0))
        p = SettlementProgram((
            SettlementRule("large", 0, 1, swap=Swap("p0", "A2B", 10, F(1))),
            SettlementRule("large", 1, 0, swap=Swap("p0", "A2B", 10, F(1,2))),
            SettlementRule("small", 0, 1, swap=Swap("p1", "A2B", 10, F(1))),
            SettlementRule("small", 1, 0, swap=Swap("p1", "A2B", 10, F(1,2))),
        ))
        x, cx, _ = verify_witness(s, p, ("large", "small"), ROLES)
        y, cy, _ = verify_witness(s, p, ("small", "large"), ROLES)
        self.assertNotEqual(x.wallet("trader").b, y.wallet("trader").b)
        self.assertEqual(x.phase, y.phase)
        self.assertLessEqual(cx["trader_gain"], cx["gain_upper_bound"])
        self.assertLessEqual(cy["trader_gain"], cy["gain_upper_bound"])
        guarded = SettlementProgram((SettlementRule("gate",0,0,
                        guards=(BalanceGuard("hook","A",2),)),))
        with self.assertRaisesRegex(ValueError, "guard condition"):
            settle(s, guarded, "gate")

    def test_11_before_swap_pool_mutation_changes_price_and_is_accounted(self):
        s = ledger(hook=Wallet(0, 20))
        p = SettlementProgram((SettlementRule("inject", 0, 0,
                    before=(Transfer("hook","p0","B",10),),
                    swap=Swap("p0","A2B", 10),
                    after=(Transfer("p0","hook","B",5),)),))
        t, cert, (receipt,) = verify_witness(s,p,("inject",),ROLES)
        self.assertEqual(receipt.swap_output, F(10))
        self.assertEqual(t.wallet("p0").b,95)
        self.assertTrue(cert["trader_gain"] <= cert["gain_upper_bound"])
        self.assertEqual(receipt.products_before, (("p0",F(10_000)),))

    def test_12_all_roles_must_be_disjoint_exhaustive(self):
        s = ledger()
        with self.assertRaisesRegex(ValueError, "disjoint and exhaustive"):
            extraction_certificate(s,s,AccountRoles("trader",("hook",), ("sponsor",)))
        with self.assertRaisesRegex(ValueError, "disjoint and exhaustive"):
            extraction_certificate(s,s,AccountRoles("trader",("hook", "treasury"), ("hook",)))

    def test_13_account_relabel_is_value_invariant(self):
        s = ledger()
        t = LedgerState(tuple(reversed(s.accounts)),s.pools,0)
        self.assertEqual(s.totals(),t.totals())
        self.assertEqual(extraction_certificate(s,t,ROLES)["trader_gain"],0)
        self.assertEqual(extraction_certificate(s,t,ROLES)["gain_upper_bound"],0)

    def test_14_certified_floor_rounding_is_conservative(self):
        s = ledger(pools=(("p0",Wallet(100,225)), ("p1",Wallet(225,100))))
        p = SettlementProgram((SettlementRule("test", 0, 0,
                             swap=Swap("p0","A2B",5)),))
        t,_ = settle(s,p,"test")
        for den in (1, 2, 11, 10000):
            c = extraction_certificate(s,t,ROLES,denominator=den)
            self.assertEqual(c["gain_upper_bound"]-c["trader_gain"],c["certificate_gap"])
            self.assertGreaterEqual(c["certificate_gap"],0)
        with self.assertRaisesRegex(ValueError,"positive approximation"):
            extraction_certificate(s,t,ROLES,denominator=0)

    def test_15_commit_product_floor_sound_without_hook_condition(self):
        s = ledger()
        p = SettlementProgram((SettlementRule("roundtrip", 0, 0,
                             swap=Swap("p0","A2B",1)),))
        t, c, _ = verify_witness(s,p,("roundtrip",),ROLES,
                                 ex_ante_pool_floors={"p0":10000})
        self.assertGreaterEqual(c["floor_based_gain_bound"], c["gain_upper_bound"])
        self.assertGreaterEqual(t.wallet("p0").a*t.wallet("p0").b, 10000)

    def test_16_invalid_registry_or_rate_or_float(self):
        with self.assertRaises(ValueError):
            LedgerState((("A",Wallet(1,1)),("A",Wallet(1,1))), ("A",))
        with self.assertRaises(ValueError):
            Transfer("trader","trader","A",1)
        with self.assertRaises(ValueError):
            Transfer("trader","hook","C",1)
        with self.assertRaises(TypeError):
            Transfer("trader","hook","B",0.1)
        with self.assertRaises(ValueError):
            Swap("p0","A2B",1,F(3,2))
        with self.assertRaises(ValueError):
            SettlementProgram((SettlementRule("a",0,0),SettlementRule("a",0,0)))
        with self.assertRaises(ValueError):
            settle(ledger(), SettlementProgram((SettlementRule("a",0,0),),
                  credit_limits=(("p0","A",F(3)),)), "a")

    def test_17_exact_parameter_grid_with_pool_mutation_and_sponsor(self):
        samples=0
        for x in (1,2,5,8):
            for y in (1,2,5):
                for q in (1,2,4):
                    for g in (F(1),F(1,2),F(3,4)):
                        s = ledger(pools=(("p0",Wallet(50+q,50+x)),),
                                   trader=Wallet(20,0),hook=Wallet(0,0),
                                   sponsor=Wallet(0,20))
                        prog = SettlementProgram((SettlementRule("mix", 0,0,
                          before=(Transfer("sponsor","p0","B",q),),
                          swap=Swap("p0","A2B",x,g),
                          after=(Transfer("p0","trader","B",y),)),))
                        t,c,_=verify_witness(s,prog,("mix",),ROLES,denominator=1000)
                        self.assertEqual(s.totals(),t.totals())
                        self.assertEqual(c["gain_upper_bound"]-c["trader_gain"],c["certificate_gap"])
                        self.assertGreaterEqual(c["certificate_gap"],0)
                        samples += 1
        self.assertEqual(samples,108)

    def test_18_funding_ledger_mismatch_detected(self):
        s=ledger()
        t=ledger(trader=Wallet(21,0))
        with self.assertRaisesRegex(ValueError,"accounting differs"):
            extraction_certificate(s,t,ROLES)

    def test_19_atomic_guard_not_final_balance_based(self):
        s=ledger(trader=Wallet(0,0),hook=Wallet(10,0))
        rule=SettlementRule("gate",0,0,
                            before=(Transfer("hook","trader","A",10),),
                            guards=(BalanceGuard("trader","A",5),))
        with self.assertRaisesRegex(ValueError,"guard condition failed"):
            settle(s,SettlementProgram((rule,)),"gate")

    def test_20_finite_graph_potential_certificate_and_violation(self):
        s0 = ledger(trader=Wallet(0,0), hook=Wallet(1,0), phase=0)
        p = SettlementProgram((
            SettlementRule("toggle",0,1,before=(Transfer("hook","trader","A",1),)),
            SettlementRule("toggle",1,0,before=(Transfer("trader","hook","A",1),)),
        ))
        s1,_ = settle(s0,p,"toggle")
        final,_=settle(s1,p,"toggle")
        self.assertEqual(final,s0)
        audit=audit_finite_superpotential((s0,s1),p,ROLES,(1,1),
                                          {s0:F(1), s1:F(0)})
        self.assertTrue(audit.certified)
        self.assertEqual(audit.transition_count,2)
        bad=audit_finite_superpotential((s0,s1),p,ROLES,(1,1),
                                        {s0:F(0),s1:F(0)})
        self.assertFalse(bad.certified)
        self.assertEqual(bad.violating_edge[1],"toggle")

    def test_21_finite_graph_refuses_incomplete_reachable_state(self):
        s0=ledger(trader=Wallet(0,0),hook=Wallet(1,0))
        p=SettlementProgram((SettlementRule("grant",0,0,
                            before=(Transfer("hook","trader","A",1),)),))
        with self.assertRaisesRegex(ValueError,"not closed"):
            audit_finite_superpotential((s0,),p,ROLES,(1,1),{s0:1})
        with self.assertRaisesRegex(ValueError,"cover the exact"):
            audit_finite_superpotential((s0,),p,ROLES,(1,1),{})



if __name__ == "__main__":
    unittest.main()
