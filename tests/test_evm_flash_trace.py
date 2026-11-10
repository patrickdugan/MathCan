"""Regression and adversarial proof tests for CHTR-06 trace-level accounting."""
import unittest
from fractions import Fraction
from itertools import product

from research.chitraverse.evm_flash_trace import (
    FlashLedger, TraceReplay, TraceRejected, UINT256, INT128, from_json_spec,
)


def balances(a=0, b=0):
    return {"A": a, "B": b}


def new_machine(*, with_sponsor=False, with_claim=False, with_hook=True):
    physical = {"manager": balances(100, 100),
                "trader": balances(100, 0), "router": balances(),
                "treasury": balances()}
    if with_hook:
        physical["hook"] = balances()
    if with_sponsor:
        physical["sponsor"] = balances(30, 0)
    claims = {"trader": balances(10, 0)} if with_claim else None
    if with_claim:
        physical["manager"]["A"] += 10
    return TraceReplay(FlashLedger(physical, {"p": balances(100, 100)},
                                    claims=claims), root="router")


def evt(op, actor="router", **kwargs):
    return dict(op=op, actor=actor, **kwargs)


def run_success(machine, events):
    answer = machine.replay([evt("unlock"), *events, evt("lock")])
    assert answer.accepted, answer.error
    return answer


class TraceTests(unittest.TestCase):
    def test_floor_swap_settles_both_currencies(self):
        m = new_machine()
        res = run_success(m, [evt("swap", pool="p", input_asset="A", amount=10, fee_num=1, fee_den=1),
                              evt("sync", asset="A"),
                              evt("transfer", source="trader", target="manager", asset="A", amount=10),
                              evt("settle"),
                              evt("take", recipient="trader", asset="B", amount=9)])
        self.assertEqual(res.final["physical"]["trader"], balances(90, 9))
        self.assertEqual(res.final["pools"]["p"], balances(110, 91))
        self.assertEqual(Fraction(res.certificate["trader_gain"]), -1)
        self.assertEqual(Fraction(res.certificate["other_account_drawdown"]), 0)
        self.assertEqual(Fraction(res.certificate["nonnegative_slack"]) >= 0, True)
        self.assertEqual(m.ledger.backing_gap(), balances())

    def test_unsettled_negative_delta_reverts_everything(self):
        m = new_machine()
        start = m.ledger.snapshot()
        res = m.replay([evt("unlock"), evt("pool_delta", pool="p", asset="A", quantity=10), evt("lock")])
        self.assertFalse(res.accepted)
        self.assertIn("nonzero currency deltas", res.error)
        self.assertEqual(res.final, start)

    def test_nested_callback_revert_restores_transient_and_physical(self):
        m = new_machine()
        res = run_success(m, [evt("enter", callee="hook"),
                              evt("pool_delta", actor="hook", pool="p", asset="A", quantity=-10),
                              evt("take", actor="hook", recipient="trader", asset="A", amount=10),
                              evt("revert", actor="hook")])
        self.assertEqual(res.final, m.ledger.initial)

    def test_hook_drain_accounted_in_pool_value(self):
        m = new_machine()
        res = run_success(m, [evt("enter", callee="hook"),
                              evt("pool_delta", actor="hook", pool="p", asset="A", quantity=-10),
                              evt("take", actor="hook", recipient="trader", asset="A", amount=10),
                              evt("return", actor="hook")])
        self.assertEqual(Fraction(res.certificate["trader_gain"]), 10)
        self.assertGreaterEqual(Fraction(res.certificate["upper_extraction_bound"]), 10)
        self.assertEqual(res.final["pools"]["p"]["A"], 90)

    def test_unbacked_manager_transfer_rejected(self):
        m = new_machine()
        res = m.replay([evt("unlock"), evt("transfer", source="manager", target="trader", asset="A", amount=10), evt("lock")])
        self.assertFalse(res.accepted)
        self.assertIn("underbacked", res.error)

    def test_funded_external_sponsor_settle_for(self):
        m = new_machine(with_sponsor=True)
        res = run_success(m, [evt("pool_delta", pool="p", asset="A", quantity=7),
                              evt("sync", asset="A"),
                              evt("transfer", source="sponsor", target="manager", asset="A", amount=7),
                              evt("settle_for", recipient="router")])
        self.assertEqual(Fraction(res.certificate["trader_gain"]), 0)
        self.assertEqual(Fraction(res.certificate["other_account_drawdown"]), 7)
        self.assertEqual(res.final["physical"]["sponsor"]["A"], 23)
        self.assertEqual(res.final["pools"]["p"]["A"], 107)

    def test_mint_redeemable_claim_consumes_delta(self):
        m = new_machine()
        res = run_success(m, [evt("pool_delta", pool="p", asset="A", quantity=-10),
                              evt("mint", recipient="trader", asset="A", amount=10)])
        self.assertEqual(res.final["claims"]["trader"]["A"], 10)
        self.assertEqual(res.final["physical"]["manager"]["A"], 100)
        self.assertEqual(Fraction(res.certificate["trader_gain"]), 10)

    def test_burn_claim_then_take_redeems_without_new_wealth(self):
        m = new_machine(with_claim=True)
        res = run_success(m, [evt("enter", callee="trader"),
                              evt("burn", actor="trader", asset="A", amount=10),
                              evt("take", actor="trader", recipient="trader", asset="A", amount=10),
                              evt("return", actor="trader")])
        self.assertEqual(res.final["claims"]["trader"]["A"], 0)
        self.assertEqual(Fraction(res.certificate["trader_gain"]), 0)
        self.assertEqual(m.ledger.backing_gap(), balances())

    def test_burn_cannot_take_someone_elses_claim(self):
        m = new_machine(with_claim=True)
        res = m.replay([evt("unlock"), evt("burn", asset="A", amount=10), evt("lock")])
        self.assertFalse(res.accepted)

    def test_clear_requires_exact_positive_delta(self):
        m = new_machine()
        bad = m.replay([evt("unlock"), evt("pool_delta", pool="p", asset="A", quantity=-4),
                        evt("clear", asset="A", amount=3), evt("lock")])
        self.assertFalse(bad.accepted)
        m = new_machine()
        good = run_success(m, [evt("pool_delta", pool="p", asset="A", quantity=-4),
                               evt("clear", asset="A", amount=4)])
        self.assertEqual(good.final["surplus"]["A"], 4)

    def test_transfer_tax_observed_manager_receipt(self):
        m = new_machine(with_sponsor=True)
        res = run_success(m, [evt("pool_delta", pool="p", asset="A", quantity=8),
                              evt("sync", asset="A"),
                              evt("tax_transfer", source="sponsor", target="manager",
                                  tax_receiver="treasury", asset="A", gross=10, tax=2),
                              evt("settle")])
        self.assertEqual(res.final["physical"]["manager"]["A"], 108)
        self.assertEqual(res.final["physical"]["treasury"]["A"], 2)
        self.assertEqual(Fraction(res.certificate["other_account_drawdown"]), 8)

    def test_synced_amount_cannot_be_reused(self):
        m = new_machine(with_sponsor=True)
        result = m.replay([evt("unlock"), evt("sync", asset="A"),
                           evt("transfer", source="sponsor", target="manager", asset="A", amount=4),
                           evt("settle"), evt("settle"), evt("lock")])
        self.assertFalse(result.accepted)
        self.assertIn("requires a sync", result.error)

    def test_caller_authentication_fails_closed(self):
        m = new_machine()
        result = m.replay([evt("unlock"), evt("enter", callee="hook"),
                           evt("pool_delta", actor="router", pool="p", asset="A", quantity=1),
                           evt("return", actor="hook"), evt("lock")])
        self.assertFalse(result.accepted)
        self.assertIn("actor", result.error)

    def test_nested_frame_may_commit(self):
        m = new_machine()
        res = run_success(m, [evt("enter", callee="hook"),
                              evt("pool_delta", actor="hook", pool="p", asset="B", quantity=-2),
                              evt("clear", actor="hook", asset="B", amount=2),
                              evt("return", actor="hook")])
        self.assertEqual(res.final["surplus"]["B"], 2)

    def test_missing_lock_reverts(self):
        m = new_machine()
        res = m.replay([evt("unlock"), evt("sync", asset="B")])
        self.assertFalse(res.accepted)
        self.assertEqual(res.final, m.ledger.initial)

    def test_unknown_or_duplicate_fields_reject(self):
        for event in (evt("swap", pool="p", input_asset="A", amount=1, fee_num=1),
                      evt("sync", asset="A", unexpected=1),
                      evt("wrong")):
            m = new_machine()
            self.assertFalse(m.replay([evt("unlock"), event, evt("lock")]).accepted)

    def test_int128_uint256_and_boolean_rejections(self):
        for amount in (-1, True, INT128+1, UINT256+1):
            m = new_machine()
            self.assertFalse(m.replay([evt("unlock"), evt("transfer", source="trader", target="manager", asset="A", amount=amount), evt("lock")]).accepted)

    def test_root_denominator_and_backing_checks(self):
        m = new_machine()
        self.assertFalse(m.replay([evt("unlock"), evt("lock")], denominator=0).accepted)
        with self.assertRaises(TraceRejected):
            FlashLedger({"manager": balances(99, 100), "trader": balances(), "router": balances()},
                        {"p": balances(100, 100)})

    def test_pool_migration_updates_virtual_allocations(self):
        physical = {"manager": balances(120, 120), "trader": balances(), "router": balances()}
        m = TraceReplay(FlashLedger(physical, {"one": balances(100, 100), "two": balances(20, 20)}))
        res = run_success(m, [evt("pool_move", source="one", target="two", asset="A", amount=30)])
        self.assertEqual(res.final["pools"]["one"]["A"], 70)
        self.assertEqual(res.final["pools"]["two"]["A"], 50)

    def test_integer_rounding_no_free_value_small_grid(self):
        count = 0
        for x, y, amt, fee in product((5, 7, 11), (6, 13), (1, 2, 4), (1, 3, 4)):
            physical = {"manager": balances(x, y), "trader": balances(100, 0), "router": balances()}
            m = TraceReplay(FlashLedger(physical, {"p": balances(x, y)}))
            inp = amt
            output = (y * fee * inp) // (x*4 + fee*inp)
            if output == 0:
                continue
            ans = run_success(m, [evt("swap", pool="p", input_asset="A", amount=inp, fee_num=fee, fee_den=4),
                                  evt("sync", asset="A"),
                                  evt("transfer", source="trader", target="manager", asset="A", amount=inp),
                                  evt("settle"),
                                  evt("take", recipient="trader", asset="B", amount=output)])
            self.assertGreaterEqual(Fraction(ans.certificate["upper_extraction_bound"]),
                                    Fraction(ans.certificate["trader_gain"]))
            self.assertGreaterEqual((x+amt)*(y-output), x*y)
            count += 1
        self.assertGreater(count, 20)

    def test_external_physical_donation_is_manager_surplus(self):
        m = new_machine(with_sponsor=True)
        res = run_success(m, [evt("transfer", source="sponsor", target="manager", asset="A", amount=3)])
        self.assertEqual(res.final["surplus"]["A"], 3)
        self.assertEqual(Fraction(res.certificate["other_account_drawdown"]), 3)
        self.assertEqual(Fraction(res.certificate["vault_surplus_drawdown"]), -3)

    def test_multiple_assets_and_erc_claim_not_counted_twice(self):
        m = new_machine()
        res = run_success(m, [evt("pool_delta", pool="p", asset="B", quantity=-5),
                              evt("mint", recipient="trader", asset="B", amount=5)])
        self.assertEqual(Fraction(res.certificate["trader_gain"]), 5)
        self.assertEqual(res.final["claims"]["trader"]["B"], 5)

    def test_initial_claims_must_be_backed(self):
        with self.assertRaises(TraceRejected):
            FlashLedger({"manager": balances(100, 100), "trader": balances(), "router": balances()},
                        {"p": balances(100, 100)}, claims={"trader": balances(1, 0)})

    def test_json_spec_roundtrip(self):
        spec = {"physical": {"manager": balances(100, 100), "trader": balances(), "router": balances()},
                "pools": {"p": balances(100, 100)}, "trader": "trader", "root": "router",
                "prices": ["1", "2"], "events": [evt("unlock"), evt("lock")]}
        res = from_json_spec(spec)
        self.assertTrue(res.accepted)
        self.assertEqual(res.certificate["trader_gain"], "0")

    def test_root_cannot_lock_with_open_frame(self):
        m = new_machine()
        ans = m.replay([evt("unlock"), evt("enter", callee="hook"), evt("lock", actor="hook")])
        self.assertFalse(ans.accepted)

    def test_premature_settle_cannot_mint_credit(self):
        m = new_machine()
        res = m.replay([evt("unlock"), evt("pool_delta", pool="p", asset="A", quantity=1),
                        evt("sync", asset="A"), evt("settle"), evt("lock")])
        self.assertFalse(res.accepted)  # delta still -1


if __name__ == "__main__":
    unittest.main()

class ObservedReceiptTests(unittest.TestCase):
    def test_explicit_physical_and_transient_observations(self):
        m = new_machine()
        ok = run_success(m, [evt("pool_delta", pool="p", asset="A", quantity=-4),
                             evt("assert_delta", owner="router", asset="A", delta=4),
                             evt("clear", asset="A", amount=4),
                             evt("assert_balance", account="manager", asset="A", balance=100)])
        self.assertTrue(ok.accepted)
        self.assertEqual(len(set(ok.event_hashes)), len(ok.event_hashes))

    def test_observed_vault_drift_fails_closed(self):
        m = new_machine()
        ans = m.replay([evt("unlock"), evt("assert_balance", account="manager", asset="A", balance=101), evt("lock")])
        self.assertFalse(ans.accepted)
        self.assertIn("observation", ans.error)

    def test_observed_phantom_credit_fails_closed(self):
        m = new_machine()
        ans = m.replay([evt("unlock"), evt("assert_delta", owner="router", asset="A", delta=1), evt("lock")])
        self.assertFalse(ans.accepted)
        self.assertIn("observation", ans.error)

class ClaimTransferTests(unittest.TestCase):
    def test_holder_directed_erc6909_transfer_preserves_manager_backing(self):
        m = new_machine(with_claim=True)
        ans = run_success(m, [evt("enter", callee="trader"),
                              evt("claim_transfer", actor="trader", recipient="router", asset="A", amount=3),
                              evt("return", actor="trader")])
        self.assertEqual(ans.final["claims"]["trader"]["A"], 7)
        self.assertEqual(ans.final["claims"]["router"]["A"], 3)
        self.assertEqual(m.ledger.backing_gap(), balances())
        self.assertEqual(Fraction(ans.certificate["trader_gain"]), -3)

    def test_claim_transfer_rejects_unowned_amount(self):
        m = new_machine(with_claim=True)
        result = m.replay([evt("unlock"), evt("claim_transfer", recipient="router", asset="A", amount=1), evt("lock")])
        self.assertFalse(result.accepted)
        self.assertEqual(result.final, m.ledger.initial)

class SyncMisuseTests(unittest.TestCase):
    def test_overwriting_sync_can_leave_prior_deposit_uncredited(self):
        m = new_machine(with_sponsor=True)
        ans = m.replay([evt("unlock"), evt("pool_delta", pool="p", asset="A", quantity=4),
                        evt("sync", asset="A"),
                        evt("transfer", source="sponsor", target="manager", asset="A", amount=4),
                        evt("sync", asset="A"),  # overwrites the saved pre-deposit balance
                        evt("settle"), evt("lock")])
        self.assertFalse(ans.accepted)
        self.assertIn("nonzero currency deltas", ans.error)

    def test_balance_received_before_sync_stays_as_donation(self):
        m = new_machine(with_sponsor=True)
        ans = run_success(m, [evt("transfer", source="sponsor", target="manager", asset="A", amount=5),
                              evt("sync", asset="A"), evt("settle")])
        self.assertEqual(ans.final["surplus"]["A"], 5)
        self.assertEqual(ans.final["deltas"]["router"]["A"], 0)
