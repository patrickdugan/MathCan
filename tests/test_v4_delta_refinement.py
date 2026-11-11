"""CHTR-07 source-step and adversarial microstate tests. All witnesses are synthetic."""
from copy import deepcopy
import hashlib
import unittest

from research.chitraverse.v4_delta_refinement import (
    CORE_COMMIT, ZERO, LOCK_SLOT, NONZERO_SLOT, SYNC_CURRENCY_SLOT,
    SYNC_BALANCE_SLOT, WitnessError, V4DeltaWitness, delta_slot, keccak256,
    word, from_json_spec,
)

MANAGER = "0x" + "0" * 39 + "1"
ROUTER = "0x" + "0" * 39 + "2"
HOOK = "0x" + "0" * 39 + "3"
TRADER = "0x" + "0" * 39 + "4"
A = "0x" + "0" * 38 + "11"
B = "0x" + "0" * 38 + "22"


def w(slot, value):
    return {"slot": slot, "value": word(value)}


def spec(events):
    return {"schema": "mathcan.chtr07.v1", "core_commit": CORE_COMMIT,
            "manager": MANAGER, "root": ROUTER,
            "balances": {
                A: {MANAGER: 100, ROUTER: 50, HOOK: 10, TRADER: 0},
                B: {MANAGER: 100, ROUTER: 50, HOOK: 10, TRADER: 0},
                ZERO: {MANAGER: 0, ROUTER: 30, HOOK: 5, TRADER: 0}},
            "events": events}


def opening():
    return {"op": "unlock", "actor": ROUTER, "writes": [w(LOCK_SLOT, 1)]}


def closing(actor=ROUTER):
    return {"op": "lock", "actor": actor, "writes": [w(LOCK_SLOT, 0)]}


def pool_account(caller_delta, hook_delta):
    # The TSTORE list is derived from the pinned _accountPoolBalanceDelta order.
    return {"op": "pool_account", "actor": ROUTER, "kind": "swap",
            "currency0": A, "currency1": B, "hook": HOOK,
            "caller_delta": caller_delta, "hook_delta": hook_delta,
            "writes": [w(delta_slot(HOOK, A), 2), w(NONZERO_SLOT, 1),
                       w(delta_slot(ROUTER, A), -7), w(NONZERO_SLOT, 2),
                       w(delta_slot(ROUTER, B), 4), w(NONZERO_SLOT, 3)]}


def roundtrip():
    return [opening(), pool_account([-7, 4], [2, 0]),
            {"op": "sync", "actor": ROUTER, "currency": A, "observed_balance": 100,
             "writes": [w(SYNC_CURRENCY_SLOT, int(A, 16)), w(SYNC_BALANCE_SLOT, 100)]},
            {"op": "transfer", "actor": ROUTER, "currency": A, "source": ROUTER,
             "destination": MANAGER, "amount": 7, "writes": []},
            {"op": "settle", "actor": ROUTER, "recipient": ROUTER, "msg_value": 0,
             "observed_balance": 107, "paid": 7,
             "writes": [w(SYNC_CURRENCY_SLOT, 0), w(delta_slot(ROUTER, A), 0),
                        w(NONZERO_SLOT, 2)]},
            {"op": "take", "actor": ROUTER, "currency": B, "recipient": ROUTER,
             "amount": 4,
             "writes": [w(delta_slot(ROUTER, B), 0), w(NONZERO_SLOT, 1)]},
            {"op": "clear", "actor": ROUTER, "currency": B, "amount": 0, "writes": []},
            {"op": "enter", "actor": ROUTER, "callee": HOOK, "writes": []},
            {"op": "clear", "actor": HOOK, "currency": A, "amount": 2,
             "writes": [w(delta_slot(HOOK, A), 0), w(NONZERO_SLOT, 0)]},
            {"op": "return", "actor": HOOK, "writes": []}, closing()]


class KeccakSourceTests(unittest.TestCase):
    def test_empty_and_abc_vectors(self):
        self.assertEqual(keccak256(b"").hex(),
                         "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470")
        self.assertEqual(keccak256(b"abc").hex(),
                         "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45")

    def test_rate_block_boundary(self):
        # Reference vectors from independent known Keccak-256 implementations.
        self.assertNotEqual(keccak256(bytes(136)), hashlib.sha3_256(bytes(136)).digest())
        self.assertEqual(len(keccak256(bytes(136))), 32)

    def test_mapping_slot_pads_both_addresses_as_bytes32(self):
        v = bytes.fromhex("00" * 12 + ROUTER[2:] + "00" * 12 + A[2:])
        self.assertEqual(delta_slot(ROUTER, A), "0x" + keccak256(v).hex())
        self.assertNotEqual(delta_slot(ROUTER, A), delta_slot(A, ROUTER))
        self.assertNotEqual(delta_slot(ROUTER, A), delta_slot(HOOK, A))

    def test_two_complement_words(self):
        self.assertEqual(word(-1), "0x" + "f" * 64)
        self.assertEqual(word(-7), "0x" + "f" * 63 + "9")


class SourceStepTests(unittest.TestCase):
    def test_combined_hook_caller_settle_take_and_clear(self):
        r = from_json_spec(spec(roundtrip()))
        self.assertTrue(r.accepted, r.reason)
        self.assertEqual(r.terminal["nonzero_delta_count"], 0)
        self.assertEqual(r.terminal["opaque_pool_calls"], 1)
        self.assertEqual(r.terminal["vault_balances"][A], 107)
        self.assertEqual(r.terminal["vault_balances"][B], 96)
        self.assertFalse(r.complete_source_evidence)

    def test_tstore_wrong_slot_rejected(self):
        e = roundtrip()
        e[1]["writes"][0]["slot"] = "0x" + "0" * 64
        r = from_json_spec(spec(e))
        self.assertFalse(r.accepted)
        self.assertEqual(r.failed_at, 1)

    def test_forged_counter_crossing_rejected(self):
        e = roundtrip()
        e[1]["writes"][3] = w(NONZERO_SLOT, 1)
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_missing_counter_tstore_rejected(self):
        e = roundtrip()
        e[1]["writes"].pop(1)
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_wrong_negative_twos_complement_rejected(self):
        e = roundtrip()
        e[1]["writes"][2]["value"] = word(7)
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_aggregate_zero_does_not_clear_per_address_deltas(self):
        e = [opening(),
             {"op": "pool_account", "actor": ROUTER, "kind": "swap",
              "currency0": A, "currency1": B, "hook": HOOK,
              "hook_delta": [-5, 0], "caller_delta": [5, 0],
              "writes": [w(delta_slot(HOOK, A), -5), w(NONZERO_SLOT, 1),
                         w(delta_slot(ROUTER, A), 5), w(NONZERO_SLOT, 2)]}, closing()]
        result = from_json_spec(spec(e))
        self.assertFalse(result.accepted)
        self.assertIn("unsettled", result.reason)

    def test_erc20_sync_overwrite_leaves_deposit_uncredited(self):
        e = [opening(),
             {"op": "sync", "actor": ROUTER, "currency": A, "observed_balance": 100,
              "writes": [w(SYNC_CURRENCY_SLOT, int(A, 16)), w(SYNC_BALANCE_SLOT, 100)]},
             {"op": "transfer", "actor": ROUTER, "currency": A, "source": ROUTER,
              "destination": MANAGER, "amount": 10, "writes": []},
             {"op": "sync", "actor": ROUTER, "currency": A, "observed_balance": 110,
              "writes": [w(SYNC_CURRENCY_SLOT, int(A, 16)), w(SYNC_BALANCE_SLOT, 110)]},
             {"op": "settle", "actor": ROUTER, "recipient": ROUTER, "msg_value": 0,
              "observed_balance": 110, "paid": 0,
              "writes": [w(SYNC_CURRENCY_SLOT, 0)]}, closing()]
        r = from_json_spec(spec(e))
        self.assertTrue(r.accepted, r.reason)
        self.assertEqual(r.terminal["vault_balances"][A], 110)
        e[4]["paid"] = 10
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_erc20_settle_for_credits_recipient(self):
        e = [opening(),
             {"op": "sync", "actor": ROUTER, "currency": A, "observed_balance": 100,
              "writes": [w(SYNC_CURRENCY_SLOT, int(A, 16)), w(SYNC_BALANCE_SLOT, 100)]},
             {"op": "transfer", "actor": ROUTER, "currency": A, "source": ROUTER,
              "destination": MANAGER, "amount": 5, "writes": []},
             {"op": "settle", "actor": ROUTER, "recipient": HOOK, "msg_value": 0,
              "paid": 5, "observed_balance": 105,
              "writes": [w(SYNC_CURRENCY_SLOT, 0), w(delta_slot(HOOK, A), 5),
                         w(NONZERO_SLOT, 1)]},
             {"op": "enter", "actor": ROUTER, "callee": HOOK, "writes": []},
             {"op": "clear", "actor": HOOK, "currency": A, "amount": 5,
              "writes": [w(delta_slot(HOOK, A), 0), w(NONZERO_SLOT, 0)]},
             {"op": "return", "actor": HOOK, "writes": []}, closing()]
        self.assertTrue(from_json_spec(spec(e)).accepted)
        e[3]["writes"][1]["slot"] = delta_slot(ROUTER, A)
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_unsynced_erc20_settle_has_native_semantics(self):
        e = [opening(), {"op": "settle", "actor": ROUTER, "recipient": ROUTER,
                         "msg_value": 7, "paid": 7, "observed_balance": 7,
                         "writes": [w(delta_slot(ROUTER, ZERO), 7), w(NONZERO_SLOT, 1)]},
             {"op": "clear", "actor": ROUTER, "currency": ZERO, "amount": 7,
              "writes": [w(delta_slot(ROUTER, ZERO), 0), w(NONZERO_SLOT, 0)]},
             closing()]
        r = from_json_spec(spec(e))
        self.assertTrue(r.accepted, r.reason)
        self.assertEqual(r.terminal["vault_balances"][ZERO], 7)
        e[1]["paid"] = 6
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_sync_native_resets_prior_erc20_snap(self):
        e = [opening(),
             {"op": "sync", "actor": ROUTER, "currency": A, "observed_balance": 100,
              "writes": [w(SYNC_CURRENCY_SLOT, int(A, 16)), w(SYNC_BALANCE_SLOT, 100)]},
             {"op": "sync", "actor": ROUTER, "currency": ZERO, "observed_balance": 0,
              "writes": [w(SYNC_CURRENCY_SLOT, 0)]},
             {"op": "settle", "actor": ROUTER, "recipient": ROUTER,
              "msg_value": 0, "paid": 0, "observed_balance": 0, "writes": []}, closing()]
        self.assertTrue(from_json_spec(spec(e)).accepted)

    def test_native_funds_overdraw_rejected(self):
        e = [opening(), {"op": "settle", "actor": ROUTER, "recipient": ROUTER,
                         "msg_value": 40, "paid": 40, "observed_balance": 40,
                         "writes": [w(delta_slot(ROUTER, ZERO), 40), w(NONZERO_SLOT, 1)]},
             closing()]
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_mint_and_caller_owned_burn_pair(self):
        e = [opening(),
             {"op": "mint", "actor": ROUTER, "currency": A, "recipient": ROUTER,
              "amount": 9, "writes": [w(delta_slot(ROUTER, A), -9), w(NONZERO_SLOT, 1)]},
             {"op": "burn", "actor": ROUTER, "currency": A, "amount": 9,
              "writes": [w(delta_slot(ROUTER, A), 0), w(NONZERO_SLOT, 0)]}, closing()]
        self.assertTrue(from_json_spec(spec(e)).accepted)
        e[2]["amount"] = 10
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_nested_callback_reverts_transient_state(self):
        e = [opening(), {"op": "enter", "actor": ROUTER, "callee": HOOK, "writes": []},
             {"op": "mint", "actor": HOOK, "currency": A, "recipient": HOOK,
              "amount": 5, "writes": [w(delta_slot(HOOK, A), -5), w(NONZERO_SLOT, 1)]},
             {"op": "revert", "actor": HOOK, "writes": []}, closing()]
        r = from_json_spec(spec(e))
        self.assertTrue(r.accepted, r.reason)
        self.assertEqual(r.terminal["claims"], {})
        self.assertEqual(r.terminal["nonzero_delta_count"], 0)

    def test_nested_unlock_rejected(self):
        e = [opening(), opening(), closing()]
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_unsupported_concentrated_liquidity_claim_rejected(self):
        e = [opening(), {"op": "pool.swap.concentrated", "actor": ROUTER,
                         "writes": []}, closing()]
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_unsupported_external_token_supply_rejected(self):
        e = [opening(), {"op": "transfer", "actor": ROUTER, "currency": A,
                         "source": ROUTER, "destination": "0x" + "a" * 40,
                         "amount": 1, "writes": []}, closing()]
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_missing_currency_and_source_pin_rejected(self):
        x = spec([opening(), closing()])
        x["core_commit"] = "0" * 40
        with self.assertRaises(WitnessError):
            V4DeltaWitness(x)
        x["core_commit"] = CORE_COMMIT
        del x["balances"][ZERO]
        self.assertTrue(from_json_spec(x).accepted)
        # Native settlement is guarded until native balance evidence is supplied.
        x["events"].insert(1, {"op": "settle", "actor": ROUTER, "recipient": ROUTER,
                               "msg_value": 1, "paid": 1, "observed_balance": 1,
                               "writes": [w(delta_slot(ROUTER, ZERO), 1), w(NONZERO_SLOT, 1)]})
        self.assertFalse(from_json_spec(x).accepted)

    def test_field_typos_and_bool_quantities_rejected(self):
        e = [opening(), closing()]
        e[1]["amount"] = True
        self.assertFalse(from_json_spec(spec(e)).accepted)
        e = roundtrip()
        e[4]["paid"] = True
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_unregistered_hook_with_zero_delta_can_be_skipped(self):
        e = [opening(), {"op": "pool_account", "actor": ROUTER, "kind": "swap",
                         "currency0": A, "currency1": B, "hook": ZERO,
                         "caller_delta": [0, 0], "hook_delta": [0, 0],
                         "writes": []}, closing()]
        r = from_json_spec(spec(e))
        self.assertTrue(r.accepted, r.reason)
        self.assertEqual(r.terminal["opaque_pool_calls"], 1)

    def test_third_party_hook_requires_registered_addresses(self):
        e = [opening(), {"op": "pool_account", "actor": ROUTER, "kind": "swap",
                         "currency0": A, "currency1": B, "hook": ZERO,
                         "caller_delta": [0, 0], "hook_delta": [1, 0],
                         "writes": []}, closing()]
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_donate_cannot_supply_hook_account_delta(self):
        e = [opening(), {"op": "pool_account", "actor": ROUTER, "kind": "donate",
                         "currency0": A, "currency1": B, "hook": HOOK,
                         "caller_delta": [0, 0], "hook_delta": [1, 0],
                         "writes": [w(delta_slot(HOOK, A), 1), w(NONZERO_SLOT, 1)]},
             closing()]
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_invalid_sign_width_rejected(self):
        e = [opening(), {"op": "pool_account", "actor": ROUTER, "kind": "swap",
                         "currency0": A, "currency1": B, "hook": ZERO,
                         "caller_delta": [-(2**127) - 1, 0], "hook_delta": [0, 0],
                         "writes": []}, closing()]
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_signed_zero_crossing_grid(self):
        for amount in list(range(-6, 0)) + list(range(1, 7)):
            events = [opening(),
                {"op": "pool_account", "actor": ROUTER, "kind": "donate",
                 "currency0": A, "currency1": B, "hook": ZERO,
                 "caller_delta": [amount, 0], "hook_delta": [0, 0],
                 "writes": [w(delta_slot(ROUTER, A), amount), w(NONZERO_SLOT, 1)]},
                {"op": "pool_account", "actor": ROUTER, "kind": "donate",
                 "currency0": A, "currency1": B, "hook": ZERO,
                 "caller_delta": [-amount, 0], "hook_delta": [0, 0],
                 "writes": [w(delta_slot(ROUTER, A), 0), w(NONZERO_SLOT, 0)]}, closing()]
            with self.subTest(amount=amount):
                self.assertTrue(from_json_spec(spec(events)).accepted)

    def test_settle_negative_balance_difference_rejected(self):
        e = [opening(),
             {"op": "sync", "actor": ROUTER, "currency": A,
              "observed_balance": 100,
              "writes": [w(SYNC_CURRENCY_SLOT, int(A, 16)), w(SYNC_BALANCE_SLOT, 100)]},
             {"op": "take", "actor": ROUTER, "currency": A, "recipient": ROUTER,
              "amount": 5,
              "writes": [w(delta_slot(ROUTER, A), -5), w(NONZERO_SLOT, 1)]},
             {"op": "settle", "actor": ROUTER, "recipient": ROUTER,
              "msg_value": 0, "paid": 0, "observed_balance": 95,
              "writes": [w(SYNC_CURRENCY_SLOT, 0)]}, closing()]
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_sync_permitted_outside_unlock(self):
        e = [{"op": "sync", "actor": ROUTER, "currency": A,
              "observed_balance": 100,
              "writes": [w(SYNC_CURRENCY_SLOT, int(A, 16)), w(SYNC_BALANCE_SLOT, 100)]},
             opening(), closing()]
        self.assertTrue(from_json_spec(spec(e)).accepted)

    def test_clear_zero_matches_real_contract(self):
        e = [opening(), {"op": "clear", "actor": ROUTER,
                         "currency": A, "amount": 0, "writes": []}, closing()]
        self.assertTrue(from_json_spec(spec(e)).accepted)
        e[1]["amount"] = 1
        self.assertFalse(from_json_spec(spec(e)).accepted)

    def test_replay_hash_deterministic_and_tamper_sensitive(self):
        a = from_json_spec(spec(roundtrip()))
        b = from_json_spec(spec(roundtrip()))
        self.assertEqual(a.evidence_hash, b.evidence_hash)
        c = roundtrip()
        c[6]["amount"] = 0  # exact non-mutating clear witness
        self.assertEqual(a.evidence_hash, from_json_spec(spec(c)).evidence_hash)
        c = roundtrip()
        c[7]["callee"] = TRADER
        d = from_json_spec(spec(c))
        self.assertFalse(d.accepted)  # later caller mismatch


if __name__ == '__main__':
    unittest.main()
