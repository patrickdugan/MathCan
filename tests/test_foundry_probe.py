"""CHTR-08 checks that a Foundry output cannot skip the recorded conservation gates.

The fixture here is synthetic; only the pinned CI Foundry step can run real Solidity.
"""
import copy
import unittest

from research.chitraverse.foundry_probe import (
    SCHEMA, SOURCE_COMMIT, ObservationError, verify_observation,
)


def base_observation():
    return {
        "schema": SCHEMA, "source_commit": SOURCE_COMMIT,
        "manager": "0x" + "01" * 20,
        "probe_router": "0x" + "02" * 20,
        "hook": "0x" + "03" * 20,
        "currency0": "0x" + "04" * 20,
        "currency1": "0x" + "05" * 20,
        "pool_id": "0x" + "ab" * 32,
        "manager_runtime_hash": "0x" + "11" * 32,
        "hook_runtime_hash": "0x" + "22" * 32,
        "swap_amount_specified": -10**12,
        "caller_delta0_before": 0, "caller_delta1_before": 0,
        "caller_delta0_settled": 0, "caller_delta1_settled": 0,
        "nonzero_before_swap": 0,
        "caller_delta0": -10**12,
        "caller_delta1": 997000000000,
        "event_delta0": -10**12,
        "event_delta1": 997000000000,
        "event_fee_pips": 3000,
        "nonzero_at_swap": 2,
        "nonzero_after_settlement": 0,
        "unlocked_at_swap": True, "unlocked_after": False,
        "before_swap_hook_observed": True, "after_swap_hook_observed": True,
        "swap_log_observed": True,
        "sqrt_price_before_x96": 79228162514264337593543950336,
        "sqrt_price_after_x96": 79228100000000000000000000000,
        "tick_before": 0, "tick_after": -1,
        "liquidity_before": 10**18,
        "liquidity_after": 10**18,
        "trader0_before": 2*10**18, "trader0_after": 2*10**18-10**12,
        "trader1_before": 2*10**18, "trader1_after": 2*10**18+997000000000,
        "vault0_before": 10**18, "vault0_after": 10**18+10**12,
        "vault1_before": 10**18, "vault1_after": 10**18-997000000000,
    }


class FoundryObservationVerificationTests(unittest.TestCase):
    def test_valid_declared_sample(self):
        result = verify_observation(base_observation())
        self.assertTrue(result["checked"])
        self.assertFalse(result["complete_source_evidence"])
        self.assertFalse(result["raw_tstore_stream_observed"])

    def _reject(self, **replacements):
        payload = base_observation()
        payload.update(replacements)
        with self.assertRaises(ObservationError):
            verify_observation(payload)

    def test_reject_source_mismatch(self):
        self._reject(source_commit="main")

    def test_reject_bad_fee(self):
        self._reject(event_fee_pips=2000)

    def test_reject_wrong_counter(self):
        self._reject(nonzero_at_swap=0)
        self._reject(nonzero_after_settlement=1)

    def test_reject_missing_caller_delta_clear(self):
        self._reject(caller_delta0_settled=-1)

    def test_reject_forged_hook(self):
        self._reject(before_swap_hook_observed=False)
        self._reject(after_swap_hook_observed=False)

    def test_reject_event_delta_mismatch(self):
        self._reject(event_delta1=997000000001)

    def test_reject_trader_money_creation(self):
        self._reject(trader1_after=2*10**18+997000000001)

    def test_reject_vault_money_creation(self):
        self._reject(vault0_after=10**18+10**12+1)

    def test_reject_wrong_price_direction(self):
        self._reject(sqrt_price_after_x96=79228162514264337593543950336)

    def test_reject_liquidity_change(self):
        self._reject(liquidity_after=10**18-1)

    def test_reject_unauthorized_extra_fields(self):
        payload = copy.deepcopy(base_observation())
        payload["complete_source_evidence"] = True
        with self.assertRaises(ObservationError):
            verify_observation(payload)

    def test_reject_noncanonical_ints(self):
        self._reject(caller_delta0=True)
        self._reject(event_delta0="-01")


if __name__ == "__main__":
    unittest.main()
