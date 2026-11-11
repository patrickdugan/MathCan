"""CHTR-08: independent checks of an instrumented, *actual* Foundry v4-core swap.

This takes the JSON produced by MathCanCHTR08.t.sol at a pinned Uniswap core
checkout. The JSON document alone is not authenticated EVM opcode coverage.
Its provenance is the CI job, compiler output, immutable core revision, and
Foundry test source; the accepted verdict is limited to observed properties.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path

SOURCE_COMMIT = "bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6"
SCHEMA = "mathcan.chtr08.foundry-observation.v1"
HEX20 = re.compile(r"0x[0-9a-fA-F]{40}\Z")
HEX32 = re.compile(r"0x[0-9a-fA-F]{64}\Z")
FIELDS = {
    "schema", "source_commit", "manager", "probe_router", "hook",
    "currency0", "currency1", "pool_id", "manager_runtime_hash",
    "hook_runtime_hash", "swap_amount_specified", "caller_delta0_before", "caller_delta1_before", "caller_delta0", "caller_delta1",
    "caller_delta0_settled", "caller_delta1_settled", "nonzero_before_swap",
    "event_delta0", "event_delta1", "event_fee_pips", "nonzero_at_swap",
    "nonzero_after_settlement", "unlocked_at_swap", "unlocked_after",
    "before_swap_hook_observed", "after_swap_hook_observed", "swap_log_observed",
    "sqrt_price_before_x96", "sqrt_price_after_x96", "tick_before", "tick_after",
    "liquidity_before", "liquidity_after", "trader0_before", "trader0_after",
    "trader1_before", "trader1_after", "vault0_before", "vault0_after",
    "vault1_before", "vault1_after",
}
NUMERIC = FIELDS - {
    "schema", "source_commit", "manager", "probe_router", "hook", "currency0", "currency1",
    "pool_id", "manager_runtime_hash", "hook_runtime_hash", "unlocked_at_swap",
    "unlocked_after", "before_swap_hook_observed", "after_swap_hook_observed", "swap_log_observed",
}


class ObservationError(ValueError):
    pass


def _integer(value, name):
    # Foundry vm.serializeInt may produce an int or a decimal string.
    if type(value) is int:
        return value
    if isinstance(value, str) and re.fullmatch(r"-?(0|[1-9][0-9]*)", value):
        return int(value)
    raise ObservationError(f"{name} must be a plain integer")


def _check(condition, label):
    if not condition:
        raise ObservationError(label)


def verify_observation(source: dict) -> dict:
    if not isinstance(source, dict) or set(source) != FIELDS:
        raise ObservationError("missing/extra observation fields")
    _check(source["schema"] == SCHEMA and source["source_commit"] == SOURCE_COMMIT,
           "schema or pinned core revision mismatch")
    for name in ("manager", "probe_router", "hook", "currency0", "currency1"):
        _check(isinstance(source[name], str) and HEX20.fullmatch(source[name]), f"invalid {name}")
    _check(len({source[k].lower() for k in ("manager", "probe_router", "hook", "currency0", "currency1")}) == 5,
           "manager/router/hook/token addresses must be distinct")
    for name in ("pool_id", "manager_runtime_hash", "hook_runtime_hash"):
        value = source[name]
        _check(isinstance(value, str) and HEX32.fullmatch(value) and int(value, 16) != 0,
               f"invalid {name}")
    for flag in ("unlocked_at_swap", "unlocked_after", "before_swap_hook_observed",
                 "after_swap_hook_observed", "swap_log_observed"):
        _check(type(source[flag]) is bool, f"{flag} must be bool")
    n = {key: _integer(source[key], key) for key in NUMERIC}
    _check(n["swap_amount_specified"] == -10**12, "unexpected exact-input amount")
    _check(n["caller_delta0"] < 0 < n["caller_delta1"], "unexpected swap delta signs")
    _check(n["caller_delta0"] >= n["swap_amount_specified"], "currency0 delta exceeds input")
    _check(abs(n["caller_delta0"]) < 2**127 and n["caller_delta1"] < 2**127, "int128 overflow")
    _check(n["caller_delta0"] == n["event_delta0"] and
           n["caller_delta1"] == n["event_delta1"], "emitted swap event disagrees with caller delta")
    _check(n["event_fee_pips"] == 3000, "unexpected pool fee")
    _check(n["caller_delta0_before"] == n["caller_delta1_before"] == 0 and
           n["caller_delta0_settled"] == n["caller_delta1_settled"] == 0 and
           n["nonzero_before_swap"] == 0, "observed before/after currency deltas not zero")
    _check(n["nonzero_at_swap"] == 2 and n["nonzero_after_settlement"] == 0,
           "two-currency nonzero-count witness failed")
    _check(source["unlocked_at_swap"] and not source["unlocked_after"], "unlock state mismatch")
    _check(source["before_swap_hook_observed"] and source["after_swap_hook_observed"]
           and source["swap_log_observed"], "hook callbacks or PoolManager event missing")
    _check(0 < n["sqrt_price_after_x96"] < n["sqrt_price_before_x96"] < 2**160,
           "concentrated-liquidity sqrt price did not decrease")
    _check(-887272 <= n["tick_after"] <= n["tick_before"] <= 887272,
           "tick movement out of expected interval")
    _check(n["liquidity_before"] == n["liquidity_after"] > 0,
           "unexpected active-liquidity change")
    for key in ("trader0_before", "trader0_after", "trader1_before", "trader1_after",
                "vault0_before", "vault0_after", "vault1_before", "vault1_after"):
        _check(0 <= n[key] <= 2**256-1, f"invalid ERC20 balance: {key}")
    d0 = n["caller_delta0"]
    d1 = n["caller_delta1"]
    _check(n["trader0_after"] - n["trader0_before"] == d0,
           "currency0 trader token movement differs from swap")
    _check(n["trader1_after"] - n["trader1_before"] == d1,
           "currency1 trader token movement differs from swap")
    _check(n["vault0_after"] - n["vault0_before"] == -d0,
           "currency0 manager custody differs from swap")
    _check(n["vault1_after"] - n["vault1_before"] == -d1,
           "currency1 manager custody differs from swap")
    encoded = json.dumps(source, sort_keys=True, separators=(",", ":")).encode()
    return {
        "schema": "mathcan.chtr08.verification.v1",
        "checked": True,
        "source_commit": SOURCE_COMMIT,
        "observation_sha256": hashlib.sha256(encoded).hexdigest(),
        "pool_id": source["pool_id"],
        "caller_delta0": str(d0),
        "caller_delta1": str(d1),
        "observed_nonzero_at_swap": 2,
        "observed_nonzero_at_unlock_end": 0,
        "observed_event_and_hook_callbacks": True,
        "observed_concentrated_liquidity_transition": True,
        "observed_exact_erc20_settlement": True,
        "complete_source_evidence": False,
        "raw_tstore_stream_observed": False,
        "proof_scope": "instrumented Foundry test observations checked against token deltas, pool slot0 and Swap log; raw opcode trace and Pool.swap tick-step reconstruction remain separate",
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description="Verify pinned v4-core Foundry observations")
    parser.add_argument("observation", type=Path)
    parser.add_argument("--result", type=Path)
    args = parser.parse_args(argv)
    try:
        result = verify_observation(json.loads(args.observation.read_text()))
    except (OSError, json.JSONDecodeError, ObservationError) as e:
        parser.error(str(e))
    encoded = json.dumps(result, sort_keys=True, indent=2) + "\n"
    if args.result:
        args.result.write_text(encoded)
    else:
        print(encoded, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
