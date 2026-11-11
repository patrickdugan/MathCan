"""CHTR-10 exact independent hook-return and four-step concentrated-liquidity audit.

Inputs are Forge-instrumented observations for one pinned test. This validates
finite EVM execution evidence and exact step arithmetic, not all deployed hooks.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from .foundry_opcode import (
    CORE_COMMIT, LOCK_SLOT, NONZERO_SLOT, Q96, FEE, FEE_DEN,
    SYNC_CURRENCY_SLOT, SYNC_BALANCE_SLOT, ProofError, _assert, _integer,
    _address, _hex32, tick_price_x96, amount0_to_target, amount1_from_move,
    ceildiv, runtime_artifact_hash,
)
from .v4_delta_refinement import delta_slot, word

SCHEMA = "mathcan.chtr10.hook-multitick.v1"
GROSS = 5 * 10**16
SPECIFIED = 10**15
BEFORE_UNSPECIFIED = 2 * 10**12
AFTER_UNSPECIFIED = 3 * 10**12
HOOK_UNSPECIFIED = BEFORE_UNSPECIFIED + AFTER_UNSPECIFIED
POOL_INPUT = GROSS - SPECIFIED
BANDS = ((-120, 10**18), (-240, 2 * 10**18),
         (-360, 3 * 10**18), (-480, 4 * 10**18))
EXPECTED_MANAGER_WRITES = 21


def quote_multitick(gross: int = POOL_INPUT, fee: int = FEE):
    """Independent exact-in SwapMath across three initialized boundaries.

    First three targets are reached; the fourth is approached without crossing.
    Bounds on gross and fee are checked rather than accepting an inapplicable
    two-step shortcut.
    """
    _assert(type(gross) is int and 0 < gross < 2**127, "invalid gross input")
    _assert(type(fee) is int and 0 <= fee < FEE_DEN, "invalid fee")
    current_price, remaining = Q96, gross
    steps = []
    for boundary_tick, liquidity in BANDS:
        target = tick_price_x96(boundary_tick)
        net_target = amount0_to_target(target, current_price, liquidity)
        spend_target = net_target + ceildiv(net_target * fee, FEE_DEN - fee)
        crossed = remaining >= spend_target
        if crossed:
            new_price, net, spent = target, net_target, spend_target
        else:
            spent = remaining
            net = remaining * (FEE_DEN - fee) // FEE_DEN
            new_price = ceildiv(liquidity * Q96 * current_price,
                                liquidity * Q96 + net * current_price)
        output = amount1_from_move(new_price, current_price, liquidity)
        _assert(0 < output and target <= new_price <= current_price, "invalid tick step")
        steps.append({
            "target_tick": boundary_tick,
            "price_before": current_price,
            "price_after": new_price,
            "liquidity": liquidity,
            "gross_spent": spent,
            "effective_input": net,
            "fee_amount": spent - net,
            "output": output,
            "crossed_tick": crossed,
        })
        current_price = new_price
        remaining -= spent
        if remaining == 0:
            break
    _assert(remaining == 0 and len(steps) == 4 and
            [step["crossed_tick"] for step in steps] == [True, True, True, False],
            "expected exactly three initialized crossings")
    _assert(sum(x["gross_spent"] for x in steps) == gross, "gross input mismatch")
    return {
        "steps": steps,
        "total_output": sum(x["output"] for x in steps),
        "sqrt_price_after_x96": current_price,
        "fee_pips": fee,
        "crossed_ticks": [-120, -240, -360],
        "active_liquidity_after": 4 * 10**18,
        "terminal_tick": max(t for t in range(-480, -360) if tick_price_x96(t) <= current_price),
    }


def expected_manager_tstores(obs: dict, quote: dict):
    hook = obs["hook"].lower()
    router = obs["router"].lower()
    c0, c1 = obs["currency0"].lower(), obs["currency1"].lower()
    hook_a = SPECIFIED
    hook_b = HOOK_UNSPECIFIED
    router_b = quote["total_output"] - hook_b
    vault_before = _integer(obs["vault0_before"], "vault0_before")
    # The hook collects its positive currency0 delta BEFORE router.sync(c0).
    # The real CurrencyReserves snapshot therefore sees the vault after take().
    synced_after_hook_take = vault_before - hook_a
    _assert(synced_after_hook_take >= 0, "vault lacks pre-sync hook payout")
    return [
        (LOCK_SLOT, word(1)),
        (delta_slot(hook,c0),word(hook_a)), (NONZERO_SLOT,word(1)),
        (delta_slot(hook,c1),word(hook_b)), (NONZERO_SLOT,word(2)),
        (delta_slot(router,c0),word(-GROSS)), (NONZERO_SLOT,word(3)),
        (delta_slot(router,c1),word(router_b)), (NONZERO_SLOT,word(4)),
        (delta_slot(hook,c0),word(0)), (NONZERO_SLOT,word(3)),
        (delta_slot(hook,c1),word(0)), (NONZERO_SLOT,word(2)),
        (SYNC_CURRENCY_SLOT,word(int(c0,16))), (SYNC_BALANCE_SLOT,word(synced_after_hook_take)),
        (SYNC_CURRENCY_SLOT,word(0)),
        (delta_slot(router,c0),word(0)), (NONZERO_SLOT,word(1)),
        (delta_slot(router,c1),word(0)), (NONZERO_SLOT,word(0)),
        (LOCK_SLOT,word(0)),
    ]


def verify_trace(obs: dict, manager_artifact: dict | None = None,
                 hook_artifact: dict | None = None):
    _assert(type(obs) is dict and obs.get("schema") == SCHEMA, "CHTR-10 schema mismatch")
    _assert(obs.get("core_commit") == CORE_COMMIT, "pinned source commit mismatch")
    for field in ("manager","router","hook","currency0","currency1"):
        _assert(_address(obs.get(field)), f"invalid {field}")
    _assert(len({obs[x].lower() for x in ("manager","router","hook","currency0","currency1")})==5,
            "duplicate addresses in witness")
    for field in ("manager_runtime_hash","hook_runtime_hash","pool_id"):
        _assert(_hex32(obs.get(field)), f"invalid {field}")
    q = quote_multitick()
    expected = {
        "amount_specified": -GROSS,
        "before_specified": SPECIFIED,
        "before_unspecified": BEFORE_UNSPECIFIED,
        "after_unspecified": AFTER_UNSPECIFIED,
        "pool_delta0": -POOL_INPUT,
        "pool_delta1": q["total_output"],
        "caller_delta0": -GROSS,
        "caller_delta1": q["total_output"] - HOOK_UNSPECIFIED,
        "hook_delta0": SPECIFIED,
        "hook_delta1": HOOK_UNSPECIFIED,
        "event_delta0": -POOL_INPUT,
        "event_delta1": q["total_output"],
        "fee_pips": FEE,
        "sqrt_price_before_x96": Q96,
        "sqrt_price_after_x96": q["sqrt_price_after_x96"],
        "tick_before": 0,
        "tick_after": q["terminal_tick"],
        "liquidity_before": 10**18,
        "liquidity_after": 4*10**18,
        "nonzero_at_swap": 4,
        "nonzero_after_settlement": 0,
    }
    for k, wanted in expected.items():
        _assert(_integer(obs.get(k),k) == wanted, f"mismatch in {k}")
    for i in (0,1):
        trader = _integer(obs[f"trader{i}_after"],f"trader{i}_after") - _integer(obs[f"trader{i}_before"],f"trader{i}_before")
        hook = _integer(obs[f"hook{i}_after"],f"hook{i}_after") - _integer(obs[f"hook{i}_before"],f"hook{i}_before")
        vault = _integer(obs[f"vault{i}_after"],f"vault{i}_after") - _integer(obs[f"vault{i}_before"],f"vault{i}_before")
        _assert(trader == expected[f"caller_delta{i}"], f"trader{i} value mismatch")
        _assert(hook == expected[f"hook_delta{i}"], f"hook{i} value mismatch")
        _assert(vault == -expected[f"pool_delta{i}"], f"vault{i} value mismatch")
        _assert(trader + hook + vault == 0, f"currency{i} physical conservation failed")
    flat=obs.get("manager_tstore_pairs")
    _assert(isinstance(flat,list) and len(flat) % 2 == 0 and all(_hex32(x) for x in flat),
            "invalid TSTORE stream")
    got=[(flat[i].lower(),flat[i+1].lower()) for i in range(0,len(flat),2)]
    _assert(_integer(obs.get("manager_tstore_count"),"manager_tstore_count") == len(got),
            "TSTORE count mismatch")
    _assert(_integer(obs.get("debug_step_count"),"debug_step_count") >= len(got),
            "debug trace step count impossible")
    want = expected_manager_tstores(obs,q)
    if got != want:
        first = next((i for i in range(min(len(got), len(want))) if got[i] != want[i]),
                     min(len(got), len(want)))
        actual = got[first] if first < len(got) else None
        target = want[first] if first < len(want) else None
        raise ProofError(f"ordered manager TSTORE mismatch at index {first}: "
                         f"observed {actual}, expected {target}, "
                         f"lengths {len(got)}/{len(want)}")
    _assert(manager_artifact is not None, "compiled PoolManager artifact required")
    _assert(hook_artifact is not None, "compiled hook artifact required")
    _assert(runtime_artifact_hash(manager_artifact, obs["manager"]).lower() == obs["manager_runtime_hash"].lower(),
            "compiled PoolManager runtime hash mismatch")
    _assert(runtime_artifact_hash(hook_artifact, obs["hook"]).lower() == obs["hook_runtime_hash"].lower(),
            "compiled hook runtime hash mismatch")
    return {
        "schema": "mathcan.chtr10.verified.v1",
        "verified": True,
        "source": CORE_COMMIT,
        "manager_tstores": len(got),
        "hook_return_specified": SPECIFIED,
        "hook_return_unspecified": HOOK_UNSPECIFIED,
        "initialized_boundaries_crossed": q["crossed_ticks"],
        "pool_output": str(q["total_output"]),
        "caller_output": str(expected["caller_delta1"]),
        "final_price_x96": str(q["sqrt_price_after_x96"]),
        "final_tick": q["terminal_tick"],
        "both_runtime_artifacts_matched": True,
        "source_evidence": "one pinned local Foundry execution; EVM proof for arbitrary hooks or mainnet is out of scope",
        "observation_sha256": hashlib.sha256(json.dumps(obs,sort_keys=True,separators=(",",":")).encode()).hexdigest(),
    }


def main(argv=None):
    p=argparse.ArgumentParser(description="CHTR-10 hook-return and multi-tick opcode verifier")
    p.add_argument("observation",type=Path)
    p.add_argument("--manager-artifact",type=Path,required=True)
    p.add_argument("--hook-artifact",type=Path,required=True)
    p.add_argument("--out",type=Path)
    a=p.parse_args(argv)
    try:
        result=verify_trace(json.loads(a.observation.read_text()),
                            json.loads(a.manager_artifact.read_text()),
                            json.loads(a.hook_artifact.read_text()))
    except (ProofError,ValueError,TypeError,OSError) as exc:
        p.error(str(exc))
    encoded=json.dumps(result,sort_keys=True,indent=2)+"\n"
    if a.out:
        a.out.write_text(encoded)
    else:
        print(encoded,end="")
    return 0

if __name__=="__main__":
    raise SystemExit(main())
