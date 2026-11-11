"""CHTR-09: independently check real Forge debug-trace TSTOREs and crossed-tick arithmetic.

This checker accepts a narrowly scoped, instrumented Foundry test observation,
its compiled PoolManager artifact, and an immutable v4-core source pin. The
Python and Solidity programs are independent implementations of the arithmetic.
An instrumented Foundry trace is runtime evidence from a test EVM, not a
formal proof that deployed mainnet bytecode refines every abstract operation.
"""
from __future__ import annotations

import argparse
import json
import hashlib
from pathlib import Path

from .v4_delta_refinement import (
    CORE_COMMIT, LOCK_SLOT, NONZERO_SLOT, SYNC_CURRENCY_SLOT, SYNC_BALANCE_SLOT,
    delta_slot, keccak256, word,
)

SCHEMA = "mathcan.chtr09.foundry-opcode.v1"
FEE_DEN = 1_000_000
Q96 = 1 << 96
L_UPPER = 10**18
L_LOWER = 2 * 10**18
GROSS_INPUT = 10**16
FEE = 3000
BOUNDARY_TICK = -120

# TickMath.getSqrtPriceAtTick, v4-core source; integer Q128.128 multipliers.
_TICK_MULT = (
    0xfffcb933bd6fad37aa2d162d1a594001,
    0xfff97272373d413259a46990580e213a,
    0xfff2e50f5f656932ef12357cf3c7fdcc,
    0xffe5caca7e10e4e61c3624eaa0941cd0,
    0xffcb9843d60f6159c9db58835c926644,
    0xff973b41fa98c081472e6896dfb254c0,
    0xff2ea16466c96a3843ec78b326b52861,
    0xfe5dee046a99a2a811c461f1969c3053,
    0xfcbe86c7900a88aedcffc83b479aa3a4,
    0xf987a7253ac413176f2b074cf7815e54,
    0xf3392b0822b70005940c7a398e4b70f3,
    0xe7159475a2c29b7443b29c7fa6e889d9,
    0xd097f3bdfd2022b8845ad8f792aa5825,
    0xa9f746462d870fdf8a65dc1f90e061e5,
    0x70d869a156d2a1b890bb3df62baf32f7,
    0x31be135f97d08fd981231505542fcfa6,
    0x9aa508b5b7a84e1c677de54f3e99bc9,
    0x5d6af8dedb81196699c329225ee604,
    0x2216e584f5fa1ea926041bedfe98,
    0x48a170391f7dc42444e8fa2,
)

class ProofError(ValueError):
    pass

def _assert(ok: bool, why: str):
    if not ok:
        raise ProofError(why)

def tick_price_x96(tick: int) -> int:
    _assert(type(tick) is int and abs(tick) <= 887272, "invalid tick")
    t = abs(tick)
    price = 1 << 128
    for i, mult in enumerate(_TICK_MULT):
        if t & (1 << i):
            price = (price * mult) >> 128
    if tick > 0:
        price = ((1 << 256) - 1) // price
    return (price + (1 << 32) - 1) >> 32

def ceildiv(a: int, b: int) -> int:
    _assert(a >= 0 and b > 0, "invalid ceiling division")
    return (a + b - 1) // b

def amount0_to_target(lo: int, hi: int, liquidity: int) -> int:
    return ceildiv(liquidity * Q96 * (hi - lo), hi * lo)

def amount1_from_move(lo: int, hi: int, liquidity: int) -> int:
    return liquidity * (hi - lo) // Q96

def quote_two_ticks(gross: int = GROSS_INPUT, fee: int = FEE):
    """Two SwapMath exact-input steps, split at initialized tick -120.

    Preconditions: starting price Q96 and active L_UPPER, adjacent L_LOWER at
    [-240,-120), no protocol fee or hook-return delta, target below -240.
    """
    _assert(type(gross) is int and gross > 0 and 0 <= fee < FEE_DEN, "bad amount/fee")
    price0 = Q96
    boundary = tick_price_x96(BOUNDARY_TICK)
    lower_limit = tick_price_x96(-240)
    net_to_boundary = amount0_to_target(boundary, price0, L_UPPER)
    step1_fee = ceildiv(net_to_boundary * fee, FEE_DEN - fee)
    spent1 = net_to_boundary + step1_fee
    _assert(spent1 < gross, "input too small to cross boundary")
    gross2 = gross - spent1
    net2 = gross2 * (FEE_DEN - fee) // FEE_DEN
    _assert(net2 > 0, "zero second-step input")
    numerator = (L_LOWER * Q96) * boundary
    denominator = L_LOWER * Q96 + net2 * boundary
    final_price = ceildiv(numerator, denominator)
    _assert(lower_limit < final_price < boundary, "input crosses more than one tick")
    out1 = amount1_from_move(boundary, price0, L_UPPER)
    out2 = amount1_from_move(final_price, boundary, L_LOWER)
    return {
        "boundary_price_x96": boundary,
        "input_step1": spent1,
        "net_input_step1": net_to_boundary,
        "fee_step1": step1_fee,
        "net_input_step2": net2,
        "fee_step2": gross2-net2,
        "amount_out_step1": out1,
        "amount_out_step2": out2,
        "total_output": out1 + out2,
        "sqrt_price_after_x96": final_price,
        "gross_input": gross,
    }

def _integer(v, name):
    if type(v) is int:
        return v
    if isinstance(v, str) and v.lstrip('-').isdigit():
        return int(v)
    raise ProofError(f"expected integer {name}")

def _address(v):
    return isinstance(v,str) and len(v)==42 and v.startswith('0x') and all(c in '0123456789abcdefABCDEF' for c in v[2:])

def _hex32(v):
    return isinstance(v,str) and len(v)==66 and v.startswith('0x') and all(c in '0123456789abcdefABCDEF' for c in v[2:])

def expected_manager_tstores(obs: dict, quote: dict):
    router = obs["probe_router"].lower()
    c0 = obs["currency0"].lower()
    c1 = obs["currency1"].lower()
    vault_before = _integer(obs["vault0_before"], "vault0_before")
    return [
        (LOCK_SLOT, word(1)),
        (delta_slot(router, c0), word(-GROSS_INPUT)),
        (NONZERO_SLOT, word(1)),
        (delta_slot(router, c1), word(quote["total_output"])),
        (NONZERO_SLOT, word(2)),
        (SYNC_CURRENCY_SLOT, word(int(c0, 16))),
        (SYNC_BALANCE_SLOT, word(vault_before)),
        (SYNC_CURRENCY_SLOT, word(0)),
        (delta_slot(router, c0), word(0)),
        (NONZERO_SLOT, word(1)),
        (delta_slot(router, c1), word(0)),
        (NONZERO_SLOT, word(0)),
        (LOCK_SLOT, word(0)),
    ]

def runtime_artifact_hash(artifact):
    _assert(isinstance(artifact, dict), "missing compiler artifact")
    deployed = artifact.get("deployedBytecode")
    _assert(isinstance(deployed,dict), "artifact lacks deployed bytecode")
    raw = deployed.get("object")
    _assert(isinstance(raw,str) and raw.startswith("0x") and len(raw)>6, "invalid deployed bytecode")
    _assert(not deployed.get("immutableReferences"), "runtime has immutable references; resolve them first")
    try:
        bytecode=bytes.fromhex(raw[2:])
    except ValueError as exc:
        raise ProofError("unlinked or malformed deployed bytecode") from exc
    return "0x" + keccak256(bytecode).hex()

def verify_trace(obs: dict, artifact: dict | None = None) -> dict:
    _assert(isinstance(obs,dict) and obs.get("schema")==SCHEMA, "unexpected schema")
    _assert(obs.get("core_commit")==CORE_COMMIT, "wrong upstream source pin")
    for key in ("manager","probe_router","currency0","currency1","hook"):
        _assert(_address(obs.get(key)), f"invalid {key}")
    _assert(len({obs[k].lower() for k in ("manager","probe_router","currency0","currency1","hook")})==5, "duplicate addresses")
    _assert(_hex32(obs.get("manager_runtime_hash")), "missing manager bytecode hash")
    _assert(_hex32(obs.get("pool_id")), "missing pool identifier")
    quote=quote_two_ticks()
    expected_nums={
        "sqrt_price_before_x96": Q96,
        "boundary_price_x96": quote["boundary_price_x96"],
        "sqrt_price_after_x96": quote["sqrt_price_after_x96"],
        "liquidity_before": L_UPPER,
        "liquidity_after": L_LOWER,
        "tick_before": 0,
        "swap_amount_specified": -GROSS_INPUT,
        "caller_delta0": -GROSS_INPUT,
        "caller_delta1": quote["total_output"],
        "event_delta0": -GROSS_INPUT,
        "event_delta1": quote["total_output"],
        "event_fee_pips": FEE,
        "nonzero_at_swap": 2,
        "nonzero_after_settlement": 0,
    }
    for key,value in expected_nums.items():
        _assert(_integer(obs.get(key),key)==value, f"mismatch in {key}")
    tick=_integer(obs.get("tick_after"),"tick_after")
    _assert(-240 < tick < BOUNDARY_TICK, "tick has not crossed exactly one liquidity boundary")
    _assert(obs.get("hooks_observed") is True and obs.get("swap_log_observed") is True,
            "hook calls or pool Swap log not observed")
    for i in (0,1):
        trader_delta=_integer(obs.get(f"trader{i}_after"),f"trader{i}_after")-_integer(obs.get(f"trader{i}_before"),f"trader{i}_before")
        vault_delta=_integer(obs.get(f"vault{i}_after"),f"vault{i}_after")-_integer(obs.get(f"vault{i}_before"),f"vault{i}_before")
        target=expected_nums[f"caller_delta{i}"]
        _assert(trader_delta==target and vault_delta==-target, f"currency{i} balance conservation failed")
    flat=obs.get("manager_tstore_pairs")
    _assert(isinstance(flat,list) and len(flat)%2==0 and len(flat)>=2, "missing raw TSTORE sequence")
    _assert(_integer(obs.get("debug_step_count"),"debug_step_count")>=len(flat)//2, "debug step count invalid")
    _assert(_integer(obs.get("manager_tstore_count"),"manager_tstore_count")==len(flat)//2, "TSTORE count mismatch")
    _assert(all(_hex32(x) for x in flat), "malformed TSTORE word")
    got=[(flat[i].lower(),flat[i+1].lower()) for i in range(0,len(flat),2)]
    expected=expected_manager_tstores(obs,quote)
    _assert(got==expected, f"ordered TSTORE sequence differs: got {len(got)} expected {len(expected)}")
    if artifact is not None:
        _assert(runtime_artifact_hash(artifact).lower()==obs["manager_runtime_hash"].lower(),
                "compiled PoolManager deployedBytecode disagrees with observed runtime hash")
    return {
        "schema":"mathcan.chtr09.verified.v1",
        "verified":True,
        "core_commit":CORE_COMMIT,
        "manager_runtime_hash":obs["manager_runtime_hash"],
        "artifact_runtime_matched":artifact is not None,
        "raw_ordered_tstores_matched":True,
        "manager_tstores":len(got),
        "debug_steps":_integer(obs["debug_step_count"],"debug_step_count"),
        "crossed_initialized_tick":BOUNDARY_TICK,
        "exact_multitick_q96_rounding":True,
        "final_price_x96":str(quote["sqrt_price_after_x96"]),
        "gross_input":str(GROSS_INPUT),
        "output":str(quote["total_output"]),
        "observation_sha256":hashlib.sha256(json.dumps(obs,sort_keys=True,separators=(",",":")).encode()).hexdigest(),
        "evm_coverage":"single Foundry test execution with one initialized-tick crossing, finite manager TSTORE sequence and standard ERC20 transfers; no universal deployment proof",
    }

def main(argv=None):
    p=argparse.ArgumentParser(description="CHTR-09 opcode and multi-tick execution verifier")
    p.add_argument("observation",type=Path)
    p.add_argument("--artifact",type=Path,required=True)
    p.add_argument("--out",type=Path)
    a=p.parse_args(argv)
    try:
        result=verify_trace(json.loads(a.observation.read_text()),json.loads(a.artifact.read_text()))
    except (ProofError,ValueError,OSError) as e:
        p.error(str(e))
    encoded=json.dumps(result,indent=2,sort_keys=True)+"\n"
    if a.out:
        a.out.write_text(encoded)
    else:
        print(encoded,end="")
    return 0

if __name__=="__main__":
    raise SystemExit(main())
