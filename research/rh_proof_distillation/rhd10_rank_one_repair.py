"""RHD-10: finite-character and exceptional-place recurrent repair gym.

Uses RHD-09 exact finite-ring arithmetic. This verifies a *finite shadow*
of the local/global rank-one construction. No adelic or upstream Lean
TyEll witness is produced by these synthetic examples.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
import hashlib
import json
from pathlib import Path

from research.rh_proof_distillation.rhd09_local_character import (
    P, P2, COEFFS, dirichlet_exponent, lifted_factors, principal_norm, theta,
)

FACTORS = lifted_factors()
TRUE_COEFFS = tuple(f[1] % P for f in FACTORS)
assert TRUE_COEFFS == tuple(c % P for c in COEFFS)
ALL_PLACES = frozenset(range(4))


@dataclass(frozen=True)
class Candidate:
    w0: int
    local_coeffs: tuple[int, int, int, int]
    global_sign: int
    conductor: int
    unit_offset: int
    exceptions: frozenset[int]


def clean_candidate(w0: int) -> Candidate:
    if w0 not in ALL_PLACES:
        raise ValueError("selected place must index one of four prime factors")
    return Candidate(w0, TRUE_COEFFS, 1, P2, 0, ALL_PLACES - {w0})


def snapshot(s: Candidate) -> dict:
    return {
        "w0": s.w0,
        "local_coeffs": list(s.local_coeffs),
        "global_sign": s.global_sign,
        "conductor": s.conductor,
        "unit_offset": s.unit_offset,
        "exceptions": sorted(s.exceptions),
    }


def fault_catalog(w0: int) -> tuple[str, ...]:
    return tuple(f"local:{j}" for j in range(4)) + (
        "global_sign", "conductor", "unit_offset",
    ) + tuple(f"exception:{j}" for j in range(4) if j != w0)


def inject_fault(s: Candidate, fault: str, shift: int = 1) -> Candidate:
    if fault.startswith("local:"):
        j = int(fault.split(":")[1])
        if j not in range(4) or shift % P == 0:
            raise ValueError("invalid local coefficient corruption")
        v = list(s.local_coeffs)
        v[j] = (v[j] + shift) % P
        return replace(s, local_coeffs=tuple(v))
    if fault == "global_sign":
        return replace(s, global_sign=-s.global_sign)
    if fault == "conductor":
        return replace(s, conductor=P)
    if fault == "unit_offset":
        return replace(s, unit_offset=shift % P or 1)
    if fault.startswith("exception:"):
        j = int(fault.split(":")[1])
        if j == s.w0 or j not in ALL_PLACES:
            raise ValueError("invalid exceptional place")
        return replace(s, exceptions=s.exceptions - {j})
    raise ValueError(f"unknown fault: {fault}")


def verify(s: Candidate) -> list[dict]:
    """Complete gate check for the deliberately restricted candidate language.

    On each degree-two first layer theta(a,b)=2a-cb; the single b=1
    witness detects *every* coefficient mutation. A scalar a=15 witness
    checks the global-sign convention. The identity unit checks the
    additive offset, and every ramified place has an explicit nontrivial
    norm-character witness. This is not a proof of adelic globalization.
    """
    failures = []
    for j, f in enumerate(FACTORS):
        expected = theta(f, 0, 1)
        observed = (-s.local_coeffs[j]) % P
        if observed != expected:
            failures.append({
                "gate": "local_character",
                "factor": j, "probe": [0, 1],
                "observed": observed, "expected": expected,
            })

    qnorm = dirichlet_exponent(principal_norm(FACTORS[s.w0], 15, 0))
    if s.global_sign * qnorm % P != theta(FACTORS[s.w0], 15, 0):
        failures.append({
            "gate": "global_norm_pullback",
            "selected_place": s.w0,
            "probe": [15, 0],
            "observed": (s.global_sign * qnorm) % P,
            "expected": theta(FACTORS[s.w0], 15, 0),
        })

    if s.conductor != P2:
        failures.append({
            "gate": "exact_conductor",
            "probe": [1 + P],
            "reason": "first principal-unit layer becomes trivial modulo 29",
            "observed": s.conductor, "expected": P2,
        })

    # A nonzero constant term violates q(1)=0, hence multiplicativity.
    if s.unit_offset % P:
        failures.append({
            "gate": "idele_unit_normalization",
            "probe": [1, -1],
            "observed": s.unit_offset % P, "expected": 0,
        })

    for j in sorted(ALL_PLACES - {s.w0}):
        qj = dirichlet_exponent(principal_norm(FACTORS[j], 15, 0))
        assert qj == 1  # explicit, first-layer witness of ramification
        if j not in s.exceptions:
            failures.append({
                "gate": "missing_exception",
                "place": j, "probe": [15, 0],
                "norm_character_exponent": qj,
            })
    if s.w0 in s.exceptions:
        failures.append({"gate": "selected_place_in_exception_set",
                         "place": s.w0})
    if s.exceptions - ALL_PLACES:
        failures.append({"gate": "unknown_exception",
                         "places": sorted(s.exceptions - ALL_PLACES)})
    return failures


def suggested_action(failure: dict) -> dict:
    gate = failure["gate"]
    if gate == "local_character":
        j = failure["factor"]
        return {"kind": "set_local_coefficient", "factor": j,
                "value": TRUE_COEFFS[j]}
    if gate == "global_norm_pullback":
        return {"kind": "set_global_sign", "value": 1}
    if gate == "exact_conductor":
        return {"kind": "set_conductor", "value": P2}
    if gate == "idele_unit_normalization":
        return {"kind": "set_unit_offset", "value": 0}
    if gate == "missing_exception":
        return {"kind": "add_exception", "place": failure["place"]}
    if gate == "selected_place_in_exception_set":
        return {"kind": "drop_exception", "place": failure["place"]}
    raise ValueError(f"unsupported failure: {gate}")


def apply_action(s: Candidate, action: dict) -> Candidate:
    kind = action["kind"]
    if kind == "set_local_coefficient":
        j, value = action["factor"], action["value"]
        if j not in range(4) or value not in range(P):
            raise ValueError("bad coefficient action")
        v = list(s.local_coeffs)
        v[j] = value
        return replace(s, local_coeffs=tuple(v))
    if kind == "set_global_sign":
        if action["value"] not in (-1, 1):
            raise ValueError("bad sign")
        return replace(s, global_sign=action["value"])
    if kind == "set_conductor":
        if action["value"] not in (P, P2):
            raise ValueError("bad conductor")
        return replace(s, conductor=action["value"])
    if kind == "set_unit_offset":
        if action["value"] not in range(P):
            raise ValueError("bad unit offset")
        return replace(s, unit_offset=action["value"])
    if kind in ("add_exception", "drop_exception"):
        j = action["place"]
        if j not in ALL_PLACES:
            raise ValueError("unknown place")
        selected = s.exceptions | {j} if kind == "add_exception" else s.exceptions - {j}
        return replace(s, exceptions=selected)
    raise ValueError(f"invalid action: {kind}")


def digest_root(w0: int, a: int, b: int) -> bytes:
    return hashlib.sha256(f"RHD10/root/{w0}/{a}/{b}".encode()).digest()


def split_for_root(w0: int, a: int, b: int) -> str:
    bucket = int.from_bytes(digest_root(w0, a, b)[:4], "big") % 10
    return "train" if bucket < 7 else "val" if bucket < 9 else "test"


def create_episode(w0: int, a: int, b: int) -> dict:
    key = f"{w0}/{a}/{b}"
    root_hash = digest_root(w0, a, b)
    k = 1 + root_hash[4] % 3
    ranked = sorted(
        fault_catalog(w0),
        key=lambda f: hashlib.sha256(f"RHD10/fault/{key}/{f}".encode()).digest(),
    )
    selected = ranked[:k]
    state = clean_candidate(w0)
    for i, fault in enumerate(selected):
        state = inject_fault(state, fault, shift=1 + root_hash[5 + i] % 5)
    first = verify(state)
    assert len(first) == k, (key, selected, first)

    initial = snapshot(state)
    trace = []
    for step in range(k):
        failures = verify(state)
        action = suggested_action(failures[0])
        next_state = apply_action(state, action)
        next_failures = verify(next_state)
        assert len(next_failures) == len(failures) - 1
        trace.append({
            "step": step,
            "action": action,
            "remaining_violations": len(next_failures),
            "verifier_pass": not next_failures,
        })
        state = next_state
    assert not verify(state)
    f = FACTORS[w0]
    return {
        "task": "rhd10_finite_rank_one_repair",
        "root_id": f"RHD10/{key}",
        "split": split_for_root(w0, a, b),
        "source_prime": P,
        "source_conductor": P2,
        "selected_factor": w0,
        "local_probe": {
            "a": a, "b": b, "factor_mod_841": list(f),
            "true_norm": principal_norm(f, a, b),
            "q_norm": dirichlet_exponent(principal_norm(f, a, b)),
        },
        "candidate": initial,
        "verifier_feedback": first,
        "oracle_actions": trace + [{"kind": "STOP", "verifier_pass": True}],
        "oracle_terminal": snapshot(state),
        "oracle_steps": k,
        "one_step_budget_pass": k == 1,
        "two_step_budget_pass": k <= 2,
        "lean_witness_proved": False,
        "automorphic_witness_proved": False,
    }


def episodes():
    for w0 in range(4):
        for a in range(P):
            for b in range(P):
                yield create_episode(w0, a, b)


def write_data(path: Path) -> dict:
    path.parent.mkdir(parents=True, exist_ok=True)
    h = hashlib.sha256()
    counts = {"train": 0, "val": 0, "test": 0}
    budgets = {"one_step": 0, "two_step": 0, "three_step": 0}
    faults_by_length = {"1": 0, "2": 0, "3": 0}
    with path.open("wb") as out:
        for episode in episodes():
            encoded = (json.dumps(episode, sort_keys=True, separators=(",", ":")) + "\n").encode()
            out.write(encoded)
            h.update(encoded)
            counts[episode["split"]] += 1
            k = episode["oracle_steps"]
            faults_by_length[str(k)] += 1
            for limit, key in ((1, "one_step"), (2, "two_step"), (3, "three_step")):
                if k <= limit:
                    budgets[key] += 1
    manifest = {
        "dataset": "RHD-10 rank-one finite repair traces",
        "generator": "research.rh_proof_distillation.rhd10_rank_one_repair",
        "sha256": h.hexdigest(),
        "examples": sum(counts.values()),
        "counts": counts,
        "oracle_budget_success": budgets,
        "faults_by_length": faults_by_length,
        "all_gold_repaired": True,
        "all_learned_model_scores": None,
        "proof_term_data": False,
        "upstream_source_commit": "f150e02623b1e2bbe1f1da8eab5ffee5e930a6a3",
    }
    path.with_suffix(".manifest.json").write_text(
        json.dumps(manifest, sort_keys=True, indent=2) + "\n"
    )
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(write_data(args.output), sort_keys=True))
