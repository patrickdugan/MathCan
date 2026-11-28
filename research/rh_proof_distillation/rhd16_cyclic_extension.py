"""RHD-16: exact cyclic finite character extension and recurrent repair.

Finite toy G = Z/p^2, H = pG. The local character on H sends
p*t to a primitive p-th root to exponent t. A character of G valued
in mu_p cannot extend it; a mu_(p^2)-valued character does.

This is an exact algebraic extension gate, NOT the existence theorem
for the adelic quotient of a norm-one torus or a trained RLT model.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
import hashlib
import json
from math import gcd
from pathlib import Path

PRIMES = (29, 5)
TORSION_ORDERS = {29: 20, 5: 24}
FAULTS = ("wrong_order", "wrong_generator_exponent", "root_unit_twist")


def local_exponent(p: int, e: int, global_order: int) -> int:
    """Restrict an ambient cyclic character to H=pG, expressed in mu_p."""
    if p not in PRIMES:
        raise ValueError("unregistered prime")
    if global_order == p:
        return 0
    if global_order == p * p:
        return e % p
    raise ValueError("unexpected character root order")


def valid_generator_exponents(p: int, target: int) -> list[int]:
    if p not in PRIMES or target not in range(p):
        raise ValueError("invalid character target")
    return [e for e in range(p*p) if (p*e) % (p*p) == p*target]


def exact_extension_certificate(p: int) -> dict:
    n = TORSION_ORDERS[p]
    if gcd(p, n) != 1:
        raise AssertionError("cyclotomic root order must be coprime to p")
    for t in range(p):
        lifts = valid_generator_exponents(p, t)
        if len(lifts) != p or any(e % p != t for e in lifts):
            raise AssertionError("extension classification changed")
        if t != 0:
            if any(local_exponent(p, e, p) == t for e in range(p)):
                raise AssertionError("mu_p-valued extension unexpectedly exists")
            if any(gcd(e, p) != 1 for e in lifts):
                raise AssertionError("nontrivial extension lacks exact p^2 order")
    for a in range(p):
        if (n*a) % p == 0 and a:
            raise AssertionError("nontrivial p-power twist on global roots of unity")
    return {
        "prime": p,
        "ambient_cyclic_order": p*p,
        "local_subgroup_order": p,
        "root_of_unity_order": n,
        "valid_mu_p2_extensions_for_local_exponent_1": p,
        "valid_mu_p_extensions_for_local_exponent_1": 0,
        "all_nontrivial_local_targets_need_mu_p2": True,
        "cyclotomic_root_twists_forced_zero": True,
    }


@dataclass(frozen=True)
class Candidate:
    p: int
    target: int
    output_order: int
    generator_exponent: int
    root_twist: int


def clean(p: int, target: int) -> Candidate:
    if p not in PRIMES or target not in range(1, p):
        raise ValueError("registered nontrivial target required")
    return Candidate(p, target, p*p, target, 0)


def inject(s: Candidate, fault: str) -> Candidate:
    if fault == "wrong_order":
        return replace(s, output_order=s.p)
    if fault == "wrong_generator_exponent":
        return replace(s, generator_exponent=s.target+1)
    if fault == "root_unit_twist":
        return replace(s, root_twist=1)
    raise ValueError(f"unknown fault {fault}")


def verify(s: Candidate) -> list[dict]:
    if s.p not in PRIMES or s.target not in range(1, s.p):
        raise ValueError("invalid target")
    if s.output_order not in (s.p, s.p*s.p):
        raise ValueError("invalid global character root order")
    if s.generator_exponent not in range(s.p*s.p):
        raise ValueError("invalid ambient exponent")
    if s.root_twist not in range(s.p):
        raise ValueError("invalid root twist")
    failures = []
    if s.output_order == s.p:
        failures.append({
            "gate": "codomain_order_inflation",
            "source_order": s.p, "required_order": s.p*s.p,
            "local_target": s.target,
        })
    # This congruence class must hold independently of the output-order gate.
    if s.generator_exponent % s.p != s.target:
        failures.append({
            "gate": "local_restriction_congruence",
            "observed_residue": s.generator_exponent % s.p,
            "local_target": s.target,
        })
    if (TORSION_ORDERS[s.p]*s.root_twist) % s.p:
        failures.append({
            "gate": "global_root_unit_compatibility",
            "root_order": TORSION_ORDERS[s.p],
            "observed_twist": s.root_twist,
        })
    if not failures and local_exponent(s.p, s.generator_exponent, s.output_order) != s.target:
        raise AssertionError("verifier missed a character restriction violation")
    return failures


def action_for(s: Candidate, failure: dict) -> dict:
    gate = failure["gate"]
    if gate == "codomain_order_inflation":
        return {"kind": "set_output_order", "value": s.p*s.p}
    if gate == "local_restriction_congruence":
        return {"kind": "set_generator_exponent", "value": s.target}
    if gate == "global_root_unit_compatibility":
        return {"kind": "set_root_twist", "value": 0}
    raise ValueError("unsupported gate")


def apply_action(s: Candidate, action: dict) -> Candidate:
    kind, value = action["kind"], action.get("value")
    if kind == "set_output_order" and value in (s.p, s.p*s.p):
        return replace(s, output_order=value)
    if kind == "set_generator_exponent" and value in range(s.p*s.p):
        return replace(s, generator_exponent=value)
    if kind == "set_root_twist" and value in range(s.p):
        return replace(s, root_twist=value)
    if kind == "STOP":
        return s
    raise ValueError("invalid repair action")


def snapshot(s: Candidate) -> dict:
    return {
        "p": s.p, "local_target": s.target,
        "output_order": s.output_order,
        "generator_exponent": s.generator_exponent,
        "root_twist": s.root_twist,
    }


def split_for(p: int, e: int) -> str:
    if p == 5:
        return "cross_prime_test"
    bucket = int.from_bytes(
        hashlib.sha256(f"RHD16/split/{p}/{e}".encode()).digest()[:4],
        "big",
    ) % 10
    return "train" if bucket < 7 else "validation" if bucket < 9 else "test"


def episodes():
    for p in PRIMES:
        for e in range(p*p):
            seed = hashlib.sha256(f"RHD16/{p}/{e}".encode()).digest()
            target = 1 + seed[0] % (p-1)
            count = seed[1] % 4
            ranking = sorted(FAULTS, key=lambda fault: hashlib.sha256(
                f"RHD16/{p}/{e}/{fault}".encode()).digest())
            state = clean(p, target)
            for fault in ranking[:count]:
                state = inject(state, fault)
            start = snapshot(state)
            feedback = verify(state)
            assert len(feedback) == count
            trace = []
            while feedback:
                action = action_for(state, feedback[0])
                state = apply_action(state, action)
                next_feedback = verify(state)
                assert len(next_feedback) == len(feedback) - 1
                trace.append({
                    "action": action,
                    "remaining_violations": len(next_feedback),
                    "verified": not next_feedback,
                })
                feedback = next_feedback
            assert state == clean(p, target)
            trace.append({"action": {"kind": "STOP"}, "verified": True})
            yield {
                "task": "rhd16_cyclic_character_extension_repair",
                "root_id": f"RHD16/{p}/{e}",
                "split": split_for(p, e),
                "prime": p,
                "root_unit_order": TORSION_ORDERS[p],
                "local_target": target,
                "candidate": start,
                "verifier_failures": verify(Candidate(
                    p, target, start["output_order"],
                    start["generator_exponent"], start["root_twist"])),
                "oracle_actions": trace,
                "oracle_steps": count,
                "oracle_terminal": snapshot(state),
                "actual_adelic_character_proved": False,
                "original_TyEll_proved": False,
            }


def write_data(output: Path) -> dict:
    output.parent.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256()
    counts = dict(train=0, validation=0, test=0, cross_prime_test=0)
    faults = {"0": 0, "1": 0, "2": 0, "3": 0}
    with output.open("wb") as out:
        for row in episodes():
            content = (json.dumps(row, sort_keys=True, separators=(",", ":"))+"\n").encode()
            out.write(content)
            digest.update(content)
            counts[row["split"]] += 1
            faults[str(row["oracle_steps"])] += 1
    manifest = {
        "experiment": "RHD-16 cyclic character order inflation",
        "episodes": sum(counts.values()),
        "splits": counts,
        "fault_lengths": faults,
        "jsonl_sha256": digest.hexdigest(),
        "finite_extension_certificates": [
            exact_extension_certificate(p) for p in PRIMES
        ],
        "trained_neural_scores": None,
        "global_character_proved": False,
        "original_TyEll_proved": False,
    }
    output.with_suffix(".manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True)+"\n"
    )
    return manifest


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(write_data(args.output), indent=2, sort_keys=True))
