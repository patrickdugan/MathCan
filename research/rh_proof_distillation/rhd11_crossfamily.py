"""RHD-11: independently verified Q(zeta_24), p=5 transfer challenge.

This is an exact finite-field / finite-ring *shadow* of local norm characters,
not a Lean proof or a constructed automorphic eigenspace. No Q(zeta_24)
examples enter the behavioral clone's training set.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass, replace
import hashlib
import json
from math import gcd
from pathlib import Path

from research.rh_proof_distillation.rhd10_rank_one_repair import (
    episodes as source_episodes,
)
from research.rh_proof_distillation.rhd10_policy_eval import FrequencyPolicy

P = 5
P2 = 25
PHI24 = (1, 0, 0, 0, -1, 0, 0, 0, 1)
BASE_FACTORS = ((2, 1, 1), (3, 2, 1), (3, -2, 1), (2, -1, 1))
EXPECTED_LIFTS = ((7, 11, 1), (18, 2, 1), (18, 23, 1), (7, 14, 1))
ALL_PLACES = frozenset(range(4))


def poly_mul(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return tuple(out)


def poly_product(factors: tuple[tuple[int, ...], ...]) -> tuple[int, ...]:
    out = (1,)
    for f in factors:
        out = poly_mul(out, f)
    return out


def solve_modp(matrix: list[list[int]], rhs: list[int]) -> tuple[int, ...]:
    n = len(rhs)
    rows = [[x % P for x in matrix[i]] + [rhs[i] % P] for i in range(n)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if rows[i][j] != 0), None)
        if pivot is None:
            raise ArithmeticError("noninvertible Hensel lifting matrix")
        rows[j], rows[pivot] = rows[pivot], rows[j]
        inverse = pow(rows[j][j], -1, P)
        rows[j] = [(x * inverse) % P for x in rows[j]]
        for i in range(n):
            if i != j:
                scalar = rows[i][j]
                rows[i] = [(x - scalar*y) % P
                           for x, y in zip(rows[i], rows[j])]
    return tuple(row[-1] for row in rows)


def hensel_factors() -> tuple[tuple[int, int, int], ...]:
    base = poly_product(BASE_FACTORS)
    if any((a-b) % P != 0 for a, b in zip(base, PHI24)):
        raise ArithmeticError("incorrect factorization modulo 5")
    target = [((PHI24[i]-base[i])//P) % P for i in range(8)]
    basis = []
    for j in range(4):
        complement = poly_product(BASE_FACTORS[:j] + BASE_FACTORS[j+1:])
        basis.extend((complement + (0,), (0,) + complement))
    matrix = [[basis[col][i] for col in range(8)] for i in range(8)]
    adjustments = solve_modp(matrix, target)
    result = tuple(
        ((factor[0] + P*adjustments[2*j]) % P2,
         (factor[1] + P*adjustments[2*j+1]) % P2,
         1)
        for j, factor in enumerate(BASE_FACTORS)
    )
    if result != EXPECTED_LIFTS:
        raise ArithmeticError("unexpected factor lifts")
    if any((a-b) % P2 for a, b in zip(poly_product(result), PHI24)):
        raise ArithmeticError("incorrect factorization modulo 25")
    for f in result:
        discriminant = (f[1]*f[1] - 4*f[0]) % P
        if pow(discriminant, (P-1)//2, P) != P-1:
            raise ArithmeticError("factor residue is reducible")
    return result


FACTORS = hensel_factors()
TRUE_COEFFS = tuple(f[1] % P for f in FACTORS)
HALF = (P + 1) // 2  # theta(half,0)=1


def local_norm(f: tuple[int, int, int], a: int, b: int) -> int:
    return (a*a - f[1]*a*b + f[0]*b*b) % P2


def theta(f: tuple[int, int, int], a: int, b: int) -> int:
    return (2*a - f[1]*b) % P


def principal_norm(f: tuple[int, int, int], a: int, b: int) -> int:
    return local_norm(f, 1 + P*a, P*b)


def q(x: int) -> int:
    x %= P2
    if gcd(x, P) != 1:
        raise ValueError("character requires a unit")
    residue = pow(x, P-1, P2)
    if (residue - 1) % P:
        raise ArithmeticError("Fermat congruence failed")
    return (-((residue-1)//P)) % P


def exact_oracle_check() -> None:
    if poly_product(FACTORS) != PHI24:
        # Integer equality need not hold, but the congruence above must.
        if any((a-b) % P2 for a, b in zip(poly_product(FACTORS), PHI24)):
            raise ArithmeticError("bad factorization")
    for f in FACTORS:
        for a in range(P):
            for b in range(P):
                if q(principal_norm(f, a, b)) != theta(f, a, b):
                    raise ArithmeticError("first-layer norm/trace mismatch")
        if q(principal_norm(f, HALF, 0)) != 1:
            raise ArithmeticError("nontrivial ramification witness missing")
    if q(1+P) != 1 or q(-1) != 0:
        raise ArithmeticError("character generator/global-unit check failed")


def ring_mul(f: tuple[int, int, int], u: tuple[int, int],
             v: tuple[int, int]) -> tuple[int, int]:
    """Quadratic local-ring multiplication modulo 25."""
    a, b = u
    c, d = v
    return ((a*c - f[0]*b*d) % P2,
            (a*d + b*c - f[1]*b*d) % P2)


def ring_pow(f: tuple[int, int, int], u: tuple[int, int],
             exponent: int) -> tuple[int, int]:
    if exponent < 0:
        raise ValueError("negative exponent")
    out = (1, 0)
    while exponent:
        if exponent & 1:
            out = ring_mul(f, out, u)
        u = ring_mul(f, u, u)
        exponent >>= 1
    return out


def cyclotomic_unit(f: tuple[int, int, int], k: int) -> tuple[int, int]:
    """Local residue of the global algebraic unit 1-zeta_24^k."""
    a, b = ring_pow(f, (0, 1), k)
    return ((1-a) % P2, (-b) % P2)


def first_layer_log(f: tuple[int, int, int],
                    u: tuple[int, int]) -> tuple[int, int]:
    """Canonical F_5^2 logarithm: (1-u^24)/5 in the residue basis."""
    a, b = ring_pow(f, u, P*P-1)
    if a % P != 1 or b % P != 0:
        raise ValueError("not a local unit")
    return (((1-a)//P) % P, ((-b)//P) % P)


def unit_obstruction() -> dict:
    """Independent 1-zeta and 1-zeta^7 spanning witnesses at every p=5 place.

    Conditional global deduction: a finite-order character of exact order
    five, trivial at infinity and unramified away from one such p-adic
    place cannot be nontrivial at that place while killing both global
    units. This function only certifies the finite ring calculations.
    """
    unit_exponents = (1, 7)
    frozen_determinants = (2, 4, 1, 3)
    norms_product = [1, 1]
    q_sum = [0, 0]
    witnesses = []
    for j, f in enumerate(FACTORS):
        units = [cyclotomic_unit(f, k) for k in unit_exponents]
        logs = [first_layer_log(f, u) for u in units]
        det = (logs[0][0]*logs[1][1] -
               logs[0][1]*logs[1][0]) % P
        if det != frozen_determinants[j]:
            raise ArithmeticError("unexpected global-unit logarithm span")
        norms = [local_norm(f, *unit) for unit in units]
        if any(n % P == 0 for n in norms):
            raise ArithmeticError("global unit became a local nonunit")
        for k in range(2):
            norms_product[k] = norms_product[k]*norms[k] % P2
            q_sum[k] = (q_sum[k] + q(norms[k])) % P
        witnesses.append({
            "factor_index": j,
            "unit_log_vectors": [list(v) for v in logs],
            "determinant_mod_5": det,
            "local_norms": norms,
            "local_norm_character_exponents": [q(n) for n in norms],
        })
    if norms_product != [1, 1] or q_sum != [0, 0]:
        raise ArithmeticError("global unit product compatibility failed")
    return {
        "global_unit_exponents": list(unit_exponents),
        "determinants_mod_5": list(frozen_determinants),
        "global_norm_products_mod_25": norms_product,
        "character_exponent_sums_mod_5": q_sum,
        "places": witnesses,
        "scope": "exact finite first-layer arithmetic, not a Lean global proof",
    }


@dataclass(frozen=True)
class Candidate:
    selected_factor: int
    local_coeffs: tuple[int, int, int, int]
    global_sign: int
    conductor: int
    unit_offset: int
    exceptions: frozenset[int]


def clean(w0: int) -> Candidate:
    return Candidate(w0, TRUE_COEFFS, 1, P2, 0, ALL_PLACES-{w0})


def snapshot(c: Candidate) -> dict:
    return {
        "selected_factor": c.selected_factor,
        "local_coeffs": list(c.local_coeffs),
        "global_sign": c.global_sign,
        "conductor": c.conductor,
        "unit_offset": c.unit_offset,
        "exceptions": sorted(c.exceptions),
    }


def from_snapshot(v: dict) -> Candidate:
    return Candidate(
        v["selected_factor"], tuple(v["local_coeffs"]), v["global_sign"],
        v["conductor"], v["unit_offset"], frozenset(v["exceptions"]),
    )


def fault_catalog(w0: int) -> tuple[str, ...]:
    return (tuple(f"local:{j}" for j in range(4)) +
            ("global_sign", "conductor", "unit_offset") +
            tuple(f"exception:{j}" for j in range(4) if j != w0))


def inject(c: Candidate, fault: str, shift: int) -> Candidate:
    if fault.startswith("local:"):
        j = int(fault.split(":")[1])
        values = list(c.local_coeffs)
        values[j] = (values[j] + shift) % P
        return replace(c, local_coeffs=tuple(values))
    if fault == "global_sign":
        return replace(c, global_sign=-c.global_sign)
    if fault == "conductor":
        return replace(c, conductor=P)
    if fault == "unit_offset":
        return replace(c, unit_offset=shift % P or 1)
    if fault.startswith("exception:"):
        j = int(fault.split(":")[1])
        if j == c.selected_factor:
            raise ValueError("cannot exclude selected place")
        return replace(c, exceptions=c.exceptions-{j})
    raise ValueError(f"unknown fault {fault}")


def verify(c: Candidate) -> list[dict]:
    if c.selected_factor not in ALL_PLACES:
        raise ValueError("invalid selected place")
    errors: list[dict] = []
    for j, f in enumerate(FACTORS):
        observed = (-c.local_coeffs[j]) % P
        expected = theta(f, 0, 1)
        if observed != expected:
            errors.append({"gate": "local_character", "factor": j,
                           "probe": [0, 1], "observed": observed,
                           "expected": expected})
    global_norm = q(principal_norm(FACTORS[c.selected_factor], HALF, 0))
    if c.global_sign * global_norm % P != 1:
        errors.append({"gate": "global_norm_pullback",
                       "selected_place": c.selected_factor, "probe": [HALF, 0],
                       "observed": c.global_sign * global_norm % P,
                       "expected": 1})
    if c.conductor != P2:
        errors.append({"gate": "exact_conductor",
                       "observed": c.conductor, "expected": P2})
    if c.unit_offset % P:
        errors.append({"gate": "idele_unit_normalization",
                       "observed": c.unit_offset % P, "expected": 0})
    for j in sorted(ALL_PLACES - {c.selected_factor}):
        if j not in c.exceptions:
            errors.append({"gate": "missing_exception", "place": j,
                           "probe": [HALF, 0]})
    for j in sorted(c.exceptions - (ALL_PLACES - {c.selected_factor})):
        errors.append({"gate": "unexpected_exception", "place": j})
    return errors


def redact_failure(f: dict) -> dict:
    public_keys = ("gate", "factor", "place", "selected_place", "probe", "observed")
    return {key: f[key] for key in public_keys if key in f}


def apply(c: Candidate, action: dict) -> Candidate:
    kind = action.get("kind")
    if kind == "set_local_coefficient":
        j, v = action["factor"], action["value"]
        if j not in ALL_PLACES or v not in range(P):
            raise ValueError("coefficient outside new field")
        values = list(c.local_coeffs)
        values[j] = v
        return replace(c, local_coeffs=tuple(values))
    if kind == "set_global_sign":
        if action["value"] not in (-1, 1):
            raise ValueError("bad sign")
        return replace(c, global_sign=action["value"])
    if kind == "set_conductor":
        if action["value"] not in (P, P2):
            raise ValueError("conductor outside new field")
        return replace(c, conductor=action["value"])
    if kind == "set_unit_offset":
        if action["value"] not in range(P):
            raise ValueError("unit offset outside new field")
        return replace(c, unit_offset=action["value"])
    if kind in ("add_exception", "drop_exception"):
        j = action["place"]
        if j not in ALL_PLACES:
            raise ValueError("invalid place")
        return replace(
            c, exceptions=c.exceptions | {j} if kind == "add_exception"
            else c.exceptions - {j},
        )
    raise ValueError(f"unsupported action: {kind}")


def root_hash(w0: int, a: int, b: int) -> bytes:
    return hashlib.sha256(f"RHD11/Qz24/p5/{w0}/{a}/{b}".encode()).digest()


def episode(w0: int, a: int, b: int) -> dict:
    h = root_hash(w0, a, b)
    k = h[4] % 4  # Includes clean STOP-only episodes; RHD-10 had none.
    candidates = sorted(
        fault_catalog(w0),
        key=lambda fault: hashlib.sha256(
            f"RHD11/fault/{w0}/{a}/{b}/{fault}".encode()
        ).digest(),
    )
    c = clean(w0)
    for i, fault in enumerate(candidates[:k]):
        c = inject(c, fault, 1 + h[5+i] % (P-1))
    if len(verify(c)) != k:
        raise ArithmeticError("fault isolation failed")
    return {
        "task": "rhd11_crossfamily_local_norm_repair",
        "root_id": f"RHD11/Qz24/p5/{w0}/{a}/{b}",
        "split": "crossfield_test",
        "family": "Q(zeta_24)",
        "prime": P,
        "candidate": snapshot(c),
        "local_probe": {"a": a, "b": b, "selected_factor": w0,
                        "factor_mod_25": list(FACTORS[w0])},
        "injected_fault_count": k,
        "source_family_used_for_training": "Q(zeta_20), p=29",
        "lean_witness_proved": False,
        "automorphic_witness_proved": False,
    }


def episodes():
    for w0 in range(4):
        for a in range(P):
            for b in range(P):
                yield episode(w0, a, b)


def public_episode(row: dict) -> dict:
    """Only source arithmetic, candidate and root ID; no fault counts."""
    return {
        "root_id": row["root_id"],
        "family": row["family"],
        "prime": row["prime"],
        "factors_mod_prime_squared": [list(f) for f in FACTORS],
        "candidate": dict(row["candidate"]),
        "local_probe": dict(row["local_probe"]),
    }


def arithmetic_action(f: dict, public: dict) -> dict:
    """Explicit mathematical adaptation; an analytic comparator, not ML."""
    gate = f["gate"]
    if gate == "verified":
        return {"kind": "STOP"}
    if gate == "local_character":
        j = f["factor"]
        return {
            "kind": "set_local_coefficient", "factor": j,
            "value": public["factors_mod_prime_squared"][j][1] % public["prime"],
        }
    if gate == "global_norm_pullback":
        return {"kind": "set_global_sign", "value": 1}
    if gate == "exact_conductor":
        return {"kind": "set_conductor", "value": public["prime"]**2}
    if gate == "idele_unit_normalization":
        return {"kind": "set_unit_offset", "value": 0}
    if gate == "missing_exception":
        return {"kind": "add_exception", "place": f["place"]}
    if gate == "unexpected_exception":
        return {"kind": "drop_exception", "place": f["place"]}
    return {"kind": "STOP"}


def score_one(row: dict, policy: FrequencyPolicy | None,
              mode: str) -> dict:
    """External verifier handles all scoring; policy sees only redacted gates."""
    public = public_episode(row)
    state = from_snapshot(public["candidate"])
    calls = edits = invalid = rejected = premature_stop = 0

    def ask(full: bool) -> list[dict]:
        nonlocal calls
        calls += 1
        found = verify(state)
        return [redact_failure(x) for x in found if full] if full else (
            [redact_failure(found[0])] if found else []
        )

    def choose(failure: dict) -> dict:
        return policy.choose(failure) if policy is not None else arithmetic_action(failure, public)

    def edit(failure: dict) -> bool:
        nonlocal state, edits, invalid, rejected, premature_stop
        action = choose(failure)
        if action.get("kind") == "STOP":
            premature_stop += 1
            return False
        before = len(verify(state))
        edits += 1
        try:
            after_state = apply(state, action)
        except (ValueError, KeyError, TypeError):
            rejected += 1
            invalid += 1
            return True
        after = len(verify(after_state))
        invalid += int(after >= before)
        state = after_state
        return True

    if mode == "full_open_loop":
        observed = ask(True)
        for failure in observed[:3]:
            if not edit(failure):
                break
        final = ask(True) if observed else observed
    elif mode in ("sparse_one_step", "sparse_recurrent"):
        remaining = ask(False)
        budget = 1 if mode == "sparse_one_step" else 3
        for _ in range(budget):
            if not remaining or not edit(remaining[0]):
                break
            remaining = ask(False)
        final = remaining
    else:
        raise ValueError(mode)
    passed = len(final) == 0
    stop = choose(final[0] if final else {"gate": "verified"})
    return {
        "solved": passed,
        "verifier_calls": calls,
        "edits": edits,
        "invalid_edits": invalid,
        "rejected_edits": rejected,
        "premature_stops": premature_stop,
        "stop_decision_correct": (stop.get("kind") == "STOP") == passed,
    }


def aggregate(rows: list[dict], policy: FrequencyPolicy | None,
              mode: str) -> dict:
    count = Counter()
    for row in rows:
        z = score_one(row, policy, mode)
        for key, value in z.items():
            count[key] += int(value)
    n = len(rows)
    return {
        "episodes": n,
        "fully_verified": count["solved"],
        "verifier_calls": count["verifier_calls"],
        "fully_verified_per_100_verifier_calls": round(
            100*count["solved"]/count["verifier_calls"], 6
        ) if count["verifier_calls"] else 0,
        "edits": count["edits"],
        "invalid_edits": count["invalid_edits"],
        "rejected_edits": count["rejected_edits"],
        "premature_stops": count["premature_stops"],
        "terminal_stop_or_continue_accuracy": round(
            count["stop_decision_correct"]/n, 6
        ) if n else 0,
    }


def report() -> dict:
    exact_oracle_check()
    roots = list(episodes())
    if len(roots) != 4 * P * P:
        raise AssertionError("missing roots")
    if len({row["root_id"] for row in roots}) != len(roots):
        raise AssertionError("root ID collision")
    # Fit only to the previously committed Q(zeta_20), p=29 archive.
    train = [row for row in source_episodes() if row["split"] == "train"]
    learned = FrequencyPolicy.fit(train)
    modes = ("sparse_one_step", "sparse_recurrent", "full_open_loop")
    counts = Counter(row["injected_fault_count"] for row in roots)
    return {
        "experiment": "RHD-11 cross-family exact finite character transfer",
        "heldout_field": "Q(zeta_24)",
        "heldout_prime": P,
        "heldout_conductor": P2,
        "heldout_examples": len(roots),
        "fault_count_distribution": dict(sorted(counts.items())),
        "training_family": "Q(zeta_20), p=29",
        "training_roots": len(train),
        "trained_policy": "RHD-10 frequency table, frozen",
        "heldout_family_used_for_training": False,
        "factor_lifts_mod_25": [list(f) for f in FACTORS],
        "global_unit_obstruction": unit_obstruction(),
        "unseen_heldout_factors": True,
        "results": {
            policy_name: {
                mode: aggregate(roots, policy, mode) for mode in modes
            }
            for policy_name, policy in (
                ("zero_shot_source_frequency", learned),
                ("explicit_arithmetic_transfer", None),
            )
        },
        "interpretation": (
            "within-family trained lookup compared against exact hand-written "
            "finite arithmetic, not a trained neural RLT or Lean proof"
        ),
        "lean_witness_proved": False,
        "automorphic_witness_proved": False,
    }


def write(output: Path) -> dict:
    result = report()
    output.parent.mkdir(parents=True, exist_ok=True)
    with output.with_suffix(".jsonl").open("wb") as writer:
        for row in episodes():
            writer.write((json.dumps(row,sort_keys=True,separators=(",", ":"))+"\n").encode())
    output.write_bytes((json.dumps(result,sort_keys=True,indent=2)+"\n").encode())
    for path in (output,output.with_suffix(".jsonl")):
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        path.with_name(path.name+".sha256").write_text(
            digest+"  "+path.name+"\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    args = parser.parse_args()
    print(json.dumps(write(args.output),indent=2,sort_keys=True))
