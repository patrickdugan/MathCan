"""RHD-15: asymmetric characters of the finite split norm-one torus.

The first-layer algebra is exact for Q(zeta20)/29 and Q(zeta24)/5.
A split E/F local unitary torus has two conjugate E-components:
the second is the inverse of the conjugate of the first.

This is a LOCAL finite-ring character construction. It does not establish
a global Hecke character, its continuity, IsAutRepU, or the original TyEll.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
import argparse
import hashlib
import json
from pathlib import Path

from research.rh_proof_distillation.rhd14_norm_one_collapse import (
    FAMILIES, conjugate_coordinates, conjugate_factor_indices,
)


def family_name(family):
    return family.label


def orbit(family, j: int) -> tuple[int, int]:
    mate = conjugate_factor_indices(family)[j]
    return tuple(sorted((j, mate)))


def real_orbits(family) -> tuple[tuple[int, int], ...]:
    return tuple(sorted(set(orbit(family, j) for j in range(4))))


def same_real_place(family, j: int, k: int) -> bool:
    return orbit(family, j) == orbit(family, k)


def residue_mul(f: tuple[int, int, int], x: tuple[int, int],
                y: tuple[int, int], p: int) -> tuple[int, int]:
    """Independent quadratic residue arithmetic for the K=Q(i) tags."""
    d, c, _ = f
    a, b = x
    v, w = y
    return ((a*v - d*b*w) % p, (a*w+b*v-c*b*w) % p)


def residue_pow(f: tuple[int, int, int], n: int, p: int) -> tuple[int, int]:
    z = (1, 0)
    alpha = (0, 1)
    while n:
        if n & 1:
            z = residue_mul(f, z, alpha, p)
        alpha = residue_mul(f, alpha, alpha, p)
        n >>= 1
    return z


def quadratic_subfield_tag(family, j: int) -> int:
    """zeta20^5 or zeta24^6 gives i in the shared quadratic subfield."""
    n = 5 if family.p == 29 else 6
    tag, remainder = residue_pow(family.factors[j], n, family.p)
    if remainder != 0 or (tag*tag+1) % family.p:
        raise AssertionError("quadratic subfield element is not scalar i")
    return tag


def oneK_apart_candidate(family, j: int) -> int:
    """Unique finite index with same Q(i) restriction but different E^+ place."""
    tag = quadratic_subfield_tag(family, j)
    matches = [
        k for k in range(4) if k != j
        and quadratic_subfield_tag(family, k) == tag
        and not same_real_place(family, j, k)
    ]
    if len(matches) != 1:
        raise AssertionError("missing transverse OneK/Apart finite witness")
    return matches[0]


def pair_witness(family, j: int, a: int, b: int) -> dict:
    """First principal-unit layer of (u,bar(u)^-1) at a split F place."""
    p = family.p
    if j not in range(4) or a not in range(p) or b not in range(p):
        raise ValueError("invalid factor or first-layer coordinates")
    k = conjugate_factor_indices(family)[j]
    ca, cb = conjugate_coordinates(family, j, a, b, p)
    negative = ((-ca) % p, (-cb) % p)
    q = family.q
    source = q(family.principal_norm(family.factors[j], a, b))
    partner = q(family.principal_norm(family.factors[k], *negative))
    if (source + partner) % p:
        raise AssertionError("split norm-one condition failed")
    if source != family.trace(family.factors[j], a, b):
        raise AssertionError("selected local character failed trace identity")
    if partner != family.trace(family.factors[k], *negative):
        raise AssertionError("mate local character failed trace identity")
    return {
        "family": family_name(family), "p": p, "selected_factor": j,
        "conjugate_factor": k, "real_place_orbit": list(orbit(family, j)),
        "first_layer": [a, b], "partner_first_layer": list(negative),
        "selected_character": source, "partner_character": partner,
        "absolute_norm_pullback_exponent": (source + partner) % p,
        "same_real_place": same_real_place(family, j, k),
        "quadratic_subfield_tag": quadratic_subfield_tag(family, j),
        "same_K_different_F_factor": oneK_apart_candidate(family, j),
    }


def root_of_unity_controls(family) -> dict:
    """The local norm character kills every global cyclotomic root of unity."""
    n = 20 if family.p == 29 else 24
    m = family.p**2
    results = []
    for j, f in enumerate(family.factors):
        d = f[0] % m  # N(alpha)=d in the quadratic quotient
        values = [family.q(pow(d, k, m)) for k in range(n)]
        if any(values):
            raise AssertionError("cyclotomic torsion character is nontrivial")
        results.append({"factor": j, "order": n,
                        "norm_alpha_mod_p2": d,
                        "all_root_of_unity_character_exponents_zero": True})
    return {"family": family_name(family), "checks": results}


def check_nontrivial_character(family) -> None:
    a = (family.p + 1) // 2
    for j in range(4):
        if pair_witness(family, j, a, 0)["selected_character"] != 1:
            raise AssertionError("local torus character not surjective")


@dataclass(frozen=True)
class Candidate:
    conjugate_factor: int
    mate_sign: int
    character_mode: str
    local_coefficient: int
    exceptional_factors: tuple[int, ...]


def clean_candidate(family, j: int) -> Candidate:
    return Candidate(conjugate_factor_indices(family)[j], -1,
                     "asymmetric_torus", family.factors[j][1] % family.p, ())


def all_faults() -> tuple[str, ...]:
    return ("wrong_conjugate", "same_sign", "absolute_norm",
            "wrong_coefficient", "extra_exception")


def inject_fault(family, j: int, s: Candidate, fault: str) -> Candidate:
    if fault == "wrong_conjugate":
        other = min(k for k in range(4) if not same_real_place(family, j, k))
        return replace(s, conjugate_factor=other)
    if fault == "same_sign":
        return replace(s, mate_sign=1)
    if fault == "absolute_norm":
        return replace(s, character_mode="absolute_norm")
    if fault == "wrong_coefficient":
        return replace(s, local_coefficient=(s.local_coefficient + 1) % family.p)
    if fault == "extra_exception":
        other = min(k for k in range(4) if not same_real_place(family, j, k))
        return replace(s, exceptional_factors=(other,))
    raise ValueError("unrecognized mutation")


def verify(family, j: int, s: Candidate) -> list[dict]:
    """A full finite verifier for a deliberately restricted repair grammar."""
    errors = []
    expected_mate = conjugate_factor_indices(family)[j]
    if s.conjugate_factor != expected_mate:
        errors.append({"gate": "wrong_conjugate_real_place",
                       "observed": s.conjugate_factor, "selected_factor": j})
    if s.mate_sign != -1:
        errors.append({"gate": "norm_one_inverse_sign",
                       "observed": s.mate_sign, "selected_factor": j})
    if s.character_mode != "asymmetric_torus":
        errors.append({"gate": "trivial_absolute_norm_character",
                       "observed": s.character_mode,
                       "nontriviality_probe": [(family.p+1)//2, 0]})
    truth = family.factors[j][1] % family.p
    if s.local_coefficient != truth:
        # At a=0,b=1 theta=-c mod p, a complete coefficient check.
        errors.append({"gate": "local_trace_mismatch",
                       "observed": (-s.local_coefficient) % family.p,
                       "probe": [0, 1]})
    if s.exceptional_factors:
        # In this candidate the other F-place is unramified, while the mate
        # of selected E-place is excluded by the source Apart condition.
        errors.append({"gate": "ramified_prime_in_GenTy_S",
                       "observed": list(s.exceptional_factors)})
    return errors


def suggested_action(family, j: int, failure: dict) -> dict:
    gate = failure["gate"]
    if gate == "wrong_conjugate_real_place":
        return {"kind": "set_conjugate", "value": conjugate_factor_indices(family)[j]}
    if gate == "norm_one_inverse_sign":
        return {"kind": "set_mate_sign", "value": -1}
    if gate == "trivial_absolute_norm_character":
        return {"kind": "set_mode", "value": "asymmetric_torus"}
    if gate == "local_trace_mismatch":
        return {"kind": "set_local_coefficient",
                "value": family.factors[j][1] % family.p}
    if gate == "ramified_prime_in_GenTy_S":
        return {"kind": "clear_exceptions"}
    raise ValueError("unknown verifier gate")


def apply_action(s: Candidate, action: dict) -> Candidate:
    kind = action["kind"]
    if kind == "set_conjugate":
        return replace(s, conjugate_factor=action["value"])
    if kind == "set_mate_sign":
        return replace(s, mate_sign=action["value"])
    if kind == "set_mode":
        return replace(s, character_mode=action["value"])
    if kind == "set_local_coefficient":
        return replace(s, local_coefficient=action["value"])
    if kind == "clear_exceptions":
        return replace(s, exceptional_factors=())
    if kind == "STOP":
        return s
    raise ValueError("invalid action")


def snapshot(s: Candidate) -> dict:
    return {"conjugate_factor": s.conjugate_factor,
            "mate_sign": s.mate_sign, "character_mode": s.character_mode,
            "local_coefficient": s.local_coefficient,
            "exceptional_factors": list(s.exceptional_factors)}


def split_for(family, j: int, a: int, b: int) -> str:
    if family.p == 5:
        return "crossfamily_test"
    raw = hashlib.sha256(f"RHD15/split/{family.p}/{j}/{a}/{b}".encode()).digest()
    bucket = int.from_bytes(raw[:4], "big") % 10
    return "train" if bucket < 7 else "val" if bucket < 9 else "test"


def episodes():
    """Root-disjoint rollouts, with explicit clean STOP-only controls."""
    for family in FAMILIES:
        check_nontrivial_character(family)
        for j in range(4):
            for a in range(family.p):
                for b in range(family.p):
                    root = f"RHD15/{family.p}/{j}/{a}/{b}"
                    h = hashlib.sha256(root.encode()).digest()
                    count = h[0] % 4  # 0,1,2,3 independent faults
                    ranked = sorted(
                        all_faults(),
                        key=lambda f: hashlib.sha256(
                            (root+"/fault/"+f).encode()).digest(),
                    )
                    state = clean_candidate(family, j)
                    for fault in ranked[:count]:
                        state = inject_fault(family, j, state, fault)
                    failures = verify(family, j, state)
                    assert len(failures) == count, (root, count, failures)
                    initial = snapshot(state)
                    actions = []
                    for _ in range(count):
                        h0 = verify(family, j, state)
                        action = suggested_action(family, j, h0[0])
                        nxt = apply_action(state, action)
                        h1 = verify(family, j, nxt)
                        assert len(h1) == len(h0) - 1
                        actions.append({
                            "action": action,
                            "remaining_gates": len(h1),
                            "verifier_pass": len(h1) == 0,
                        })
                        state = nxt
                    assert state == clean_candidate(family, j)
                    actions.append({"action": {"kind":"STOP"}, "verifier_pass":True})
                    yield {
                        "task": "rhd15_split_torus_character_repair",
                        "root_id": root,
                        "split": split_for(family, j, a, b),
                        "field": family.label,
                        "p": family.p,
                        "finite_witness": pair_witness(family, j, a, b),
                        "candidate": initial,
                        "verifier_gates": failures,
                        "oracle_actions": actions,
                        "oracle_steps": count,
                        "oracle_terminal": snapshot(state),
                        "kernel_TyEll_proved": False,
                        "automorphic_character_proved": False,
                    }


def generate(path: Path) -> dict:
    path.parent.mkdir(parents=True, exist_ok=True)
    digest = hashlib.sha256()
    splits = {"train":0, "val":0, "test":0, "crossfamily_test":0}
    defects = {"0":0, "1":0, "2":0, "3":0}
    with path.open("wb") as f:
        for e in episodes():
            row = (json.dumps(e, sort_keys=True, separators=(",", ":"))+"\n").encode()
            f.write(row)
            digest.update(row)
            splits[e["split"]] += 1
            defects[str(e["oracle_steps"])] += 1
    return {
        "experiment":"RHD15 exact split unitary torus character first layer",
        "sha256": digest.hexdigest(),
        "episodes":sum(splits.values()),
        "splits":splits, "faults":defects,
        "root_of_unity_controls":[root_of_unity_controls(f) for f in FAMILIES],
        "crossfamily_training_examples":0,
        "trained_model_scores":None,
        "original_TyEll_proved":False,
        "global_Hecke_character_proved":False,
    }


def write_data(path: Path) -> dict:
    result=generate(path)
    manifest=path.with_suffix(".manifest.json")
    manifest.write_text(json.dumps(result, sort_keys=True, indent=2)+"\n")
    return result


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    print(json.dumps(write_data(args.output),sort_keys=True,indent=2))
