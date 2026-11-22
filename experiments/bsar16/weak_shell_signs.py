"""BSAR-16H: a.e.-time shell sign certificates for Leray--Hopf solutions.

Mathematical premise, proved in BSAR16H_LERAY_HOPF_RELATIVE_ENERGY.md:
The standard Leray--Hopf weak formulation and global energy inequality
give a relative-energy inequality against the smooth but residual-forced
finite Galerkin field. Its comparison bound is the same BSAR-16B rational
L2 estimate used by BSAR-16G. The finite-shell transfer can be defined
on divergence-free L2 fields by shifting the derivative onto its finite
projector, so the 36 BSAR-16G signs hold for a.e. time for *every*
Leray--Hopf weak solution of the registered initial datum.

This Python module reaudits exact-rational consequences of that analytic
argument, including source identity and algebraic signs. It is NOT a Lean
formalization of the infinite-dimensional weak PDE proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

from experiments.bsar16.conditional_nse_shells import generate as source_generate
from experiments.bsar16.exact_residual import (
    GRID_SIZES,
    ROOTS,
    SOURCE_BSAR14_BLOB,
    SOURCE_MATHCAN,
    Q,
    VISCOSITY,
    Field,
    encode,
    exact_decomposition,
    ksq,
    pair_real,
    source_modes,
    validate_field,
    zero_vec,
)
from experiments.bsar16.rational_enclosure import (
    add_field,
    laplacian_field,
    projected_product,
    scale_field,
)
from experiments.bsar16.shell_signs import SHELLS

SOURCE_BSAR16G_ROWS_SHA256 = (
    "6eb0137156069d8fb969134acf313df53ea5938fd6c815c53063eb208ba820bf"
)
HORIZON = Q(3, 250)
MEASURABLE_TIME_SCOPE = "almost every t in [0,3/250] for a Leray-Hopf representative"


def pairing(left: Field, right: Field) -> Q:
    """Real Fourier L2 pairing, including every mode in the left support."""
    return sum(
        (pair_real(u, right.get(k, zero_vec())) for k, u in left.items()),
        Q(0),
    )


def gradient_squared(field: Field) -> Q:
    return sum((ksq(k) * sum(x.squared_modulus() for x in u)
                for k, u in field.items()), Q(0))


def exact_residual_sign_audit(n: int = 2, phase: int = 1, grid: int = 16) -> dict[str, str]:
    """Exact finite-Fourier audit of the relative-energy forcing SIGN.

    Use the original finite Galerkin source and a nonzero high-mode rational
    perturbation, then compare the formal NSE/Galerkin vector fields. This
    checks the sign of the omitted high-mode forcing and nonlinear transport
    cancellation. The infinite-dimensional weak-inequality passage is
    handled in the analytic note, not by this finite arithmetic test.
    """
    if (n, phase) not in ROOTS or grid not in GRID_SIZES:
        raise ValueError("unregistered source")
    kmax = (grid - 1) // 3
    v = source_modes(n, phase)
    decomposition = exact_decomposition(v, kmax, VISCOSITY)
    r = decomposition["high_residual"]
    if not r:
        raise ValueError("choose root with genuine positive high forcing")
    w = scale_field(r, Q(1, 11))
    u = add_field(v, w)
    validate_field(u)
    validate_field(w)

    # Galerkin v_t = -nu*(-Delta)v - P_<=K P B(v,v).
    # Full approximate residual r = P_>K P B(v,v), with v_t+nu A v+B(v,v)=r.
    gal_rhs = add_field(
        laplacian_field(v, VISCOSITY),
        scale_field(decomposition["low_projected"], -1),
    )
    full_rhs = add_field(
        laplacian_field(u, VISCOSITY),
        scale_field(projected_product(u, u), -1),
    )
    w_t = add_field(full_rhs, scale_field(gal_rhs, -1))
    transport = pairing(w, projected_product(u, w))
    b_w_v = pairing(w, projected_product(w, v))
    source_work = pairing(w, r)
    assert transport == 0, "periodic transport energy cancellation failed"
    assert source_work > 0, "constructed high-mode sign witness vanished"

    # <w,w_t> + nu||grad w||² = -<w,B(w,v)> - <w,r>.
    lhs = pairing(w, w_t) + VISCOSITY * gradient_squared(w)
    rhs = -b_w_v - source_work
    if lhs != rhs:
        raise ArithmeticError("relative-energy residual sign or factor mismatch")

    # For the full finite shell, periodic integration by parts gives
    # T_s(u)=-<Q_s u,B(u,u)> = <u,B(u,Q_s u)>.
    transfer_receipts: dict[str, str] = {}
    nonlinear = projected_product(u, u)
    for shell in SHELLS:
        q_u = {k: velocity for k, velocity in u.items()
               if ksq(k) == shell*n*n}
        direct = -pairing(q_u, nonlinear)
        derivative_shifted = pairing(u, projected_product(u, q_u))
        if direct != derivative_shifted:
            raise ArithmeticError("finite-shell trilinear sign convention changed")
        transfer_receipts[str(shell)] = encode(direct)

    return {
        "frequency_N": str(n),
        "phase_sigma": str(phase),
        "grid_M": str(grid),
        "relative_energy_left": encode(lhs),
        "relative_energy_right": encode(rhs),
        "high_mode_work": encode(source_work),
        "transport_cancellation": encode(transport),
        "residual_sign": "error equation forcing is -r_K",
        "shell_transfers": transfer_receipts,
    }


def generate() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    source_rows, source_manifest = source_generate()
    if source_manifest["rows_sha256"] != SOURCE_BSAR16G_ROWS_SHA256:
        raise ValueError("BSAR-16G input rational archive hash changed")
    if source_manifest["case_count"] != 12:
        raise ValueError("BSAR-16G root count changed")
    if source_manifest["conditional_shell_certificates"] != 36:
        raise ValueError("BSAR-16G shell certificate count changed")
    if source_manifest["source_bsar14_blob"] != SOURCE_BSAR14_BLOB:
        raise ValueError("BSAR-14 source blob changed")
    if source_manifest["source_exact_mathcan"] != SOURCE_MATHCAN:
        raise ValueError("BSAR-14 source commit changed")
    if source_manifest["registered_horizon"] != encode(HORIZON):
        raise ValueError("BSAR-16G horizon changed")

    algebra = exact_residual_sign_audit()
    if Q(algebra["high_mode_work"]) <= 0:
        raise ArithmeticError("source residual forcing witness vanished")

    records: list[dict[str, Any]] = []
    for source in source_rows:
        n, phase, grid = (
            source["frequency_N"], source["phase_sigma"], source["grid_M"]
        )
        if (n, phase) not in ROOTS or grid not in GRID_SIZES:
            raise ValueError("unexpected source/grid")
        if source["time_horizon"] != encode(HORIZON):
            raise ValueError("root horizon mismatch")
        shells = []
        for entry in source["shells"]:
            if not entry["conditional_smooth_nse_existence_required"]:
                raise ValueError("BSAR-16G precondition custody lost")
            if not entry["full_T_conditional_sign_certified"]:
                raise ArithmeticError("input source lacks full-window sign")
            if entry["certified_duration_if_smooth"] != encode(HORIZON):
                raise ArithmeticError("source sign duration changed")
            if Q(entry["conditional_full_NSE_signed_transfer_lower"]) <= 0:
                raise ArithmeticError("nonpositive source sign bound")
            expected = {
                1: Q(phase*n, 4), 4: -Q(phase*n), 5: Q(3*phase*n, 4),
            }
            shell = entry["shell_normalized"]
            if shell not in SHELLS or Q(entry["original_signed_transfer"]) != expected[shell]:
                raise ValueError("BSAR-14 exact shell source mismatch")
            shells.append({
                "shell_normalized": shell,
                "original_signed_transfer": entry["original_signed_transfer"],
                "certified_ae_duration": encode(HORIZON),
                "leray_hopf_ae_signed_transfer_lower":
                    entry["conditional_full_NSE_signed_transfer_lower"],
                "weak_solution_L2_to_reference_upper":
                    entry["full_NSE_to_rational_reference_L2_upper"],
                "transfer_perturbation_upper":
                    entry["finite_shell_transfer_error_upper"],
                "signed_reference_lower":
                    entry["reference_signed_transfer_lower"],
                "time_quantifier": MEASURABLE_TIME_SCOPE,
                "source_strong_hypothesis_discharge":
                    "Leray-Hopf relative-energy comparison with smooth residual-forced v_K",
            })
        if set(s["shell_normalized"] for s in shells) != set(SHELLS):
            raise ValueError("missing or repeated shell")
        records.append({
            "frequency_N": n,
            "phase_sigma": phase,
            "grid_M": grid,
            "retained_cutoff_K": source["retained_cutoff_K"],
            "time_horizon": encode(HORIZON),
            "source_shells": shells,
            "valid_for": "every periodic mean-zero Leray-Hopf solution of this initial datum",
            "valid_times": MEASURABLE_TIME_SCOPE,
            "full_smooth_nse_existence_premise": False,
            "requires_leray_hopf_weak_form_and_energy_inequality": True,
            "does_not_certify": "global smoothness or full NSE vorticity-core geometry",
        })

    if len(records) != len(ROOTS)*len(GRID_SIZES):
        raise ArithmeticError("wrong number of weak shell roots")
    data = json.dumps(records, sort_keys=True, separators=(",", ":")).encode()
    manifest = {
        "experiment": "BSAR-16H Leray-Hopf a.e. shell-transfer sign certificates",
        "cases": len(records),
        "a.e._shell_certificates": sum(len(x["source_shells"]) for x in records),
        "registered_horizon": encode(HORIZON),
        "source_bsar14_blob": SOURCE_BSAR14_BLOB,
        "source_exact_mathcan": SOURCE_MATHCAN,
        "source_bsar16g_rows_sha256": SOURCE_BSAR16G_ROWS_SHA256,
        "relative_energy_algebra": algebra,
        "weak_solution_class": "global Leray-Hopf, periodic mean-zero solenoidal",
        "time_scope": MEASURABLE_TIME_SCOPE,
        "smooth_nse_lifespan_premise": False,
        "mathematical_proof_scope":
            "written relative-energy argument plus Python exact-rational re-audit; not Lean",
        "exclusion": "no 3D strong global regularity, uniqueness or pointwise full-NSE core proof",
        "rows_sha256": hashlib.sha256(data).hexdigest(),
    }
    return records, manifest


def freeze(path: Path) -> dict[str, Any]:
    records, manifest = generate()
    path.mkdir(parents=True, exist_ok=True)
    (path/"rows.json").write_bytes(
        json.dumps(records, sort_keys=True, separators=(",", ":")).encode()
    )
    (path/"manifest.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True)+"\n", encoding="utf-8"
    )
    return manifest


def audit(path: Path) -> dict[str, Any]:
    expected_rows, expected_manifest = generate()
    actual_rows = json.loads((path/"rows.json").read_text(encoding="utf-8"))
    actual_manifest = json.loads((path/"manifest.json").read_text(encoding="utf-8"))
    if actual_rows != expected_rows or actual_manifest != expected_manifest:
        raise ValueError("BSAR-16H weak solution rational evidence changed")
    return expected_manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("generate", "audit"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(
        freeze(args.out) if args.action == "generate" else audit(args.out),
        sort_keys=True, indent=2,
    ))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
