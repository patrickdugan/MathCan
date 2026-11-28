"""Static theorem-statement audit of the pinned BSA-R Step7 Lean source.

Checks the surface claims and assumptions; compilation and mathematical validity
of proofs need separate Lean kernel verification.
"""

import argparse
import hashlib
import json
import re
from pathlib import Path

UPSTREAM_REPO = "VivienSweetbrier/bsa-r"
UPSTREAM_COMMIT = "80c62433b0eb671175bd8d6169822d3ebd922b60"
UPSTREAM_PATH = "lean/Step7VorticityDirectionPdeRound6.lean"

# Roles are an independent audit classification of theorem *statements*.
TARGETS = {
    "step7_polar_palinstrophy_lagrange_splitting": (
        "integer vector/Jacobian polynomial identity",
        "Need field-valued derivatives and a justified global integration step."),
    "step7_zero_gap_bony_paraproduct_uv_gate": (
        "conditional integer inequality for T_LL, T_lin, T_HH and gate bounds",
        "Need uniform PDE estimates establishing the gate hypotheses for every solution."),
    "step7_holder_half_cone_biot_savart_bound": (
        "integer determinant bound conditional on a chord/coherence inequality",
        "Need a spatial singular-integral estimate and a priori cone coherence."),
    "step7_holder_half_quadratic_d3_to_d2_reduction": (
        "integer completion-of-square inequality on free scalar variables",
        "Need the PDE energy inequality identifying all algebraic scalars with norms."),
    "step7_leray_quadratic_doubling_closure": (
        "finite inductive bound conditioned on LerayDoublingChain",
        "Need a PDE-derived chain plus a bound on K uniform toward possible blow-up."),
}


def theorem_signature(source: str, name: str) -> str | None:
    match = re.search(r"(?m)^theorem\s+" + re.escape(name) + r"\b", source)
    if match is None:
        return None
    stop = source.find(":= by", match.end())
    if stop < 0 or stop - match.start() > 25000:
        return None
    return " ".join(source[match.start():stop].split())


def assess_source(source: str) -> dict:
    results = []
    for name, (role, missing) in TARGETS.items():
        signature = theorem_signature(source, name)
        results.append({
            "name": name,
            "found": signature is not None,
            "uses_integer_parameters": bool(signature and ": Int" in signature),
            "declares_real_or_pde_objects": bool(signature and re.search(
                r"(?<![A-Za-z])Real\b|ℝ|∫|Measure|NavierStokes|SmoothMap", signature)),
            "premise_names": re.findall(r"\(\s*(h[a-zA-Z0-9_]+)\s*:", signature or ""),
            "statement": signature,
            "statement_role": role,
            "missing_bridge": missing,
        })
    return {
        "repository": UPSTREAM_REPO,
        "commit": UPSTREAM_COMMIT,
        "path": UPSTREAM_PATH,
        "source_sha256": hashlib.sha256(source.encode("utf-8")).hexdigest(),
        "scope": "Static signatures of five Step7 declarations; not a kernel proof check",
        "all_found": all(r["found"] for r in results),
        "theorems": results,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True,
                        help="BSA-R Step7 Lean file checked out at pinned commit")
    parser.add_argument("--output", type=Path, help="Optional JSON output file")
    args = parser.parse_args(argv)
    report = assess_source(args.source.read_text(encoding="utf-8"))
    rendered = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")
    return 0 if report["all_found"] else 2


if __name__ == "__main__":
    raise SystemExit(main())
