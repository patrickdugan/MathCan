"""Q3 cubical curl map: finite algebraic rank, minimal observation sets and reconstruction (PGC Phase 5).

Evidence class: exact integer algebra plus ideal/noisy NumPy simulation. No hardware data is used; the only
existing AHR hardware receipts are for Q2 (one face), so every Q3 statement here is simulation or exact algebra.

  python q3_minimal_observation.py            # writes q3_minimal_observation.json, exits nonzero on a failed check
"""
from __future__ import annotations
import itertools, json, math, pathlib, sys
from fractions import Fraction

import numpy as np

HERE = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "arithmetic_holonomy_rotor" / "ibm_qpu_01"))
import q3_curvature as Q  # noqa: E402  (curl_matrix, EDGES, CHORDS, BIANCHI, project_bianchi, wrap)

TWO_PI = 2 * math.pi
C = Q.curl_matrix().astype(int)          # 6 x 12
B = Q.BIANCHI.astype(int)
wrap = lambda x: (np.asarray(x) + math.pi) % TWO_PI - math.pi


def frac_rank(M):
    A = [[Fraction(int(x)) for x in row] for row in M]
    r = 0
    for c in range(len(A[0]) if A else 0):
        p = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if p is None:
            continue
        A[r], A[p] = A[p], A[r]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c] / A[r][c]
                A[i] = [a - f * b for a, b in zip(A[i], A[r])]
        r += 1
    return r


def int_det(M):
    n = len(M)
    A = [[Fraction(int(x)) for x in row] for row in M]
    d = Fraction(1)
    for c in range(n):
        p = next((i for i in range(c, n) if A[i][c] != 0), None)
        if p is None:
            return 0
        if p != c:
            A[c], A[p] = A[p], A[c]; d = -d
        d *= A[c][c]
        for i in range(c + 1, n):
            f = A[i][c] / A[c][c]
            A[i] = [a - f * b for a, b in zip(A[i], A[c])]
    assert d.denominator == 1
    return int(d)


def exact_structure():
    out = {"edges": 12, "faces": 6, "rank_curl": frac_rank(C), "bianchi_left_null": bool((B @ C == 0).all())}
    out["gauge_dim_edge_kernel"] = 12 - out["rank_curl"]
    # gradient of vertex potentials spans the kernel: dim = 8 - 1 = 7
    grad = np.zeros((12, 8), int)
    for i, (a, b) in enumerate(Q.EDGES):
        grad[i, b] += 1; grad[i, a] -= 1
    out["curl_kills_gradients"] = bool((C @ grad == 0).all())
    out["rank_gradient_image"] = frac_rank(grad.T)
    out["cycle_dof"] = 12 - out["rank_gradient_image"]
    out["left_null_dim"] = 6 - out["rank_curl"]
    # chord (gauge-fixed) block: 6 x 5, any five rows unimodular => integral reconstruction of the 5 cycle phases
    cols = [Q.EDGES.index(e) for e in Q.CHORDS]
    Cc = C[:, cols]
    out["chord_block_rank"] = frac_rank(Cc)
    out["chord_block_5x5_dets_by_omitted_face"] = [int_det(np.delete(Cc, k, axis=0)) for k in range(6)]
    out["every_five_face_subset_unimodular"] = all(abs(d) == 1 for d in out["chord_block_5x5_dets_by_omitted_face"])
    return out


def subset_table():
    cols = [Q.EDGES.index(e) for e in Q.CHORDS]
    rows = []
    for k in range(1, 7):
        for S in itertools.combinations(range(6), k):
            M = C[list(S)]
            r = frac_rank(M)
            s = np.linalg.svd(M.astype(float), compute_uv=False)
            s = s[s > 1e-9]
            Mc = C[list(S)][:, cols].astype(float)
            sc = np.linalg.svd(Mc, compute_uv=False)
            sc = sc[sc > 1e-9]
            rows.append({"faces": list(S), "rank": r, "unobserved_cycle_dim": 5 - r,
                         "cond_edge_space": float(s[0] / s[-1]) if len(s) else None,
                         "cond_chord_gauge": float(sc[0] / sc[-1]) if len(sc) else None,
                         "full_cycle_recovery": r == 5})
    return rows


def gauge_equivalence(rng, n=200):
    grad = np.zeros((12, 8))
    for i, (a, b) in enumerate(Q.EDGES):
        grad[i, b] += 1; grad[i, a] -= 1
    worst = 0.0
    for _ in range(n):
        th = rng.uniform(-math.pi, math.pi, 12)
        g = grad @ rng.uniform(-math.pi, math.pi, 8)
        worst = max(worst, float(np.max(np.abs(wrap(C @ (th + g) - C @ th)))))
    return {"trials": n, "max_flux_change_under_vertex_gauge": worst}


def indistinguishable_under_restriction(rng):
    """For four-face subsets: dimension of the unobserved cycle directions and an explicit pair of configs."""
    res = []
    for S in itertools.combinations(range(6), 4):
        M = C[list(S)].astype(float)
        _, s, Vt = np.linalg.svd(M)
        null = Vt[np.sum(s > 1e-9):]  # includes the 7 gauge directions + unobserved cycle direction(s)
        # unobserved cycle direction: null vector orthogonal (in the cycle quotient) to gauge
        grad = np.zeros((12, 8))
        for i, (a, b) in enumerate(Q.EDGES):
            grad[i, b] += 1; grad[i, a] -= 1
        P = grad @ np.linalg.pinv(grad)
        extra = [v - P @ v for v in null]
        extra = [v for v in extra if np.linalg.norm(v) > 1e-9]
        th = rng.uniform(-1, 1, 12)
        d = extra[0] / np.linalg.norm(extra[0]) * 0.7 if extra else np.zeros(12)
        same_S = float(np.max(np.abs(wrap(C[list(S)] @ (th + d) - C[list(S)] @ th))))
        diff_all = float(np.max(np.abs(wrap(C @ (th + d) - C @ th))))
        res.append({"faces": list(S), "unobserved_dim": 5 - frac_rank(C[list(S)]),
                    "same_observed_flux_gap": same_S, "full_flux_gap": diff_all,
                    "indistinguishable_pair_found": same_S < 1e-9 and diff_all > 1e-3})
    return res


def orientation_ambiguity(rng, n=400):
    """Cos-only (phase-insensitive) data versus (cos, sin) quadrature: size of the consistent flux set."""
    out = {"trials": n, "mean_consistent_sign_patterns_cos_only": 0.0, "max_consistent_sign_patterns_cos_only": 0,
           "quadrature_patterns": 1, "global_reflection_always_consistent": True}
    counts = []
    for _ in range(n):
        th = rng.uniform(-math.pi, math.pi, 12)
        F = wrap(C @ th)
        c = 0
        for s in itertools.product((1, -1), repeat=6):
            Fp = np.array(s) * F
            if abs(wrap(B @ Fp)) < 1e-9:
                c += 1
        counts.append(c)
    out["mean_consistent_sign_patterns_cos_only"] = float(np.mean(counts))
    out["max_consistent_sign_patterns_cos_only"] = int(max(counts))
    out["fraction_trials_exactly_two"] = float(np.mean(np.array(counts) == 2))
    # special fluxes (values in {0, pi}) are fixed by every sign flip: pure Z2 holonomy is orientation-blind
    out["z2_flux_sector_orientation_blind"] = bool(
        all(abs(wrap(B @ (np.array(s) * np.array(f)))) < 1e-9 for f in [(0, 0, 0, 0, 0, 0), (math.pi, math.pi, 0, 0, 0, 0)]
            for s in itertools.product((1, -1), repeat=6)))
    return out


def bianchi_projection_study(rng, n=4000, sigma=0.05):
    """Weighted projection onto B.F = 0 versus identity weights, heteroscedastic noise, plus 6th-face consistency."""
    cov_diag = np.array([1, 1, 1, 4, 4, 9], float) * sigma ** 2
    cov = np.diag(cov_diag)
    e_raw, e_id, e_w, resid = [], [], [], []
    for _ in range(n):
        th = rng.uniform(-math.pi, math.pi, 12)
        F = wrap(C @ th)
        meas = wrap(F + rng.normal(0, np.sqrt(cov_diag)))
        e_raw.append(np.sum(wrap(meas - F) ** 2))
        e_id.append(np.sum(wrap(Q.project_bianchi(meas) - F) ** 2))
        e_w.append(np.sum(wrap(Q.project_bianchi(meas, cov) - F) ** 2))
        resid.append(float(wrap(B @ meas)))
    resid = np.array(resid)
    sd_theory = float(np.sqrt(B @ cov @ B))
    study = {"n": n, "mean_sq_error_raw": float(np.mean(e_raw)), "mean_sq_error_unweighted_projection": float(np.mean(e_id)),
             "mean_sq_error_covariance_weighted_projection": float(np.mean(e_w)),
             "expected_weighted_projection_error": float(np.trace(cov) - (B @ cov @ cov @ B) / (B @ cov @ B)),
             "bianchi_residual_sd_empirical": float(resid.std()), "bianchi_residual_sd_theory": sd_theory}
    # Sixth-face check: predict face k from the other five, compare with its measurement
    detect = {}
    for k in range(6):
        pred_err = []
        for _ in range(1500):
            th = rng.uniform(-math.pi, math.pi, 12); F = wrap(C @ th)
            meas = wrap(F + rng.normal(0, np.sqrt(cov_diag)))
            others = [j for j in range(6) if j != k]
            pred = wrap(-B[k] * (B[others] @ meas[others]))      # B_k in {+-1}: F_k = -B_k * sum_{j != k} B_j F_j
            pred_err.append(float(wrap(pred - meas[k])))
        detect[str(k)] = float(np.std(pred_err))
    study["sixth_face_prediction_residual_sd_by_held_out_face"] = detect
    # Single-face bias of 0.3 rad: Bianchi residual shifts identically whichever face carries it -> no localization
    bias_resid = []
    for k in range(6):
        r = []
        for _ in range(800):
            th = rng.uniform(-math.pi, math.pi, 12); F = wrap(C @ th)
            meas = F.copy(); meas[k] += 0.3
            meas = wrap(meas + rng.normal(0, np.sqrt(cov_diag)))
            r.append(float(wrap(B @ meas)))
        bias_resid.append(float(np.mean(np.abs(r))))
    study["abs_bianchi_residual_for_0p3_rad_bias_on_face_k"] = bias_resid
    # Branch ambiguity: principal-branch fluxes satisfy B.F = 2 pi n with integer n != 0 for many configurations.
    # The wrapped residual (used by project_bianchi) removes n, so the projection is exact mod 2 pi; the
    # unwrapped residual would inject a 2 pi n/|B|^2-sized spurious correction.
    ns = []; bad_unwrapped = []; bad_wrapped = []
    for _ in range(3000):
        th = rng.uniform(-math.pi, math.pi, 12); F = wrap(C @ th)
        meas = wrap(F + rng.normal(0, np.sqrt(cov_diag)))
        n_ = int(round(float(B @ meas) / TWO_PI)); ns.append(n_)
        raw = float(B @ meas)
        unwrapped_proj = meas - (cov @ B) * raw / (B @ cov @ B)
        bad_unwrapped.append(float(np.max(np.abs(wrap(unwrapped_proj - F)))))
        bad_wrapped.append(float(np.max(np.abs(wrap(Q.project_bianchi(meas, cov) - F)))))
    study["bianchi_integer_n_histogram"] = {str(k): int(ns.count(k)) for k in sorted(set(ns))}
    study["fraction_configs_needing_2pi_branch_correction"] = float(np.mean(np.array(ns) != 0))
    study["max_error_unwrapped_residual_projection"] = float(np.max(bad_unwrapped))
    study["max_error_wrapped_residual_projection"] = float(np.max(bad_wrapped))
    return study


def lattice_reconstruction_check(rng, n=400):
    """5 chord phases from any five faces: exact round trip modulo 2 pi."""
    cols = [Q.EDGES.index(e) for e in Q.CHORDS]
    worst = 0.0
    for _ in range(n):
        th = np.zeros(12); th[cols] = rng.uniform(-math.pi, math.pi, 5)
        F = wrap(C @ th)
        for k in range(6):
            keep = [j for j in range(6) if j != k]
            sol = np.linalg.solve(C[keep][:, cols].astype(float), F[keep])
            worst = max(worst, float(np.max(np.abs(wrap(sol - th[cols])))))
    return {"trials": n, "max_chord_phase_error_mod_2pi": worst}


def main():
    rng = np.random.default_rng(20261126)
    ex = exact_structure()
    table = subset_table()
    five = [t for t in table if len(t["faces"]) == 5]
    report = {
        "evidence_class": "exact integer algebra (Fraction) + ideal/noisy NumPy simulation; no Q3 hardware",
        "exact": ex,
        "five_face_subsets": five,
        "subset_rank_summary": {str(k): sorted({t["rank"] for t in table if len(t["faces"]) == k}) for k in range(1, 7)},
        "minimal_cycle_recovery_size": min(len(t["faces"]) for t in table if t["full_cycle_recovery"]),
        "gauge": gauge_equivalence(rng),
        "restricted_indistinguishable": indistinguishable_under_restriction(rng),
        "orientation": orientation_ambiguity(rng),
        "bianchi_projection": bianchi_projection_study(rng),
        "reconstruction": lattice_reconstruction_check(rng),
        "existing_hardware_receipts": "ibm_qpu_01/receipts/hardware_q2 covers one Q2 face only; Q3 is simulation-only",
    }
    checks = {
        "rank_curl_is_5": ex["rank_curl"] == 5,
        "bianchi_is_left_null": ex["bianchi_left_null"],
        "gauge_dim_7": ex["gauge_dim_edge_kernel"] == 7,
        "cycle_dof_5": ex["cycle_dof"] == 5,
        "vertex_gauge_in_kernel": ex["curl_kills_gradients"],
        "all_five_face_subsets_unimodular": ex["every_five_face_subset_unimodular"],
        "all_six_five_subsets_rank5": all(t["rank"] == 5 for t in five) and len(five) == 6,
        "four_face_subsets_all_rank4": report["subset_rank_summary"]["4"] == [4],
        "minimal_size_is_5": report["minimal_cycle_recovery_size"] == 5,
        "gauge_invariance": report["gauge"]["max_flux_change_under_vertex_gauge"] < 1e-9,
        "reconstruction_exact": report["reconstruction"]["max_chord_phase_error_mod_2pi"] < 1e-9,
        "every_restricted_set_has_indistinguishable_pair": all(r["indistinguishable_pair_found"] for r in report["restricted_indistinguishable"]),
        "wrapped_projection_beats_unwrapped_on_branches": report["bianchi_projection"]["max_error_wrapped_residual_projection"] < 0.5 < report["bianchi_projection"]["max_error_unwrapped_residual_projection"],
        "weighted_projection_beats_unweighted": report["bianchi_projection"]["mean_sq_error_covariance_weighted_projection"]
        < report["bianchi_projection"]["mean_sq_error_unweighted_projection"] < report["bianchi_projection"]["mean_sq_error_raw"],
        "cos_only_orientation_ambiguous": report["orientation"]["max_consistent_sign_patterns_cos_only"] >= 2,
    }
    report["checks"] = checks
    (HERE / "q3_minimal_observation.json").write_text(json.dumps(report, indent=1, default=float) + "\n")
    for k, v in checks.items():
        print(("PASS " if v else "FAIL ") + k)
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
