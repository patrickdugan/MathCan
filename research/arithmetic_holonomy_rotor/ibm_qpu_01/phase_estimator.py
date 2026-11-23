"""Signed phase calibration, Bernoulli intervals, information and shot comparisons."""

import numpy as np
from scipy.stats import beta

from exact_oracle import harmonic, masked_probabilities, phase_scan, wrap
from hamiltonian import PLANTED_PHASE, REFERENCE_OFFSET

SEED = 20261123
REPLICATES = 2500
SYSTEMATIC_FLOOR = 0.003


def rectangle(successes, shots, coverage=.95):
    """Simultaneous Clopper–Pearson rectangles propagated through the 4-phase DFT."""
    hits = np.asarray(successes, dtype=int)
    n = np.broadcast_to(np.asarray(shots, dtype=int), (4,))
    if hits.shape != (4,) or np.any(n <= 0) or np.any(hits < 0) or np.any(hits > n):
        raise ValueError("four valid binomial counts are required")
    tail = (1-coverage)/8
    low = np.where(hits == 0, 0, beta.ppf(tail, hits, n-hits+1))
    high = np.where(hits == n, 1, beta.ppf(1-tail, hits+1, n-hits))
    return {
        "coverage_at_least": coverage,
        "probability_intervals": np.stack([low, high], axis=1).tolist(),
        "real": [(low[0]-high[2])/2, (high[0]-low[2])/2],
        "imag": [(low[3]-high[1])/2, (high[3]-low[1])/2],
    }


def _angle_radius(value, box):
    r = np.hypot(max(abs(value.real-i) for i in box["real"]),
                 max(abs(value.imag-i) for i in box["imag"]))
    return float(np.arcsin(r/abs(value))) if r < abs(value) else None


def estimate(signal_counts, reference_counts, shots):
    signal, reference = np.asarray(signal_counts), np.asarray(reference_counts)
    a, b = harmonic(signal/shots), harmonic(reference/shots)
    # Bonferroni over the separately sampled signal and reference.
    a_rect, b_rect = rectangle(signal, shots, .975), rectangle(reference, shots, .975)
    ar, br = _angle_radius(a, a_rect), _angle_radius(b, b_rect)
    calibrated = float(np.angle(a*b.conjugate())) if abs(a)*abs(b) > 1e-14 else None
    return {
        "signal_harmonic": complex_record(a), "reference_harmonic": complex_record(b),
        "signal_rectangle": a_rect, "reference_rectangle": b_rect,
        "relative_phase_rad": calibrated,
        "joint_95_phase_halfwidth_rad": min(np.pi, ar+br) if ar is not None and br is not None else None,
        "phase_identifiable_at_95": ar is not None and br is not None and ar+br < np.pi,
    }


def complex_record(value):
    return [float(value.real), float(value.imag)]


def acceptance(counts, shots, target, modeled_probabilities):
    """One declared primary test: exact target inside inflated 95% joint rectangle."""
    measured = harmonic(np.asarray(counts)/shots)
    rect = rectangle(counts, shots)
    residuals = [harmonic(p) - target for p in modeled_probabilities]
    allowances = [float(max([0.0, *[abs(z.real if axis == "real" else z.imag) for z in residuals]]))
                  + SYSTEMATIC_FLOOR for axis in ("real", "imag")]
    enlarged = [[rect[name][0]-allowance, rect[name][1]+allowance]
                for name, allowance in zip(("real", "imag"), allowances, strict=True)]
    return {
        "observed": complex_record(measured), "target": complex_record(target),
        "unexpanded_joint_95_rectangle": rect, "systematic_allowances_real_imag": allowances,
        "policy_floor_per_component": SYSTEMATIC_FLOOR, "expanded_joint_rectangle": enlarged,
        "passes": all(lo <= x <= hi for x, (lo, hi) in zip(complex_record(target), enlarged, strict=True)),
    }


def _statistics(angles, truth):
    residual = wrap(angles-truth)
    return {
        "replicates": len(residual),
        "circular_bias_deg": float(np.degrees(np.angle(np.exp(1j*residual).mean()))),
        "angular_rmse_deg": float(np.degrees(np.sqrt(np.mean(residual**2)))),
        "angular_error_2p5_97p5_deg": np.degrees(np.quantile(residual, [.025, .975])).tolist(),
    }


def shot_benchmark(time, probabilities, *, seed=SEED):
    """The fully masked estimator pays for all arms, including all reference shots."""
    result = {}
    exact_signal = phase_scan(time, PLANTED_PHASE+REFERENCE_OFFSET)
    exact_ref = phase_scan(time, REFERENCE_OFFSET)
    signs, masked_signal = masked_probabilities(time, PLANTED_PHASE+REFERENCE_OFFSET)
    _, masked_ref = masked_probabilities(time, REFERENCE_OFFSET)
    for shots in (2048, 8192):
        rng = np.random.default_rng(seed+shots)
        outcomes = {}
        for name, (a, b) in probabilities.items():
            sample_a = rng.binomial(shots, a, size=(REPLICATES, 4)) / shots
            sample_b = rng.binomial(shots, b, size=(REPLICATES, 4)) / shots
            za, zb = harmonic(sample_a), harmonic(sample_b)
            outcomes[name] = {
                **_statistics(np.angle(za*zb.conj()), PLANTED_PHASE),
                "empirical_signal_Z95_real": np.quantile(za.real, [.025, .975]).tolist(),
                "empirical_signal_Z95_imag": np.quantile(za.imag, [.025, .975]).tolist(),
            }
        reduced = shots // len(signs)
        a = rng.binomial(reduced, masked_signal, size=(REPLICATES, len(signs), 4))/reduced
        b = rng.binomial(reduced, masked_ref, size=(REPLICATES, len(signs), 4))/reduced
        za, zb = harmonic(signs @ a), harmonic(signs @ b)
        outcomes["exhaustive_ideal_equal_total"] = _statistics(np.angle(za*zb.conj()), PLANTED_PHASE)
        outcomes["total_shots_both_arms_each_protocol"] = 8*shots
        outcomes["exhaustive_shots_per_setting"] = reduced
        outcomes["exact_exhaustive_mean_residual"] = float(max(
            abs(harmonic(signs @ masked_signal)-harmonic(exact_signal)),
            abs(harmonic(signs @ masked_ref)-harmonic(exact_ref)),
        ))
        result[str(shots)] = outcomes
    return result


def fisher(time, theta=PLANTED_PHASE, offset=REFERENCE_OFFSET, shots=2048):
    """Exact-probability conditional Fisher information for theta and shared offset."""
    def information(angle):
        probabilities = phase_scan(time, angle)
        eps = 1e-5
        coarse = (phase_scan(time, angle+eps)-phase_scan(time, angle-eps))/(2*eps)
        fine = (phase_scan(time, angle+eps/2)-phase_scan(time, angle-eps/2))/eps
        np.testing.assert_allclose(coarse, fine, atol=1e-8, rtol=0)
        return float(shots*np.sum(fine**2/(probabilities*(1-probabilities))))

    signal, reference = information(theta+offset), information(offset)
    return {
        "shots_per_setting_per_arm": shots, "signal_info_if_reference_phase_known": signal,
        "reference_info": reference, "joint_fisher_theta_beta": [[signal, signal], [signal, signal+reference]],
        "known_reference_cr_sd_deg": float(np.degrees(np.sqrt(1/signal))),
        "estimated_reference_cr_sd_deg": float(np.degrees(np.sqrt(1/signal+1/reference))),
    }
