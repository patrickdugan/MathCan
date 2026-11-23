"""Registered training-time sweep, sealed-count evaluation kept separate."""
from dataclasses import replace

import numpy as np
from scipy.stats import norm

from controls import CENTER
from noise_benchmark import benchmark
from plaquette_estimator import harmonic, probability, settings
from q3_hamiltonian import chord_field, face_flux, wrap

COARSE = np.round(np.arange(.1, 2.001, .1), 3)
TRAIN_SHOTS = 4096
FINE_STEP = .025


def phase_gradient(p):
    offsets = 2 * np.pi * np.arange(p.shape[-1]) / p.shape[-1]
    z = harmonic(p)
    safe = np.where(abs(z) > 1e-14, z, 1e-14)
    return np.imag((2 / p.shape[-1]) * np.exp(-1j * offsets) / safe[..., None])


def four(p):
    return p[..., ::2]


def grid_sweep(times, method, target, snapshot, aer):
    field = chord_field(CENTER)
    scan = settings(times, 8)
    contrast = face_flux(field)
    _, _, native, noisy = benchmark(field, scan, method, target, snapshot, aer)
    _, _, _, reference = benchmark(np.zeros(12), scan, method, target, snapshot, aer)
    shape = (6, len(times), 8)
    exact = probability(field, scan).reshape(shape)
    ideal_reference = probability(np.zeros(12), scan).reshape(shape)
    native, noisy, reference = (p.reshape(shape) for p in (native, noisy, reference))
    higher = probability(field, settings(times, 32)).reshape(6, len(times), 32)
    amplitude = abs(harmonic(higher))
    alias = abs(harmonic(higher, 3))
    # Score single-time harmonic measurements with the same registered 4096
    # shots per setting, including the independently measured zero reference.
    row = []
    for count, pick in [(4, four), (8, lambda p: p)]:
        z = harmonic(pick(noisy))
        z_ref = harmonic(pick(reference))
        z_exact = harmonic(pick(exact))
        z_exact_ref = harmonic(pick(ideal_reference))
        calibrated = wrap(np.angle(z / z_ref))
        ideal = wrap(np.angle(z_exact / z_exact_ref))
        bias = wrap(calibrated - contrast[:, None])
        n, r = pick(noisy), pick(reference)
        variance = np.sum(phase_gradient(n)**2 * n * (1-n) / TRAIN_SHOTS +
                          phase_gradient(r)**2 * r * (1-r) / TRAIN_SHOTS, axis=-1)
        sd = np.sqrt(variance)
        coverage = norm.cdf(1.959964 - bias/sd) - norm.cdf(-1.959964 - bias/sd)
        rms = np.degrees(np.sqrt(bias**2 + variance))
        for k, t in enumerate(times):
            row.append({"time": float(t), "offsets": count, "max_rmse_proxy_deg": float(max(rms[:, k])),
                        "phase_bias_deg": np.degrees(wrap(ideal[:, k] - contrast)).tolist(),
                        "noise_bias_deg": np.degrees(wrap(calibrated[:, k] - ideal[:, k])).tolist(),
                        "amplitude": amplitude[:, k].tolist(), "third_harmonic": alias[:, k].tolist(),
                        "max_compiled_abs_p_error": np.max(abs(native[:, k, :] - exact[:, k, :]),
                                                           axis=-1).tolist(),
                        "shot_variance_rad2": variance[:, k].tolist(),
                        "delta_normal_95_coverage": coverage[:, k].tolist()})
    return row


def optimize(method, target, snapshot, aer):
    coarse = grid_sweep(COARSE, method, target, snapshot, aer)
    promising = [min((r for r in coarse if r["offsets"] == count),
                     key=lambda r: r["max_rmse_proxy_deg"])["time"] for count in (4, 8)]
    # A second window explores the high-amplitude likelihood regime without
    # inspecting any held-out fields or counts.
    promising.append(max((r for r in coarse if r["offsets"] == 8),
                         key=lambda r: np.min(r["amplitude"]))["time"])
    refine = sorted({round(t + d * FINE_STEP, 3) for t in promising for d in range(-3, 4)
                     if .1 <= round(t + d * FINE_STEP, 3) <= 2.0} - set(COARSE))
    rows = sorted(coarse + grid_sweep(refine, method, target, snapshot, aer),
                  key=lambda r: (r["offsets"], r["time"]))
    winner = {str(count): min((r for r in rows if r["offsets"] == count),
                             key=lambda r: r["max_rmse_proxy_deg"])["time"] for count in (4, 8)}
    # Pick likelihood time by the smallest eigenvalue of calibrated-proxy
    # five-chord Fisher; phase unwrapping and bias are evaluated separately.
    from fisher_design import response
    conditioning = {}
    for row in rows:
        if row["offsets"] != 4:
            continue
        p, j = response(CENTER, settings([row["time"]]))
        fisher = (j.T / np.clip(p*(1-p), 1e-8, None)) @ j
        conditioning[row["time"]] = float(np.linalg.eigvalsh(fisher)[0])
    winner["likelihood"] = max(conditioning, key=conditioning.get)
    winner["richardson"] = winner["4"]
    return {"coarse_grid": COARSE.tolist(), "refinement_grid": refine,
            "reference_t0p12": grid_sweep([.12], method, target, snapshot, aer),
            "refinement_step": FINE_STEP, "registered_shots_per_setting": TRAIN_SHOTS,
            "selection": winner, "likelihood_exact_fisher_lambda_min": conditioning,
            "rows": rows}


def richardson_cases(time):
    return [replace(c, time=round(c.time, 8)) for c in settings([time, time / np.sqrt(2)])]
