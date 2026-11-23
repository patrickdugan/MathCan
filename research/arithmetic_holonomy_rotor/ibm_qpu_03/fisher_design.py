"""Binomial likelihood, shared-calibration Fisher matrices, and allocation."""
from dataclasses import dataclass

import numpy as np

from bianchi_reconstruction import summarize
from plaquette_estimator import harmonic, probability
from q3_hamiltonian import (BIANCHI, CHORD_COLUMNS, D1, EDGE_U, EDGE_V, chord_field, face_flux, matrix, wrap)

FACE_JACOBIAN = D1[:, CHORD_COLUMNS]
NUISANCE_NAMES = ("readout", "coherent_phase", "common_drift", "coupling")
LEVELS = (2048, 4096, 8192)
REPLICATES = 1000
EVALUATION_SEED = 987411


def response(chords, cases):
    """Exact binomial response and its five analytical derivatives."""
    c = len(cases)
    indices = np.arange(c)
    starts = [s.start for s in cases]
    time = np.asarray([s.time for s in cases])
    offsets = np.zeros((c, 12))
    offsets[indices, [s.edge for s in cases]] = [s.offset * s.direction for s in cases]
    h = matrix(chord_field(chords)[..., None, :] + offsets)
    values, vectors = np.linalg.eigh(h)
    phase = np.exp(-1j * time[:, None] * values)
    sv = vectors[..., indices, starts, :]
    amplitude = np.sum(abs(sv)**2 * phase, axis=-1)
    ta = time[:, None] * values
    divided = (-1j * time[:, None, None] *
               np.exp(-.5j * (ta[..., :, None] + ta[..., None, :])) *
               np.sinc((ta[..., :, None] - ta[..., None, :]) / (2 * np.pi)))
    core = sv[..., :, None] * sv.conj()[..., None, :] * divided
    edge_kernel = vectors.conj() @ core @ vectors.swapaxes(-2, -1)
    up, down = EDGE_U[CHORD_COLUMNS], EDGE_V[CHORD_COLUMNS]
    dh = 1j * h[..., up, down]
    d_amp = edge_kernel[..., up, down] * dh + edge_kernel[..., down, up] * dh.conj()
    return abs(amplitude)**2, 2 * np.real(amplitude.conj()[..., None] * d_amp)


def nuisance_templates(chords, cases, p, readout_scale):
    from dataclasses import replace

    field = chord_field(chords)
    step = 1e-4
    plus = [replace(c, offset=c.offset + step) for c in cases]
    minus = [replace(c, offset=c.offset - step) for c in cases]
    phase = (probability(field, plus) - probability(field, minus)) / (2 * step)
    coupling = (probability(field, cases, 1+step) - probability(field, cases, 1-step)) / (2*step)
    time = np.array([c.time for c in cases])
    drift = .012 * (time / time.max()) * (p - .125)
    return np.column_stack((readout_scale * (.125 - p), .025 * phase, drift, .015 * coupling))


@dataclass(frozen=True)
class Calibration:
    intercept: np.ndarray
    contrast: np.ndarray
    nuisance: np.ndarray
    transfer_modes: np.ndarray

    @property
    def shared(self):
        return np.column_stack((self.nuisance, self.transfer_modes))

    def map(self, p):
        return np.clip(self.intercept + self.contrast * p, .001, .999)


def fit_transfer(exact_training, aer_training, nuisance):
    x = exact_training - np.mean(exact_training, axis=0)
    y = aer_training - np.mean(aer_training, axis=0)
    # Shrink ill-constrained per-setting transfer slopes toward the pooled slope.
    pooled = np.sum(x*y) / max(np.sum(x*x), 1e-10)
    slopes = np.clip((np.sum(x*y, axis=0) + .004 * pooled) /
                     (np.sum(x*x, axis=0) + .004), .30, 1.15)
    intercept = np.mean(aer_training - slopes*exact_training, axis=0)
    residual = aer_training - intercept - slopes*exact_training
    return Calibration(intercept, slopes, nuisance, residual.T / np.sqrt(len(residual)-1))


def fisher(p, derivative, shots, nuisance_count=0):
    weights = shots / np.clip(p*(1-p), 1e-8, None)
    information = np.einsum("...si,...s,...sj->...ij", derivative, weights, derivative)
    if nuisance_count:
        info_diag = np.r_[np.zeros(information.shape[-1]-nuisance_count), np.ones(nuisance_count)]
        information = information + np.diag(info_diag)
    return information


def allocate(p, derivative, budget, nuisance_count):
    """Local A-optimal allocation minimizing total oriented-face variance."""
    n = len(p)
    shots = np.full(n, budget/n)
    metric = np.zeros((derivative.shape[-1], derivative.shape[-1]))
    metric[:5, :5] = FACE_JACOBIAN.T @ FACE_JACOBIAN
    for _ in range(80):
        covariance = np.linalg.inv(fisher(p, derivative, shots, nuisance_count))
        cv = derivative @ covariance
        sensitivity = np.einsum("si,ij,sj->s", cv, metric, cv) / np.clip(p*(1-p), 1e-8, None)
        shots = np.maximum(shots * np.sqrt(sensitivity / max(sensitivity.mean(), 1e-20)), budget / (30*n))
        shots *= budget / shots.sum()
    rounded = np.floor(shots).astype(int)
    remaining = budget - sum(rounded)
    rounded[np.argsort(-(shots-rounded))[:remaining]] += 1
    assert rounded.sum() == budget and min(rounded) > 0
    return rounded


def _objective(counts, shots, p, nuisance):
    return np.sum(counts*np.log(p) + (shots-counts)*np.log1p(-p), axis=-1) - .5*np.sum(nuisance**2, axis=-1)


def _predict(z, cases, calibration):
    ideal, jac = response(z[..., :5], cases)
    p = np.clip(calibration.map(ideal) + z[..., 5:] @ calibration.shared.T, .001, .999)
    n = np.broadcast_to(calibration.shared, (*jac.shape[:-2], *calibration.shared.shape))
    return p, np.concatenate((jac * calibration.contrast[:, None], n), axis=-1)


def fit_likelihood(counts, shots, cases, calibration, center, iterations=9):
    """Damped Fisher scoring on the exact response, conditioned on a local chart."""
    shot_n = calibration.shared.shape[-1]
    counts = np.asarray(counts, dtype=float)
    answer, covariances, convergence = [], [], []
    for batch in np.array_split(counts, max(1, int(np.ceil(len(counts)/100)))):
        z = np.broadcast_to(np.r_[center, np.zeros(shot_n)], (len(batch), 5 + shot_n)).copy()
        for _ in range(iterations):
            p, derivative = _predict(z, cases, calibration)
            information = fisher(p, derivative, shots, shot_n)
            residual = (batch - shots*p) / (p*(1-p))
            grad = np.einsum("...si,...s->...i", derivative, residual)
            grad[..., 5:] -= z[..., 5:]
            d = np.linalg.solve(information, grad[..., None])[..., 0]
            step = d / np.maximum(1, np.max(abs(d[..., :5]), axis=-1)[..., None]/.35)
            score = _objective(batch, shots, p, z[..., 5:])
            trial = z.copy()
            for scale in (1, .5, .25, .125):
                proposal = z + step * scale
                ideal = probability(chord_field(proposal[..., :5]), cases)
                pp = np.clip(calibration.map(ideal) + proposal[..., 5:] @ calibration.shared.T, .001, .999)
                valid = (np.max(abs(proposal[..., :5] - center), axis=-1) < 1.2) & (
                    _objective(batch, shots, pp, proposal[..., 5:]) >= score - 1e-9)
                unresolved = np.all(trial == z, axis=-1)
                trial = np.where((valid & unresolved)[..., None], proposal, trial)
                if not np.any(np.all(trial == z, axis=-1)):
                    break
            z = trial
            if np.max(abs(step)) < 2e-5:
                break
        p, j = _predict(z, cases, calibration)
        cov = np.linalg.inv(fisher(p, j, shots, shot_n))
        final_score = np.einsum("...si,...s->...i", j, (batch - shots*p)/(p*(1-p)))
        final_score[..., 5:] -= z[..., 5:]
        score_norm = np.sqrt(np.einsum("...i,...ij,...j->...", final_score, cov, final_score))
        answer.append(wrap(z[..., :5]))
        covariances.append(cov[..., :5, :5])
        convergence.append(score_norm < .1)
    return np.concatenate(answer), np.concatenate(covariances), np.concatenate(convergence)


def likelihood_summary(estimated, covariance, truth, converged):
    errors = wrap(estimated-truth)
    flux_errors = wrap(errors @ FACE_JACOBIAN.T)
    faces = np.degrees(np.sqrt(np.mean(flux_errors**2, axis=0))).tolist()
    phase_cov = FACE_JACOBIAN @ covariance @ FACE_JACOBIAN.T
    from scipy.stats import chi2

    dist = np.einsum("...i,...ij,...j->...", errors, np.linalg.inv(covariance), errors)
    closure = wrap(face_flux(chord_field(estimated)) @ BIANCHI)
    return {"chord_rmse_deg": np.degrees(np.sqrt(np.mean(errors**2, axis=0))).tolist(),
            "face_rmse_deg": faces, "max_face_rmse_deg": max(faces),
            "face_coverage_95": np.mean(abs(flux_errors) <= 1.959964*np.sqrt(
                np.diagonal(phase_cov, axis1=-2, axis2=-1)), axis=0).tolist(),
            "median_face_halfwidth_deg": np.degrees(1.959964*np.median(
                np.sqrt(np.diagonal(phase_cov, axis1=-2, axis2=-1)), axis=0)).tolist(),
            "joint_chord_coverage_95": float(np.mean(dist <= chi2.ppf(.95, 5))),
            "converged_fraction": float(np.mean(converged)),
            "max_abs_projected_bianchi_deg": float(np.degrees(np.max(abs(closure))))}


def mirror_reference(cases):
    used = {}
    groups = []
    for case in cases:
        mirror = min(case.offset_index, case.offset_count-case.offset_index)
        marked = (case.edge, mirror) if mirror else (-1, 0)
        key = (case.start, case.time, case.offset_count, marked)
        if key not in used:
            used[key] = len(used)
        groups.append(used[key])
    return np.asarray(groups)


def harmonics_from_data(observed, n_target, reference_groups, count, richardson=False):
    target = observed[..., :n_target]
    reference = observed[..., n_target:][..., reference_groups]
    shape = (*target.shape[:-1], 6, 2 if richardson else 1, count)
    ratio = harmonic(target.reshape(shape)) / (harmonic(reference.reshape(shape)) + 1e-15)
    if richardson:
        ratio = 2 * ratio[..., 1] - ratio[..., 0]
    else:
        ratio = ratio[..., 0]
    return np.angle(ratio)


def harmonic_summary(observed, shots, shared, true_chords, count, groups, richardson):
    n_target = len(groups)
    raw = harmonics_from_data(observed, n_target, groups, count, richardson)
    mean = (observed * shots + .5) / (shots + 1)
    n = len(shots)
    # Delta method with independent shot noise and common calibration modes.
    # Shared references are represented by gathering the same independent count.
    eps = 1e-5
    perturb = eps * np.eye(n)
    differential = wrap(
        harmonics_from_data(mean[:, None, :] + perturb, n_target, groups, count, richardson) -
        harmonics_from_data(mean[:, None, :] - perturb, n_target, groups, count, richardson)
    ) / (2 * eps)
    j = differential.transpose(0, 2, 1)
    shared_effect = j @ shared
    covariance = (j * (mean*(1-mean)/shots)[:, None, :]) @ j.transpose(0, 2, 1)
    covariance += shared_effect @ shared_effect.transpose(0, 2, 1)
    report = summarize(raw, covariance, face_flux(chord_field(true_chords)), true_chords)
    report["max_face_rmse_deg"] = max(report["projected_face_rmse_deg"])
    report["face_coverage_95"] = report["projected_face_coverage_95"]
    return report
