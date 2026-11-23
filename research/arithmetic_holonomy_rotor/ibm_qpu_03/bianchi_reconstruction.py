"""Covariance-aware reconstruction on a local chart of the phase torus."""
import numpy as np
from scipy.stats import chi2

from q3_hamiltonian import BIANCHI, CHORD_INVERSE, wrap


def project(raw, covariance):
    cb = np.einsum("...ij,j->...i", covariance, BIANCHI)
    variance = cb @ BIANCHI
    if np.any(variance <= 0):
        raise ValueError("Bianchi residual must have positive variance")
    residual = wrap(raw @ BIANCHI)
    projected = wrap(raw - cb * (residual / variance)[..., None])
    reduced_covariance = covariance - cb[..., :, None] * cb[..., None, :] / variance[..., None, None]
    return projected, reduced_covariance, residual


def reconstruct(projected, covariance):
    phase = wrap(projected[..., :5] @ CHORD_INVERSE.T)
    chord_covariance = CHORD_INVERSE @ covariance[..., :5, :5] @ CHORD_INVERSE.T
    return phase, chord_covariance


def summarize(raw, covariance, true_faces, true_chords):
    projected, face_covariance, residual = project(raw, covariance)
    chords, chord_covariance = reconstruct(projected, face_covariance)
    raw_error = wrap(raw - true_faces)
    face_error = wrap(projected - true_faces)
    chord_error = wrap(chords - true_chords)
    raw_sd = np.sqrt(np.diagonal(covariance, axis1=-2, axis2=-1))
    face_sd = np.sqrt(np.maximum(0, np.diagonal(face_covariance, axis1=-2, axis2=-1)))
    chord_sd = np.sqrt(np.diagonal(chord_covariance, axis1=-2, axis2=-1))
    mahalanobis = np.einsum("...i,...ij,...j->...", chord_error,
                            np.linalg.pinv(chord_covariance, hermitian=True), chord_error)
    return {
        "raw_face_rmse_deg": np.degrees(np.sqrt(np.mean(raw_error**2, axis=0))).tolist(),
        "projected_face_rmse_deg": np.degrees(np.sqrt(np.mean(face_error**2, axis=0))).tolist(),
        "chord_rmse_deg": np.degrees(np.sqrt(np.mean(chord_error**2, axis=0))).tolist(),
        "raw_face_coverage_95": np.mean(abs(raw_error) <= 1.959964 * raw_sd, axis=0).tolist(),
        "projected_face_coverage_95": np.mean(abs(face_error) <= 1.959964 * face_sd, axis=0).tolist(),
        "joint_chord_coverage_95": float(np.mean(mahalanobis <= chi2.ppf(.95, 5))),
        "median_face_halfwidth_deg": np.degrees(1.959964 * np.median(face_sd, axis=0)).tolist(),
        "median_chord_halfwidth_deg": np.degrees(1.959964 * np.median(chord_sd, axis=0)).tolist(),
        "raw_bianchi_rms_deg": float(np.degrees(np.sqrt(np.mean(residual**2)))),
        "raw_bianchi_outside_local_chart_rate": float(np.mean(
            abs(raw @ BIANCHI - true_faces @ BIANCHI) > np.pi)),
        "max_abs_projected_bianchi_deg": float(np.degrees(np.max(abs(wrap(projected @ BIANCHI))))),
    }


def branch_audit(rng, replicates=2000):
    from q3_hamiltonian import chord_field, face_flux

    fixtures = [("near_pi", np.array([np.pi - .025, -np.pi + .06, .04, .04, -.05])),
                ("near_minus_pi", np.array([-np.pi + .02, np.pi - .05, -.04, -.05, .06]))]
    answer = {}
    for label, chords in fixtures:
        truth = face_flux(chord_field(chords))
        for sigma in (.09, .85, 1.5):
            covariance = sigma**2 * (.85 * np.eye(6) + .15 * np.ones((6, 6)))
            latent = rng.multivariate_normal(np.zeros(6), covariance, size=replicates)
            phase = wrap(truth + latent)
            report = summarize(phase, covariance, truth, chords)
            report["wide_error_branch_ambiguity_rate"] = float(np.mean(abs(latent @ BIANCHI) >= np.pi))
            report["seam_crossing_rate"] = float(np.mean(np.any(abs(truth + latent) >= np.pi, axis=1)))
            answer[f"{label}_{sigma:g}"] = report
    return answer
