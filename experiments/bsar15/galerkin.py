"""BSAR-15: short-time 3D Navier–Stokes Fourier–Galerkin experiment.

Real-valued divergence-free initial data are copied from the exact BSAR-14
Gaussian-rational Fourier oracle. An explicit RK4 time step applies the
Leray projector and a strict 2/3 de-aliasing mask to all nonlinear terms.

This is a numerical *finite-dimensional Galerkin* experiment. Convergence
comparisons are empirical, not validated outward error enclosures for the
infinite-dimensional PDE or a proof of any cone integral bound.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any

import numpy as np

from scripts.bsar14_initial_triad_transfer import (
    NORMALIZED_SHELLS,
    modes as source_modes,
)

SOURCE_MATHCAN = "e2c0e1c56f6e5d2291536156709f75668d1e0f8f"
SOURCE_BSAR = "80c62433b0eb671175bd8d6169822d3ebd922b60"
SCENARIOS = ((1, -1), (1, 1), (2, -1), (2, 1))
GRIDS = (16, 24, 32)
VISCOSITY = 0.1
T_END = 0.012
COARSE_DT = 0.001
FINE_DT = 0.0005
AMPLITUDE = Fraction(1)


def _jfloat(number: float) -> float:
    """Round observational values for compact deterministic JSON receipts."""
    return round(float(number), 12)


def _complex_list(z: complex) -> list[float]:
    return [_jfloat(z.real), _jfloat(z.imag)]


def _complex(z: Any) -> complex:
    return complex(float(z.real), float(z.imag))


@dataclass
class FourierGalerkin:
    grid: int
    mode_n: int
    phase: int
    viscosity: float = VISCOSITY
    amplitude: Fraction = AMPLITUDE

    def __post_init__(self) -> None:
        if self.grid < 12 or self.grid % (4 * self.mode_n):
            raise ValueError("grid must fit the exact anchored Fourier points")
        if self.mode_n < 1 or self.phase not in (-1, 1):
            raise ValueError("invalid mode frequency or phase")
        if self.amplitude <= 0 or not self.viscosity > 0:
            raise ValueError("expected positive amplitude and viscosity")
        freq = np.fft.fftfreq(self.grid, d=1 / self.grid)
        self.k = np.stack(np.meshgrid(freq, freq, freq, indexing="ij"))
        self.ksq = np.sum(self.k * self.k, axis=0)
        self.cutoff = (self.grid - 1) // 3
        self.mask = (np.max(np.abs(self.k), axis=0) <= self.cutoff)
        if self.cutoff < 2 * self.mode_n:
            raise ValueError("grid cannot resolve the initial source modes")
        self.factor = self.grid**3
        self.initial = np.zeros(
            (3, self.grid, self.grid, self.grid), dtype=np.complex128
        )
        self.modes = source_modes(self.mode_n, self.amplitude, self.phase)
        for wave, components in self.modes.items():
            index = tuple(v % self.grid for v in wave)
            self.initial[(slice(None), *index)] = [
                _complex(x) for x in components
            ]
        assert np.max(np.abs(self.initial[:, ~self.mask])) == 0

    def _inverse(self, hats: np.ndarray) -> np.ndarray:
        return np.fft.ifftn(hats * self.factor, axes=(-3, -2, -1))

    def _fft(self, values: np.ndarray) -> np.ndarray:
        return np.fft.fftn(values, axes=(-3, -2, -1)) / self.factor

    def project(self, field: np.ndarray) -> np.ndarray:
        dotted = np.sum(self.k * field, axis=0)
        denominator = np.where(self.ksq > 0, self.ksq, 1)
        result = field - self.k * (dotted / denominator)[None, ...]
        result *= self.mask[None, ...]
        result[:, 0, 0, 0] = 0
        return result

    def curl_hat(self, hats: np.ndarray) -> np.ndarray:
        return 1j * np.stack((
            self.k[1] * hats[2] - self.k[2] * hats[1],
            self.k[2] * hats[0] - self.k[0] * hats[2],
            self.k[0] * hats[1] - self.k[1] * hats[0],
        ))

    def nonlinear_hat(self, hats: np.ndarray) -> np.ndarray:
        """Compute P[(u·grad)u] using FFT pseudospectral products."""
        physical = self._inverse(hats).real
        nonlinear = np.zeros_like(physical)
        for j in range(3):
            for axis in range(3):
                derivative = self._inverse(1j * self.k[axis] * hats[j]).real
                nonlinear[j] += physical[axis] * derivative
        spectral = self._fft(nonlinear)
        return self.project(spectral)

    def rhs(self, hats: np.ndarray) -> np.ndarray:
        return -self.nonlinear_hat(hats) - self.viscosity * self.ksq * hats

    def step(self, hats: np.ndarray, dt: float) -> np.ndarray:
        if dt <= 0:
            raise ValueError("positive time increment required")
        k1 = self.rhs(hats)
        k2 = self.rhs(hats + (dt / 2) * k1)
        k3 = self.rhs(hats + (dt / 2) * k2)
        k4 = self.rhs(hats + dt * k3)
        next_hats = hats + dt * (k1 + 2*k2 + 2*k3 + k4) / 6
        return self.project(next_hats)

    def energy(self, hats: np.ndarray) -> float:
        return float(np.sum(np.abs(hats)**2) / 2)

    def enstrophy(self, hats: np.ndarray) -> float:
        return float(np.sum(np.abs(self.curl_hat(hats))**2))

    def shell_transfer(self, hats: np.ndarray) -> dict[str, float]:
        projected = self.nonlinear_hat(hats)
        transfer: dict[str, float] = {}
        for shell in NORMALIZED_SHELLS:
            which = self.ksq == shell * self.mode_n * self.mode_n
            transfer[str(shell)] = -float(
                np.real(np.sum(np.conj(hats[:, which]) * projected[:, which]))
            )
        return transfer

    def _anchor(self, omega: np.ndarray, x_pi: bool) -> np.ndarray:
        x = (self.grid // (2 * self.mode_n)) if x_pi else 0
        z = self.grid // (4 * self.mode_n)
        return omega[:, x, 0, z]

    def _sample_core(self, omega: np.ndarray, norms: np.ndarray) -> dict[str, Any]:
        """Sampled-core diagnostic and conditional Galerkin analytic envelopes.

        Sampled core is relative to the GRID maximum and hence its K estimate
        is not automatically a lower bound for the true continuum high-core.
        The anchor lower witness uses an independently computed continuum
        maximum upper envelope for the finite Galerkin trigonometric field.
        """
        peak = float(norms.max())
        core = norms >= peak / 2
        unit = omega / np.maximum(norms, 1e-200)[None, ...]
        offsets = {(1, 0, 0), (0, 1, 0), (0, 0, 1)}
        for scale in (2, 3, 4, self.grid // (2 * self.mode_n)):
            if scale <= self.grid // 2:
                offsets.update({
                    (scale, 0, 0), (0, scale, 0), (0, 0, scale)
                })
        offsets.update({(1, 1, 0), (1, 0, 1), (0, 1, 1)})
        sampled_max = 0.0
        sample_pairs = 0
        for offset in sorted(offsets):
            distance = 2 * math.pi / self.grid * math.sqrt(
                sum(min(v, self.grid - v)**2 for v in offset)
            )
            other_core = np.roll(core, shift=offset, axis=(0, 1, 2))
            active = core & other_core
            if not bool(np.any(active)):
                continue
            other = np.roll(unit, shift=offset, axis=(1, 2, 3))
            differences = np.sum((unit - other)**2, axis=0)
            sampled_max = max(
                sampled_max, float(np.max(differences[active] / distance))
            )
            sample_pairs += int(np.count_nonzero(active))
        omega_hat = self.curl_hat(self._latest_hats)
        omega0_hat = self.curl_hat(self.initial)
        delta_l1 = float(
            np.sum(np.linalg.norm(omega_hat - omega0_hat, axis=0))
        )
        # Initial source-specific exact bound |omega_0(x)|<=sqrt(65) A N.
        # Triangle inequality extends it to the current Galerkin polynomial.
        global_max_upper = math.sqrt(65) * float(self.amplitude) * self.mode_n + delta_l1
        w0, w1 = self._anchor(omega, False), self._anchor(omega, True)
        n0 = float(np.linalg.norm(w0))
        n1 = float(np.linalg.norm(w1))
        guaranteed_core_pair = (
            n0 >= 0.5 * global_max_upper + 1e-10
            and n1 >= 0.5 * global_max_upper + 1e-10
        )
        anchor_difference = float(
            np.sum((w0 / n0 - w1 / n1)**2)
        ) if min(n0, n1) > 1e-15 else 0.0
        lower_witness = (
            anchor_difference * self.mode_n / math.pi
            if guaranteed_core_pair else None
        )
        # For any two true high-core endpoints min(|omega|)>=max|omega|/2.
        # The finite trigonometric field has a global Lipschitz bound:
        # L <= sum_k |k|*|omega_hat(k)|.
        omega_lipschitz = float(np.sum(
            np.sqrt(self.ksq) * np.linalg.norm(omega_hat, axis=0)
        ))
        upper_envelope = 8 * omega_lipschitz / peak
        assert upper_envelope + 1e-9 >= sampled_max
        return {
            "grid_core_fraction": _jfloat(float(core.mean())),
            "grid_core_sample_pair_count": sample_pairs,
            "sampled_grid_relative_cone_K": _jfloat(sampled_max),
            "true_core_anchor_pair_by_galerkin_max_upper": guaranteed_core_pair,
            "anchor_continuum_cone_lower_if_valid": (
                _jfloat(lower_witness) if lower_witness is not None else None
            ),
            "anchor_direction_difference_sq": _jfloat(anchor_difference),
            "galerkin_sup_vorticity_upper": _jfloat(global_max_upper),
            "sampled_vorticity_peak": _jfloat(peak),
            "galerkin_cone_upper_from_lipschitz": _jfloat(upper_envelope),
            "grid_near_zero_fraction": _jfloat(
                float(np.mean(norms <= peak * 1e-4))
            ),
            "rounding_scope": "numerical estimates, no certified outward rounding",
        }

    def diagnostics(self, hats: np.ndarray, t: float) -> dict[str, Any]:
        self._latest_hats = hats
        omega_hat = self.curl_hat(hats)
        physical_omega = self._inverse(omega_hat).real
        norms = np.linalg.norm(physical_omega, axis=0)
        transfer = self.shell_transfer(hats)
        projected = self.nonlinear_hat(hats)
        energy = self.energy(hats)
        enstrophy = self.enstrophy(hats)
        nonlinear_power = -float(
            np.real(np.sum(np.conj(hats) * projected))
        )
        divergence = float(np.max(np.abs(np.sum(self.k * hats, axis=0))))
        new_mode = hats[:, self.mode_n, 0, self.mode_n]
        return {
            "t": _jfloat(t),
            "energy": _jfloat(energy),
            "enstrophy": _jfloat(enstrophy),
            "nonlinear_energy_power": _jfloat(nonlinear_power),
            "energy_derivative_from_rhs": _jfloat(
                nonlinear_power - self.viscosity * enstrophy
            ),
            "divergence_hat_max": _jfloat(divergence),
            "shell_transfer": {key: _jfloat(val) for key, val in transfer.items()},
            "new_mode_velocity_y": _complex_list(new_mode[1]),
            "new_mode_vector_norm": _jfloat(float(np.linalg.norm(new_mode))),
            "core": self._sample_core(physical_omega, norms),
        }

    def run(self, dt: float, t_end: float) -> dict[str, Any]:
        total = round(t_end / dt)
        if total < 1 or abs(total * dt - t_end) > 1e-12:
            raise ValueError("t_end must be an integral multiple of dt")
        hats = self.initial.copy()
        initial = self.diagnostics(hats, 0.0)
        core_snapshots = [initial]
        signs: dict[str, list[float]] = {
            shell: [] for shell in map(str, NORMALIZED_SHELLS)
        }
        max_divergence = 0.0
        energies: list[float] = [self.energy(hats)]
        enstrophies: list[float] = [self.enstrophy(hats)]
        for tick in range(total + 1):
            if tick:
                hats = self.step(hats, dt)
                energies.append(self.energy(hats))
                enstrophies.append(self.enstrophy(hats))
            if tick in (total // 2, total) and tick > 0:
                core_snapshots.append(self.diagnostics(hats, tick * dt))
            transfer = self.shell_transfer(hats)
            for key in signs:
                signs[key].append(transfer[key])
            max_divergence = max(
                max_divergence,
                float(np.max(np.abs(np.sum(self.k * hats, axis=0))))
            )
        for shell in signs:
            expected_sign = 1 if initial["shell_transfer"][shell] > 0 else -1
            if not all(value * expected_sign > 0 for value in signs[shell]):
                # Record first loss of sign, rather than asserting it persists
                # for an arbitrary horizon.
                first = next(
                    i * dt for i, val in enumerate(signs[shell])
                    if val * expected_sign <= 0
                )
                signs[shell] = [first]
            else:
                signs[shell] = []
        integral_D = dt * (
            (enstrophies[0] + enstrophies[-1]) / 2
            + sum(enstrophies[1:-1])
        )
        dissipation = self.viscosity * integral_D
        energy_defect = energies[-1] - energies[0] + dissipation
        return {
            "grid": self.grid,
            "mode_n": self.mode_n,
            "phase": self.phase,
            "amplitude": str(self.amplitude),
            "nu": self.viscosity,
            "cutoff": self.cutoff,
            "dt": dt,
            "t_end": t_end,
            "steps": total,
            "diagnostics": core_snapshots,
            "sign_flip_first_time": {
                key: (_jfloat(val[0]) if val else None) for key, val in signs.items()
            },
            "all_initial_shell_transfer_signs_persist": all(
                not vals for vals in signs.values()
            ),
            "max_divergence_hat": _jfloat(max_divergence),
            "energy_defect_trapezoid": _jfloat(energy_defect),
            "dissipation_integral_trapezoid": _jfloat(dissipation),
            "reality_and_time_scope": "float64 periodic 2/3 Galerkin RK4",
        }


def campaign() -> dict[str, Any]:
    runs = []
    comparisons = []
    for mode_n, phase in SCENARIOS:
        group = {}
        for grid in GRIDS:
            solver = FourierGalerkin(grid, mode_n, phase)
            result = solver.run(COARSE_DT, T_END)
            group[grid] = result
            runs.append(result)
        fine = FourierGalerkin(32, mode_n, phase).run(FINE_DT, T_END)
        runs.append(fine)
        coarse_final = group[32]["diagnostics"][-1]
        fine_final = fine["diagnostics"][-1]
        medium_final = group[24]["diagnostics"][-1]
        comparisons.append({
            "mode_n": mode_n,
            "phase": phase,
            "fine_grid": 32,
            "medium_grid": 24,
            "coarse_grid": 16,
            "temporal_energy_abs_diff": _jfloat(
                abs(fine_final["energy"] - coarse_final["energy"])
            ),
            "temporal_new_mode_y_abs_diff": _jfloat(abs(
                complex(*[fine_final["new_mode_velocity_y"][0],
                           fine_final["new_mode_velocity_y"][1]])
                - complex(*[coarse_final["new_mode_velocity_y"][0],
                             coarse_final["new_mode_velocity_y"][1]])
            )),
            "spatial_energy_abs_diff_grid24_32": _jfloat(
                abs(medium_final["energy"] - coarse_final["energy"])
            ),
            "spatial_new_mode_y_abs_diff_grid24_32": _jfloat(abs(
                complex(*medium_final["new_mode_velocity_y"])
                - complex(*coarse_final["new_mode_velocity_y"])
            )),
            "sampled_core_fraction_grid24_32_abs_diff": _jfloat(abs(
                medium_final["core"]["grid_core_fraction"]
                - coarse_final["core"]["grid_core_fraction"]
            )),
            "all_reference_anchor_core_guarantees": all(
                snap["core"]["true_core_anchor_pair_by_galerkin_max_upper"]
                for snap in fine["diagnostics"]
            ),
            "reference_time_series_shell_sign_persistence": fine[
                "all_initial_shell_transfer_signs_persist"
            ],
        })
    return {
        "experiment": "BSAR-15 dealiased numerical Fourier-Galerkin short-time",
        "source_exact_mathcan": SOURCE_MATHCAN,
        "source_bsa_r": SOURCE_BSAR,
        "viscosity": VISCOSITY,
        "t_end": T_END,
        "phase_matched_roots": len(SCENARIOS) // 2,
        "run_count": len(runs),
        "runs": runs,
        "grid_time_comparisons": comparisons,
        "disclaimer": (
            "Float64 two-thirds dealiased 3D Fourier-Galerkin and RK4; "
            "grid/time comparisons are empirical and provide NO rigorous "
            "infinite-dimensional PDE or cone-integral error bound"
        ),
    }


def freeze(out: Path) -> dict[str, Any]:
    results = campaign()
    out.mkdir(parents=True, exist_ok=True)
    data = json.dumps(
        results["runs"], sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    (out / "runs.json").write_bytes(data)
    (out / "comparisons.json").write_text(
        json.dumps(results["grid_time_comparisons"], sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )
    manifest = {
        key: val for key, val in results.items()
        if key not in ("runs", "grid_time_comparisons")
    }
    manifest["run_sha256"] = hashlib.sha256(data).hexdigest()
    (out / "manifest.json").write_text(
        json.dumps(manifest, sort_keys=True, indent=2) + "\n",
        encoding="utf-8",
    )
    return manifest


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    report = freeze(args.out)
    print(json.dumps(report, sort_keys=True, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
