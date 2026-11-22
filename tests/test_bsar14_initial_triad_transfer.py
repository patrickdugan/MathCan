"""BSAR-14 exact initial NSE triad, Leray pressure and direction-core gates."""

from __future__ import annotations

import json
import tempfile
import unittest
from collections import defaultdict
from fractions import Fraction as Q
from pathlib import Path

from scripts.bsar10_beltrami_energy_audit import G, ZERO, gauss_dot
from scripts.bsar14_initial_triad_transfer import (
    BASES,
    EXPONENT_QUARTERS,
    PHASES,
    VISCOSITIES,
    audit,
    convolution,
    encode,
    exact_certificate,
    exact_point,
    generate,
    inner_real,
    kminus,
    modes,
    pressure_projection,
    root_bounds,
    vortex_stretching,
)


class TestBSAR14InitialTriad(unittest.TestCase):
    def test_four_real_mode_pairs_and_divergence(self):
        for n in (1, 2, 7, 31):
            for phase in PHASES:
                original = modes(n, Q(1, 3), phase)
                self.assertEqual(len(original), 8)
                self.assertNotIn((0, 0, 0), original)
                self.assertEqual(
                    {tuple(abs(v) for v in k) for k in original},
                    {(n, 0, 0), (0, 2*n, 0), (n, 2*n, 0), (0, 0, n)},
                )
                for k, v in original.items():
                    self.assertEqual(v[2], ZERO)
                    self.assertEqual(gauss_dot(v, k), ZERO)
                    other = original[kminus(k)]
                    self.assertTrue(all(x.real == y.real and x.imag == -y.imag
                                        for x, y in zip(v, other)))

    def test_non_gradient_convective_term_and_poisson_projection(self):
        for phase in PHASES:
            given = modes(1, Q(1), phase)
            conv = convolution(given)
            p, projected = pressure_projection(conv)
            self.assertTrue(any(x != (ZERO, ZERO, ZERO) for x in projected.values()))
            self.assertEqual(conv.get((0, 0, 0)), (ZERO, ZERO, ZERO))
            self.assertEqual(
                projected[(1, 0, 1)],
                (ZERO, G(Q(0), Q(1, 4)), ZERO),
            )
            self.assertEqual(p.get((1, 0, 1), ZERO), ZERO)
            self.assertEqual(
                -inner_real(given[(1, 2, 0)], projected[(1, 2, 0)]),
                Q(phase*3, 8),
            )
            self.assertTrue(all(gauss_dot(value, k) == ZERO
                                for k, value in projected.items()))

    def test_exact_shell_nonlinear_energy_flux_conserves_total(self):
        for m, q, phase in (
            (2, 0, 1), (2, 0, -1), (3, 1, 1),
            (5, 2, -1), (8, 3, 1), (32, 4, -1),
        ):
            row = exact_certificate(m, q, Q(1, 10), phase)
            n, amp = row["frequency_N"], Q(row["amplitude_A"])
            factor = amp**3*n
            flux = {int(k): Q(v) for k, v in row["shell_nonlinear_transfer"].items()}
            self.assertEqual(flux, {
                1: phase*factor/4,
                4: -phase*factor,
                5: phase*3*factor/4,
            })
            self.assertEqual(sum(flux.values()), 0)
            self.assertEqual(
                Q(row["enstrophy_density_initial"]), Q(31, 2)*amp*amp*n*n
            )
            self.assertEqual(
                Q(row["viscous_total_energy_derivative_initial"]),
                -Q(1, 10)*Q(31, 2)*amp*amp*n*n,
            )
            self.assertEqual(
                sum(Q(v) for v in row["shell_total_derivative"].values()),
                Q(row["viscous_total_energy_derivative_initial"]),
            )
            self.assertEqual(row["new_3D_mode"], [n, 0, n])
            self.assertEqual(
                Q(row["new_3D_mode_solenoidal_derivative_y"]), -amp*amp*n/4
            )

    def test_nonzero_vortex_stretching_and_high_core_pair(self):
        for phase in PHASES:
            n, amp = 7, Q(3, 5)
            coeff = modes(n, amp, phase)
            first = exact_point(coeff, n, x_pi_over_n=False)
            second = exact_point(coeff, n, x_pi_over_n=True)
            w0, w1 = first["vorticity"], second["vorticity"]
            self.assertEqual(w0, (ZERO, G(-amp*n), G(-5*phase*amp*n)))
            self.assertEqual(w1, (ZERO, G(-amp*n), G(5*phase*amp*n)))
            self.assertEqual(inner_real(w0, w0), 26*amp*amp*n*n)
            self.assertEqual(inner_real(w1, w1), 26*amp*amp*n*n)
            self.assertEqual(
                vortex_stretching(w0, first["gradient"]),
                (G(phase*amp*amp*n*n), G(2*phase*amp*amp*n*n), ZERO),
            )
            row = exact_certificate(2, 0, Q(1, 100), phase)
            self.assertEqual(Q(row["anchor_direction_difference_sq"]), Q(50, 13))
            self.assertEqual(
                Q(row["initial_cone_K_lower"]),
                Q(25, 26)*row["frequency_N"],
            )
            self.assertEqual(
                Q(row["initial_cone_K_upper"]), 26*row["frequency_N"]
            )
            self.assertEqual(row["convection_is_not_pure_gradient"], True)

    def test_phase_flip_changes_transfer_direction_but_not_energy(self):
        for m, q, nu in ((2, 0, Q(1)), (3, 2, Q(1, 100)), (8, 4, Q(1, 10))):
            positive = exact_certificate(m, q, nu, 1)
            negative = exact_certificate(m, q, nu, -1)
            self.assertEqual(
                positive["shell_energy"], negative["shell_energy"]
            )
            self.assertEqual(
                positive["enstrophy_density_initial"],
                negative["enstrophy_density_initial"],
            )
            self.assertEqual(
                positive["Hs_squared_lower"], negative["Hs_squared_lower"]
            )
            self.assertEqual(
                positive["Hs_squared_upper"], negative["Hs_squared_upper"]
            )
            self.assertEqual(
                positive["anchor_direction_difference_sq"],
                negative["anchor_direction_difference_sq"],
            )
            self.assertEqual(
                positive["new_3D_mode_solenoidal_derivative_y"],
                negative["new_3D_mode_solenoidal_derivative_y"],
            )
            for key, value in positive["shell_nonlinear_transfer"].items():
                self.assertEqual(Q(value), -Q(negative["shell_nonlinear_transfer"][key]))
            self.assertEqual(positive["energy_transfer_direction"], "shell4_loses")
            self.assertEqual(negative["energy_transfer_direction"], "shell4_gains")

    def test_homogeneous_quarter_sobolev_enclosures(self):
        for q in EXPONENT_QUARTERS:
            lower, upper = root_bounds(q)
            self.assertLessEqual(Q(4), lower)
            self.assertLessEqual(lower, upper)
            self.assertLessEqual(upper, Q(31, 2))
        self.assertEqual(root_bounds(0), (Q(4), Q(4)))
        self.assertEqual(root_bounds(4), (Q(31, 2), Q(31, 2)))
        for m in BASES:
            for q in EXPONENT_QUARTERS:
                plus = exact_certificate(m, q, Q(1), 1)
                self.assertEqual(Q(plus["Hs_squared_lower"]), root_bounds(q)[0])
                self.assertEqual(Q(plus["Hs_squared_upper"]), root_bounds(q)[1])

    def test_invalid_arguments_and_divergence_control(self):
        for n, amp, phase in (
            (0, Q(1), 1), (1, Q(0), 1), (1, Q(1), 0),
            (1, Q(1), 2), (1, Q(-1), -1),
        ):
            with self.assertRaises(ValueError):
                modes(n, amp, phase)
        bad = dict(modes(1, Q(1), 1))
        bad[(1, 0, 0)] = (G(Q(1)), G(Q(1, 2)), ZERO)
        self.assertNotEqual(gauss_dot(bad[(1, 0, 0)], (1, 0, 0)), ZERO)
        with self.assertRaises(ValueError):
            exact_certificate(2, 0, Q(0), 1)
        with self.assertRaises(ValueError):
            root_bounds(5)

    def test_corpus_determinism_and_paired_phase_custody(self):
        rows, manifest = generate()
        self.assertEqual(len(rows), 360)
        self.assertEqual(manifest["phase_matched_pairs"], 180)
        self.assertEqual(manifest["cases"], 360)
        self.assertEqual(rows, generate()[0])
        self.assertEqual(manifest, generate()[1])
        grouped = defaultdict(list)
        for row in rows:
            grouped[row["pair_id"]].append(row)
        self.assertEqual(len(grouped), 180)
        for pair in grouped.values():
            self.assertEqual({r["phase_sigma"] for r in pair}, {-1, 1})
            self.assertEqual(len({r["Hs_squared_lower"] for r in pair}), 1)
            self.assertEqual(len({r["kinetic_energy_density_initial"] for r in pair}), 1)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "cases.jsonl").write_text(
                "".join(json.dumps(x, sort_keys=True)+"\n" for x in rows),
                encoding="utf-8",
            )
            (root / "manifest.json").write_text(
                json.dumps(manifest, sort_keys=True), encoding="utf-8",
            )
            self.assertEqual(audit(root), manifest)
            damaged = [dict(x) for x in rows]
            damaged[0]["shell_nonlinear_transfer"] = {"1": encode(Q(0))}
            (root / "cases.jsonl").write_text(
                "".join(json.dumps(x, sort_keys=True)+"\n" for x in damaged),
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "changed"):
                audit(root)


if __name__ == "__main__":
    unittest.main()
