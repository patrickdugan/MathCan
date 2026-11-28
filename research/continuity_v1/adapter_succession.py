"""Exact-rational, conditional margin receipts for successive adapter updates.

The proof obligation comes from a pointwise Taylor/Hessian bound along each
ACTUAL sequential step. These declared local bounds are not measured neural
certificates. The previous step's output is the next step's starting point.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence


def exact(value: Fraction | int | str) -> Fraction:
    if isinstance(value, float):
        raise TypeError("floating point is not an exact certificate input")
    if not isinstance(value, (Fraction, int, str)):
        raise TypeError("expected Fraction, int or rational string")
    return Fraction(value)


@dataclass(frozen=True)
class AdapterStep:
    source: str
    destination: str
    before: Fraction
    after: Fraction
    gradient_dot_step: Fraction
    hessian_norm_cap: Fraction
    squared_step_norm: Fraction

    def loss_cap(self) -> Fraction:
        h, n = exact(self.hessian_norm_cap), exact(self.squared_step_norm)
        if h < 0 or n < 0:
            raise ValueError("Hessian bound and squared displacement norm must be nonnegative")
        return abs(exact(self.gradient_dot_step)) + h * n / 2

    def realized_loss(self) -> Fraction:
        return exact(self.before) - exact(self.after)

    def validate(self) -> None:
        if not self.source or not self.destination or self.source == self.destination:
            raise ValueError("step requires distinct nonempty checkpoint IDs")
        if self.realized_loss() > self.loss_cap():
            raise ValueError("observed step violates its declared Taylor bound")


@dataclass(frozen=True)
class SuccessionResult:
    initial_margin: Fraction
    terminal_margin: Fraction
    total_declared_loss: Fraction
    realized_loss: Fraction
    residual_slack: Fraction
    conditionally_preserves_positive: bool
    actually_positive: bool
    checkpoint_path: tuple[str, ...]

    def public(self) -> dict[str, object]:
        return {
            "initial_margin": str(self.initial_margin),
            "terminal_margin": str(self.terminal_margin),
            "total_declared_loss": str(self.total_declared_loss),
            "realized_loss": str(self.realized_loss),
            "residual_slack": str(self.residual_slack),
            "conditionally_preserves_positive": self.conditionally_preserves_positive,
            "actually_positive": self.actually_positive,
            "checkpoint_path": list(self.checkpoint_path),
            "assurance": "declared-local-bounds; neural Hessian premise is unverified",
        }


def audit_succession(steps: Sequence[AdapterStep]) -> SuccessionResult:
    """Verify exact arithmetic and cumulative budget for a fixed protected margin.

    For every step i, the *assumed* Taylor bound is
      m_i - m_(i+1) <= abs(grad_i . delta_i) + H_i ||delta_i||^2/2.
    The function checks numeric consistency with supplied margins, and adds
    the per-step bounds. It cannot certify the Hessian cap against a model.
    """
    if not steps:
        raise ValueError("at least one adapter step required")
    checkpoints = [steps[0].source]
    cumulative = Fraction(0)
    for i, step in enumerate(steps):
        step.validate()
        if i and (steps[i-1].destination != step.source or
                  exact(steps[i-1].after) != exact(step.before)):
            raise ValueError("checkpoint or margin discontinuity")
        cumulative += step.loss_cap()
        checkpoints.append(step.destination)
    initial = exact(steps[0].before)
    terminal = exact(steps[-1].after)
    realized = initial - terminal
    if realized > cumulative:
        raise AssertionError("telescoping inequality violated")
    preserve = initial > cumulative
    if preserve and terminal <= 0:
        raise AssertionError("positive-margin theorem violated")
    return SuccessionResult(initial, terminal, cumulative, realized,
                            cumulative-realized, preserve, terminal > 0,
                            tuple(checkpoints))


def bilinear_margin(a: Fraction | int, b: Fraction | int) -> Fraction:
    """m(a,b) = 1/4 - ab; each isolated unit edit has no effect."""
    return Fraction(1, 4) - exact(a) * exact(b)


def bilinear_step(source: str, destination: str,
                  old: tuple[int, int], new: tuple[int, int]) -> AdapterStep:
    """An exact witness: Hessian operator norm is one for m(a,b)=1/4-ab."""
    da, db = exact(new[0]-old[0]), exact(new[1]-old[1])
    gradient_dot = -exact(old[1])*da - exact(old[0])*db
    return AdapterStep(source, destination,
                       bilinear_margin(*old), bilinear_margin(*new),
                       gradient_dot, Fraction(1), da*da+db*db)
