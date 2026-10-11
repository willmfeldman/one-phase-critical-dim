/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Basic

/-!
# The headline statement

Every nonzero, nonnegative, one-homogeneous global minimizer of the one-phase Bernoulli energy
`J(v; B) = ∫_B |∇v|² + 1_{v > 0}` in `ℝᵈ`, `1 ≤ d ≤ 6`, is flat: `u(x) = (x · e)₊` for a unit
vector `e`.

Minimality is `IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u` with `u ≥ 0` almost everywhere
(see the module docstring of `OnePhaseDimension.Basic` for the competitor class).
One-homogeneity is assumed almost everywhere for each dilation factor, as in the source, and
flatness and "nonzero" are understood almost everywhere, as statements about Sobolev classes.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open MeasureTheory

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-- One-homogeneity almost everywhere, for each dilation factor: for every `r > 0`,
`u (r x) = r u x` for almost every `x`. -/
def OneHomogeneousAE {d : ℕ} (u : E d → ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ᵐ x ∂(volume : Measure (E d)), u (r • x) = r * u x

/-- Flatness almost everywhere: `u x = max ⟪x, e⟫ 0` for almost every `x`, for some unit
vector `e`. -/
def FlatAE {d : ℕ} (u : E d → ℝ) : Prop :=
  ∃ e : E d, ‖e‖ = 1 ∧ ∀ᵐ x ∂(volume : Measure (E d)), u x = max (inner ℝ x e) 0

/-- Every nonzero, nonnegative, one-homogeneous global minimizer of the one-phase energy in
`ℝᵈ`, `1 ≤ d ≤ 6`, is flat. -/
def HeadlineStatement : Prop :=
  ∀ (d : ℕ), 1 ≤ d → d ≤ 6 → ∀ u : E d → ℝ,
    (∀ᵐ x ∂(volume : Measure (E d)), 0 ≤ u x) →
    IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u →
    OneHomogeneousAE u → ¬ (u =ᵐ[volume] 0) → FlatAE u

end OnePhaseDimension
