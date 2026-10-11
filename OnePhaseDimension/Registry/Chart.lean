/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Connected.Basic
public import EllipticBernoulli.Hodograph.Chart

/-!
# Smooth one-sided charts at regular points

If a continuous nonnegative global minimizer of the one-phase energy has a half-space blowup at
a free boundary point `x₀`, then near `x₀` it is the positive part of a smooth function `F` with
nonvanishing gradient, `|∇F| = 1` on `{F = 0}`, `F` harmonic on `{F > 0}`, and `{F > 0}`
connected in a small ball. It is proved in elliptic-bernoulli-foundations
(`chart_of_flat_blowup_univ`).

The chart combines: the `C^{1,α}` regularity of the free boundary from a flat blowup, the
viscosity free boundary condition, higher regularity up to the free boundary, boundary regularity
for harmonic functions with zero Dirichlet data, and a smooth extension across the free boundary
of the positive side.

## References

* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer (2023), Theorem 8.1, Corollary 8.2, Proposition 7.1.
* D. De Silva, F. Ferrari, S. Salsa, *Regularity of higher order in two-phase free boundary
  problems*, Trans. Amer. Math. Soc. 371 (2019), Theorem 1.1 and Corollary 1.2.
* D. Kinderlehrer, L. Nirenberg, *Regularity in free boundary problems*, Ann. Sc. Norm. Super.
  Pisa Cl. Sci. (4) 4 (1977).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Classics in Mathematics, Springer (2001), Chapter 6 (boundary regularity for harmonic functions
  with zero Dirichlet data).
* R. T. Seeley, *Extension of `C^∞` functions defined in a half space*, Proc. Amer. Math. Soc. 15
  (1964).
-/

open Metric
open scoped ContDiff Gradient Laplacian

@[expose] public section

namespace OnePhaseDimension.Registry

open EllipticBernoulli

/-- A half-space blowup at `x₀` gives a smooth one-sided chart on a ball around `x₀`:
`u = max F 0` with `F` smooth, `∇F ≠ 0`, `|∇F| = 1` on `{F = 0}`, `ΔF = 0` on `{F > 0}`, and
`{F > 0}` connected in the ball (Velichkov 2023, Theorem 8.1, Corollary 8.2, Proposition 7.1;
De Silva–Ferrari–Salsa 2019, Theorem 1.1 and Corollary 1.2; Kinderlehrer–Nirenberg 1977;
Gilbarg–Trudinger 2001, Chapter 6, for boundary regularity of the harmonic positive part; Seeley
1964 for the extension across the free boundary). -/
theorem chart_of_flat_blowup {d : ℕ} (hd : 2 ≤ d) {u : E d → ℝ} (hc : Continuous u)
    (hnn : ∀ x, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u)
    {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u Set.univ) {e : E d} (he : ‖e‖ = 1)
    (hU₀ : IsBlowupLimit u x₀ (fun y ↦ max (inner ℝ y e) 0)) :
    ∃ ρ > 0, ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F (ball x₀ ρ) ∧
      (∀ x ∈ ball x₀ ρ, u x = max (F x) 0) ∧
      (∀ x ∈ ball x₀ ρ, ∇ F x ≠ 0) ∧
      (∀ x ∈ ball x₀ ρ, F x = 0 → ‖∇ F x‖ = 1) ∧
      (∀ x ∈ ball x₀ ρ, 0 < F x → Δ F x = 0) ∧
      IsPreconnected {x ∈ ball x₀ ρ | 0 < F x} := by
  exact chart_of_flat_blowup_univ hd hc hnn hmin hx₀ he hU₀

end OnePhaseDimension.Registry
