/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Variational
public import InnerVariational.Monotonicity.Density

/-!
# Blowup limits of minimizers are one-homogeneous

Every blowup limit of a continuous nonnegative global minimizer of the one-phase energy is
one-homogeneous. A minimizer is a variational solution in the sense of Kriventsov–Weiss on every
ball (`isVariationalSolution_of_isLocalEnergyMinimizer`), and blowup limits of variational
solutions are one-homogeneous by the Weiss monotonicity formula
(`InnerVariational.IsVariationalSolution.blowup_homogeneous`). The blowup `u(x₀ + r y)/r` used
here is the rescaling of Kriventsov–Weiss, equation (3.6).

## Differences from the source

The 2026-09-24 version cites the Weiss monotonicity formula for minimizers (Velichkov,
Proposition 9.12). We use the monotonicity formula for variational solutions, and prove that
minimizers are variational solutions through stationarity under domain variations.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
* G. S. Weiss, *Partial regularity for a minimum problem with free boundary*, J. Geom. Anal. 9
  (1999).
* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131 (Propositions 3.4 and 3.5).
-/

open Set Filter Topology Metric

@[expose] public section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ}

/-- The blowup `u(x₀ + r ·)/r` is the one-homogeneous rescaling of Kriventsov–Weiss. -/
theorem blowup_eq_oneHomRescale (u : E d → ℝ) (x₀ : E d) (r : ℝ) :
    blowup u x₀ r = InnerVariational.oneHomRescale u x₀ r :=
  rfl

/-- **Blowup limits are one-homogeneous.** Every blowup limit of a continuous nonnegative global
minimizer of the one-phase energy in `ℝᵈ`, `d ≥ 2`, is homogeneous of degree one. The free
boundary hypothesis is not needed: a locally uniform limit of the blowups forces `u(x₀) = 0`. -/
theorem blowup_limit_oneHomogeneous_proof {d : ℕ} (hd : 2 ≤ d) {u : E d → ℝ} (hc : Continuous u)
    (hnn : ∀ x, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u)
    {x₀ : E d} (_hx₀ : x₀ ∈ freeBoundary u Set.univ) {U₀ : E d → ℝ}
    (hU₀ : IsBlowupLimit u x₀ U₀) :
    ∀ r : ℝ, 0 < r → ∀ y, U₀ (r • y) = r * U₀ y := by
  have : NeZero d := ⟨by omega⟩
  obtain ⟨C, hsol⟩ := isVariationalSolution_of_isLocalEnergyMinimizer hd hc hnn hmin x₀ 1
  obtain ⟨r, hr, hr0, hconv⟩ := hU₀
  exact hsol.blowup_homogeneous (mem_ball_self one_pos) hr hr0 hconv

end OnePhaseDimension
