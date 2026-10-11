/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.DomainVariation
public import OnePhaseDimension.Registry.Regularity

/-!
# Minimizers are variational solutions

A continuous nonnegative local minimizer `u` of the one-phase energy in `ℝᵈ`, `d ≥ 2`, together
with `χ = 1_{u > 0}`, is a variational solution in the sense of Kriventsov–Weiss on every ball:
`u` is locally Lipschitz and smooth in `{u > 0}` by the Lipschitz regularity of minimizers, and
the domain-variation identity is stationarity under domain variations
(`innerVariation_eq_zero_of_isLocalEnergyMinimizer`). The Lipschitz bound of a variational
solution is uniform on its domain, which is why the statement is on balls.

## Main results

* `isVariationalSolution_of_isLocalEnergyMinimizer`

## References

* D. Kriventsov and G. S. Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
  non-minimizing Bernoulli free boundaries*, Comm. Pure Appl. Math. 78 (2025), no. 3, 545–591;
  arXiv:2306.10131 (Section 3.2).
-/

open Set Filter Topology Metric MeasureTheory
open scoped ContDiff NNReal

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ}

/-- A continuous nonnegative global minimizer in `ℝᵈ`, `d ≥ 2`, is locally Lipschitz and smooth in
its positivity set. -/
theorem locallyLipschitz_and_contDiffOn_of_isLocalEnergyMinimizer (hd : 2 ≤ d) {u : E d → ℝ}
    (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) :
    LocallyLipschitz u ∧ ContDiffOn ℝ ∞ u {x | 0 < u x} := by
  obtain ⟨v, hvu, hlip, -, hsmooth, -⟩ :=
    Registry.exists_continuous_representative hd (Eventually.of_forall hnn) hmin
  have hv : v = u := (Continuous.ae_eq_iff_eq volume hlip.continuous hc).1 hvu
  subst hv
  exact ⟨hlip, hsmooth⟩

/-- **Minimizers are variational solutions.** A continuous nonnegative global minimizer `u` in
`ℝᵈ`, `d ≥ 2`, together with `χ = 1_{u > 0}`, is a variational solution on every ball, with some
constant. -/
theorem isVariationalSolution_of_isLocalEnergyMinimizer (hd : 2 ≤ d) {u : E d → ℝ}
    (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (x₀ : E d) (R : ℝ) :
    ∃ C : ℝ≥0, InnerVariational.IsVariationalSolution (ball x₀ R) C u
      (InnerVariational.posIndicator u) := by
  obtain ⟨hlip, hsmooth⟩ :=
    locallyLipschitz_and_contDiffOn_of_isLocalEnergyMinimizer hd hc hnn hmin
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall x₀ R) (hlip.locallyLipschitzOn (s := closedBall x₀ R))
  have hpos : IsOpen {x | 0 < u x} := isOpen_lt continuous_const hc
  have hχ : Measurable (InnerVariational.posIndicator u) :=
    measurable_const.indicator hpos.measurableSet
  refine ⟨C, ⟨isOpen_ball, fun x _ ↦ hnn x, hc.continuousOn, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (hsmooth.of_le (WithTop.coe_le_coe.2 le_top)).mono inter_subset_right
  · exact fun x r hr ↦ hC.mono (hr.trans ball_subset_closedBall)
  · exact hχ.indicator isOpen_ball.measurableSet
  · intro x _
    by_cases h : 0 < u x
    · exact Or.inr (InnerVariational.posIndicator_of_pos h)
    · exact Or.inl (InnerVariational.posIndicator_of_nonpos (not_lt.1 h))
  · exact Eventually.of_forall fun x ↦ le_rfl
  · rintro ξ ⟨hξL, hξc, -⟩
    exact innerVariation_eq_zero_of_isLocalEnergyMinimizer hlip hmin hξL hξc

end OnePhaseDimension
