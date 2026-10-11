/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Sanity.Minimizer

/-!
# The minimizer class sees the Dirichlet energy

A global minimizer of `J(v; B) = ∫_B |∇v|² + 1_{v > 0}` is harmonic in its positivity set. We
check one explicit instance of this: in every dimension `d ≥ 1`, the positive, strictly
subharmonic function `u(x) = 1 + |x|²` is not a global minimizer.

The competitor is `v = max(u, 5/4)`. It agrees with `u` off the ball `B_{1/2}`, it is positive
wherever `u` is, and its gradient vanishes on `B_{1/2}`, where `|∇u| = 2|x| > 0` away from the
origin. So `J(v; B_1) < J(u; B_1)`.

A first-variation argument with a bump, `u + εφ`, would give the general statement for `C²`
functions with `Δu ≠ 0` somewhere in the positivity set; the explicit competitor above avoids the
integration by parts.
-/

open Set Filter Topology MeasureTheory Metric
open scoped Gradient RealInnerProductSpace ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension.Sanity

open EllipticBernoulli

variable {d : ℕ}

/-- The gradient of `x ↦ 1 + ‖x‖²` is `x ↦ 2 x`. -/
theorem gradient_one_add_norm_sq (x : E d) : ∇ (fun y : E d ↦ 1 + ‖y‖ ^ 2) x = (2 : ℝ) • x := by
  refine HasGradientAt.gradient ?_
  rw [hasGradientAt_iff_hasFDerivAt]
  convert ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_add 1 using 1
  ext y
  simp

/-- `x ↦ 1 + ‖x‖²` is in `H¹_loc(ℝᵈ)` with weak gradient `x ↦ 2 x`. -/
theorem memH1Loc_one_add_norm_sq :
    MemH1Loc univ (fun y : E d ↦ 1 + ‖y‖ ^ 2) (fun y ↦ (2 : ℝ) • y) := by
  have h := memH1Loc_gradient_of_contDiff (U := univ) isOpen_univ
    (contDiff_const.add (contDiff_norm_sq ℝ) : ContDiff ℝ 1 fun y : E d ↦ 1 + ‖y‖ ^ 2)
  rwa [show ∇ (fun y : E d ↦ 1 + ‖y‖ ^ 2) = fun y ↦ (2 : ℝ) • y from
    funext gradient_one_add_norm_sq] at h

/-- **Harmonicity is enforced.** In every dimension `d ≥ 1`, the positive subharmonic function
`x ↦ 1 + ‖x‖²` is not a global minimizer. -/
theorem not_isLocalEnergyMinimizer_one_add_norm_sq (hd : 1 ≤ d) :
    ¬ IsLocalEnergyMinimizer univ (fun _ ↦ 1) (fun x : E d ↦ 1 + ‖x‖ ^ 2) := by
  intro hmin
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  set u : E d → ℝ := fun x ↦ 1 + ‖x‖ ^ 2 with hu_def
  set G : E d → E d := fun y ↦ (2 : ℝ) • y with hG_def
  have hu : MemH1Loc univ u G := memH1Loc_one_add_norm_sq
  set m : ℝ := 5 / 4 with hm_def
  have hv := MemH1Loc.max isOpen_univ hu (memH1Loc_const (U := univ) m)
  set v : E d → ℝ := fun y ↦ max (u y) m with hv_def
  set Gv : E d → E d := fun y ↦ if u y < m then 0 else G y with hGv_def
  have hoff : ∀ y ∉ ball (0 : E d) 1, v y = u y := by
    intro y hy
    have h1 : 1 ≤ ‖y‖ := by simpa using hy
    refine max_eq_left ?_
    simp only [hu_def, hm_def]
    nlinarith
  have hle := energyJ_le_of_eqOn_compl hmin hu hv one_pos hoff
  have hupos : ∀ x, 0 < u x := fun x ↦ by positivity
  have hvpos : ∀ x, 0 < v x := fun x ↦ lt_of_lt_of_le (hupos x) (le_max_left _ _)
  have hne0 : ∀ᵐ x : E d, x ≠ 0 := by
    rw [ae_iff]
    simp
  have hmeasG : Measurable G := measurable_const_smul 2
  have hposu : MeasurableSet (posSet u (ball 0 1)) :=
    measurableSet_ball.inter (measurableSet_lt measurable_const
      (continuous_const.add (continuous_norm.pow 2)).measurable)
  have hlt : energyJ (ball 0 1) (fun _ ↦ 1) v Gv < energyJ (ball 0 1) (fun _ ↦ 1) u G := by
    unfold energyJ
    refine lintegral_strict_mono_of_ae_le_of_ae_lt_on (s := ball 0 (1 / 2)) ?_ ?_ ?_ ?_ ?_
    · exact (((hmeasG.norm.pow_const 2).add (measurable_const.mul
        (measurable_const.indicator hposu))).ennreal_ofReal).aemeasurable
    · exact (energyJ_ball_lt_top hv 0 1).ne
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      refine ENNReal.ofReal_le_ofReal ?_
      rw [indicator_of_mem (show x ∈ posSet v (ball 0 1) from ⟨hx, hvpos x⟩),
        indicator_of_mem (show x ∈ posSet u (ball 0 1) from ⟨hx, hupos x⟩)]
      gcongr
      simp only [hGv_def]
      split_ifs <;> simp
    · rw [Measure.restrict_apply' measurableSet_ball,
        inter_eq_left.2 (ball_subset_ball (by norm_num))]
      exact (measure_ball_pos volume 0 (by norm_num)).ne'
    · filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne0] with x hx hx0 hxs
      have hxn : ‖x‖ < 1 / 2 := by simpa using hxs
      have hxp : 0 < ‖x‖ := norm_pos_iff.2 hx0
      have hum : u x < m := by
        simp only [hu_def, hm_def]
        nlinarith
      rw [indicator_of_mem (show x ∈ posSet v (ball 0 1) from ⟨hx, hvpos x⟩),
        indicator_of_mem (show x ∈ posSet u (ball 0 1) from ⟨hx, hupos x⟩)]
      simp only [hGv_def, hum, ite_true, hG_def, norm_zero, norm_smul, Real.norm_two]
      rw [ENNReal.ofReal_lt_ofReal_iff']
      constructor <;> norm_num <;> nlinarith
  exact absurd hle (not_le.2 hlt)

end OnePhaseDimension.Sanity
