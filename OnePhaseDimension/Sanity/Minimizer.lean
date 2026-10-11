/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Statements.Headline
public import OnePhaseDimension.Reduction.HalfSpace
public import OnePhaseDimension.Reduction.OneDim
public import OnePhaseDimension.Reduction.Isometry

/-!
# Sanity checks on the minimizer class: non-vacuity and teeth

The headline theorem is a statement about the class
`IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1)` of global minimizers of the one-phase energy
`J(v; B) = ∫_B |∇v|² + 1_{v > 0}`. This file records elementary facts showing that the class is
neither empty nor too large, and that each hypothesis of the headline theorem is needed.

* Non-vacuity: every half-space solution `x ↦ max ⟪x, e⟫ 0`, `‖e‖ = 1`, is a minimizer, in every
  dimension.
* The weak gradient carried as data is unique almost everywhere, and the energy of an `H¹_loc`
  function on a ball is finite, so the comparison of energies is never `∞ ≤ ∞`.
* Teeth: on the line, the slope of a one-sided linear minimizer is exactly `1` (so the volume
  term has coefficient `1` and the gradient term is `|∇v|²`, not `½|∇v|²`), and the two-sided
  cone `a x₊ + b x₋` is not a minimizer.
* The hypotheses of the headline theorem do work: `0` is a minimizer that is not flat, and the
  translated half-space solution `x ↦ max (⟪x, e⟫ - 1) 0` is a nonzero, nonnegative minimizer that
  is not flat (it is not one-homogeneous).
-/

open Set Filter Topology MeasureTheory Metric
open scoped RealInnerProductSpace ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension.Sanity

open EllipticBernoulli

variable {d : ℕ}

/-! ### Non-vacuity -/

/-- Every half-space solution `x ↦ max ⟪x, e⟫ 0`, `‖e‖ = 1`, is a global minimizer. -/
theorem isLocalEnergyMinimizer_max_inner {e : E d} (he : ‖e‖ = 1) :
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) (fun x ↦ max ⟪x, e⟫ 0) :=
  isLocalEnergyMinimizer_halfSpaceSol he

/-! ### The weak gradient and the energy -/

/-- Weak gradients on `ℝᵈ` are unique almost everywhere. -/
theorem weakGradient_ae_eq {u : E d → ℝ} {G G' : E d → E d} (hG : HasWeakGradient univ u G)
    (hG' : HasWeakGradient univ u G') : G =ᵐ[volume] G' := by
  have h := HasWeakGradient.ae_eq_of_eqOn isOpen_univ isOpen_univ subset_rfl hG hG'
    (fun _ _ ↦ rfl)
  rwa [Measure.restrict_univ] at h

/-- The energy on a ball of an `H¹_loc(ℝᵈ)` function is finite. -/
theorem energyJ_ball_lt_top {u : E d → ℝ} {G : E d → E d} (hu : MemH1Loc univ u G) (x : E d)
    (r : ℝ) : energyJ (ball x r) (fun _ ↦ 1) u G < ⊤ :=
  energyJ_lt_top hu isBounded_ball.isCompact_closure (subset_univ _) (CQ := 1)
    fun _ _ ↦ by simp

/-! ### Teeth on the line -/

/-- A unit vector of `E 1` is `±` the basis vector. -/
theorem isAxisOne_of_norm_eq_one {e : E 1} (he : ‖e‖ = 1) : IsAxisOne e := by
  have habs : |e 0| = 1 := by rw [← norm_eq_abs_one, he]
  have hext : ∀ c : ℝ, e 0 = c → e = c • basisOne := fun c hc ↦ by
    ext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    simp [basisOne, hc]
  rcases abs_eq (zero_le_one' ℝ) |>.1 habs with h | h
  · exact Or.inl (by rw [hext 1 h, one_smul])
  · exact Or.inr (by rw [hext (-1) h, neg_one_smul])

/-- **Slope normalization on the line.** For a unit vector `e` of `E 1` and a slope `s > 0`,
`s ≠ 1`, the one-sided linear function `x ↦ s ⟪x, e⟫₊` is not a global minimizer. -/
theorem not_isLocalEnergyMinimizer_smul_max_inner {e : E 1} (he : ‖e‖ = 1) {s : ℝ} (hs : 0 < s)
    (hs1 : s ≠ 1) : ¬ IsLocalEnergyMinimizer univ (fun _ ↦ 1) (fun x ↦ s * max ⟪x, e⟫ 0) := by
  intro hmin
  have h : (fun x : E 1 ↦ s * max ⟪x, e⟫ 0) = slopeProfile e s 0 := by
    funext x
    rw [slopeProfile, sub_zero, mul_max_of_nonneg _ _ hs.le, mul_zero]
  rw [h] at hmin
  exact hs1 (slope_eq_one (isAxisOne_of_norm_eq_one he) hs hmin)

/-- **The two-sided cone on the line is not a minimizer.** For `a, b > 0`, the function
`x ↦ a x₊ + b x₋` on `E 1` is not a global minimizer. -/
theorem not_isLocalEnergyMinimizer_two_sided {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬ IsLocalEnergyMinimizer univ (fun _ ↦ 1)
      (fun x : E 1 ↦ a * max (x 0) 0 + b * max (-x 0) 0) := by
  have h : (fun x : E 1 ↦ a * max (x 0) 0 + b * max (-x 0) 0) =
      fun x ↦ slopeProfile basisOne a 0 x + slopeProfile (-basisOne) b 0 x := by
    funext x
    simp only [slopeProfile, inner_basisOne, inner_neg_right, sub_zero]
    rw [mul_max_of_nonneg _ _ ha.le, mul_max_of_nonneg _ _ hb.le, mul_zero, mul_zero]
  rw [h]
  exact not_isLocalEnergyMinimizer_two_slopes ha hb

/-! ### The hypotheses of the headline theorem do work -/

/-- The zero function is a global minimizer. -/
theorem isLocalEnergyMinimizer_zero :
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) (fun _ : E d ↦ (0 : ℝ)) := by
  refine ⟨fun _ ↦ 0, memH1Loc_const 0, fun x r _ _ ↦ ⟨memH1Loc_const 0, fun _ _ ↦ rfl,
    fun _ _ ↦ mem_univ _, fun v Gv _ _ _ ↦ ?_⟩⟩
  have h0 : energyJ (ball x r) (fun _ ↦ 1) (fun _ : E d ↦ (0 : ℝ)) (fun _ ↦ 0) = 0 := by
    simp [energyJ, posSet]
  rw [h0]
  exact bot_le

/-- A half-space solution is not almost everywhere equal to a continuous function `f` that
vanishes at `e / 2`. -/
theorem not_ae_eq_max_inner_of_eq_zero {e : E d} (he : ‖e‖ = 1) {f : E d → ℝ}
    (hf : Continuous f) (hf0 : f ((1 / 2 : ℝ) • e) = 0) :
    ¬ ∀ᵐ x ∂(volume : Measure (E d)), f x = max ⟪x, e⟫ 0 := by
  intro h
  have hc : Continuous fun x : E d ↦ max ⟪x, e⟫ 0 :=
    (continuous_id.inner continuous_const).max continuous_const
  have heq := congrFun ((hf.ae_eq_iff_eq volume hc).1 h) ((1 / 2 : ℝ) • e)
  rw [hf0, real_inner_smul_left, real_inner_self_eq_norm_sq, he] at heq
  norm_num at heq

/-- The zero function is not flat. -/
theorem not_flatAE_zero : ¬ FlatAE (fun _ : E d ↦ (0 : ℝ)) := by
  rintro ⟨e, he, h⟩
  exact not_ae_eq_max_inner_of_eq_zero he continuous_const rfl h

/-- The translated half-space solution `x ↦ max (⟪x, e⟫ - 1) 0` is a global minimizer. -/
theorem isLocalEnergyMinimizer_max_inner_sub_one {e : E d} (he : ‖e‖ = 1) :
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) (fun x ↦ max (⟪x, e⟫ - 1) 0) := by
  have h := isLocalEnergyMinimizer_comp_affineIsometry
    (L := LinearIsometryEquiv.refl ℝ (E d)) (c := -e) (isLocalEnergyMinimizer_halfSpaceSol he)
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  convert h using 2 with x
  simp only [halfSpaceSol, LinearIsometryEquiv.coe_refl, id, inner_add_left, inner_neg_left, hee,
    sub_eq_add_neg]

/-- The translated half-space solution is nonzero and not flat. -/
theorem not_ae_eq_zero_and_not_flatAE_max_inner_sub_one {e : E d} (he : ‖e‖ = 1) :
    ¬ (fun x ↦ max (⟪x, e⟫ - 1) 0) =ᵐ[volume] 0 ∧ ¬ FlatAE fun x ↦ max (⟪x, e⟫ - 1) 0 := by
  have hc : Continuous fun x : E d ↦ max (⟪x, e⟫ - 1) 0 :=
    ((continuous_id.inner continuous_const).sub continuous_const).max continuous_const
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  refine ⟨fun h ↦ ?_, ?_⟩
  · have h2 : max (⟪(2 : ℝ) • e, e⟫ - 1) 0 = 0 :=
      congrFun ((hc.ae_eq_iff_eq volume continuous_zero).1 h) ((2 : ℝ) • e)
    rw [real_inner_smul_left, hee] at h2
    norm_num at h2
  · rintro ⟨e', he', h⟩
    refine not_ae_eq_max_inner_of_eq_zero he' hc ?_ h
    have h1 : ⟪e', e⟫ ≤ 1 := by
      have := real_inner_le_norm e' e
      rwa [he, he', one_mul] at this
    rw [real_inner_smul_left]
    exact max_eq_right (by linarith)

end OnePhaseDimension.Sanity
