/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.BoundaryJets
public import OnePhaseDimension.Vendor.TauCeti.Analysis.InnerProductSpace.Laplacian.HopfLemma

/-!
# The interior ball and the Hopf lemma at a regular free-boundary point

Let `F` be smooth on an open set `U ∋ x₀`, with `F(x₀) = 0`, `|∇F| = 1` on `{F = 0}` and `F`
harmonic on `{F > 0}`.

* `exists_sq_bound_sub_fderiv`: a `C²` function satisfies
  `|F(x) - F(x₀) - DF(x₀)(x - x₀)| ≤ K |x - x₀|²` near `x₀`.
* `exists_interior_ball`: the interior ball. If `F(x₀) = 0` and `|∇F(x₀)| = 1`, then for small
  `r > 0` the closed ball of radius `r` about `x₀ + r ∇F(x₀)` lies in `{F > 0} ∪ {x₀}`.
* `contDiffAt_gradient`: the gradient of a `C^{k+1}` function is `Cᵏ`.
* `fderiv_normSq_gradient_apply_eq`: `D|∇F|²(x)[a] = 2 D²F(x)[a, ∇F(x)]`.
* `hessian_gradient_neg_of_chart`: **Hopf.** If moreover `|∇F| < 1` on `{F > 0}`, then
  `D²F(x₀)[N, N] < 0` for `N = ∇F(x₀)`, i.e. the mean curvature `H = -D²F(x₀)[N, N]` is positive.
  The subharmonic function `|∇F|²` (Bochner: `Δ|∇F|² = 2|D²F|²` where `F` is harmonic) attains
  its strict maximum `1` over the interior ball at `x₀`, so the Hopf lemma gives
  `D|∇F|²(x₀)[-N] > 0`.
-/

open Function Filter Topology Set Metric Laplacian EllipticBernoulli
open scoped ContDiff RealInnerProductSpace Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

section Ball

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- **Second-order Taylor bound.** A function that is `C²` at `x₀` satisfies
`|F(x) - F(x₀) - DF(x₀)(x - x₀)| ≤ K |x - x₀|²` on a ball about `x₀`. -/
theorem exists_sq_bound_sub_fderiv {F : E → ℝ} {x₀ : E} (hF : ContDiffAt ℝ 2 F x₀) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ ρ > 0, ∀ x ∈ ball x₀ ρ,
      |F x - F x₀ - fderiv ℝ F x₀ (x - x₀)| ≤ K * ‖x - x₀‖ ^ 2 := by
  obtain ⟨K, t, ht, hK⟩ := (hF.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  have hd : ∀ᶠ y in 𝓝 x₀, DifferentiableAt ℝ F y :=
    (hF.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by norm_num)
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem ht hd)
  refine ⟨K, K.2, ρ, hρ, fun x hx ↦ ?_⟩
  set g : E → ℝ := fun y ↦ F y - fderiv ℝ F x₀ y with hg
  have hsub : closedBall x₀ ‖x - x₀‖ ⊆ ball x₀ ρ :=
    closedBall_subset_ball (by rwa [← dist_eq_norm, ← mem_ball])
  have hgd : ∀ y ∈ closedBall x₀ ‖x - x₀‖,
      HasFDerivAt g (fderiv ℝ F y - fderiv ℝ F x₀) y := fun y hy ↦
    (hball (hsub hy)).2.hasFDerivAt.sub (fderiv ℝ F x₀).hasFDerivAt
  have hbound : ∀ y ∈ closedBall x₀ ‖x - x₀‖, ‖fderiv ℝ g y‖ ≤ K * ‖x - x₀‖ := fun y hy ↦ by
    rw [(hgd y hy).fderiv]
    calc ‖fderiv ℝ F y - fderiv ℝ F x₀‖ ≤ K * ‖y - x₀‖ :=
          hK.norm_sub_le (hball (hsub hy)).1 (hball (mem_ball_self hρ)).1
      _ ≤ K * ‖x - x₀‖ := by
          gcongr
          rwa [mem_closedBall, dist_eq_norm] at hy
  have key := (convex_closedBall x₀ ‖x - x₀‖).norm_image_sub_le_of_norm_fderiv_le
    (fun y hy ↦ (hgd y hy).differentiableAt) hbound (mem_closedBall_self (norm_nonneg _))
    (by rw [mem_closedBall, dist_eq_norm])
  have hgx : g x - g x₀ = F x - F x₀ - fderiv ℝ F x₀ (x - x₀) := by
    simp only [hg, map_sub]
    ring
  rw [hgx, Real.norm_eq_abs] at key
  calc _ ≤ K * ‖x - x₀‖ * ‖x - x₀‖ := key
    _ = K * ‖x - x₀‖ ^ 2 := by ring

/-- The gradient of a `C^{k+1}` function is `Cᵏ`. -/
theorem contDiffAt_gradient {F : E → ℝ} {x : E} {k : ℕ} (hF : ContDiffAt ℝ (k + 1 : ℕ) F x) :
    ContDiffAt ℝ k (∇ F) x := by
  have h1 : ContDiffAt ℝ k (fderiv ℝ F) x := hF.fderiv_right (by push_cast; exact le_rfl)
  have : ∇ F = fun z ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ F z) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp x h1

/-- **The interior ball.** If `F` is `C²` at a zero `x₀` with `|∇F(x₀)| = 1`, then for every
neighbourhood `V` of `x₀` there is `r > 0` such that the closed ball of radius `r` about
`x₀ + r ∇F(x₀)` lies in `V`, and `F > 0` on it except at `x₀`. -/
theorem exists_interior_ball {F : E → ℝ} {x₀ : E} (hF : ContDiffAt ℝ 2 F x₀) (hF0 : F x₀ = 0)
    (hN : ‖∇ F x₀‖ = 1) {V : Set E} (hV : V ∈ 𝓝 x₀) :
    ∃ r > 0, closedBall (x₀ + r • ∇ F x₀) r ⊆ V ∧
      ∀ x ∈ closedBall (x₀ + r • ∇ F x₀) r, x ≠ x₀ → 0 < F x := by
  obtain ⟨K, hK, ρ, hρ, hT⟩ := exists_sq_bound_sub_fderiv hF
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.1 hV
  set N := ∇ F x₀
  set r : ℝ := min (min (ρ / 4) (ε / 4)) (1 / (4 * (K + 1))) with hr
  have hr0 : 0 < r := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hrρ : r ≤ ρ / 4 := (min_le_left _ _).trans (min_le_left _ _)
  have hrε : r ≤ ε / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hrK : r ≤ 1 / (4 * (K + 1)) := min_le_right _ _
  have hrK' : 2 * r * K < 1 := by
    have h1 : r * (4 * (K + 1)) ≤ 1 := by
      rwa [le_div_iff₀ (by positivity)] at hrK
    nlinarith
  -- Points of the ball are within `2r` of `x₀`, and `|x - x₀|² ≤ 2r⟨N, x - x₀⟩`.
  have hnear : ∀ x ∈ closedBall (x₀ + r • N) r, ‖x - x₀‖ ≤ 2 * r ∧
      ‖x - x₀‖ ^ 2 ≤ 2 * r * ⟪N, x - x₀⟫ := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    have hx' : ‖(x - x₀) - r • N‖ ≤ r := by
      rwa [show x - x₀ - r • N = x - (x₀ + r • N) by abel]
    have hrN : ‖r • N‖ = r := by rw [norm_smul, hN, mul_one, Real.norm_of_nonneg hr0.le]
    constructor
    · calc ‖x - x₀‖ = ‖(x - x₀ - r • N) + r • N‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - x₀ - r • N‖ + ‖r • N‖ := norm_add_le _ _
        _ ≤ 2 * r := by rw [hrN]; linarith
    · have h2 := norm_sub_sq_real (x - x₀) (r • N)
      rw [hrN, real_inner_smul_right, real_inner_comm] at h2
      have h3 : ‖x - x₀ - r • N‖ ^ 2 ≤ r ^ 2 := by
        have := norm_nonneg (x - x₀ - r • N)
        nlinarith
      nlinarith
  refine ⟨r, hr0, fun x hx ↦ hεV ?_, fun x hx hne ↦ ?_⟩
  · rw [mem_ball, dist_eq_norm]
    linarith [(hnear x hx).1]
  · obtain ⟨h1, h2⟩ := hnear x hx
    have hxρ : x ∈ ball x₀ ρ := by rw [mem_ball, dist_eq_norm]; linarith
    have hT' := hT x hxρ
    rw [hF0, sub_zero, fderiv_apply_eq_inner_gradient] at hT'
    have hpos : 0 < ‖x - x₀‖ ^ 2 := by
      have : x - x₀ ≠ 0 := sub_ne_zero.2 hne
      positivity
    have hlow : ⟪N, x - x₀⟫ - K * ‖x - x₀‖ ^ 2 ≤ F x := by
      have := neg_abs_le (F x - ⟪N, x - x₀⟫)
      linarith
    -- `2r F(x) ≥ |x - x₀|² (1 - 2rK) > 0`.
    have : 0 < 2 * r * F x := by nlinarith
    exact pos_of_mul_pos_right this (by positivity)

end Ball

section Hopf

variable {n : ℕ}

/-- `D|∇F|²(x)[a] = 2 D²F(x)[a, ∇F(x)]`. -/
theorem fderiv_normSq_gradient_apply_eq {F : E n → ℝ} {x : E n} (hF : ContDiffAt ℝ 2 F x)
    (a : E n) :
    fderiv ℝ (fun y ↦ ‖∇ F y‖ ^ 2) x a = 2 * iteratedFDeriv ℝ 2 F x ![a, ∇ F x] := by
  set e := stdOrthonormalBasis ℝ (E n)
  have hfun : (fun y ↦ ‖∇ F y‖ ^ 2) = jetNormSq e 1 F := funext fun y ↦ (jetNormSq_one e F y).symm
  rw [hfun, fderiv_jetNormSq_one_apply e hF]
  simp only [iteratedFDeriv_one_apply, iteratedFDeriv_two_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [sum_fderiv_mul_apply e F x (fderiv ℝ (fderiv ℝ F) x a)]

/-- `|∇F|²` is subharmonic where `F` is harmonic: `Δ|∇F|² = 2|D²F|² ≥ 0`. -/
theorem laplacian_normSq_gradient_nonneg {F : E n → ℝ} {x : E n}
    (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 F y) (hΔ : ∀ᶠ y in 𝓝 x, Δ F y = 0) :
    0 ≤ Δ (fun y ↦ ‖∇ F y‖ ^ 2) x := by
  rw [laplacian_normSq_gradient_eq (stdOrthonormalBasis ℝ (E n)) hF hΔ]
  exact mul_nonneg zero_le_two (jetNormSq_nonneg _ _ _ _)

/-- **Hopf at a regular free-boundary point.** Let `F` be smooth on an open set `U ∋ x₀`, with
`F(x₀) = 0`, `|∇F| = 1` on `{F = 0}`, `F` harmonic on `{F > 0}`, and `|∇F| < 1` on `{F > 0}`.
Then `D²F(x₀)[N, N] < 0` for `N = ∇F(x₀)`. -/
theorem hessian_gradient_neg_of_chart {F : E n → ℝ} {U : Set (E n)} {x₀ : E n} (hU : IsOpen U)
    (hx₀ : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hF0 : F x₀ = 0)
    (hgrad : ∀ x ∈ U, F x = 0 → ‖∇ F x‖ = 1) (hΔ : ∀ x ∈ U, 0 < F x → Δ F x = 0)
    (hlt : ∀ x ∈ U, 0 < F x → ‖∇ F x‖ < 1) :
    iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] < 0 := by
  have hFat : ∀ k : ℕ, ∀ y ∈ U, ContDiffAt ℝ k F y := fun k y hy ↦
    (hF.contDiffAt (hU.mem_nhds hy)).of_le (natCast_le_infty k)
  set N := ∇ F x₀ with hNdef
  have hN : ‖N‖ = 1 := hgrad x₀ hx₀ hF0
  obtain ⟨r, hr, hsub, hpos⟩ := exists_interior_ball (hFat 2 x₀ hx₀) hF0 hN (hU.mem_nhds hx₀)
  set s : E n → ℝ := fun y ↦ ‖∇ F y‖ ^ 2 with hs
  have hsC : ∀ y ∈ U, ContDiffAt ℝ 2 s y := fun y hy ↦
    (contDiffAt_gradient (k := 2) (hFat 3 y hy)).norm_sq ℝ
  -- The positive set of the chart is open.
  set S : Set (E n) := {y | y ∈ U ∧ 0 < F y}
  have hSopen : IsOpen S := hF.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  -- Apply the Hopf lemma on the ball about `y₀ = x₀ + rN`, in the direction `-N`.
  set y₀ := x₀ + r • N
  have hx₀eq : y₀ + r • (-N) = x₀ := by simp [y₀]
  have hball_S : ∀ x ∈ ball y₀ r, x ∈ S := fun x hx ↦ by
    refine ⟨hsub (ball_subset_closedBall hx), hpos x (ball_subset_closedBall hx) ?_⟩
    rintro rfl
    rw [mem_ball, dist_eq_norm] at hx
    simp [y₀, norm_smul, hN, abs_of_pos hr] at hx
  have hH := TauCeti.fderiv_pos_of_laplacian_nonneg_of_lt_closedBall (u := s) (y := y₀) hr
    (by rw [norm_neg, hN])
    (fun x hx ↦ (hsC x (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx ↦ hsC x (hsub (ball_subset_closedBall hx)))
    (by rw [hx₀eq]; exact (hsC x₀ hx₀).differentiableAt (by norm_num))
    (fun x hx ↦ by
      have hxS := hball_S x hx
      refine laplacian_normSq_gradient_nonneg ?_ ?_
      · filter_upwards [hSopen.mem_nhds hxS] with z hz using hFat 3 z hz.1
      · filter_upwards [hSopen.mem_nhds hxS] with z hz using hΔ z hz.1 hz.2)
    (fun x hx hne ↦ by
      rw [hx₀eq] at hne ⊢
      have hFx := hpos x hx hne
      have h1 := hlt x (hsub hx) hFx
      have h2 : ‖∇ F x‖ ^ 2 < ‖N‖ ^ 2 := by
        rw [hN]
        nlinarith [norm_nonneg (∇ F x)]
      exact h2)
  rw [hx₀eq, fderiv_normSq_gradient_apply_eq (hFat 2 x₀ hx₀)] at hH
  have hneg : iteratedFDeriv ℝ 2 F x₀ ![-N, N] = -iteratedFDeriv ℝ 2 F x₀ ![N, N] := by
    have := (consCLM (iteratedFDeriv ℝ 2 F x₀) ![N]).map_neg N
    simp only [consCLM_apply] at this
    exact this
  rw [← hNdef, hneg] at hH
  linarith

end Hopf

end OnePhaseDimension
