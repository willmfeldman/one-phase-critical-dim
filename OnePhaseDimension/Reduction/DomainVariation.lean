/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.DomainVariationFlow
public import InnerVariational.Defs.VariationalSolution
public import GMTFoundations.GMT.HausdorffLebesgue
public import GMTFoundations.Sobolev.Lipschitz
public import EllipticBernoulli.Sobolev.Uniqueness
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Minimizers are stationary for domain variations

A locally Lipschitz local minimizer `u` of the one-phase energy in `ℝᵈ` satisfies the inner
variation identity

`∫ ((|∇u|² + 1_{u>0}) div ξ − 2 ∇u · Dξ ∇u) = 0`

for every Lipschitz vector field `ξ` with compact support
(`innerVariation_eq_zero_of_isLocalEnergyMinimizer`).

## Proof

Fix a ball `B ⊇ tsupport ξ`. For small `|t|`, `Φ_t = id + t ξ` is a bi-Lipschitz bijection of
`ℝᵈ` mapping `B` onto itself (`DomainVariationFlow.lean`), so `v_t = u ∘ Φ_t⁻¹` is a locally
Lipschitz competitor that agrees with `u` off `B`. Its weak gradient is its a.e. gradient. The
change of variables `x = Φ_t(y)` (Mathlib's area formula on the set where `ξ` and `u` are
differentiable, whose complement and its image under the Lipschitz map `Φ_t` are null) gives

`J(v_t; B) = ∫_B Θ(t, Dξ(y), ∇u(y), 1_{u>0}(y)) dy`

(`lintegral_energy_comp_dvFlow`), with the density `Θ` of `DomainVariationDensity.lean`. So
`t ↦ ∫_B Θ(t, ⋯)` has a local minimum at `t = 0`. It is differentiable at `0` by
differentiation under the integral sign, `Θ` being Lipschitz in `t` uniformly on the bounded
data, and its derivative is the inner variation.
-/

open Set Filter Topology Metric MeasureTheory
open scoped RealInnerProductSpace NNReal ENNReal Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ}

/-- A Lipschitz self-map of `ℝᵈ` maps Lebesgue-null sets to Lebesgue-null sets. -/
theorem volume_image_eq_zero_of_lipschitzWith {f : E d → E d} {K : ℝ≥0} (hf : LipschitzWith K f)
    {s : Set (E d)} (hs : volume s = 0) : volume (f '' s) = 0 := by
  rw [← GMTFoundations.GMT.hausdorffN_self_eq_volume, GMTFoundations.GMT.hausdorffN_eq_zero_iff]
    at hs ⊢
  have h := hf.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d) s
  rw [hs, mul_zero] at h
  exact le_antisymm h bot_le

variable {u : E d → ℝ} {ξ : E d → E d} {L : ℝ≥0} {t R : ℝ}

/-- The pulled-back energy density of `u ∘ Φ_t⁻¹` along the data of `u` and `ξ`:
`y ↦ Θ(t, Dξ(y), ∇u(y), 1_{u>0}(y))`. -/
def dvIntegrand (u : E d → ℝ) (ξ : E d → E d) (t : ℝ) (y : E d) : ℝ :=
  domainVariationDensity t (fderiv ℝ ξ y) (∇ u y) (InnerVariational.posIndicator u y)

theorem measurable_posIndicator (hu : Measurable u) :
    Measurable (InnerVariational.posIndicator u) :=
  measurable_const.indicator (measurableSet_lt measurable_const hu)

theorem dvIntegrand_eq_comp (u : E d → ℝ) (ξ : E d → E d) (t : ℝ) :
    dvIntegrand u ξ t = domainVariationDensityProd ∘ fun y ↦
      ((t, fderiv ℝ ξ y, ∇ u y, InnerVariational.posIndicator u y) :
        ℝ × (E d →L[ℝ] E d) × E d × ℝ) :=
  rfl

theorem measurable_dvIntegrand (hu : Measurable u) (ξ : E d → E d) (t : ℝ) :
    Measurable (dvIntegrand u ξ t) := by
  have h : Measurable fun y ↦ ((t, fderiv ℝ ξ y, ∇ u y, InnerVariational.posIndicator u y) :
      ℝ × (E d →L[ℝ] E d) × E d × ℝ) :=
    measurable_const.prodMk ((measurable_fderiv ℝ ξ).prodMk
      ((GMTFoundations.measurable_gradient u).prodMk (measurable_posIndicator hu)))
  rw [dvIntegrand_eq_comp]
  exact measurable_domainVariationDensityProd.comp h

theorem posIndicator_mem_Icc (u : E d → ℝ) (y : E d) :
    InnerVariational.posIndicator u y ∈ Icc (0 : ℝ) 1 := by
  by_cases h : 0 < u y
  · rw [InnerVariational.posIndicator_of_pos h]; exact ⟨zero_le_one, le_rfl⟩
  · rw [InnerVariational.posIndicator_of_nonpos (not_lt.1 h)]; exact ⟨le_rfl, zero_le_one⟩

theorem norm_smul_fderiv_lt_one (hξ : LipschitzWith L ξ) (ht : |t| * L < 1) (y : E d) :
    ‖t • fderiv ℝ ξ y‖ < 1 := by
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hξ) (abs_nonneg t)).trans_lt ht

/-! ### The energy of the competitor -/

/-- **Change of variables for the competitor.** If `|t| L < 1` and `tsupport ξ ⊆ B_R`, the
energy of `u ∘ Φ_t⁻¹` on `B_R` is `∫_{B_R} Θ(t, Dξ, ∇u, 1_{u>0})`. -/
theorem lintegral_energy_comp_dvFlow (hlip : LocallyLipschitz u) (hξ : LipschitzWith L ξ)
    (ht : |t| * L < 1) (hR : tsupport ξ ⊆ ball 0 R) :
    energyJ (ball 0 R) (fun _ ↦ 1) (u ∘ (dvFlowEquiv hξ ht).symm)
        (∇ (u ∘ (dvFlowEquiv hξ ht).symm)) =
      ∫⁻ y in ball 0 R, ENNReal.ofReal (dvIntegrand u ξ t y) := by
  set B := ball (0 : E d) R
  set e := dvFlowEquiv hξ ht
  set v := u ∘ e.symm
  set D := {y | DifferentiableAt ℝ ξ y} ∩ {y | DifferentiableAt ℝ u y}
  set s := B ∩ D
  have hDm : MeasurableSet D :=
    (measurableSet_of_differentiableAt ℝ ξ).inter (measurableSet_of_differentiableAt ℝ u)
  have hs : MeasurableSet s := measurableSet_ball.inter hDm
  obtain ⟨C, hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E d) R) (hlip.locallyLipschitzOn (s := closedBall 0 R))
  have hDae : ∀ᵐ y ∂(volume : Measure (E d)), y ∈ B → y ∈ D := by
    filter_upwards [hξ.ae_differentiableAt,
      (hC.mono ball_subset_closedBall).ae_differentiableWithinAt_of_mem] with y hy1 hy2 hyB
    exact ⟨hy1, (hy2 hyB).differentiableAt (isOpen_ball.mem_nhds hyB)⟩
  have hnull : volume (B \ D) = 0 :=
    measure_eq_zero_iff_ae_notMem.2 (hDae.mono fun y hy hyBD ↦ hyBD.2 (hy hyBD.1))
  have hsB : s =ᵐ[volume] B := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [sdiff_eq_empty.2 inter_subset_left, measure_empty]
    · rwa [sdiff_self_inter]
  have hΦB := image_dvFlow_eq hξ ht hR
  have himage : dvFlow ξ t '' s =ᵐ[volume] B := by
    refine ae_eq_set.2 ⟨?_, ?_⟩
    · rw [sdiff_eq_empty.2 ((image_mono inter_subset_left).trans hΦB.subset), measure_empty]
    · refine measure_mono_null ?_
        (volume_image_eq_zero_of_lipschitzWith (lipschitzWith_dvFlow hξ t) hnull)
      rintro x ⟨hxB, hxs⟩
      rw [← hΦB] at hxB
      obtain ⟨y, hyB, rfl⟩ := hxB
      exact ⟨y, ⟨hyB, fun hyD ↦ hxs ⟨y, ⟨hyB, hyD⟩, rfl⟩⟩, rfl⟩
  have hderiv : ∀ y ∈ s, HasFDerivWithinAt (dvFlow ξ t) (1 + t • fderiv ℝ ξ y) s y :=
    fun y hy ↦ (hasFDerivAt_dvFlow hy.2.1 t).hasFDerivWithinAt
  have hinj : InjOn (dvFlow ξ t) s := (injective_dvFlow hξ ht).injOn
  set g : E d → ℝ≥0∞ := fun x ↦ ENNReal.ofReal
    (‖∇ v x‖ ^ 2 + (fun _ : E d ↦ (1 : ℝ)) x ^ 2 * (posSet v B).indicator 1 x)
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hderiv hinj g
  have hpt : ∀ y ∈ s, ENNReal.ofReal |(1 + t • fderiv ℝ ξ y).det| * g (dvFlow ξ t y) =
      ENNReal.ofReal (dvIntegrand u ξ t y) := by
    intro y hy
    have hsmall := norm_smul_fderiv_lt_one hξ ht y
    have hdet : (1 + t • fderiv ℝ ξ y).det = opDet (1 + t • fderiv ℝ ξ y) := rfl
    have hpos := opDet_one_add_pos hsmall
    have hgrad : ‖∇ v (dvFlow ξ t y)‖ ^ 2 =
        pullbackSq (Ring.inverse (1 + t • fderiv ℝ ξ y)) (∇ u y) :=
      norm_gradient_comp_symm_sq hξ ht hy.2.1 hy.2.2 hsmall
    have hΦyB : dvFlow ξ t y ∈ B := hΦB.subset ⟨y, hy.1, rfl⟩
    have hvy : v (dvFlow ξ t y) = u y := by
      simp only [v, Function.comp_apply]
      exact congrArg u (e.symm_apply_apply y)
    have hind : (posSet v B).indicator (1 : E d → ℝ) (dvFlow ξ t y) =
        InnerVariational.posIndicator u y := by
      by_cases hu : 0 < u y
      · rw [indicator_of_mem (show dvFlow ξ t y ∈ posSet v B from ⟨hΦyB, hvy ▸ hu⟩),
          InnerVariational.posIndicator_of_pos hu, Pi.one_apply]
      · rw [indicator_of_notMem (fun h : dvFlow ξ t y ∈ posSet v B ↦ hu (hvy ▸ h.2)),
          InnerVariational.posIndicator_of_nonpos (not_lt.1 hu)]
    simp only [g, hgrad, hind, hdet, abs_of_pos hpos, one_pow, one_mul]
    rw [← ENNReal.ofReal_mul hpos.le, dvIntegrand, domainVariationDensity, mul_comm]
  calc energyJ B (fun _ ↦ 1) v (∇ v) = ∫⁻ x in B, g x := rfl
    _ = ∫⁻ x in dvFlow ξ t '' s, g x := setLIntegral_congr himage.symm
    _ = ∫⁻ y in s, ENNReal.ofReal |(1 + t • fderiv ℝ ξ y).det| * g (dvFlow ξ t y) := hcov
    _ = ∫⁻ y in s, ENNReal.ofReal (dvIntegrand u ξ t y) := setLIntegral_congr_fun hs hpt
    _ = ∫⁻ y in B, ENNReal.ofReal (dvIntegrand u ξ t y) := setLIntegral_congr hsB

/-- The energy of `u` itself is `∫_{B_R} Θ(0, ⋯) = ∫_{B_R} |∇u|² + 1_{u>0}`. -/
theorem energyJ_eq_lintegral_dvIntegrand_zero (hlip : LocallyLipschitz u) {Gu : E d → E d}
    (hGu : HasWeakGradient univ u Gu) (ξ : E d → E d) (R : ℝ) :
    energyJ (ball 0 R) (fun _ ↦ 1) u Gu =
      ∫⁻ y in ball 0 R, ENNReal.ofReal (dvIntegrand u ξ 0 y) := by
  have hgrad : HasWeakGradient univ u (∇ u) :=
    (GMTFoundations.memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
      hlip.locallyLipschitzOn).1
  have hae := HasWeakGradient.ae_eq_of_eqOn isOpen_univ isOpen_ball (subset_univ _) hGu hgrad
    (eqOn_refl u (ball 0 R))
  refine setLIntegral_congr_fun_ae measurableSet_ball ?_
  filter_upwards [(ae_restrict_iff' measurableSet_ball).1 hae] with y hy hyB
  rw [dvIntegrand, domainVariationDensity_zero, hy hyB]
  congr 2
  by_cases hu : 0 < u y
  · rw [indicator_of_mem (show y ∈ posSet u (ball 0 R) from ⟨hyB, hu⟩),
      InnerVariational.posIndicator_of_pos hu]
    simp
  · rw [indicator_of_notMem (fun h : y ∈ posSet u (ball 0 R) ↦ hu h.2),
      InnerVariational.posIndicator_of_nonpos (not_lt.1 hu)]
    simp

/-- **Minimality against domain variations**, in integrated form. -/
theorem lintegral_dvIntegrand_zero_le (hlip : LocallyLipschitz u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hξ : LipschitzWith L ξ)
    (ht : |t| * L < 1) (hR0 : 0 < R) (hR : tsupport ξ ⊆ ball 0 R) :
    ∫⁻ y in ball 0 R, ENNReal.ofReal (dvIntegrand u ξ 0 y) ≤
      ∫⁻ y in ball 0 R, ENNReal.ofReal (dvIntegrand u ξ t y) := by
  obtain ⟨Gu, hGu, hmin⟩ := hmin
  have hobs := hmin 0 R hR0 (subset_univ _)
  set e := dvFlowEquiv hξ ht
  have hvlip : LocallyLipschitz (u ∘ e.symm) :=
    hlip.comp (lipschitzWith_dvFlowEquiv_symm hξ ht).locallyLipschitz
  have hvH : MemH1Loc univ (u ∘ e.symm) (∇ (u ∘ e.symm)) :=
    GMTFoundations.memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ hvlip.locallyLipschitzOn
  have hoff : ∀ᵐ y ∂(volume.restrict (univ \ ball (0 : E d) R)), (u ∘ e.symm) y = u y := by
    refine (ae_restrict_iff' (MeasurableSet.univ.diff measurableSet_ball)).2
      (Eventually.of_forall fun y hy ↦ ?_)
    have hyK : y ∉ tsupport ξ := fun h ↦ hy.2 (hR h)
    simp only [Function.comp_apply]
    exact congrArg u (e.symm_apply_eq.2 (dvFlow_of_notMem_tsupport hyK).symm)
  rw [← energyJ_eq_lintegral_dvIntegrand_zero hlip hGu.1 ξ R,
    ← lintegral_energy_comp_dvFlow hlip hξ ht hR]
  exact hobs.2.2.2 _ _ hvH hoff (Eventually.of_forall fun _ ↦ mem_univ _)

/-! ### Stationarity -/

/-- **Stationarity of minimizers under domain variations.** A locally Lipschitz local minimizer
`u` of the one-phase energy in `ℝᵈ` satisfies, for every Lipschitz vector field `ξ` with
compact support, `∫ ((|∇u|² + 1_{u>0}) div ξ − 2 ∇u · Dξ ∇u) = 0`. -/
theorem innerVariation_eq_zero_of_isLocalEnergyMinimizer (hlip : LocallyLipschitz u)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hξ : ∃ C, LipschitzWith C ξ) (hξc : HasCompactSupport ξ) :
    InnerVariational.innerVariation u (InnerVariational.posIndicator u) ξ = 0 := by
  obtain ⟨L, hξ⟩ := hξ
  obtain ⟨R₀, hR₀⟩ := hξc.isCompact.isBounded.subset_ball (0 : E d)
  set R := max R₀ 1
  have hR0 : 0 < R := lt_max_of_lt_right one_pos
  have hR : tsupport ξ ⊆ ball 0 R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  set B := ball (0 : E d) R
  have hum : Measurable u := hlip.continuous.measurable
  obtain ⟨Cu, hCu⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E d) R) (hlip.locallyLipschitzOn (s := closedBall 0 R))
  have hgradB : ∀ y ∈ B, ‖∇ u y‖ ≤ Cu := fun y hy ↦ by
    rw [GMTFoundations.norm_gradient_eq_norm_fderiv]
    exact norm_fderiv_le_of_lipschitzOn ℝ (isOpen_ball.mem_nhds hy)
      (hCu.mono ball_subset_closedBall)
  obtain ⟨δ, hδ, K, hK⟩ := exists_lipschitzOnWith_domainVariationDensity (d := d) L Cu
  set χ := InnerVariational.posIndicator u
  set F : ℝ → E d → ℝ := fun t y ↦ dvIntegrand u ξ t y
  set F' : E d → ℝ := fun y ↦ (‖∇ u y‖ ^ 2 + χ y) *
      LinearMap.trace ℝ (E d) (fderiv ℝ ξ y : E d →ₗ[ℝ] E d) -
    2 * ⟪∇ u y, fderiv ℝ ξ y (∇ u y)⟫
  have hlipF : ∀ y ∈ B, LipschitzOnWith K (fun t ↦ F t y) (closedBall 0 δ) := fun y hy ↦
    (hK _ _ _ (norm_fderiv_le_of_lipschitz ℝ hξ) (hgradB y hy) (posIndicator_mem_Icc u y)).1
  have hBfin : volume B ≠ ∞ := measure_ball_lt_top.ne
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hBfin
  -- the integrands are bounded on `B`, hence integrable
  have hint : ∀ t ∈ closedBall (0 : ℝ) δ, IntegrableOn (F t) B := by
    intro t ht
    refine Measure.integrableOn_of_bounded (M := (Cu : ℝ) ^ 2 + 1 + K * δ) hBfin
      (measurable_dvIntegrand hum ξ t).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun y hy ↦ ?_)
    have h1 := (hlipF y hy).dist_le_mul t ht 0 (mem_closedBall_self hδ.le)
    have h0 : F 0 y = ‖∇ u y‖ ^ 2 + χ y := domainVariationDensity_zero _ _ _
    have hχ := posIndicator_mem_Icc u y
    have hg := hgradB y hy
    rw [mem_closedBall, dist_zero_right] at ht
    rw [Real.dist_eq, Real.dist_eq, sub_zero, h0] at h1
    rw [Real.norm_eq_abs]
    have hsq : ‖∇ u y‖ ^ 2 ≤ (Cu : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hg 2
    have hK' : (K : ℝ) * |t| ≤ K * δ := mul_le_mul_of_nonneg_left ht K.2
    have habs := abs_sub_abs_le_abs_sub (F t y) (‖∇ u y‖ ^ 2 + χ y)
    rw [abs_of_nonneg (add_nonneg (sq_nonneg _) hχ.1)] at habs
    linarith [hχ.2]
  -- `|t| L < 1` near `0`
  set δ' := min δ (1 / (L + 1))
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  have htL : ∀ t ∈ ball (0 : ℝ) δ', |t| * L < 1 := by
    intro t ht
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    have h1 : |t| < 1 / (L + 1) := ht.trans_le (min_le_right _ _)
    have hL : (0 : ℝ) ≤ L := L.2
    calc |t| * L ≤ 1 / (L + 1) * L := mul_le_mul_of_nonneg_right h1.le hL
      _ < 1 := by rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
  -- the comparison `J(0) ≤ J(t)`
  have hcomp : ∀ t ∈ ball (0 : ℝ) δ', ∫ y in B, F 0 y ≤ ∫ y in B, F t y := by
    intro t ht
    have htδ : t ∈ closedBall (0 : ℝ) δ :=
      ball_subset_closedBall (ball_subset_ball (min_le_left _ _) ht)
    have hnn : ∀ s : ℝ, |s| * L < 1 → 0 ≤ᵐ[volume.restrict B] F s := fun s hs ↦
      Eventually.of_forall fun y ↦ domainVariationDensity_nonneg
        (norm_smul_fderiv_lt_one hξ hs y) _ (posIndicator_mem_Icc u y).1
    have h0L : |(0 : ℝ)| * L < 1 := by simp
    have hle := lintegral_dvIntegrand_zero_le hlip hmin hξ (htL t ht) hR0 hR
    rw [← ofReal_integral_eq_lintegral_ofReal (hint 0 (mem_closedBall_self hδ.le)) (hnn 0 h0L),
      ← ofReal_integral_eq_lintegral_ofReal (hint t htδ) (hnn t (htL t ht))] at hle
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae (hnn t (htL t ht)))).1 hle
  -- differentiation under the integral sign
  have hF'm : Measurable F' := by
    have hA := measurable_fderiv ℝ ξ
    have hp := GMTFoundations.measurable_gradient u
    have happ : Measurable fun y ↦ fderiv ℝ ξ y (∇ u y) :=
      isBoundedBilinearMap_apply.continuous.measurable.comp (hA.prodMk hp)
    exact (((hp.norm.pow_const 2).add (measurable_posIndicator hum)).mul
      (continuous_trace.measurable.comp hA)).sub (measurable_const.mul (hp.inner happ))
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume.restrict B)
    (F := F) (F' := F') (x₀ := 0) (bound := fun _ ↦ (K : ℝ)) (ball_mem_nhds 0 hδ)
    (Eventually.of_forall fun t ↦ (measurable_dvIntegrand hum ξ t).aestronglyMeasurable)
    (hint 0 (mem_closedBall_self hδ.le)) hF'm.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun y hy ↦ by
      simpa using (hlipF y hy).mono ball_subset_closedBall))
    (integrable_const _)
    (Eventually.of_forall fun y ↦ hasDerivAt_domainVariationDensity _ _ _)
  have hlocmin : IsLocalMin (fun t ↦ ∫ y in B, F t y) 0 :=
    Filter.eventually_of_mem (ball_mem_nhds 0 hδ') hcomp
  have hzero : ∫ y in B, F' y = 0 := hlocmin.hasDerivAt_eq_zero hderiv.2
  -- identify the derivative with the inner variation
  have hoff : ∀ y, y ∉ B → F' y = 0 := by
    intro y hy
    have hyK : y ∉ tsupport ξ := fun h ↦ hy (hR h)
    simp [F', fderiv_of_notMem_tsupport ℝ hyK]
  rw [← hzero, setIntegral_eq_integral_of_forall_compl_eq_zero hoff]
  rfl

end OnePhaseDimension
