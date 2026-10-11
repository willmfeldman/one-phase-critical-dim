/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Isometry
public import EllipticBernoulli.Sobolev.Uniqueness
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Fubini in the splitting `ℝ^{k+1} = ℝᵏ × ℝ` and suspended Sobolev functions

Write `x = (y, s)` with `y = π x ∈ ℝᵏ` (`π = projInit k`) and `s = x_{k+1}`, and
`joinLast y s` for the point with these coordinates.

## Main results

* `integral_eq_integral_slices`, `integral_eq_integral_slices'`: Fubini, with the vertical or the
  horizontal variable outside; `lintegral_eq_lintegral_slices`, `lintegral_le_lintegral_slices`,
  `ae_ae_slices`: the same for lower integrals and almost-everywhere statements.
* `locallyIntegrable_comp_projInit`, `memLp_comp_projInit`: integrability of `g ∘ π`.
* `hasWeakGradient_comp_projInit`, `memH1Loc_comp_projInit`: if `G` is a weak gradient of `ψ`
  in `ℝᵏ`, then `π† ∘ G ∘ π` is a weak gradient of `ψ ∘ π` in `ℝ^{k+1}`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff RealInnerProductSpace ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {k : ℕ}

/-! ### Coordinates -/

/-- The point of `ℝ^{k+1}` with first coordinates `y` and last coordinate `s`. -/
def joinLast (y : E k) (s : ℝ) : E (k + 1) := (splitLast k).symm (y, s)

@[simp]
theorem projInit_joinLast (y : E k) (s : ℝ) : projInit k (joinLast y s) = y :=
  projInit_splitLast_symm _

@[simp]
theorem joinLast_last (y : E k) (s : ℝ) : joinLast y s (Fin.last k) = s :=
  splitLast_symm_apply_last _

theorem joinLast_projInit (x : E (k + 1)) : joinLast (projInit k x) (x (Fin.last k)) = x :=
  (splitLast k).symm_apply_apply x

theorem joinLast_eq (y : E k) (s : ℝ) : joinLast y s = (projInit k).adjoint y + s • lastVec k := by
  conv_lhs => rw [← adjoint_projInit_add_smul_lastVec (joinLast y s)]
  simp

theorem inner_adjoint_projInit (y : E k) (x : E (k + 1)) :
    ⟪(projInit k).adjoint y, x⟫ = ⟪y, projInit k x⟫ :=
  ContinuousLinearMap.adjoint_inner_left _ _ _

theorem norm_projInit_le (x : E (k + 1)) : ‖projInit k x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq_splitLast x
  simp only [splitLast_apply_fst, splitLast_apply_snd] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [sq_nonneg (x (Fin.last k))])

theorem abs_last_le (x : E (k + 1)) : |x (Fin.last k)| ≤ ‖x‖ := by
  have h := norm_sq_eq_splitLast x
  simp only [splitLast_apply_fst, splitLast_apply_snd] at h
  exact abs_le_of_sq_le_sq' (by nlinarith [sq_nonneg ‖projInit k x‖]) (norm_nonneg _) |>.elim
    (fun h1 h2 ↦ abs_le.2 ⟨h1, h2⟩)

theorem hasFDerivAt_joinLast_left (y : E k) (s : ℝ) :
    HasFDerivAt (fun y ↦ joinLast y s) ((projInit k).adjoint : E k →L[ℝ] E (k + 1)) y := by
  simp_rw [joinLast_eq]
  exact ((projInit k).adjoint.hasFDerivAt).add_const _

theorem hasDerivAt_joinLast_right (y : E k) (s : ℝ) :
    HasDerivAt (fun s ↦ joinLast y s) (lastVec k) s := by
  simp_rw [joinLast_eq]
  simpa using ((hasDerivAt_id s).smul_const (lastVec k)).const_add ((projInit k).adjoint y)

theorem continuous_joinLast : Continuous fun p : E k × ℝ ↦ joinLast p.1 p.2 :=
  (splitLast k).symm.continuous

/-! ### Fubini -/

/-- Slice coordinates `x ↦ (x_{k+1}, π x)`. -/
def sliceEquiv : E (k + 1) ≃ᵐ ℝ × E k :=
  (splitLast k).toHomeomorph.toMeasurableEquiv.trans MeasurableEquiv.prodComm

theorem sliceEquiv_symm_apply (p : ℝ × E k) : sliceEquiv.symm p = joinLast p.2 p.1 := rfl

theorem measurePreserving_sliceEquiv :
    MeasurePreserving (sliceEquiv (k := k)) volume
      ((volume : Measure ℝ).prod (volume : Measure (E k))) :=
  (Measure.measurePreserving_swap).comp measurePreserving_splitLast

theorem measurePreserving_sliceEquiv_symm :
    MeasurePreserving (sliceEquiv (k := k)).symm
      ((volume : Measure ℝ).prod (volume : Measure (E k))) volume :=
  MeasurePreserving.symm _ measurePreserving_sliceEquiv

/-- The splitting as a measurable equivalence. -/
def splitEquiv : E (k + 1) ≃ᵐ E k × ℝ := (splitLast k).toHomeomorph.toMeasurableEquiv

theorem splitEquiv_symm_apply (p : E k × ℝ) : splitEquiv.symm p = joinLast p.1 p.2 := rfl

theorem measurePreserving_splitEquiv_symm :
    MeasurePreserving (splitEquiv (k := k)).symm
      ((volume : Measure (E k)).prod (volume : Measure ℝ)) volume :=
  MeasurePreserving.symm _ measurePreserving_splitLast

/-- **Fubini**, vertical variable outside. -/
theorem integral_eq_integral_slices {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E (k + 1) → F} (hf : Integrable f) :
    ∫ x, f x = ∫ s, ∫ y, f (joinLast y s) := by
  rw [← measurePreserving_sliceEquiv_symm.integral_comp' f]
  have hint : Integrable (f ∘ sliceEquiv.symm) ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_sliceEquiv_symm.integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding _)).2 hf
  exact integral_prod _ hint

/-- **Fubini**, horizontal variable outside. -/
theorem integral_eq_integral_slices' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E (k + 1) → F} (hf : Integrable f) :
    ∫ x, f x = ∫ y, ∫ s, f (joinLast y s) := by
  rw [← measurePreserving_splitEquiv_symm.integral_comp' f]
  have hint : Integrable (f ∘ splitEquiv.symm) ((volume : Measure (E k)).prod volume) :=
    (measurePreserving_splitEquiv_symm.integrable_comp_emb
      (MeasurableEquiv.measurableEmbedding _)).2 hf
  exact integral_prod _ hint

/-- Integrability of the composition with the slice coordinates. -/
theorem integrable_comp_sliceEquiv_symm {F : Type*} [NormedAddCommGroup F]
    {f : E (k + 1) → F} (hf : Integrable f) :
    Integrable (fun p : ℝ × E k ↦ f (joinLast p.2 p.1)) ((volume : Measure ℝ).prod volume) :=
  (measurePreserving_sliceEquiv_symm.integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)).2 hf

/-- **Tonelli**, vertical variable outside. -/
theorem lintegral_eq_lintegral_slices {f : E (k + 1) → ℝ≥0∞} (hf : AEMeasurable f) :
    ∫⁻ x, f x = ∫⁻ s, ∫⁻ y, f (joinLast y s) := by
  rw [← measurePreserving_sliceEquiv_symm.lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) f]
  exact lintegral_prod _ (hf.comp_quasiMeasurePreserving
    measurePreserving_sliceEquiv_symm.quasiMeasurePreserving)

/-- The inequality half of Tonelli, without measurability. -/
theorem lintegral_le_lintegral_slices (f : E (k + 1) → ℝ≥0∞) :
    ∫⁻ x, f x ≤ ∫⁻ s, ∫⁻ y, f (joinLast y s) := by
  rw [← measurePreserving_sliceEquiv_symm.lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) f]
  exact lintegral_prod_le _

/-- Almost every slice of an almost-everywhere statement holds almost everywhere. -/
theorem ae_ae_slices {P : E (k + 1) → Prop} (h : ∀ᵐ x, P x) :
    ∀ᵐ s : ℝ, ∀ᵐ y : E k, P (joinLast y s) :=
  Measure.ae_ae_of_ae_prod (measurePreserving_sliceEquiv_symm.quasiMeasurePreserving.ae h)

/-- An almost-everywhere statement on `ℝᵏ` lifts to `ℝ^{k+1}`. -/
theorem ae_comp_projInit {P : E k → Prop} (h : ∀ᵐ y, P y) : ∀ᵐ x : E (k + 1), P (projInit k x) := by
  have h2 : ∀ᵐ p ∂((volume : Measure (E k)).prod (volume : Measure ℝ)), P p.1 :=
    Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst) h
  exact measurePreserving_splitLast.quasiMeasurePreserving.ae h2

/-! ### Integrability of suspended functions -/

/-- The box `closedBall 0 R × [-R, R]` in slice coordinates. -/
def sliceBox (k : ℕ) (R : ℝ) : Set (E (k + 1)) :=
  (splitLast k) ⁻¹' (closedBall (0 : E k) R ×ˢ Icc (-R) R)

theorem closedBall_subset_sliceBox (R : ℝ) : closedBall (0 : E (k + 1)) R ⊆ sliceBox k R := by
  intro x hx
  rw [mem_closedBall, dist_zero_right] at hx
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right]
    exact (norm_projInit_le x).trans hx
  · exact abs_le.1 ((abs_last_le x).trans hx)

theorem exists_subset_sliceBox {K : Set (E (k + 1))} (hK : IsCompact K) :
    ∃ R, K ⊆ sliceBox k R := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  exact ⟨R, hR.trans (closedBall_subset_sliceBox R)⟩

theorem isCompact_sliceBox (R : ℝ) : IsCompact (sliceBox k R) := by
  have : sliceBox k R = (splitLast k).symm '' (closedBall (0 : E k) R ×ˢ Icc (-R) R) :=
    ((splitLast k).toEquiv.image_symm_eq_preimage _).symm
  rw [this]
  exact ((isCompact_closedBall _ _).prod isCompact_Icc).image (splitLast k).symm.continuous

instance (R : ℝ) : IsFiniteMeasure ((volume : Measure ℝ).restrict (Icc (-R) R)) :=
  isFiniteMeasure_restrict.2 measure_Icc_lt_top.ne

theorem integrableOn_sliceBox_comp_projInit {F : Type*} [NormedAddCommGroup F] {g : E k → F}
    {R : ℝ} (hg : IntegrableOn g (closedBall 0 R)) :
    IntegrableOn (fun x ↦ g (projInit k x)) (sliceBox k R) := by
  have h : IntegrableOn (fun p : E k × ℝ ↦ g p.1) (closedBall 0 R ×ˢ Icc (-R) R)
      ((volume : Measure (E k)).prod volume) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact hg.comp_fst _
  exact (measurePreserving_splitLast.integrableOn_comp_preimage
    (splitLast k).toHomeomorph.measurableEmbedding).2 h

theorem memLp_sliceBox_comp_projInit {F : Type*} [NormedAddCommGroup F] {g : E k → F} {R : ℝ}
    (hg : MemLp g 2 (volume.restrict (closedBall 0 R))) :
    MemLp (fun x ↦ g (projInit k x)) 2 (volume.restrict (sliceBox k R)) := by
  have h : MemLp (fun p : E k × ℝ ↦ g p.1) 2
      (((volume : Measure (E k)).prod volume).restrict (closedBall 0 R ×ˢ Icc (-R) R)) := by
    rw [← Measure.prod_restrict]
    exact hg.comp_fst _
  exact h.comp_measurePreserving (measurePreserving_splitLast.restrict_preimage_emb
    (splitLast k).toHomeomorph.measurableEmbedding _)

theorem locallyIntegrable_comp_projInit {F : Type*} [NormedAddCommGroup F] {g : E k → F}
    (hg : LocallyIntegrable g) : LocallyIntegrable (fun x ↦ g (projInit k x)) := by
  refine (locallyIntegrable_iff).2 fun K hK ↦ ?_
  obtain ⟨R, hR⟩ := exists_subset_sliceBox hK
  exact (integrableOn_sliceBox_comp_projInit
    (hg.integrableOn_isCompact (isCompact_closedBall 0 R))).mono_set hR

/-! ### Suspended weak gradients -/

/-- The horizontal slice `y ↦ φ(y, s)` of a test function is a test function. -/
theorem contDiff_slice {φ : E (k + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ) (s : ℝ) :
    ContDiff ℝ ∞ fun y ↦ φ (joinLast y s) := by
  simp_rw [joinLast_eq]
  exact hφ.comp (((projInit k).adjoint.contDiff).add contDiff_const)

theorem hasCompactSupport_slice {φ : E (k + 1) → ℝ} (hφc : HasCompactSupport φ) (s : ℝ) :
    HasCompactSupport fun y ↦ φ (joinLast y s) := by
  refine HasCompactSupport.intro (hφc.image (projInit k).continuous) fun y hy ↦ ?_
  by_contra h
  exact hy ⟨joinLast y s, subset_tsupport _ h, projInit_joinLast y s⟩

theorem fderiv_slice {φ : E (k + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ) (y w : E k) (s : ℝ) :
    fderiv ℝ (fun y ↦ φ (joinLast y s)) y w =
      fderiv ℝ φ (joinLast y s) ((projInit k).adjoint w) := by
  have h := ((hφ.differentiable (by simp)) (joinLast y s)).hasFDerivAt.comp y
    (hasFDerivAt_joinLast_left y s)
  rw [show (fun y ↦ φ (joinLast y s)) = φ ∘ (fun y ↦ joinLast y s) from rfl, h.fderiv]
  rfl

theorem hasCompactSupport_vertical {f : E (k + 1) → ℝ} (hfc : HasCompactSupport f) (y : E k) :
    HasCompactSupport fun s ↦ f (joinLast y s) := by
  refine HasCompactSupport.intro
    (hfc.image (EuclideanSpace.proj (Fin.last k) : E (k + 1) →L[ℝ] ℝ).continuous) fun s hs ↦ ?_
  by_contra h
  exact hs ⟨joinLast y s, subset_tsupport _ h, by simp⟩

/-- The vertical derivative of a test function integrates to zero along every vertical line. -/
theorem integral_fderiv_lastVec_eq_zero {φ : E (k + 1) → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (y : E k) :
    ∫ s, fderiv ℝ φ (joinLast y s) (lastVec k) = 0 := by
  have hd : ∀ s, HasDerivAt (fun s ↦ φ (joinLast y s)) (fderiv ℝ φ (joinLast y s) (lastVec k)) s :=
    fun s ↦ ((hφ.differentiable (by simp)) (joinLast y s)).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_joinLast_right y s)
  have hcj : Continuous fun s ↦ joinLast y s :=
    continuous_joinLast.comp (continuous_const.prodMk continuous_id)
  refine integral_eq_zero_of_hasDerivAt_of_integrable hd ?_ ?_
  · refine Continuous.integrable_of_hasCompactSupport
      (((hφ.continuous_fderiv (by simp)).comp hcj).clm_apply continuous_const) ?_
    have hfc : HasCompactSupport fun x ↦ fderiv ℝ φ x (lastVec k) :=
      HasCompactSupport.intro hφc fun x hx ↦
        EllipticBernoulli.fderiv_apply_eq_zero_of_notMem_tsupport hx _
    exact hasCompactSupport_vertical hfc y
  · exact Continuous.integrable_of_hasCompactSupport (hφ.continuous.comp hcj)
      (hasCompactSupport_vertical hφc y)

/-- **Suspended weak gradients.** If `G` is a weak gradient of `ψ` in `ℝᵏ`, then `π† (G ∘ π)` is a
weak gradient of `ψ ∘ π` in `ℝ^{k+1}`. -/
theorem hasWeakGradient_comp_projInit {ψ : E k → ℝ} {G : E k → E k}
    (h : HasWeakGradient univ ψ G) :
    HasWeakGradient univ (fun x ↦ ψ (projInit k x))
      (fun x ↦ (projInit k).adjoint (G (projInit k x))) := by
  have hψ : LocallyIntegrable (fun x ↦ ψ (projInit k x)) :=
    locallyIntegrable_comp_projInit (locallyIntegrableOn_univ.1 h.1)
  have hG : LocallyIntegrable (fun x ↦ (projInit k).adjoint (G (projInit k x))) := by
    have : LocallyIntegrable (fun y ↦ (projInit k).adjoint (G y)) := by
      refine (locallyIntegrable_iff).2 fun K hK ↦ ?_
      exact ((projInit k).adjoint).integrable_comp
        ((locallyIntegrableOn_univ.1 h.2.1).integrableOn_isCompact hK)
    exact locallyIntegrable_comp_projInit this
  refine ⟨locallyIntegrableOn_univ.2 hψ, locallyIntegrableOn_univ.2 hG,
    fun φ hφ hφc _ v ↦ ?_⟩
  simp only [Measure.restrict_univ]
  set w := projInit k v
  have hv : v = (projInit k).adjoint w + v (Fin.last k) • lastVec k :=
    (adjoint_projInit_add_smul_lastVec v).symm
  have hψ' : LocallyIntegrableOn (fun x ↦ ψ (projInit k x)) univ :=
    locallyIntegrableOn_univ.2 hψ
  have i1 := integrable_fderiv_apply_mul hψ' hφ hφc (subset_univ _) ((projInit k).adjoint w)
  have i2 := integrable_fderiv_apply_mul hψ' hφ hφc (subset_univ _) (lastVec k)
  have i3 := integrable_inner_mul (locallyIntegrableOn_univ.2 hG) hφ.continuous hφc
    (subset_univ _) v
  -- the horizontal part
  have hhor : ∫ x, ψ (projInit k x) * fderiv ℝ φ x ((projInit k).adjoint w) =
      -∫ x, ⟪(projInit k).adjoint (G (projInit k x)), v⟫ * φ x := by
    rw [integral_eq_integral_slices i1, integral_eq_integral_slices i3, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
    simp only [projInit_joinLast, inner_adjoint_projInit]
    have := h.2.2 _ (contDiff_slice hφ s) (hasCompactSupport_slice hφc s) (subset_univ _) w
    simp only [Measure.restrict_univ, fderiv_slice hφ] at this
    exact this
  -- the vertical part
  have hver : ∫ x, ψ (projInit k x) * fderiv ℝ φ x (lastVec k) = 0 := by
    rw [integral_eq_integral_slices' i2]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [projInit_joinLast, Pi.zero_apply]
    rw [integral_const_mul, integral_fderiv_lastVec_eq_zero hφ hφc y, mul_zero]
  have hsplit : (fun x ↦ ψ (projInit k x) * fderiv ℝ φ x v) = fun x ↦
      ψ (projInit k x) * fderiv ℝ φ x ((projInit k).adjoint w) +
        v (Fin.last k) * (ψ (projInit k x) * fderiv ℝ φ x (lastVec k)) := by
    funext x
    conv_lhs => rw [hv]
    rw [map_add, map_smul, smul_eq_mul]
    ring
  rw [hsplit, integral_add i1 (i2.const_mul _), integral_const_mul, hver, mul_zero, add_zero,
    hhor]

/-- `H¹_loc` is preserved by suspension. -/
theorem memH1Loc_comp_projInit {ψ : E k → ℝ} {G : E k → E k}
    (h : MemH1Loc univ ψ G) :
    MemH1Loc univ (fun x ↦ ψ (projInit k x)) (fun x ↦ (projInit k).adjoint (G (projInit k x))) := by
  refine ⟨hasWeakGradient_comp_projInit h.1, fun K _ hK ↦ ?_⟩
  obtain ⟨R, hR⟩ := exists_subset_sliceBox hK
  obtain ⟨h1, h2⟩ := h.2 (closedBall 0 R) (subset_univ _) (isCompact_closedBall 0 R)
  exact ⟨(memLp_sliceBox_comp_projInit h1).mono_measure (Measure.restrict_mono hR le_rfl),
    (memLp_sliceBox_comp_projInit (h2.continuousLinearMap_comp (projInit k).adjoint)).mono_measure
      (Measure.restrict_mono hR le_rfl)⟩

end OnePhaseDimension
