/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Product
public import EllipticBernoulli.Sobolev.Lattice
public import EllipticBernoulli.Sobolev.Lipschitz
public import EllipticBernoulli.Common.Calculus
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Slices of Sobolev functions

If `G` is a weak gradient of `V` in `ℝ^{k+1} = ℝᵏ × ℝ`, then for almost every `s` the horizontal
slice `V(·, s)` is locally integrable and has weak gradient `π G(·, s)` in `ℝᵏ`, where `π` drops
the last coordinate.

## Proof

* Slices of locally integrable functions are locally integrable for almost every `s` (Fubini on
  the boxes `closedBall 0 n × [-n, n]`).
* For a fixed test function `φ` on `ℝᵏ` and a fixed direction, the defect
  `F(s) = ∫ V(y, s) ∂φ(y) + ∫ ⟪π G(y, s), e⟫ φ(y)` is locally integrable in `s`, and
  `∫ χ(s) F(s) ds = 0` for every test function `χ` on `ℝ`: this is the weak gradient identity
  for the test function `φ(y) χ(s)` on `ℝ^{k+1}`. Hence `F = 0` almost everywhere.
* The test functions supported in `closedBall 0 n` form a separable family for the uniform
  convergence of values and gradients on `closedBall 0 n` (the space `C(closedBall 0 n, ℝ × ℝᵏ)`
  is second countable). For `s` outside a null set, `F = 0` for a countable dense family, hence
  for all test functions by uniform approximation.

## Main results

* `ae_locallyIntegrable_slice`: slices of locally integrable functions.
* `ae_hasWeakGradient_slice`: slices of weak gradients.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient RealInnerProductSpace ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {k : ℕ}

/-! ### Integrability of slices -/

theorem integrable_prod_of_integrableOn_sliceBox {F : Type*} [NormedAddCommGroup F]
    {f : E (k + 1) → F} {R : ℝ} (hf : IntegrableOn f (sliceBox k R)) :
    Integrable (fun p : E k × ℝ ↦ f (joinLast p.1 p.2))
      (((volume : Measure (E k)).restrict (closedBall 0 R)).prod
        ((volume : Measure ℝ).restrict (Icc (-R) R))) := by
  rw [Measure.prod_restrict]
  have h := (measurePreserving_splitEquiv_symm.integrableOn_comp_preimage
    (MeasurableEquiv.measurableEmbedding _)).2 hf
  have hpre : (splitEquiv (k := k)).symm ⁻¹' sliceBox k R = closedBall 0 R ×ˢ Icc (-R) R := by
    ext p
    simp only [mem_preimage, sliceBox, splitEquiv_symm_apply, joinLast,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [hpre] at h
  exact h

/-- Slices of a locally integrable function are locally integrable for almost every `s`. -/
theorem ae_locallyIntegrable_slice {F : Type*} [NormedAddCommGroup F] {f : E (k + 1) → F}
    (hf : LocallyIntegrable f) : ∀ᵐ s : ℝ, LocallyIntegrable (fun y ↦ f (joinLast y s)) := by
  have hn : ∀ n : ℕ, ∀ᵐ s : ℝ, s ∈ Icc (-(n : ℝ)) n →
      IntegrableOn (fun y ↦ f (joinLast y s)) (closedBall 0 n) := fun n ↦ by
    have := (integrable_prod_of_integrableOn_sliceBox
      (hf.integrableOn_isCompact (isCompact_sliceBox (n : ℝ)))).prod_left_ae
    exact (ae_restrict_iff' measurableSet_Icc).1 this
  filter_upwards [ae_all_iff.2 hn] with s hs
  refine (locallyIntegrable_iff).2 fun K hK ↦ ?_
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨n, hn'⟩ := exists_nat_ge (max R |s|)
  exact (hs n (abs_le.1 ((le_max_right _ _).trans hn'))).mono_set
    (hR.trans (closedBall_subset_closedBall ((le_max_left _ _).trans hn')))

/-! ### Slice integrals against a fixed test function -/

theorem hasCompactSupport_mul_last {g : E k → ℝ} (hgc : HasCompactSupport g) {χ : ℝ → ℝ}
    (hχc : HasCompactSupport χ) :
    HasCompactSupport fun x : E (k + 1) ↦ g (projInit k x) * χ (x (Fin.last k)) := by
  obtain ⟨R₁, hR₁⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R₂, hR₂⟩ := hχc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_sliceBox (k := k) (max R₁ R₂)) fun x hx ↦ ?_
  simp only [sliceBox, mem_preimage, mem_prod, splitLast_apply_fst, splitLast_apply_snd,
    not_and_or] at hx
  rcases hx with hx | hx
  · have : projInit k x ∉ tsupport g := fun h ↦
      hx (closedBall_subset_closedBall (le_max_left _ _) (hR₁ h))
    rw [image_eq_zero_of_notMem_tsupport this, zero_mul]
  · have : x (Fin.last k) ∉ tsupport χ := fun h ↦ by
      have h' := closedBall_subset_closedBall (le_max_right R₁ R₂) (hR₂ h)
      rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at h'
      exact hx h'
    rw [image_eq_zero_of_notMem_tsupport this, mul_zero]

theorem continuous_last : Continuous fun x : E (k + 1) ↦ x (Fin.last k) :=
  (EuclideanSpace.proj (Fin.last k) : E (k + 1) →L[ℝ] ℝ).continuous

/-- The slice integral `s ↦ ∫ f(y, s) g(y) dy` against a continuous compactly supported `g` is
locally integrable. -/
theorem locallyIntegrable_sliceIntegral {f : E (k + 1) → ℝ} (hf : LocallyIntegrable f)
    {g : E k → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    LocallyIntegrable (fun s ↦ ∫ y, f (joinLast y s) * g y) := by
  refine (locallyIntegrable_iff).2 fun K hK ↦ ?_
  obtain ⟨R₁, hR₁⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨R₂, hR₂⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  set R := max R₁ R₂
  have hfg : IntegrableOn (fun x ↦ f x * g (projInit k x)) (sliceBox k R) :=
    (hf.integrableOn_isCompact (isCompact_sliceBox R)).mul_continuousOn
      (hg.comp (projInit k).continuous).continuousOn (isCompact_sliceBox R)
  have h := (integrable_prod_of_integrableOn_sliceBox hfg).integral_prod_right
  simp only [projInit_joinLast] at h
  have hK' : K ⊆ Icc (-R) R := by
    intro s hs
    have := closedBall_subset_closedBall (le_max_left R₁ R₂) (hR₁ hs)
    rwa [Real.closedBall_eq_Icc, zero_sub, zero_add] at this
  refine (IntegrableOn.mono_set ?_ hK')
  refine h.congr (Eventually.of_forall fun s ↦ ?_)
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_
  have : y ∉ tsupport g := fun h ↦ hy (closedBall_subset_closedBall (le_max_right _ _) (hR₂ h))
  rw [image_eq_zero_of_notMem_tsupport this, mul_zero]

/-- Fubini for slice integrals. -/
theorem integral_mul_sliceIntegral {f : E (k + 1) → ℝ} (hf : LocallyIntegrable f)
    {g : E k → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) {χ : ℝ → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    ∫ s, χ s * ∫ y, f (joinLast y s) * g y =
      ∫ x, f x * (g (projInit k x) * χ (x (Fin.last k))) := by
  have hint : Integrable fun x ↦ f x * (g (projInit k x) * χ (x (Fin.last k))) :=
    hf.integrable_smul_right_of_hasCompactSupport
      ((hg.comp (projInit k).continuous).mul (hχ.comp continuous_last))
      (hasCompactSupport_mul_last hgc hχc)
  rw [integral_eq_integral_slices hint]
  refine integral_congr_ae (Eventually.of_forall fun s ↦ ?_)
  simp only [projInit_joinLast, joinLast_last]
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

/-! ### The weak gradient identity on almost every slice, for a fixed test function -/

theorem hasFDerivAt_mul_last {φ : E k → ℝ} (hφ : ContDiff ℝ ∞ φ) {χ : ℝ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (x : E (k + 1)) (w : E k) :
    fderiv ℝ (fun x : E (k + 1) ↦ φ (projInit k x) * χ (x (Fin.last k))) x
      ((projInit k).adjoint w) = fderiv ℝ φ (projInit k x) w * χ (x (Fin.last k)) := by
  set P : E (k + 1) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last k)
  have h1 : HasFDerivAt (fun x ↦ φ (projInit k x)) ((fderiv ℝ φ (projInit k x)).comp (projInit k))
      x := ((hφ.differentiable (by simp)) _).hasFDerivAt.comp x (projInit k).hasFDerivAt
  have h2 : HasFDerivAt (fun x : E (k + 1) ↦ χ (P x)) ((fderiv ℝ χ (P x)).comp P) x :=
    ((hχ.differentiable (by simp)) _).hasFDerivAt.comp x P.hasFDerivAt
  have h := h1.mul h2
  have hP : ∀ x : E (k + 1), P x = x (Fin.last k) := fun x ↦ rfl
  simp only [hP] at h
  rw [show (fun x : E (k + 1) ↦ φ (projInit k x) * χ (x (Fin.last k))) =
    (fun x ↦ φ (projInit k x)) * (fun x : E (k + 1) ↦ χ (x (Fin.last k))) from rfl, h.fderiv]
  have : P ((projInit k).adjoint w) = 0 := projInit_adjoint_apply_last w
  simp [this, projInit_adjoint_apply, mul_comm]

/-- For a fixed test function and direction, the weak gradient identity holds on almost every
slice. -/
theorem ae_slice_identity {V : E (k + 1) → ℝ} {G : E (k + 1) → E (k + 1)}
    (h : HasWeakGradient univ V G) {φ : E k → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (w : E k) :
    ∀ᵐ s : ℝ, (∫ y, V (joinLast y s) * fderiv ℝ φ y w) +
      ∫ y, ⟪projInit k (G (joinLast y s)), w⟫ * φ y = 0 := by
  have hV : LocallyIntegrable V := locallyIntegrableOn_univ.1 h.1
  have hf₂ : LocallyIntegrable fun x ↦ ⟪projInit k (G x), w⟫ := by
    have := locallyIntegrableOn_univ.1
      (locallyIntegrableOn_inner_const h.2.1 ((projInit k).adjoint w))
    convert this using 2 with x
    rw [ContinuousLinearMap.adjoint_inner_right]
  have hg₁ : Continuous fun y ↦ fderiv ℝ φ y w :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hg₁c : HasCompactSupport fun y ↦ fderiv ℝ φ y w :=
    HasCompactSupport.intro hφc fun y hy ↦
      EllipticBernoulli.fderiv_apply_eq_zero_of_notMem_tsupport hy w
  have hI₁ := locallyIntegrable_sliceIntegral hV hg₁ hg₁c
  have hI₂ := locallyIntegrable_sliceIntegral hf₂ hφ.continuous hφc
  have h0 := isOpen_univ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (locallyIntegrableOn_univ.2 (hI₁.add hI₂)) fun χ hχ hχc _ ↦ ?_
  · filter_upwards [h0] with s hs
    simpa only [Pi.add_apply] using hs (mem_univ s)
  have i₁ := hI₁.integrable_smul_left_of_hasCompactSupport hχ.continuous hχc
  have i₂ := hI₂.integrable_smul_left_of_hasCompactSupport hχ.continuous hχc
  simp only [Pi.add_apply, smul_add]
  rw [integral_add i₁ i₂]
  simp only [smul_eq_mul]
  rw [integral_mul_sliceIntegral hV hg₁ hg₁c hχ.continuous hχc,
    integral_mul_sliceIntegral hf₂ hφ.continuous hφc hχ.continuous hχc]
  set Φ : E (k + 1) → ℝ := fun x ↦ φ (projInit k x) * χ (x (Fin.last k))
  have hlast : ContDiff ℝ ∞ (fun x : E (k + 1) ↦ x (Fin.last k)) :=
    (EuclideanSpace.proj (Fin.last k) : E (k + 1) →L[ℝ] ℝ).contDiff
  have hΦ : ContDiff ℝ ∞ Φ := (hφ.comp (projInit k).contDiff).mul (hχ.comp hlast)
  have hΦc : HasCompactSupport Φ := hasCompactSupport_mul_last hφc hχc
  have hw := h.2.2 Φ hΦ hΦc (subset_univ _) ((projInit k).adjoint w)
  simp only [Measure.restrict_univ] at hw
  have e1 : ∀ x, V x * fderiv ℝ Φ x ((projInit k).adjoint w) =
      V x * (fderiv ℝ φ (projInit k x) w * χ (x (Fin.last k))) := fun x ↦ by
    rw [hasFDerivAt_mul_last hφ hχ]
  have e2 : ∀ x, ⟪G x, (projInit k).adjoint w⟫ * Φ x =
      ⟪projInit k (G x), w⟫ * (φ (projInit k x) * χ (x (Fin.last k))) := fun x ↦ by
    rw [ContinuousLinearMap.adjoint_inner_right]
  simp_rw [e1, e2] at hw
  linarith

/-! ### Directions -/

/-- It suffices to check the weak gradient identity along the coordinate directions. -/
theorem hasWeakGradient_of_forall_single {u : E k → ℝ} {G : E k → E k} (hu : LocallyIntegrable u)
    (hG : LocallyIntegrable G)
    (h : ∀ φ : E k → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∀ i : Fin k,
      ∫ x, u x * fderiv ℝ φ x (EuclideanSpace.single i 1) =
        -∫ x, ⟪G x, EuclideanSpace.single i 1⟫ * φ x) :
    HasWeakGradient univ u G := by
  refine ⟨locallyIntegrableOn_univ.2 hu, locallyIntegrableOn_univ.2 hG,
    fun φ hφ hφc _ v ↦ ?_⟩
  simp only [Measure.restrict_univ]
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr v]
    simp
  have hu' : LocallyIntegrableOn u univ := locallyIntegrableOn_univ.2 hu
  have hG' : LocallyIntegrableOn G univ := locallyIntegrableOn_univ.2 hG
  have i1 : ∀ i ∈ (Finset.univ : Finset (Fin k)), Integrable fun x ↦
      v i * (u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := fun i _ ↦
    (integrable_fderiv_apply_mul hu' hφ hφc (subset_univ _) _).const_mul _
  have i2 : ∀ i ∈ (Finset.univ : Finset (Fin k)), Integrable fun x ↦
      v i * (⟪G x, EuclideanSpace.single i 1⟫ * φ x) := fun i _ ↦
    (integrable_inner_mul hG' hφ.continuous hφc (subset_univ _) _).const_mul _
  have e1 : (fun x ↦ u x * fderiv ℝ φ x v) =
      fun x ↦ ∑ i, v i * (u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) := by
    funext x
    conv_lhs => rw [hv]
    rw [map_sum, Finset.mul_sum]
    simp only [map_smul, smul_eq_mul]
    congr 1; funext i; ring
  have e2 : (fun x ↦ ⟪G x, v⟫ * φ x) =
      fun x ↦ ∑ i, v i * (⟪G x, EuclideanSpace.single i 1⟫ * φ x) := by
    funext x
    conv_lhs => rw [hv]
    rw [inner_sum, Finset.sum_mul]
    simp only [real_inner_smul_right]
    congr 1; funext i; ring
  rw [e1, e2, integral_finsetSum _ i1, integral_finsetSum _ i2, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_const_mul, integral_const_mul, h φ hφ hφc i, mul_neg]

/-! ### Uniform approximation of test functions -/

/-- `|∫ f h| ≤ ε ∫_K |f|` when `|h| ≤ ε` and `h = 0` off `K`. -/
theorem abs_integral_mul_le {f h : E k → ℝ} {K : Set (E k)} (hK : MeasurableSet K)
    (hf : IntegrableOn f K) {ε : ℝ} (hh : ∀ y, |h y| ≤ ε) (h0 : ∀ y ∉ K, h y = 0) :
    |∫ y, f y * h y| ≤ ε * ∫ y in K, |f y| := by
  have hint : Integrable (K.indicator fun y ↦ ε * |f y|) :=
    (integrable_indicator_iff hK).2 (Integrable.const_mul (Integrable.norm hf) ε)
  have := norm_integral_le_of_norm_le (f := fun y ↦ f y * h y) hint
    (Eventually.of_forall fun y ↦ ?_)
  · rw [integral_indicator hK, integral_const_mul] at this
    simpa using this
  · by_cases hy : y ∈ K
    · rw [indicator_of_mem hy, Real.norm_eq_abs, abs_mul, mul_comm ε]
      exact mul_le_mul_of_nonneg_left (hh y) (abs_nonneg _)
    · rw [indicator_of_notMem hy, h0 y hy, mul_zero, norm_zero]

/-- The test functions supported in `closedBall 0 n`. -/
def TestBall (k n : ℕ) : Set (E k → ℝ) :=
  {φ | ContDiff ℝ ∞ φ ∧ tsupport φ ⊆ closedBall 0 n}

/-- Values and gradients on `closedBall 0 n`. -/
def testJet {n : ℕ} (φ : TestBall k n) : C(closedBall (0 : E k) n, ℝ × E k) :=
  ⟨fun y ↦ (φ.1 y.1, ∇ φ.1 y.1), ((φ.2.1.continuous.comp continuous_subtype_val).prodMk
    ((continuous_gradient (φ.2.1.of_le (by simp))).comp continuous_subtype_val))⟩

/-- A countable family of test functions, dense for the uniform convergence of values and
gradients. -/
theorem exists_countable_dense_testBall (n : ℕ) :
    ∃ D : Set (TestBall k n), D.Countable ∧ ∀ φ : TestBall k n,
      ∃ ψ : ℕ → TestBall k n, (∀ j, ψ j ∈ D) ∧
        Tendsto (fun j ↦ ‖testJet (ψ j) - testJet φ‖) atTop (𝓝 0) := by
  have hsep : TopologicalSpace.IsSeparable (range (testJet (k := k) (n := n))) :=
    (TopologicalSpace.isSeparable_univ_iff.2 inferInstance).mono (subset_univ _)
  obtain ⟨t, hts, htc, hdense⟩ := hsep.exists_countable_dense_subset
  have hpre : ∀ c : t, ∃ φ : TestBall k n, testJet φ = c.1 := fun c ↦ hts c.2
  choose f hf using hpre
  have := htc.to_subtype
  refine ⟨range f, countable_range f, fun φ ↦ ?_⟩
  obtain ⟨c, hct, hc⟩ := mem_closure_iff_seq_limit.1 (hdense (mem_range_self φ))
  refine ⟨fun j ↦ f ⟨c j, hct j⟩, fun j ↦ mem_range_self _, ?_⟩
  simp only [hf]
  exact tendsto_iff_norm_sub_tendsto_zero.1 hc

theorem abs_sub_le_testJet {n : ℕ} (φ ψ : TestBall k n) (y : E k) :
    |φ.1 y - ψ.1 y| ≤ ‖testJet φ - testJet ψ‖ ∧
      ‖∇ φ.1 y - ∇ ψ.1 y‖ ≤ ‖testJet φ - testJet ψ‖ := by
  by_cases hy : y ∈ closedBall (0 : E k) n
  · have h := ContinuousMap.norm_coe_le_norm (testJet φ - testJet ψ) ⟨y, hy⟩
    simp only [ContinuousMap.sub_apply, testJet, ContinuousMap.coe_mk, Prod.norm_def,
      Prod.fst_sub, Prod.snd_sub, max_le_iff, Real.norm_eq_abs] at h
    exact h
  · have h1 : y ∉ tsupport φ.1 := fun h ↦ hy (φ.2.2 h)
    have h2 : y ∉ tsupport ψ.1 := fun h ↦ hy (ψ.2.2 h)
    have g1 : ∇ φ.1 y = 0 := by
      rw [gradient, EllipticBernoulli.fderiv_apply_eq_zero_of_notMem_tsupport h1 |> fun _ ↦
        (show fderiv ℝ φ.1 y = 0 from
          Function.notMem_support.1 fun h ↦ h1 (support_fderiv_subset ℝ h)), map_zero]
    have g2 : ∇ ψ.1 y = 0 := by
      rw [gradient, (show fderiv ℝ ψ.1 y = 0 from
          Function.notMem_support.1 fun h ↦ h2 (support_fderiv_subset ℝ h)), map_zero]
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2, g1, g2]
    simp

/-! ### Slices of weak gradients -/

/-- **Slices of weak gradients.** If `G` is a weak gradient of `V` in `ℝ^{k+1}`, then for almost
every `s`, `π G(·, s)` is a weak gradient of `V(·, s)` in `ℝᵏ`. -/
theorem ae_hasWeakGradient_slice {V : E (k + 1) → ℝ} {G : E (k + 1) → E (k + 1)}
    (h : HasWeakGradient univ V G) :
    ∀ᵐ s : ℝ, HasWeakGradient univ (fun y ↦ V (joinLast y s))
      (fun y ↦ projInit k (G (joinLast y s))) := by
  have hV : LocallyIntegrable V := locallyIntegrableOn_univ.1 h.1
  have hG : LocallyIntegrable fun x ↦ projInit k (G x) := by
    refine (locallyIntegrable_iff).2 fun K hK ↦ ?_
    exact (projInit k).integrable_comp
      ((locallyIntegrableOn_univ.1 h.2.1).integrableOn_isCompact hK)
  choose D hDc hD using fun n : ℕ ↦ exists_countable_dense_testBall (k := k) n
  have hgood : ∀ n : ℕ, ∀ φ : D n, ∀ i : Fin k, ∀ᵐ s : ℝ,
      (∫ y, V (joinLast y s) * fderiv ℝ φ.1.1 y (EuclideanSpace.single i 1)) +
        ∫ y, ⟪projInit k (G (joinLast y s)), EuclideanSpace.single i 1⟫ * φ.1.1 y = 0 :=
    fun n φ i ↦ ae_slice_identity h φ.1.2.1
      (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 n)
        (subset_tsupport _ |>.trans φ.1.2.2)) _
  have hall : ∀ᵐ s : ℝ, ∀ n : ℕ, ∀ φ : D n, ∀ i : Fin k,
      (∫ y, V (joinLast y s) * fderiv ℝ φ.1.1 y (EuclideanSpace.single i 1)) +
        ∫ y, ⟪projInit k (G (joinLast y s)), EuclideanSpace.single i 1⟫ * φ.1.1 y = 0 := by
    refine ae_all_iff.2 fun n ↦ ?_
    have := (hDc n).to_subtype
    exact ae_all_iff.2 fun φ ↦ ae_all_iff.2 fun i ↦ hgood n φ i
  filter_upwards [hall, ae_locallyIntegrable_slice hV, ae_locallyIntegrable_slice hG]
    with s hs hVs hGs
  refine hasWeakGradient_of_forall_single hVs hGs fun φ hφ hφc i ↦ ?_
  set e : E k := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨n, hn⟩ := exists_nat_ge R
  have hsupp : tsupport φ ⊆ closedBall 0 n := hR.trans (closedBall_subset_closedBall hn)
  set φ' : TestBall k n := ⟨φ, hφ, hsupp⟩
  obtain ⟨ψ, hψD, hψ⟩ := hD n φ'
  set A : (E k → ℝ) → ℝ := fun g ↦ (∫ y, V (joinLast y s) * fderiv ℝ g y e) +
    ∫ y, ⟪projInit k (G (joinLast y s)), e⟫ * g y
  have hA0 : ∀ j, A (ψ j).1 = 0 := fun j ↦ hs n ⟨ψ j, hψD j⟩ i
  set M := (∫ y in closedBall (0 : E k) n, |V (joinLast y s)|) +
    ∫ y in closedBall (0 : E k) n, |⟪projInit k (G (joinLast y s)), e⟫|
  have hVs' : LocallyIntegrableOn (fun y ↦ V (joinLast y s)) univ := locallyIntegrableOn_univ.2 hVs
  have hGs' : LocallyIntegrableOn (fun y ↦ projInit k (G (joinLast y s))) univ :=
    locallyIntegrableOn_univ.2 hGs
  have hcs : ∀ g : TestBall k n, HasCompactSupport g.1 := fun g ↦
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 n)
      (subset_tsupport _ |>.trans g.2.2)
  have hbound : ∀ j, |A φ| ≤ ‖testJet (ψ j) - testJet φ'‖ * M := by
    intro j
    set ε := ‖testJet (ψ j) - testJet φ'‖
    have hψj := (ψ j).2.1
    have i1 := integrable_fderiv_apply_mul hVs' hφ hφc (subset_univ _) e
    have i2 := integrable_fderiv_apply_mul hVs' hψj (hcs (ψ j)) (subset_univ _) e
    have i3 := integrable_inner_mul hGs' hφ.continuous hφc (subset_univ _) e
    have i4 := integrable_inner_mul hGs' hψj.continuous (hcs (ψ j)) (subset_univ _) e
    have hdiff : A φ = A φ - A (ψ j).1 := by rw [hA0 j, sub_zero]
    have hsplit : A φ - A (ψ j).1 =
        (∫ y, V (joinLast y s) * (fderiv ℝ φ y e - fderiv ℝ (ψ j).1 y e)) +
          ∫ y, ⟪projInit k (G (joinLast y s)), e⟫ * (φ y - (ψ j).1 y) := by
      have : A φ - A (ψ j).1 =
          ((∫ y, V (joinLast y s) * fderiv ℝ φ y e) - ∫ y, V (joinLast y s) * fderiv ℝ (ψ j).1 y e)
          + ((∫ y, ⟪projInit k (G (joinLast y s)), e⟫ * φ y) -
            ∫ y, ⟪projInit k (G (joinLast y s)), e⟫ * (ψ j).1 y) := by
        simp only [A]; ring
      rw [this, ← integral_sub i1 i2, ← integral_sub i3 i4]
      simp only [mul_sub]
    have hK := measurableSet_closedBall (x := (0 : E k)) (ε := (n : ℝ))
    have b1 := abs_integral_mul_le (h := fun y ↦ fderiv ℝ φ y e - fderiv ℝ (ψ j).1 y e) hK
      (hVs.integrableOn_isCompact (isCompact_closedBall 0 n)) (ε := ε)
      (fun y ↦ by
        have h3 := (abs_sub_le_testJet (ψ j) φ' y).2
        rw [← inner_gradient_left_eq_fderiv, ← inner_gradient_left_eq_fderiv, ← inner_sub_left]
        calc |⟪∇ φ y - ∇ (ψ j).1 y, e⟫| ≤ ‖∇ φ y - ∇ (ψ j).1 y‖ * ‖e‖ :=
              abs_real_inner_le_norm _ _
          _ = ‖∇ (ψ j).1 y - ∇ φ y‖ := by rw [he, mul_one, norm_sub_rev]
          _ ≤ ε := h3)
      (fun y hy ↦ by
        have h1 : y ∉ tsupport φ := fun h ↦ hy (hsupp h)
        have h2 : y ∉ tsupport (ψ j).1 := fun h ↦ hy ((ψ j).2.2 h)
        rw [EllipticBernoulli.fderiv_apply_eq_zero_of_notMem_tsupport h1,
          EllipticBernoulli.fderiv_apply_eq_zero_of_notMem_tsupport h2, sub_zero])
    have hGint : IntegrableOn (fun y ↦ ⟪projInit k (G (joinLast y s)), e⟫) (closedBall 0 n) :=
      (locallyIntegrableOn_univ.1 (locallyIntegrableOn_inner_const hGs' e)).integrableOn_isCompact
        (isCompact_closedBall 0 n)
    have b2 := abs_integral_mul_le (h := fun y ↦ φ y - (ψ j).1 y) hK hGint (ε := ε)
      (fun y ↦ by
        have := (abs_sub_le_testJet (ψ j) φ' y).1
        rw [abs_sub_comm]; exact this)
      (fun y hy ↦ by
        have h1 : y ∉ tsupport φ := fun h ↦ hy (hsupp h)
        have h2 : y ∉ tsupport (ψ j).1 := fun h ↦ hy ((ψ j).2.2 h)
        rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2, sub_zero])
    rw [hdiff, hsplit]
    calc _ ≤ _ := abs_add_le _ _
      _ ≤ ε * (∫ y in closedBall (0 : E k) n, |V (joinLast y s)|) +
            ε * ∫ y in closedBall (0 : E k) n, |⟪projInit k (G (joinLast y s)), e⟫| :=
            add_le_add b1 b2
      _ = ε * M := by ring
  have hlim : Tendsto (fun j ↦ ‖testJet (ψ j) - testJet φ'‖ * M) atTop (𝓝 0) := by
    simpa using hψ.mul_const M
  have habs : |A φ| ≤ 0 := ge_of_tendsto' hlim hbound
  have hA : A φ = 0 := abs_nonpos_iff.1 habs
  simp only [A] at hA
  linarith

end OnePhaseDimension
