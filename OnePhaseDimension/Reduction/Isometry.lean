/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Regular
public import EllipticBernoulli.Sobolev.Energy
public import EllipticBernoulli.Sobolev.Lattice
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Isometry invariance and the splitting `ℝ^{k+1} = ℝᵏ × ℝ`

## Main results

* `hasWeakGradient_comp_affineIsometry`, `memH1Loc_comp_affineIsometry`: for an affine isometry
  `T x = L x + c`, the function `u ∘ T` has weak gradient `L⁻¹ (G ∘ T)`.
* `energyJ_comp_affineIsometry`: the energy is invariant under affine isometries.
* `isLocalEnergyMinimizer_comp_affineIsometry`: global minimality is invariant under affine
  isometries.
* `splitLast`: the linear equivalence `ℝ^{k+1} ≃ ℝᵏ × ℝ` splitting off the last coordinate, with
  `measurePreserving_splitLast` (Lebesgue measure goes to the product measure),
  `inner_eq_splitLast` and `norm_sq_eq_splitLast`.
* The first factor of `splitLast` is `projInit`, which is `dropLast` in dimension six.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff RealInnerProductSpace ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ}

/-! ### Affine isometries -/

section AffineIsometry

variable (L : E d ≃ₗᵢ[ℝ] E d) (c : E d)

/-- The affine isometry `x ↦ L x + c` as a homeomorphism. -/
def affineIsometryHomeomorph : E d ≃ₜ E d :=
  L.toHomeomorph.trans (Homeomorph.addRight c)

@[simp]
theorem affineIsometryHomeomorph_apply (x : E d) : affineIsometryHomeomorph L c x = L x + c :=
  rfl

@[simp]
theorem affineIsometryHomeomorph_symm_apply (y : E d) :
    (affineIsometryHomeomorph L c).symm y = L.symm (y - c) := by
  rw [Homeomorph.symm_apply_eq]
  simp

theorem affineIsometry_symm_apply_apply (x : E d) : L.symm (L x + c) + -L.symm c = x := by
  rw [map_add, LinearIsometryEquiv.symm_apply_apply, add_neg_cancel_right]

theorem affineIsometry_apply_symm_apply (y : E d) : L (L.symm y + -L.symm c) + c = y := by
  rw [map_add, map_neg, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply,
    neg_add_cancel_right]

theorem measurePreserving_affineIsometry :
    MeasurePreserving (fun x : E d ↦ L x + c) volume volume :=
  (measurePreserving_add_right volume c).comp L.measurePreserving

theorem measurableEmbedding_affineIsometry : MeasurableEmbedding (fun x : E d ↦ L x + c) :=
  (affineIsometryHomeomorph L c).measurableEmbedding

theorem preimage_affineIsometry_ball (y : E d) (r : ℝ) :
    (fun x : E d ↦ L x + c) ⁻¹' ball y r = ball (L.symm (y - c)) r := by
  ext x
  simp only [mem_preimage, mem_ball, dist_eq_norm]
  rw [← L.norm_map (x - L.symm (y - c)), map_sub, LinearIsometryEquiv.apply_symm_apply,
    show L x + c - y = L x - (y - c) by abel]

theorem injective_affineIsometry : Function.Injective (fun x : E d ↦ L x + c) :=
  (affineIsometryHomeomorph L c).injective

theorem hasFDerivAt_affineIsometry (x : E d) :
    HasFDerivAt (fun x : E d ↦ L x + c) (L.toContinuousLinearEquiv : E d →L[ℝ] E d) x :=
  (L.toContinuousLinearEquiv.hasFDerivAt).add_const c

/-- Local integrability is preserved by composition with an affine isometry. -/
theorem locallyIntegrable_comp_affineIsometry {F : Type*} [NormedAddCommGroup F] {g : E d → F}
    (hg : LocallyIntegrable g) : LocallyIntegrable (fun x ↦ g (L x + c)) := by
  refine (locallyIntegrable_iff).2 fun K hK ↦ ?_
  have hK' : IsCompact ((fun x : E d ↦ L x + c) '' K) :=
    hK.image (affineIsometryHomeomorph L c).continuous
  have h := ((measurePreserving_affineIsometry L c).integrableOn_comp_preimage
    (measurableEmbedding_affineIsometry L c)).2 (hg.integrableOn_isCompact hK')
  rwa [preimage_image_eq _ (injective_affineIsometry L c)] at h

/-- `L²` integrability on a compact set, transported by an affine isometry. -/
theorem memLp_comp_affineIsometry {F : Type*} [NormedAddCommGroup F] {g : E d → F} {K : Set (E d)}
    (hg : MemLp g 2 (volume.restrict ((fun x : E d ↦ L x + c) '' K))) :
    MemLp (fun x ↦ g (L x + c)) 2 (volume.restrict K) := by
  have hmp := (measurePreserving_affineIsometry L c).restrict_preimage_emb
    (measurableEmbedding_affineIsometry L c) ((fun x : E d ↦ L x + c) '' K)
  rw [preimage_image_eq _ (injective_affineIsometry L c)] at hmp
  exact hg.comp_measurePreserving hmp

variable {L c}

/-- **Weak gradients under affine isometries.** If `G` is a weak gradient of `u` in `ℝᵈ`, then
`x ↦ L⁻¹ G(L x + c)` is a weak gradient of `x ↦ u(L x + c)`. -/
theorem hasWeakGradient_comp_affineIsometry {u : E d → ℝ}
    {G : E d → E d} (h : HasWeakGradient univ u G) :
    HasWeakGradient univ (fun x ↦ u (L x + c)) (fun x ↦ L.symm (G (L x + c))) := by
  have hu : LocallyIntegrable u := locallyIntegrableOn_univ.1 h.1
  have hG : LocallyIntegrable G := locallyIntegrableOn_univ.1 h.2.1
  refine ⟨locallyIntegrableOn_univ.2 (locallyIntegrable_comp_affineIsometry L c hu),
    locallyIntegrableOn_univ.2 ?_, fun φ hφ hφc _ v ↦ ?_⟩
  · have hG' : LocallyIntegrable fun y ↦ L.symm (G y) := by
      refine (locallyIntegrable_iff).2 fun K hK ↦ ?_
      exact (L.symm.toContinuousLinearEquiv : E d →L[ℝ] E d).integrable_comp
        (hG.integrableOn_isCompact hK)
    exact locallyIntegrable_comp_affineIsometry L c hG'
  set T := affineIsometryHomeomorph L c
  set ψ : E d → ℝ := φ ∘ T.symm with hψ
  have hψs : ContDiff ℝ ∞ ψ := by
    have : ψ = fun y ↦ φ (L.symm.toContinuousLinearEquiv (y - c)) := by
      funext y; simp [hψ, T]
    rw [this]
    exact hφ.comp ((L.symm.toContinuousLinearEquiv : E d →L[ℝ] E d).contDiff.comp
      (contDiff_id.sub contDiff_const))
  have hψc : HasCompactSupport ψ := hφc.comp_homeomorph T.symm
  have hφψ : ∀ x, φ x = ψ (L x + c) := fun x ↦ by
    simp [hψ, T]
  have hder : ∀ x, fderiv ℝ φ x v = fderiv ℝ ψ (L x + c) (L v) := by
    intro x
    have hφeq : φ = fun x ↦ ψ (L x + c) := funext hφψ
    have hd : HasFDerivAt (fun x ↦ ψ (L x + c))
        ((fderiv ℝ ψ (L x + c)).comp (L.toContinuousLinearEquiv : E d →L[ℝ] E d)) x :=
      ((hψs.differentiable (by simp)) _).hasFDerivAt.comp x (hasFDerivAt_affineIsometry L c x)
    rw [hφeq, hd.fderiv]
    rfl
  have hw := h.2.2 ψ hψs hψc (subset_univ _) (L v)
  simp only [Measure.restrict_univ] at hw ⊢
  have hmp := measurePreserving_affineIsometry L c
  have hme := measurableEmbedding_affineIsometry L c
  calc ∫ x, u (L x + c) * fderiv ℝ φ x v
      = ∫ x, (fun y ↦ u y * fderiv ℝ ψ y (L v)) (L x + c) := by
        simp_rw [hder]
    _ = ∫ y, u y * fderiv ℝ ψ y (L v) :=
        hmp.integral_comp hme (fun y ↦ u y * fderiv ℝ ψ y (L v))
    _ = -∫ y, ⟪G y, L v⟫ * ψ y := hw
    _ = -∫ x, (fun y ↦ ⟪G y, L v⟫ * ψ y) (L x + c) := by
        rw [hmp.integral_comp hme (fun y ↦ ⟪G y, L v⟫ * ψ y)]
    _ = -∫ x, ⟪L.symm (G (L x + c)), v⟫ * φ x := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only
        rw [← hφψ]
        conv_rhs => rw [← L.inner_map_map, LinearIsometryEquiv.apply_symm_apply]

/-- `H¹_loc(ℝᵈ)` is invariant under affine isometries. -/
theorem memH1Loc_comp_affineIsometry {u : E d → ℝ} {G : E d → E d}
    (h : MemH1Loc univ u G) :
    MemH1Loc univ (fun x ↦ u (L x + c)) (fun x ↦ L.symm (G (L x + c))) := by
  refine ⟨hasWeakGradient_comp_affineIsometry h.1, fun K _ hK ↦ ?_⟩
  have hK' : IsCompact ((fun x : E d ↦ L x + c) '' K) :=
    hK.image (affineIsometryHomeomorph L c).continuous
  obtain ⟨h1, h2⟩ := h.2 _ (subset_univ _) hK'
  exact ⟨memLp_comp_affineIsometry L c h1, memLp_comp_affineIsometry L c
    (h2.continuousLinearMap_comp (L.symm.toContinuousLinearEquiv : E d →L[ℝ] E d))⟩

variable (L c)

/-- **Energy invariance under affine isometries.** -/
theorem energyJ_comp_affineIsometry (V : Set (E d)) (Q u : E d → ℝ) (G : E d → E d) :
    energyJ ((fun x ↦ L x + c) ⁻¹' V) (fun x ↦ Q (L x + c)) (fun x ↦ u (L x + c))
      (fun x ↦ L.symm (G (L x + c))) = energyJ V Q u G := by
  unfold energyJ
  conv_rhs => rw [← (measurePreserving_affineIsometry L c).setLIntegral_comp_preimage_emb
    (measurableEmbedding_affineIsometry L c)]
  refine lintegral_congr fun x ↦ ?_
  congr 3
  exact L.symm.norm_map _

variable {L c}

/-- **Minimality under affine isometries.** If `u` is a local energy minimizer in `ℝᵈ`, so is
`x ↦ u(L x + c)` for every linear isometry `L` and every `c`. -/
theorem isLocalEnergyMinimizer_comp_affineIsometry {Q u : E d → ℝ}
    (h : IsLocalEnergyMinimizer univ Q u) :
    IsLocalEnergyMinimizer univ (fun x ↦ Q (L x + c)) (fun x ↦ u (L x + c)) := by
  obtain ⟨Gu, hGu, hmin⟩ := h
  refine ⟨_, memH1Loc_comp_affineIsometry hGu, fun x r hr _ ↦
    ⟨memH1Loc_comp_affineIsometry hGu, fun _ _ ↦ rfl,
    fun _ _ ↦ mem_univ _, fun w Gw hw hwB _ ↦ ?_⟩⟩
  -- transport the competitor by the inverse isometry
  set w' : E d → ℝ := fun y ↦ w (L.symm y + -L.symm c)
  set Gw' : E d → E d := fun y ↦ L.symm.symm (Gw (L.symm y + -L.symm c))
  have hw' : MemH1Loc univ w' Gw' := memH1Loc_comp_affineIsometry (L := L.symm) (c := -L.symm c) hw
  have hball : (fun x ↦ L x + c) ⁻¹' ball (L x + c) r = ball x r := by
    rw [preimage_affineIsometry_ball, add_sub_cancel_right, LinearIsometryEquiv.symm_apply_apply]
  have hoff : ∀ᵐ y ∂(volume.restrict (univ \ ball (L x + c) r)), w' y = u y := by
    have hmp := (measurePreserving_affineIsometry L.symm (-L.symm c)).restrict_preimage_emb
      (measurableEmbedding_affineIsometry L.symm (-L.symm c)) (univ \ ball x r)
    have hpre : (fun y ↦ L.symm y + -L.symm c) ⁻¹' (univ \ ball x r) =
        univ \ ball (L x + c) r := by
      rw [preimage_sdiff, preimage_univ, preimage_affineIsometry_ball,
        LinearIsometryEquiv.symm_symm, sub_neg_eq_add, map_add,
        LinearIsometryEquiv.apply_symm_apply]
    rw [hpre] at hmp
    filter_upwards [hmp.quasiMeasurePreserving.ae hwB] with y hy
    change w (L.symm y + -L.symm c) = u y
    rw [hy, affineIsometry_apply_symm_apply]
  have hle := (hmin (L x + c) r hr (subset_univ _)).2.2.2 w' Gw' hw' hoff
    (Eventually.of_forall fun _ ↦ mem_univ _)
  have h1 := energyJ_comp_affineIsometry L c (ball (L x + c) r) Q u Gu
  have h2 := energyJ_comp_affineIsometry L c (ball (L x + c) r) Q w' Gw'
  rw [hball] at h1 h2
  have hw'T : (fun x ↦ w' (L x + c)) = w := funext fun y ↦ by
    simp only [w', affineIsometry_symm_apply_apply]
  have hGw'T : (fun x ↦ L.symm (Gw' (L x + c))) = Gw := funext fun y ↦ by
    simp only [Gw', LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply,
      affineIsometry_symm_apply_apply]
  rw [hw'T, hGw'T] at h2
  rw [h1, h2]
  exact hle

/-- Global minimality is invariant under linear isometries. -/
theorem isometryMinimality_holds : IsometryMinimality := by
  intro n L v h
  have := isLocalEnergyMinimizer_comp_affineIsometry (L := L) (c := 0) h
  simp only [add_zero] at this
  exact this

end AffineIsometry

/-! ### Splitting off the last coordinate -/

section Split

variable (k : ℕ)

/-- The linear equivalence `ℝ^{k+1} ≃ ℝᵏ × ℝ`, `x ↦ (x₁, …, x_k; x_{k+1})`. -/
def splitLastLinear : E (k + 1) ≃ₗ[ℝ] E k × ℝ where
  toFun x := (projInit k x, x (Fin.last k))
  invFun p := WithLp.toLp 2 (Fin.snoc (α := fun _ ↦ ℝ) (WithLp.ofLp p.1) p.2)
  map_add' x y := by ext <;> simp
  map_smul' a x := by ext <;> simp
  left_inv x := by
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  right_inv p := by
    ext i
    · simp
    · simp

/-- The splitting `ℝ^{k+1} ≃ ℝᵏ × ℝ` as a continuous linear equivalence. -/
def splitLast : E (k + 1) ≃L[ℝ] E k × ℝ :=
  (splitLastLinear k).toContinuousLinearEquiv

variable {k}

@[simp]
theorem splitLast_apply_fst (x : E (k + 1)) : (splitLast k x).1 = projInit k x := rfl

@[simp]
theorem splitLast_apply_snd (x : E (k + 1)) : (splitLast k x).2 = x (Fin.last k) := rfl

@[simp]
theorem splitLast_symm_apply_castSucc (p : E k × ℝ) (i : Fin k) :
    (splitLast k).symm p (Fin.castSucc i) = p.1 i := by
  change Fin.snoc (α := fun _ ↦ ℝ) (WithLp.ofLp p.1) p.2 (Fin.castSucc i) = _
  simp

@[simp]
theorem splitLast_symm_apply_last (p : E k × ℝ) : (splitLast k).symm p (Fin.last k) = p.2 := by
  change Fin.snoc (α := fun _ ↦ ℝ) (WithLp.ofLp p.1) p.2 (Fin.last k) = _
  simp

@[simp]
theorem projInit_splitLast_symm (p : E k × ℝ) : projInit k ((splitLast k).symm p) = p.1 := by
  ext i
  simp

/-- The inner product splits as the sum of the inner products of the factors. -/
theorem inner_eq_splitLast (x y : E (k + 1)) :
    ⟪x, y⟫ = ⟪(splitLast k x).1, (splitLast k y).1⟫ + (splitLast k x).2 * (splitLast k y).2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_castSucc, splitLast_apply_fst, splitLast_apply_snd,
    projInit_apply, RCLike.inner_apply, conj_trivial]
  ring

theorem norm_sq_eq_splitLast (x : E (k + 1)) :
    ‖x‖ ^ 2 = ‖(splitLast k x).1‖ ^ 2 + (splitLast k x).2 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_eq_splitLast, sq]

/-- **Fubini coordinates.** The splitting `ℝ^{k+1} ≃ ℝᵏ × ℝ` maps Lebesgue measure to the
product measure. -/
theorem measurePreserving_splitLast :
    MeasurePreserving (splitLast k) volume
      ((volume : Measure (E k)).prod (volume : Measure ℝ)) := by
  have h1 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (k + 1))
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℝ) (Fin.last k)
  rw [Measure.volume_eq_prod] at h2
  have h3 := Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure (Fin k → ℝ)))
  have h4 := (MeasurePreserving.symm _
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin k))).prod
    (MeasurePreserving.id (volume : Measure ℝ))
  have h := h4.comp (h3.comp (h2.comp h1))
  convert h using 1
  funext x
  ext i
  · simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init]
  · simp [MeasurableEquiv.piFinSuccAbove_apply]

theorem measurePreserving_splitLast_symm :
    MeasurePreserving (splitLast k).symm ((volume : Measure (E k)).prod (volume : Measure ℝ))
      volume :=
  MeasurePreserving.symm (splitLast k).toHomeomorph.toMeasurableEquiv measurePreserving_splitLast

end Split

end OnePhaseDimension
