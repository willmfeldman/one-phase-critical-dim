/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.DomainVariationDensity
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The flow of a domain variation

For a Lipschitz vector field `ξ` with constant `L` and `|t| L < 1`, the map
`Φ_t(y) = y + t ξ(y)` is a bi-Lipschitz bijection of `ℝᵈ`. It fixes every point outside the
support of `ξ`, hence maps every set containing `tsupport ξ` onto itself. At a point `y` where
`ξ` is differentiable, `DΦ_t(y) = I + t Dξ(y)`; if `u` is also differentiable at `y` and
`‖t Dξ(y)‖ < 1`, then `v = u ∘ Φ_t⁻¹` is differentiable at `Φ_t(y)` with
`|∇v(Φ_t(y))|² = ∑ᵢ (∇u(y) · (I + t Dξ(y))⁻¹ eᵢ)²`.
-/

open Set Filter Topology Metric
open scoped RealInnerProductSpace NNReal Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ} {ξ : E d → E d} {L : ℝ≥0} {t : ℝ}

/-- The domain variation `Φ_t(y) = y + t ξ(y)`. -/
def dvFlow (ξ : E d → E d) (t : ℝ) (y : E d) : E d :=
  y + t • ξ y

theorem dvFlow_sub (ξ : E d → E d) (t : ℝ) (x y : E d) :
    dvFlow ξ t x - dvFlow ξ t y - (x - y) = t • (ξ x - ξ y) := by
  simp only [dvFlow, smul_sub]
  abel

theorem norm_dvFlow_sub_le (hξ : LipschitzWith L ξ) (x y : E d) :
    ‖dvFlow ξ t x - dvFlow ξ t y - (x - y)‖ ≤ |t| * L * ‖x - y‖ := by
  rw [dvFlow_sub, norm_smul, Real.norm_eq_abs, mul_assoc]
  gcongr
  simpa [dist_eq_norm] using hξ.dist_le_mul x y

/-- `Φ_t` expands distances by at least the factor `1 - |t| L`. -/
theorem mul_dist_le_dist_dvFlow (hξ : LipschitzWith L ξ) (x y : E d) :
    (1 - |t| * L) * dist x y ≤ dist (dvFlow ξ t x) (dvFlow ξ t y) := by
  have h := norm_dvFlow_sub_le (t := t) hξ x y
  have htri : ‖x - y‖ ≤ ‖dvFlow ξ t x - dvFlow ξ t y‖ +
      ‖dvFlow ξ t x - dvFlow ξ t y - (x - y)‖ := by
    simpa using norm_sub_le (dvFlow ξ t x - dvFlow ξ t y) (dvFlow ξ t x - dvFlow ξ t y - (x - y))
  rw [dist_eq_norm, dist_eq_norm]
  nlinarith

theorem approximatesLinearOn_dvFlow (hξ : LipschitzWith L ξ) (t : ℝ) :
    ApproximatesLinearOn (dvFlow ξ t) ((ContinuousLinearEquiv.refl ℝ (E d) : E d →L[ℝ] E d))
      univ (‖t‖₊ * L) := by
  intro x _ y _
  simpa [Real.norm_eq_abs] using norm_dvFlow_sub_le (t := t) hξ x y

theorem surjective_dvFlow (hξ : LipschitzWith L ξ) (ht : |t| * L < 1) :
    Function.Surjective (dvFlow ξ t) := by
  refine (approximatesLinearOn_dvFlow hξ t).surjective ?_
  rcases subsingleton_or_nontrivial (E d) with h | h
  · exact Or.inl h
  · right
    have hN : ‖((ContinuousLinearEquiv.refl ℝ (E d)).symm : E d →L[ℝ] E d)‖₊ = 1 := by
      simp
    rw [hN, inv_one, ← NNReal.coe_lt_coe]
    simpa [Real.norm_eq_abs] using ht

theorem injective_dvFlow (hξ : LipschitzWith L ξ) (ht : |t| * L < 1) :
    Function.Injective (dvFlow ξ t) := by
  intro x y hxy
  have h := mul_dist_le_dist_dvFlow (t := t) hξ x y
  rw [hxy, dist_self] at h
  have hpos : 0 < 1 - |t| * L := by linarith
  refine dist_le_zero.1 ?_
  by_contra hc
  push Not at hc
  nlinarith [mul_pos hpos hc]

/-- `Φ_t` as an equivalence of `ℝᵈ`. -/
def dvFlowEquiv (hξ : LipschitzWith L ξ) (ht : |t| * L < 1) : E d ≃ E d :=
  Equiv.ofBijective (dvFlow ξ t) ⟨injective_dvFlow hξ ht, surjective_dvFlow hξ ht⟩

@[simp]
theorem dvFlowEquiv_apply (hξ : LipschitzWith L ξ) (ht : |t| * L < 1) (y : E d) :
    dvFlowEquiv hξ ht y = dvFlow ξ t y :=
  rfl

theorem lipschitzWith_dvFlow (hξ : LipschitzWith L ξ) (t : ℝ) :
    LipschitzWith (1 + ‖t‖₊ * L) (dvFlow ξ t) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have h := norm_dvFlow_sub_le (t := t) hξ x y
  have htri := norm_add_le (dvFlow ξ t x - dvFlow ξ t y - (x - y)) (x - y)
  simp only [sub_add_cancel] at htri
  rw [dist_eq_norm, dist_eq_norm]
  push_cast
  simp only [Real.norm_eq_abs]
  nlinarith [norm_nonneg (x - y)]

/-- `Φ_t⁻¹` is Lipschitz with constant `(1 - |t| L)⁻¹`. -/
theorem lipschitzWith_dvFlowEquiv_symm (hξ : LipschitzWith L ξ) (ht : |t| * L < 1) :
    LipschitzWith (Real.toNNReal (1 - |t| * L)⁻¹) (dvFlowEquiv hξ ht).symm := by
  have hpos : 0 < 1 - |t| * L := by linarith
  refine LipschitzWith.of_dist_le_mul fun a b ↦ ?_
  set e := dvFlowEquiv hξ ht
  have h := mul_dist_le_dist_dvFlow (t := t) hξ (e.symm a) (e.symm b)
  have hea : dvFlow ξ t (e.symm a) = a := e.apply_symm_apply a
  have heb : dvFlow ξ t (e.symm b) = b := e.apply_symm_apply b
  rw [hea, heb] at h
  rw [Real.coe_toNNReal _ (inv_nonneg.2 hpos.le), ← div_eq_inv_mul, le_div_iff₀ hpos, mul_comm]
  exact h

/-- `Φ_t` fixes every point outside the support of `ξ`. -/
theorem dvFlow_of_notMem_tsupport {y : E d} (hy : y ∉ tsupport ξ) : dvFlow ξ t y = y := by
  simp [dvFlow, image_eq_zero_of_notMem_tsupport hy]

/-- `Φ_t` maps every set containing `tsupport ξ` onto itself. -/
theorem image_dvFlow_eq (hξ : LipschitzWith L ξ) (ht : |t| * L < 1) {B : Set (E d)}
    (hB : tsupport ξ ⊆ B) : dvFlow ξ t '' B = B := by
  have hinj := injective_dvFlow hξ ht
  have hK : ∀ y ∈ tsupport ξ, dvFlow ξ t y ∈ tsupport ξ := by
    intro y hy
    by_contra h
    have := dvFlow_of_notMem_tsupport (t := t) h
    rw [hinj this] at h
    exact h hy
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hyK : y ∈ tsupport ξ
    · exact hB (hK y hyK)
    · rwa [dvFlow_of_notMem_tsupport hyK]
  · intro hx
    obtain ⟨y, rfl⟩ := surjective_dvFlow hξ ht x
    by_cases hyK : y ∈ tsupport ξ
    · exact ⟨y, hB hyK, rfl⟩
    · rw [dvFlow_of_notMem_tsupport hyK] at hx ⊢
      exact ⟨y, hx, dvFlow_of_notMem_tsupport hyK⟩

/-! ### Derivatives -/

theorem hasFDerivAt_dvFlow {y : E d} (hy : DifferentiableAt ℝ ξ y) (t : ℝ) :
    HasFDerivAt (dvFlow ξ t) (1 + t • fderiv ℝ ξ y) y :=
  (hasFDerivAt_id y).add (hy.hasFDerivAt.const_smul t)

/-- The inner product of a gradient with a vector is the directional derivative. -/
theorem inner_gradient_eq (f : E d → ℝ) (x v : E d) : ⟪∇ f x, v⟫ = fderiv ℝ f x v := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

/-- `|w|² = ∑ᵢ (w · eᵢ)²`. -/
theorem norm_sq_eq_pullbackSq_one (w : E d) : ‖w‖ ^ 2 = pullbackSq 1 w :=
  (pullbackSq_one w).symm

/-- **The gradient of `u ∘ Φ_t⁻¹`.** If `ξ` and `u` are differentiable at `y` and
`‖t Dξ(y)‖ < 1`, then `|∇(u ∘ Φ_t⁻¹)(Φ_t(y))|² = ∑ᵢ (∇u(y) · (I + t Dξ(y))⁻¹ eᵢ)²`. -/
theorem norm_gradient_comp_symm_sq (hξ : LipschitzWith L ξ) (ht : |t| * L < 1) {u : E d → ℝ}
    {y : E d} (hξy : DifferentiableAt ℝ ξ y) (huy : DifferentiableAt ℝ u y)
    (hsmall : ‖t • fderiv ℝ ξ y‖ < 1) :
    ‖∇ (u ∘ (dvFlowEquiv hξ ht).symm) (dvFlow ξ t y)‖ ^ 2 =
      pullbackSq (Ring.inverse (1 + t • fderiv ℝ ξ y)) (∇ u y) := by
  set e := dvFlowEquiv hξ ht
  set U := (isUnit_one_add hsmall).unit
  set f' := ContinuousLinearEquiv.unitsEquiv ℝ (E d) U
  have hf' : (f' : E d →L[ℝ] E d) = 1 + t • fderiv ℝ ξ y :=
    (isUnit_one_add hsmall).unit_spec
  have hsymm : (f'.symm : E d →L[ℝ] E d) = Ring.inverse (1 + t • fderiv ℝ ξ y) := by
    rw [← (isUnit_one_add hsmall).unit_spec, Ring.inverse_unit]
    rfl
  have hcont : Continuous e.symm := (lipschitzWith_dvFlowEquiv_symm hξ ht).continuous
  have hey : e.symm (dvFlow ξ t y) = y := e.symm_apply_apply y
  have hΦ : HasFDerivAt (dvFlow ξ t) (f' : E d →L[ℝ] E d) (e.symm (dvFlow ξ t y)) := by
    rw [hey, hf']
    exact hasFDerivAt_dvFlow hξy t
  have hΨ : HasFDerivAt e.symm (f'.symm : E d →L[ℝ] E d) (dvFlow ξ t y) :=
    HasFDerivAt.of_local_left_inverse hcont.continuousAt hΦ
      (Eventually.of_forall fun z ↦ (e.apply_symm_apply z : dvFlow ξ t (e.symm z) = z))
  have hu : HasFDerivAt u (fderiv ℝ u y) (e.symm (dvFlow ξ t y)) := by
    rw [hey]
    exact huy.hasFDerivAt
  have hv := hu.comp (dvFlow ξ t y) hΨ
  rw [norm_sq_eq_pullbackSq_one, pullbackSq, pullbackSq]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [inner_gradient_eq, inner_gradient_eq, hv.fderiv, ContinuousLinearMap.comp_apply, hsymm]
  rfl

end OnePhaseDimension
