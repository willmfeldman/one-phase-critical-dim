/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# The Rodrigues rotation

For unit vectors `a, b` of a real inner product space with `⟪a, b⟫ ≠ -1`, the Rodrigues rotation

  `R_{a→b} = I + K + (1 + ⟪a, b⟫)⁻¹ K²`,  `K = b aᵀ - a bᵀ`, i.e. `K v = ⟪a, v⟫ b - ⟪b, v⟫ a`,

is the rotation in the plane `span {a, b}` taking `a` to `b`, fixing the orthogonal complement of
that plane. It preserves inner products, depends smoothly on `b` on `{⟪a, b⟫ ≠ -1}`, equals the
identity at `b = a`, and its derivative in `b` at `b = a` is `v ↦ K_{a,v} = v aᵀ - a vᵀ`.

It is used to transport tangent frames along the unit sphere: near a base point `x₀`, the frame
`R_{x₀→y} τᵢ` is a smooth orthonormal frame of `y^⊥`.

## Main results

* `rodrigues`, `rodrigues_apply`, `rodrigues_self`.
* `rodrigues_apply_self`: `R_{a→b} a = b`.
* `rodrigues_orthogonal`: `⟪R v, R w⟫ = ⟪v, w⟫`; `rodriguesIsometry` as a linear isometry.
* `contDiffOn_rodrigues`: smoothness in `b` on `{b | ⟪a, b⟫ ≠ -1}`.
* `hasFDerivAt_rodrigues_self`, `fderiv_rodrigues_at_self`: the derivative at `b = a` is
  `v ↦ rotGen a v`.
-/

open scoped RealInnerProductSpace ContDiff

@[expose] public noncomputable section

namespace OnePhaseDimension

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {a b : F}

/-- The real inner product as a continuous bilinear map. -/
def realInnerCLM : F →L[ℝ] F →L[ℝ] ℝ := innerSL ℝ

@[simp] theorem realInnerCLM_apply (a b : F) : realInnerCLM a b = ⟪a, b⟫ := rfl

/-- The infinitesimal rotation `K_{a,b} = b aᵀ - a bᵀ`, `v ↦ ⟪a, v⟫ b - ⟪b, v⟫ a`. -/
def rotGen (a b : F) : F →L[ℝ] F :=
  (realInnerCLM a).smulRight b - (realInnerCLM b).smulRight a

@[simp] theorem rotGen_apply (a b v : F) : rotGen a b v = ⟪a, v⟫ • b - ⟪b, v⟫ • a := by
  simp [rotGen]

@[simp] theorem rotGen_self (a : F) : rotGen a a = 0 := by
  ext v
  simp

/-- `b ↦ K_{a,b}` as a continuous linear map. -/
def rotGenL (a : F) : F →L[ℝ] F →L[ℝ] F :=
  ContinuousLinearMap.smulRightL ℝ F F (realInnerCLM a) -
    ((ContinuousLinearMap.smulRightL ℝ F F).flip a).comp realInnerCLM

@[simp] theorem rotGenL_apply (a b : F) : rotGenL a b = rotGen a b := by
  ext v
  simp [rotGenL]

/-- The Rodrigues rotation `R_{a→b} = I + K + (1 + ⟪a, b⟫)⁻¹ K²` with `K = K_{a,b}`. -/
def rodrigues (a b : F) : F →L[ℝ] F :=
  1 + rotGen a b + (1 + ⟪a, b⟫)⁻¹ • (rotGen a b).comp (rotGen a b)

theorem rodrigues_apply (a b v : F) :
    rodrigues a b v = v + rotGen a b v + (1 + ⟪a, b⟫)⁻¹ • rotGen a b (rotGen a b v) := by
  rfl

@[simp] theorem rodrigues_self (a : F) : rodrigues a a = 1 := by
  simp [rodrigues]

/-- Explicit form: `R v = v + β b + γ a` with `β = s + α(sc - t)`, `γ = -t + α(tc - s)`, where
`s = ⟪a, v⟫`, `t = ⟪b, v⟫`, `c = ⟪a, b⟫`, `α = (1 + c)⁻¹`, for unit `a, b`. -/
theorem rodrigues_apply_eq (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (v : F) :
    rodrigues a b v = v + (⟪a, v⟫ + (1 + ⟪a, b⟫)⁻¹ * (⟪a, v⟫ * ⟪a, b⟫ - ⟪b, v⟫)) • b +
      (-⟪b, v⟫ + (1 + ⟪a, b⟫)⁻¹ * (⟪b, v⟫ * ⟪a, b⟫ - ⟪a, v⟫)) • a := by
  have haa : ⟪a, a⟫ = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hbb : ⟪b, b⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
  have hba : ⟪b, a⟫ = ⟪a, b⟫ := real_inner_comm _ _
  rw [rodrigues_apply]
  simp only [rotGen_apply, inner_sub_right, inner_smul_right, haa, hbb, hba]
  module

/-- `R_{a→b} a = b`. -/
theorem rodrigues_apply_self {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫ ≠ -1) :
    rodrigues a b a = b := by
  have haa : ⟪a, a⟫ = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hba : ⟪b, a⟫ = ⟪a, b⟫ := real_inner_comm _ _
  have h1 : 1 + ⟪a, b⟫ ≠ 0 := fun h ↦ hab (by linarith)
  rw [rodrigues_apply_eq ha hb, haa, hba]
  have e1 : 1 + (1 + ⟪a, b⟫)⁻¹ * (1 * ⟪a, b⟫ - ⟪a, b⟫) = 1 := by ring
  have e2 : -⟪a, b⟫ + (1 + ⟪a, b⟫)⁻¹ * (⟪a, b⟫ * ⟪a, b⟫ - 1) = -1 := by
    field_simp
    ring
  rw [e1, e2]
  module

/-- **Orthogonality.** For unit `a, b` with `⟪a, b⟫ ≠ -1`, `R_{a→b}` preserves inner products. -/
theorem rodrigues_orthogonal {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫ ≠ -1)
    (v w : F) : ⟪rodrigues a b v, rodrigues a b w⟫ = ⟪v, w⟫ := by
  have haa : ⟪a, a⟫ = 1 := by rw [real_inner_self_eq_norm_sq, ha]; norm_num
  have hbb : ⟪b, b⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hb]; norm_num
  have hba : ⟪b, a⟫ = ⟪a, b⟫ := real_inner_comm _ _
  have h1 : 1 + ⟪a, b⟫ ≠ 0 := fun h ↦ hab (by linarith)
  rw [rodrigues_apply_eq ha hb, rodrigues_apply_eq ha hb]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, haa, hbb, hba,
    RCLike.conj_to_real, real_inner_comm v b, real_inner_comm v a, real_inner_comm w b,
    real_inner_comm w a]
  field_simp
  ring

theorem norm_rodrigues_apply {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫ ≠ -1)
    (v : F) : ‖rodrigues a b v‖ = ‖v‖ := by
  rw [norm_eq_sqrt_real_inner, rodrigues_orthogonal ha hb hab, ← norm_eq_sqrt_real_inner]

/-- `R_{a→b}` as a linear isometry. -/
def rodriguesIsometry {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hab : ⟪a, b⟫ ≠ -1) :
    F →ₗᵢ[ℝ] F :=
  ⟨(rodrigues a b).toLinearMap, norm_rodrigues_apply ha hb hab⟩

@[simp] theorem rodriguesIsometry_apply {a b : F} (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : ⟪a, b⟫ ≠ -1) (v : F) : rodriguesIsometry ha hb hab v = rodrigues a b v := rfl

/-! ### Smoothness and the derivative at `b = a` -/

theorem contDiff_rotGen (a : F) {n : WithTop ℕ∞} : ContDiff ℝ n (rotGen a) := by
  have : rotGen a = fun b ↦ rotGenL a b := funext fun b ↦ (rotGenL_apply a b).symm
  rw [this]
  exact (rotGenL a).contDiff

/-- **Smoothness.** `b ↦ R_{a→b}` is smooth on `{b | ⟪a, b⟫ ≠ -1}`. -/
theorem contDiffOn_rodrigues (a : F) {n : WithTop ℕ∞} :
    ContDiffOn ℝ n (rodrigues a) {b | ⟪a, b⟫ ≠ -1} := by
  intro b hb
  have h1 : 1 + realInnerCLM a b ≠ 0 := fun h ↦ hb (by simp at h; linarith)
  have hK := contDiff_rotGen a (n := n)
  have hc : ContDiff ℝ n fun b : F ↦ realInnerCLM a b := (realInnerCLM a).contDiff
  refine ContDiffAt.contDiffWithinAt ?_
  change ContDiffAt ℝ n (fun b ↦ 1 + rotGen a b +
    (1 + realInnerCLM a b)⁻¹ • (rotGen a b).comp (rotGen a b)) b
  have hinv : ContDiffAt ℝ n (fun b ↦ (1 + realInnerCLM a b)⁻¹) b :=
    (contDiffAt_const.add hc.contDiffAt).inv h1
  exact (contDiffAt_const.add hK.contDiffAt).add
    (hinv.smul (hK.contDiffAt.clm_comp hK.contDiffAt))

/-- **The derivative at `b = a`.** `D_b R_{a→b}|_{b = a} v = K_{a,v} = v aᵀ - a vᵀ`. -/
theorem hasFDerivAt_rodrigues_self (a : F) : HasFDerivAt (rodrigues a) (rotGenL a) a := by
  have hK : ∀ b, HasFDerivAt (rotGen a) (rotGenL a) b := fun b ↦ by
    have : rotGen a = fun b ↦ rotGenL a b := funext fun b ↦ (rotGenL_apply a b).symm
    rw [this]
    exact (rotGenL a).hasFDerivAt
  have hc : HasFDerivAt (fun b : F ↦ 1 + realInnerCLM a b) (realInnerCLM a) a := by
    simpa using ((realInnerCLM a).hasFDerivAt (x := a)).const_add 1
  have h1 : 1 + realInnerCLM a a ≠ 0 := by
    simp only [realInnerCLM_apply, real_inner_self_eq_norm_sq]
    positivity
  have hinv := (hasFDerivAt_inv h1).comp a hc
  have hsq := (hK a).clm_comp (hK a)
  have hprod := hinv.smul hsq
  have hsum := ((hasFDerivAt_const (1 : F →L[ℝ] F) a).add (hK a)).add hprod
  convert hsum using 1
  · funext b
    simp [rodrigues]
  · ext v w
    simp

theorem fderiv_rodrigues_at_self (a v : F) : fderiv ℝ (rodrigues a) a v = rotGen a v := by
  rw [(hasFDerivAt_rodrigues_self a).fderiv, rotGenL_apply]

end OnePhaseDimension
