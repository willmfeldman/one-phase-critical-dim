/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.Rotation
public import OnePhaseDimension.Geometry.Jets
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import OnePhaseDimension.Statements.CertificateGen

/-!
# Covariant derivatives on the sphere by Rodrigues transport

Fix a unit vector `x₀ ∈ ℝⁿ` and a linear isometry `ι : ℝ^{n-1} → x₀^⊥` with frame `τᵢ = ι eᵢ`.
For `x` near `x₀` let `x̂ = x/|x|` and let `R_x = R_{x₀→x̂}` be the Rodrigues rotation. The
transported frame `τᵢ(x) = R_x τᵢ` is an orthonormal frame of `x̂^⊥`, smooth in `x`, with
`τᵢ(x₀) = τᵢ` and derivative `Dτᵢ(x₀)[v] = -⟪v, τᵢ⟫ x₀`.

For a field `M` of `k`-linear forms, its transported components `x ↦ M(x)[τ_{i₁}(x), …,
τ_{i_k}(x)]` have derivative at `x₀`

  `DM(x₀)[v](τ_{i₁}, …, τ_{i_k}) - ∑ₛ ⟪v, τ_{iₛ}⟫ M(x₀)[τ_{i₁}, …, x₀ (slot s), …, τ_{i_k}]`

(`fderiv_transport_apply`). For a tangential field (one that vanishes when any slot is `x₀`) this
is the tangential part of the Euclidean derivative (`fderiv_transport_apply_of_tangential`): the
covariant derivative of a field on the sphere is the tangential projection of the ambient
derivative of its `0`-homogeneous extension.

Applied to the jets of a one-homogeneous function `u`, with `M = Dᵏu(x̂)`, this identifies the
spherical data of `ConeJets` with derivatives of transported quantities: `∇g = p`,
`∇_l pᵢ = T_{li} - g δ_{li}`, `∇T = B` and `∇B = DB`, where
`DB_{lijk} = D⁴u_{lijk} + δ_{li}T_{jk} + δ_{lj}T_{ik} + δ_{lk}T_{ij}`. The `δT` terms come from the
slots where `x₀` is inserted, through the Euler relation `D³u(x₀)[x₀, a, b] = -T(a, b)`.

## Main results

* `transFrame`, `hasFDerivAt_transFrame`, `fderiv_transFrame_apply`.
* `transFrame_self`, `inner_transFrame_transFrame`, `inner_transFrame_radialProj`,
  `transportIsometry`.
* `hasFDerivAt_transport_apply`, `fderiv_transport_apply`,
  `fderiv_transport_apply_of_tangential` (the projection identity).
* `transJet`, `fderiv_transJet_frame`.
* `transported_g`, `transported_p`, `transported_T`, `transported_B`.
-/

open Function Filter Topology Set
open scoped RealInnerProductSpace ContDiff

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### Radial projection -/

section Radial

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The radial projection `x ↦ x / |x|`. -/
def radialProj (x : F) : F := ‖x‖⁻¹ • x

theorem radialProj_of_norm_eq_one {x : F} (hx : ‖x‖ = 1) : radialProj x = x := by
  simp [radialProj, hx]

theorem norm_radialProj {x : F} (hx : x ≠ 0) : ‖radialProj x‖ = 1 := by
  rw [radialProj, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hx)]

/-- The orthogonal projection `v ↦ v - ⟪x₀, v⟫ x₀` onto `x₀^⊥`, for a unit vector `x₀`. -/
def tangentProj (x₀ : F) : F →L[ℝ] F := 1 - (realInnerCLM x₀).smulRight x₀

@[simp] theorem tangentProj_apply (x₀ v : F) : tangentProj x₀ v = v - ⟪x₀, v⟫ • x₀ := by
  simp [tangentProj]

theorem tangentProj_apply_of_inner_eq_zero {x₀ v : F} (h : ⟪x₀, v⟫ = 0) :
    tangentProj x₀ v = v := by
  simp [h]

theorem hasFDerivAt_norm_of_norm_eq_one {x₀ : F} (hx : ‖x₀‖ = 1) :
    HasFDerivAt (fun x : F ↦ ‖x‖) (realInnerCLM x₀) x₀ := by
  have h2 : HasFDerivAt (fun x : F ↦ ‖x‖ ^ 2) (2 • realInnerCLM x₀) x₀ :=
    (hasStrictFDerivAt_norm_sq x₀).hasFDerivAt
  have hs := h2.sqrt (by simp [hx])
  have heq : (fun x : F ↦ √(‖x‖ ^ 2)) = fun x ↦ ‖x‖ := funext fun x ↦ Real.sqrt_sq (norm_nonneg x)
  rw [heq] at hs
  convert hs using 1
  rw [hx]
  ext v
  simp

/-- The derivative of the radial projection at a unit vector is the tangential projection. -/
theorem hasFDerivAt_radialProj {x₀ : F} (hx : ‖x₀‖ = 1) :
    HasFDerivAt radialProj (tangentProj x₀) x₀ := by
  have hinv := (hasFDerivAt_inv (by simp [hx] : ‖x₀‖ ≠ 0)).comp x₀
    (hasFDerivAt_norm_of_norm_eq_one hx)
  exact (hinv.smul (hasFDerivAt_id x₀)).congr_fderiv (by
    ext v
    simp [hx, sub_eq_add_neg])

end Radial

/-! ### The transported frame -/

variable {n : ℕ}

/-- The transported frame `τᵢ(x) = R_{x₀→x̂} τᵢ`. -/
def transFrame (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (x : E n) (i : Fin (n - 1)) : E n :=
  rodrigues x₀ (radialProj x) (frameVec ι i)

variable {x₀ : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n}

theorem transFrame_self (hx : ‖x₀‖ = 1) (i : Fin (n - 1)) :
    transFrame x₀ ι x₀ i = frameVec ι i := by
  simp [transFrame, radialProj_of_norm_eq_one hx]

theorem inner_frameVec_self (hι : ∀ v, ⟪ι v, x₀⟫ = 0) (i : Fin (n - 1)) :
    ⟪x₀, frameVec ι i⟫ = 0 := by
  rw [real_inner_comm]
  exact hι _

/-- The derivative of the transported frame: `Dτᵢ(x₀)[v] = K_{x₀, Pv} τᵢ`. -/
theorem hasFDerivAt_transFrame (hx : ‖x₀‖ = 1) (i : Fin (n - 1)) :
    HasFDerivAt (fun x ↦ transFrame x₀ ι x i)
      ((ContinuousLinearMap.apply ℝ (E n) (frameVec ι i)).comp
        ((rotGenL x₀).comp (tangentProj x₀))) x₀ := by
  have hR : HasFDerivAt (rodrigues x₀) (rotGenL x₀) (radialProj x₀) := by
    rw [radialProj_of_norm_eq_one hx]
    exact hasFDerivAt_rodrigues_self x₀
  have h := (hR.comp x₀ (hasFDerivAt_radialProj hx))
  exact (ContinuousLinearMap.apply ℝ (E n) (frameVec ι i)).hasFDerivAt.comp x₀ h

/-- `Dτᵢ(x₀)[v] = -⟪v, τᵢ⟫ x₀`. -/
theorem fderiv_transFrame_apply (hx : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0)
    (i : Fin (n - 1)) (v : E n) :
    fderiv ℝ (fun x ↦ transFrame x₀ ι x i) x₀ v = -⟪v, frameVec ι i⟫ • x₀ := by
  rw [(hasFDerivAt_transFrame hx i).fderiv]
  have h0 := inner_frameVec_self hι i
  simp [h0, inner_sub_left, inner_smul_left]

/-! ### The transported frame is an orthonormal frame of `x̂^⊥` -/

/-- Near `x₀` the transport is defined: `x ≠ 0` and `⟪x₀, x̂⟫ ≠ -1`. -/
theorem eventually_transport_defined (hx : ‖x₀‖ = 1) :
    ∀ᶠ x in 𝓝 x₀, x ≠ 0 ∧ ⟪x₀, radialProj x⟫ ≠ -1 := by
  have hc : ContinuousAt (fun x ↦ ⟪x₀, radialProj x⟫) x₀ :=
    continuousAt_const.inner (hasFDerivAt_radialProj hx).continuousAt
  have h1 : ⟪x₀, radialProj x₀⟫ = 1 := by
    rw [radialProj_of_norm_eq_one hx, real_inner_self_eq_norm_sq, hx]; norm_num
  have hne : ∀ᶠ x in 𝓝 x₀, ⟪x₀, radialProj x⟫ ≠ -1 :=
    hc.eventually_ne (by rw [h1]; norm_num)
  have h0 : ∀ᶠ x in 𝓝 x₀, x ≠ 0 := isOpen_ne.mem_nhds (by rintro rfl; simp at hx)
  exact h0.and hne

/-- The transported frame as a linear isometry `ℝ^{n-1} → x̂^⊥`. -/
def transportIsometry (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) {x : E n} (hx₀ : ‖x₀‖ = 1)
    (hx : x ≠ 0) (hne : ⟪x₀, radialProj x⟫ ≠ -1) : E (n - 1) →ₗᵢ[ℝ] E n :=
  (rodriguesIsometry hx₀ (norm_radialProj hx) hne).comp ι

theorem frameVec_transportIsometry (hx₀ : ‖x₀‖ = 1) {x : E n} (hx : x ≠ 0)
    (hne : ⟪x₀, radialProj x⟫ ≠ -1) (i : Fin (n - 1)) :
    frameVec (transportIsometry x₀ ι hx₀ hx hne) i = transFrame x₀ ι x i := rfl

theorem inner_transportIsometry_radialProj (hx₀ : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0)
    {x : E n} (hx : x ≠ 0) (hne : ⟪x₀, radialProj x⟫ ≠ -1) (v : E (n - 1)) :
    ⟪transportIsometry x₀ ι hx₀ hx hne v, radialProj x⟫ = 0 := by
  have hR := rodrigues_apply_self hx₀ (norm_radialProj hx) hne
  change ⟪rodrigues x₀ (radialProj x) (ι v), radialProj x⟫ = 0
  calc ⟪rodrigues x₀ (radialProj x) (ι v), radialProj x⟫
      = ⟪rodrigues x₀ (radialProj x) (ι v), rodrigues x₀ (radialProj x) x₀⟫ := by rw [hR]
    _ = 0 := by rw [rodrigues_orthogonal hx₀ (norm_radialProj hx) hne]; exact hι v

theorem inner_transFrame_transFrame (hx₀ : ‖x₀‖ = 1) {x : E n} (hx : x ≠ 0)
    (hne : ⟪x₀, radialProj x⟫ ≠ -1) (i j : Fin (n - 1)) :
    ⟪transFrame x₀ ι x i, transFrame x₀ ι x j⟫ = if i = j then 1 else 0 := by
  rw [transFrame, transFrame, rodrigues_orthogonal hx₀ (norm_radialProj hx) hne,
    inner_frameVec_frameVec]

theorem inner_transFrame_radialProj (hx₀ : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0) {x : E n}
    (hx : x ≠ 0) (hne : ⟪x₀, radialProj x⟫ ≠ -1) (i : Fin (n - 1)) :
    ⟪transFrame x₀ ι x i, radialProj x⟫ = 0 :=
  inner_transportIsometry_radialProj hx₀ hι hx hne _

/-! ### Transport of multilinear fields -/

section Transport

variable {k : ℕ} {M : E n → ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E n) ℝ}
  {M' : E n →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E n) ℝ}

/-- The transported components `x ↦ M(x)[τ_{i₁}(x), …, τ_{i_k}(x)]` of a field of `k`-linear
forms are differentiable at `x₀`, with the product-rule derivative. -/
theorem hasFDerivAt_transport_apply (hM : HasFDerivAt M M' x₀) (hx : ‖x₀‖ = 1)
    (idx : Fin k → Fin (n - 1)) :
    HasFDerivAt (fun x ↦ M x (fun s ↦ transFrame x₀ ι x (idx s)))
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E n) ℝ
          (fun s ↦ transFrame x₀ ι x₀ (idx s)) ∘L M' +
        ∑ s, (M x₀).toContinuousLinearMap (fun s ↦ transFrame x₀ ι x₀ (idx s)) s ∘L
          ((ContinuousLinearMap.apply ℝ (E n) (frameVec ι (idx s))).comp
            ((rotGenL x₀).comp (tangentProj x₀)))) x₀ :=
  hM.continuousMultilinearMap_apply (g := fun s x ↦ transFrame x₀ ι x (idx s))
    fun s ↦ hasFDerivAt_transFrame hx (idx s)

/-- **Transport formula.** The derivative at `x₀` of the transported components of `M` is
`DM(x₀)[v](τ) - ∑ₛ ⟪v, τ_{iₛ}⟫ M(x₀)[τ with x₀ in slot s]`. -/
theorem fderiv_transport_apply (hM : DifferentiableAt ℝ M x₀) (hx : ‖x₀‖ = 1)
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) (idx : Fin k → Fin (n - 1)) (v : E n) :
    fderiv ℝ (fun x ↦ M x (fun s ↦ transFrame x₀ ι x (idx s))) x₀ v =
      fderiv ℝ M x₀ v (fun s ↦ frameVec ι (idx s)) -
        ∑ s, ⟪v, frameVec ι (idx s)⟫ * M x₀ (update (fun s ↦ frameVec ι (idx s)) s x₀) := by
  rw [(hasFDerivAt_transport_apply hM.hasFDerivAt hx idx).fderiv]
  have h0 : ∀ i, ⟪x₀, frameVec ι i⟫ = 0 := inner_frameVec_self hι
  simp only [add_apply, ContinuousLinearMap.coe_comp, comp_apply,
    ContinuousMultilinearMap.apply_apply, sum_apply,
    ContinuousMultilinearMap.toContinuousLinearMap_apply, ContinuousLinearMap.apply_apply,
    rotGenL_apply, rotGen_apply, tangentProj_apply, transFrame_self hx, h0, zero_smul,
    sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  have hin : ⟪v + -(⟪x₀, v⟫ • x₀), frameVec ι (idx s)⟫ = ⟪v, frameVec ι (idx s)⟫ := by
    rw [inner_add_left, inner_neg_left, real_inner_smul_left, h0, mul_zero, neg_zero, add_zero]
  rw [zero_add, hin, ← neg_smul, ContinuousMultilinearMap.map_update_smul, smul_eq_mul,
    neg_mul]

/-- **Projection identity.** If `M(x₀)` vanishes as soon as one slot is `x₀` (a tangential field),
the derivative of the transported components is the Euclidean derivative evaluated on the
frame: `∇S(x₀)[v] = ιᵀ(P DS̃(x₀)[v])` in every slot. -/
theorem fderiv_transport_apply_of_tangential (hM : DifferentiableAt ℝ M x₀) (hx : ‖x₀‖ = 1)
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) (idx : Fin k → Fin (n - 1))
    (htan : ∀ s, M x₀ (update (fun s ↦ frameVec ι (idx s)) s x₀) = 0) (v : E n) :
    fderiv ℝ (fun x ↦ M x (fun s ↦ transFrame x₀ ι x (idx s))) x₀ v =
      fderiv ℝ M x₀ v (fun s ↦ frameVec ι (idx s)) := by
  rw [fderiv_transport_apply hM hx hι, Finset.sum_eq_zero fun s _ ↦ by rw [htan, mul_zero],
    sub_zero]

end Transport

/-- **Transport of a vector field.** The transported components `x ↦ ⟪τᵢ(x), V(x)⟫` of a vector
field have derivative `⟪τᵢ, DV(x₀)[v]⟫ - ⟪v, τᵢ⟫ ⟪x₀, V(x₀)⟫` at `x₀`. -/
theorem fderiv_inner_transFrame {V : E n → E n} (hV : DifferentiableAt ℝ V x₀) (hx : ‖x₀‖ = 1)
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) (i : Fin (n - 1)) (v : E n) :
    fderiv ℝ (fun x ↦ ⟪transFrame x₀ ι x i, V x⟫) x₀ v =
      ⟪frameVec ι i, fderiv ℝ V x₀ v⟫ - ⟪v, frameVec ι i⟫ * ⟪x₀, V x₀⟫ := by
  rw [fderiv_inner_apply ℝ (hasFDerivAt_transFrame hx i).differentiableAt hV,
    fderiv_transFrame_apply hx hι, transFrame_self hx, real_inner_smul_left]
  ring

/-- For a tangential vector field (`⟪x₀, V(x₀)⟫ = 0`), the derivative of the transported
components is the tangential component of the Euclidean derivative. -/
theorem fderiv_inner_transFrame_of_tangential {V : E n → E n} (hV : DifferentiableAt ℝ V x₀)
    (hx : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0) (htan : ⟪x₀, V x₀⟫ = 0) (i : Fin (n - 1))
    (v : E n) :
    fderiv ℝ (fun x ↦ ⟪transFrame x₀ ι x i, V x⟫) x₀ v = ⟪frameVec ι i, fderiv ℝ V x₀ v⟫ := by
  rw [fderiv_inner_transFrame hV hx hι, htan, mul_zero, sub_zero]

/-! ### Transported jets -/

section Jets

variable {u : E n → ℝ} {k : ℕ}

/-- The transported `k`-jet `x ↦ Dᵏu(x̂)[τ_{i₁}(x), …, τ_{i_k}(x)]`: the spherical data of `u` at
`x̂` in the transported frame. -/
def transJet (u : E n → ℝ) (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (k : ℕ)
    (idx : Fin k → Fin (n - 1)) (x : E n) : ℝ :=
  iteratedFDeriv ℝ k u (radialProj x) (fun s ↦ transFrame x₀ ι x (idx s))

/-- The transported value `g(x) = u(x̂)`. -/
def transG (u : E n → ℝ) (x : E n) : ℝ := u (radialProj x)

/-- The transported tangential gradient `pᵢ(x) = Du(x̂)[τᵢ(x)]`. -/
def transP (u : E n → ℝ) (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (x : E n) (i : Fin (n - 1)) :
    ℝ :=
  transJet u x₀ ι 1 ![i] x

/-- The transported spherical Hessian `T_{ij}(x) = D²u(x̂)[τᵢ(x), τⱼ(x)]`. -/
def transT (u : E n → ℝ) (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (x : E n)
    (i j : Fin (n - 1)) : ℝ :=
  transJet u x₀ ι 2 ![i, j] x

/-- The transported third jet `B_{ijk}(x) = D³u(x̂)[τᵢ(x), τⱼ(x), τ_k(x)]`. -/
def transB (u : E n → ℝ) (x₀ : E n) (ι : E (n - 1) →ₗᵢ[ℝ] E n) (x : E n)
    (i j k : Fin (n - 1)) : ℝ :=
  transJet u x₀ ι 3 ![i, j, k] x

theorem hasFDerivAt_iteratedFDeriv_radialProj
    (hu : DifferentiableAt ℝ (iteratedFDeriv ℝ k u) x₀) (hx : ‖x₀‖ = 1) :
    HasFDerivAt (fun x ↦ iteratedFDeriv ℝ k u (radialProj x))
      ((fderiv ℝ (iteratedFDeriv ℝ k u) x₀).comp (tangentProj x₀)) x₀ := by
  have h : HasFDerivAt (iteratedFDeriv ℝ k u) (fderiv ℝ (iteratedFDeriv ℝ k u) x₀)
      (radialProj x₀) := by
    rw [radialProj_of_norm_eq_one hx]
    exact hu.hasFDerivAt
  exact h.comp x₀ (hasFDerivAt_radialProj hx)

theorem differentiableAt_transJet (hu : DifferentiableAt ℝ (iteratedFDeriv ℝ k u) x₀)
    (hx : ‖x₀‖ = 1) (idx : Fin k → Fin (n - 1)) :
    DifferentiableAt ℝ (transJet u x₀ ι k idx) x₀ :=
  (hasFDerivAt_transport_apply (hasFDerivAt_iteratedFDeriv_radialProj hu hx) hx idx
    ).differentiableAt

theorem transJet_self (hx : ‖x₀‖ = 1) (idx : Fin k → Fin (n - 1)) :
    transJet u x₀ ι k idx x₀ = iteratedFDeriv ℝ k u x₀ (fun s ↦ frameVec ι (idx s)) := by
  simp [transJet, radialProj_of_norm_eq_one hx, transFrame_self hx]

/-- **Transported derivative of a jet.** Along a frame direction `τ_l`,
`∇_l (Dᵏu[τ_{i₁}, …]) = D^{k+1}u[τ_l, τ_{i₁}, …] - ∑ₛ δ_{l iₛ} Dᵏu[…, x₀ (slot s), …]`. -/
theorem fderiv_transJet_frame (hu : DifferentiableAt ℝ (iteratedFDeriv ℝ k u) x₀)
    (hx : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0) (idx : Fin k → Fin (n - 1)) (l : Fin (n - 1)) :
    fderiv ℝ (transJet u x₀ ι k idx) x₀ (frameVec ι l) =
      iteratedFDeriv ℝ (k + 1) u x₀ (Fin.cons (frameVec ι l) fun s ↦ frameVec ι (idx s)) -
        ∑ s, (if l = idx s then 1 else 0) *
          iteratedFDeriv ℝ k u x₀ (update (fun s ↦ frameVec ι (idx s)) s x₀) := by
  have hM := hasFDerivAt_iteratedFDeriv_radialProj hu hx
  have h := fderiv_transport_apply (ι := ι) hM.differentiableAt hx hι idx (frameVec ι l)
  rw [hM.fderiv, radialProj_of_norm_eq_one hx] at h
  change fderiv ℝ (fun x ↦ iteratedFDeriv ℝ k u (radialProj x)
    (fun s ↦ transFrame x₀ ι x (idx s))) x₀ (frameVec ι l) = _
  rw [h]
  simp only [ContinuousLinearMap.coe_comp, comp_apply,
    tangentProj_apply_of_inner_eq_zero (inner_frameVec_self hι l), inner_frameVec_frameVec]
  rfl

end Jets

/-! ### Identification with the jet record -/

namespace ConeJets.IsConeJet

variable {u : E n → ℝ} {J : ConeJets n}

theorem transG_self (h : IsConeJet u J) : transG u J.x₀ = J.g := by
  rw [transG, radialProj_of_norm_eq_one h.norm_x₀, h.g_eq]

theorem transP_self (h : IsConeJet u J) (i : Fin (n - 1)) : transP u J.x₀ J.ι J.x₀ i = J.p i := by
  rw [transP, transJet_self h.norm_x₀, h.p_eq', iteratedFDeriv_one_apply, iteratedFDeriv_one_apply]
  rfl

theorem transT_self (h : IsConeJet u J) (i j : Fin (n - 1)) :
    transT u J.x₀ J.ι J.x₀ i j = J.T i j := by
  rw [transT, transJet_self h.norm_x₀, h.T_eq]
  congr 1
  funext s
  fin_cases s <;> rfl

theorem transB_self (h : IsConeJet u J) (i j k : Fin (n - 1)) :
    transB u J.x₀ J.ι J.x₀ i j k = J.B i j k := by
  rw [transB, transJet_self h.norm_x₀, h.B_eq]
  congr 1
  funext s
  fin_cases s <;> rfl

/-- **`∇g = p`.** -/
theorem transported_g (h : IsConeJet u J) (hu : DifferentiableAt ℝ u J.x₀) (l : Fin (n - 1)) :
    fderiv ℝ (transG u) J.x₀ (frameVec J.ι l) = J.p l := by
  have hu' : HasFDerivAt u (fderiv ℝ u J.x₀) (radialProj J.x₀) := by
    rw [radialProj_of_norm_eq_one h.norm_x₀]
    exact hu.hasFDerivAt
  rw [show transG u = u ∘ radialProj from rfl,
    (hu'.comp J.x₀ (hasFDerivAt_radialProj h.norm_x₀)).fderiv]
  simp only [ContinuousLinearMap.coe_comp, comp_apply,
    tangentProj_apply_of_inner_eq_zero (inner_frameVec_self h.inner_ι l), h.p_eq]

/-- **`∇_l pᵢ = T_{li} - g δ_{li}`.** -/
theorem transported_p (h : IsConeJet u J) (hu : ContDiffAt ℝ 2 u J.x₀) (i l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ transP u J.x₀ J.ι x i) J.x₀ (frameVec J.ι l) =
      J.T l i - if l = i then J.g else 0 := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 u) J.x₀ :=
    hu.differentiableAt_iteratedFDeriv (by norm_num)
  change fderiv ℝ (transJet u J.x₀ J.ι 1 ![i]) J.x₀ (frameVec J.ι l) = _
  rw [fderiv_transJet_frame hd h.norm_x₀ h.inner_ι, h.T_eq]
  have e1 : (Fin.cons (frameVec J.ι l) fun s ↦ frameVec J.ι (![i] s) : Fin 2 → E n) =
      ![frameVec J.ι l, frameVec J.ι i] := by
    funext s; fin_cases s <;> rfl
  have e2 : update (fun s ↦ frameVec J.ι (![i] s)) 0 J.x₀ = ![J.x₀] := by
    funext s; fin_cases s; simp
  rw [e1, Fin.sum_univ_one, e2, h.facts.D1_self, ← h.g_eq]
  simp

/-- **`∇T = B`.** -/
theorem transported_T (h : IsConeJet u J) (hu : ContDiffAt ℝ 3 u J.x₀) (i j l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ transT u J.x₀ J.ι x i j) J.x₀ (frameVec J.ι l) = J.B l i j := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 u) J.x₀ :=
    hu.differentiableAt_iteratedFDeriv (by norm_num)
  change fderiv ℝ (transJet u J.x₀ J.ι 2 ![i, j]) J.x₀ (frameVec J.ι l) = _
  rw [fderiv_transJet_frame hd h.norm_x₀ h.inner_ι, h.B_eq]
  have e1 : (Fin.cons (frameVec J.ι l) fun s ↦ frameVec J.ι (![i, j] s) : Fin 3 → E n) =
      ![frameVec J.ι l, frameVec J.ι i, frameVec J.ι j] := by
    funext s; fin_cases s <;> rfl
  have e2 : update (fun s ↦ frameVec J.ι (![i, j] s)) 0 J.x₀ = ![J.x₀, frameVec J.ι j] := by
    funext s; fin_cases s <;> simp
  have e3 : update (fun s ↦ frameVec J.ι (![i, j] s)) 1 J.x₀ = ![frameVec J.ι i, J.x₀] := by
    funext s; fin_cases s <;> simp
  rw [e1, Fin.sum_univ_two, e2, e3, h.facts.D2_self_left, h.facts.D2_self_right]
  simp

/-- **`∇B = DB`**: `∇_l B_{ijk} = D⁴u_{lijk} + δ_{li}T_{jk} + δ_{lj}T_{ik} + δ_{lk}T_{ij}`, the
defining formula of `ConeJets.DB`. The `δT` terms come from `D³u(x₀)[x₀, a, b] = -T(a, b)`. -/
theorem transported_B (h : IsConeJet u J) (hu : ContDiffAt ℝ 4 u J.x₀) (i j k l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ transB u J.x₀ J.ι x i j k) J.x₀ (frameVec J.ι l) = J.DB l i j k := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 3 u) J.x₀ :=
    hu.differentiableAt_iteratedFDeriv (by norm_num)
  change fderiv ℝ (transJet u J.x₀ J.ι 3 ![i, j, k]) J.x₀ (frameVec J.ι l) = _
  rw [fderiv_transJet_frame hd h.norm_x₀ h.inner_ι, h.DB_eq]
  have e1 : (Fin.cons (frameVec J.ι l) fun s ↦ frameVec J.ι (![i, j, k] s) : Fin 4 → E n) =
      ![frameVec J.ι l, frameVec J.ι i, frameVec J.ι j, frameVec J.ι k] := by
    funext s; fin_cases s <;> rfl
  have s0 : (if l = ![i, j, k] 0 then (1 : ℝ) else 0) *
      iteratedFDeriv ℝ 3 u J.x₀ (update (fun s ↦ frameVec J.ι (![i, j, k] s)) 0 J.x₀) =
      -(if l = i then J.T j k else 0) := by
    have e : update (fun s ↦ frameVec J.ι (![i, j, k] s)) 0 J.x₀ =
        ![J.x₀, frameVec J.ι j, frameVec J.ι k] := by
      funext s; fin_cases s <;> simp
    rw [e, h.facts.D3_self₁, ← h.T_eq]
    split_ifs <;> simp_all
  have s1 : (if l = ![i, j, k] 1 then (1 : ℝ) else 0) *
      iteratedFDeriv ℝ 3 u J.x₀ (update (fun s ↦ frameVec J.ι (![i, j, k] s)) 1 J.x₀) =
      -(if l = j then J.T i k else 0) := by
    have e : update (fun s ↦ frameVec J.ι (![i, j, k] s)) 1 J.x₀ =
        ![frameVec J.ι i, J.x₀, frameVec J.ι k] := by
      funext s; fin_cases s <;> simp
    rw [e, h.facts.D3_self₂, ← h.T_eq]
    split_ifs <;> simp_all
  have s2 : (if l = ![i, j, k] 2 then (1 : ℝ) else 0) *
      iteratedFDeriv ℝ 3 u J.x₀ (update (fun s ↦ frameVec J.ι (![i, j, k] s)) 2 J.x₀) =
      -(if l = k then J.T i j else 0) := by
    have e : update (fun s ↦ frameVec J.ι (![i, j, k] s)) 2 J.x₀ =
        ![frameVec J.ι i, frameVec J.ι j, J.x₀] := by
      funext s; fin_cases s <;> simp
    rw [e, h.facts.D3_self₃, ← h.T_eq]
    split_ifs <;> simp_all
  rw [e1, Fin.sum_univ_three, s0, s1, s2]
  ring

end ConeJets.IsConeJet

/-! ### Derivation compatibility -/

section ChainRule

variable {G W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup W]
  [NormedSpace ℝ W] {m : ℕ}

/-- The derivative of a data triple `y ↦ (A(y), p(y), g(y))` is the triple of derivatives. -/
theorem fderiv_dataTriple_apply {A : G → Gen.Ten2 m} {p : G → Gen.Ten1 m} {g : G → ℝ} {x : G}
    (hA : DifferentiableAt ℝ A x) (hp : DifferentiableAt ℝ p x) (hg : DifferentiableAt ℝ g x)
    (v : G) :
    fderiv ℝ (fun y ↦ (A y, p y, g y)) x v = (fderiv ℝ A x v, fderiv ℝ p x v, fderiv ℝ g x v) := by
  rw [(hA.hasFDerivAt.prodMk (hp.hasFDerivAt.prodMk hg.hasFDerivAt)).fderiv]
  rfl

/-- Entries of the derivative of a tensor-valued map are derivatives of its entries. -/
theorem fderiv_ten2_apply {A : G → Gen.Ten2 m} {x : G} (hA : DifferentiableAt ℝ A x) (v : G)
    (i j : Fin m) : fderiv ℝ A x v i j = fderiv ℝ (fun y ↦ A y i j) x v := by
  have h1 : DifferentiableAt ℝ (fun y ↦ A y i) x := differentiableAt_pi.1 hA i
  rw [fderiv_apply h1 j, fderiv_apply hA i]
  rfl

/-- Entries of the derivative of a vector-valued map are derivatives of its entries. -/
theorem fderiv_ten1_apply {p : G → Gen.Ten1 m} {x : G} (hp : DifferentiableAt ℝ p x) (v : G)
    (i : Fin m) : fderiv ℝ p x v i = fderiv ℝ (fun y ↦ p y i) x v := by
  rw [fderiv_apply hp i]
  rfl

/-- **Derivation compatibility.** If the data `y ↦ (A(y), p(y), g(y))` has derivative equal to the
generator `(D_l A, D_l p, D_l g)` of the certificate in the direction `v`, then for every map `Φ`
differentiable at the data, the derivative of `y ↦ Φ(A(y), p(y), g(y))` in the direction `v` is
`D_l Φ`. With the transported data and `v = τ_l`, this is the statement that `D_l` is covariant
differentiation on every coefficient map. For orthogonally equivariant `Φ` the ambient fields built
from `Φ` do not depend on the frame in which the data are read (`Geometry.FrameChange`), so the
transported frame may be used to compute their derivatives. -/
theorem equivariant_chain_rule (Φ : Gen.Ten2 m × Gen.Ten1 m × ℝ → W)
    {data : G → Gen.Ten2 m × Gen.Ten1 m × ℝ} {x v : G} {A : Gen.Ten2 m} {X : Gen.Ten3 m}
    {p : Gen.Ten1 m} {g w z : ℝ} {l : Fin m}
    (hΦ : DifferentiableAt ℝ Φ (A, p, g)) (hd : DifferentiableAt ℝ data x)
    (h0 : data x = (A, p, g)) (hgen : fderiv ℝ data x v = Gen.gen A X p g w z l) :
    fderiv ℝ (fun y ↦ Φ (data y)) x v = Gen.Dl Φ A X p g w z l := by
  rw [← h0] at hΦ
  rw [show (fun y ↦ Φ (data y)) = Φ ∘ data from rfl, fderiv_comp x hΦ hd,
    ContinuousLinearMap.coe_comp, comp_apply, hgen, h0, Gen.Dl]

end ChainRule

end OnePhaseDimension
