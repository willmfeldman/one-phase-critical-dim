/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.GradientBound

/-!
# The gradient bound and boundary positivity on the suspension

Let `W = O × ℝ` be the suspension of a cone `O` in `ℝ⁵` with `O.Sing = {0}`. Then:

* `IsSuspension.sSq_lt_one`: `|∇ũ|² < 1` on the component of `W`, since `ũ = u_o ∘ π` with `π` the
  projection dropping the last coordinate, so `|∇ũ(z)| ≤ |∇u_o(π z)| < 1`;
* `IsSuspension.hessian_gradient_neg`, `IsSuspension.Tpp_neg`, `IsSuspension.w_pos`,
  `IsSuspension.lam_neg`: at every point of the side boundary `closure D̃ \ D̃` and for every
  chart `F̃` there, `D²F̃[Ñ, Ñ] < 0`; at unit points `T̃(p̃, p̃) = -H̃ < 0`, `w̃ ≥ H̃ > 0` and
  `λ̃ < 0`.

No maximum principle is used at the tips: the strict bound comes from the original cone, and
the boundary signs follow from the local Hopf argument at the regular side boundary.

## Differences from the source

The 2026-09-24 version transports the boundary signs from the original cone through the
suspension formulas `H̃ = ρ⁻¹ H_o`, `w̃ = ρ⁻¹ w_o`. We transport only the interior bound
`s̃² ≤ s_o²(π ·) < 1` and rerun the local Hopf argument at the side boundary.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Function Filter Topology Set Metric Laplacian EllipticBernoulli
open scoped ContDiff RealInnerProductSpace Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

theorem norm_dropLast_le (x : E 6) : ‖dropLast x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  rw [Fin.sum_univ_castSucc (f := fun j ↦ ‖x j‖ ^ 2)]
  have h : ∀ i : Fin 5, dropLast x i = x (Fin.castSucc i) := fun _ ↦ rfl
  simp only [h]
  linarith [sq_nonneg ‖x (Fin.last 5)‖]

theorem opNorm_dropLast_le : ‖dropLast‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    rw [one_mul]
    exact norm_dropLast_le x

theorem norm_gradient_eq_norm_fderiv {n : ℕ} (f : E n → ℝ) (x : E n) :
    ‖∇ f x‖ = ‖fderiv ℝ f x‖ := by
  rw [gradient, LinearIsometryEquiv.norm_map]

namespace IsSuspension

variable {W : ConeData 6} {O : ConeData 5} (hW : IsSuspension W O) (hO : O.Sing = {0})
include hW

theorem mem_D_iff {z : E 6} : z ∈ W.D ↔ dropLast z ∈ O.D := by
  rw [hW.D_eq]
  rfl

include hO

/-- `|∇ũ(z)| ≤ |∇u_o(π z)|`. -/
theorem norm_gradient_le {z : E 6} (hz : z ∈ W.D) : ‖∇ W.u z‖ ≤ ‖∇ O.u (dropLast z)‖ := by
  have hd : DifferentiableAt ℝ O.u (dropLast z) :=
    ((O.contDiffAt_u hO (hW.mem_D_iff.1 hz)).of_le (natCast_le_infty 1)).differentiableAt
      one_ne_zero
  have hfun : W.u = O.u ∘ dropLast := funext hW.u_eq
  have hfd : fderiv ℝ W.u z = (fderiv ℝ O.u (dropLast z)).comp dropLast := by
    rw [hfun]
    exact (hd.hasFDerivAt.comp z dropLast.hasFDerivAt).fderiv
  rw [norm_gradient_eq_norm_fderiv, norm_gradient_eq_norm_fderiv, hfd]
  calc _ ≤ ‖fderiv ℝ O.u (dropLast z)‖ * ‖dropLast‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ O.u (dropLast z)‖ * 1 := by gcongr; exact opNorm_dropLast_le
    _ = _ := mul_one _

/-- **`s̃² < 1`** on the component of the suspension. -/
theorem sSq_lt_one {z : E 6} (hz : z ∈ W.D) : ‖∇ W.u z‖ ^ 2 < 1 := by
  have h1 := hW.norm_gradient_le hO hz
  have h2 := O.norm_gradient_lt_one hO (hW.mem_D_iff.1 hz)
  have h3 : ‖∇ W.u z‖ < 1 := h1.trans_lt h2
  nlinarith [norm_nonneg (∇ W.u z)]

variable {U : Set (E 6)} {F : E 6 → ℝ} {x₀ : E 6}

/-- **`H̃ > 0`** on the side boundary: `D²F̃(x₀)[Ñ, Ñ] < 0` for every chart `F̃`. -/
theorem hessian_gradient_neg (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, W.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ W.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure W.D) (hx₀D : x₀ ∉ W.D) :
    iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] < 0 :=
  ConeData.hessian_gradient_neg_of_sSq_lt (fun _ hy ↦ hW.sSq_lt_one hO hy) hU hx₀U hF hu hD
    hgrad hΔ hx₀ hx₀D

/-- **`T̃(p̃, p̃) = -H̃ < 0`** at a unit point of the side boundary. -/
theorem Tpp_neg (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, W.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ W.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure W.D) (hx₀D : x₀ ∉ W.D) (hx₁ : ‖x₀‖ = 1) {ι : E (6 - 1) →ₗᵢ[ℝ] E 6}
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) : (ConeJets.ofFun F x₀ ι).Tpp < 0 :=
  ConeData.Tpp_neg_of_sSq_lt (fun _ hy ↦ hW.sSq_lt_one hO hy) hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D
    hx₁ hι

/-- **`w̃ ≥ H̃ > 0`** at a unit point of the side boundary. -/
theorem w_pos (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, W.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ W.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure W.D) (hx₀D : x₀ ∉ W.D) (hx₁ : ‖x₀‖ = 1) {ι : E (6 - 1) →ₗᵢ[ℝ] E 6}
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) : 0 < (ConeJets.ofFun F x₀ ι).w :=
  (ConeData.isBoundaryJet_chart hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι).w_pos_of_Tpp_neg
    (hW.Tpp_neg hO hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι)

/-- **`λ̃ < 0`** at a unit point of the side boundary. -/
theorem lam_neg (hU : IsOpen U) (hx₀U : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (hu : ∀ y ∈ U, W.u y = max (F y) 0) (hD : ∀ y ∈ U, 0 < F y → y ∈ W.D)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hΔ : ∀ y ∈ U, 0 < F y → Δ F y = 0)
    (hx₀ : x₀ ∈ closure W.D) (hx₀D : x₀ ∉ W.D) (hx₁ : ‖x₀‖ = 1) {ι : E (6 - 1) →ₗᵢ[ℝ] E 6}
    (hι : ∀ v, ⟪ι v, x₀⟫ = 0) : (ConeJets.ofFun F x₀ ι).lam < 0 :=
  div_neg_of_neg_of_pos (hW.Tpp_neg hO hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι)
    (hW.w_pos hO hU hx₀U hF hu hD hgrad hΔ hx₀ hx₀D hx₁ hι)

end IsSuspension

end OnePhaseDimension
