/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Flux.Fields
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Normalized differentiation

Let `u` be one-homogeneous, smooth and harmonic near the unit vector `x₀`, with jet record `J`
(frame `τ_l = ι e_l`). The data read in the Rodrigues-transported frame near `x₀` have, along
`τ_l` at `x₀`, the derivatives (with `w = |T|`, `A = T/w`, `X = B/w`, `q_l = X_{lij}A_{ij}`)

  `∇_l w = w q_l`, `∇_l A_{ij} = X_{lij} - q_l A_{ij}`, `∇_l p_i = w A_{li} - g δ_{li}`,
  `∇_l g = p_l`, `∇_l X_{ijk} = w⁻¹ (∇B)_{lijk} - q_l X_{ijk}`.

The first four are the generator of the certificate derivation `D_l` at `z = 1`
(`fderiv_normalizedData`), so for every coefficient map `Φ` differentiable at `(A, p, g)` the
derivative of `x ↦ Φ(A(x), p(x), g(x))` along `τ_l` is `D_l Φ` (`fderiv_certPoly_eq_Dl`).
Everything here holds for `u` on `ℝⁿ`, with the data indexed by `Fin (n - 1)` and the derivation
`Gen.Dl` of the dimension-generic certificate.

## Differences from the source

The 2026-09-24 version computes these derivatives with the Levi-Civita connection of the sphere
in a covariantly constant frame. We differentiate the data read in the Rodrigues-transported
frame, whose derivative at `x₀` is normal to the sphere.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Function Filter Topology Set
open scoped RealInnerProductSpace ContDiff Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### Directional product rules -/

section Rules

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ ψ : F → ℝ} {x v : F}

theorem fderiv_mul_apply' (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    fderiv ℝ (fun y ↦ φ y * ψ y) x v = φ x * fderiv ℝ ψ x v + ψ x * fderiv ℝ φ x v := by
  rw [fderiv_fun_mul hφ hψ]
  simp

theorem fderiv_add_apply' (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x) :
    fderiv ℝ (fun y ↦ φ y + ψ y) x v = fderiv ℝ φ x v + fderiv ℝ ψ x v := by
  rw [fderiv_fun_add hφ hψ]
  rfl

theorem fderiv_sum_apply' {ι : Type*} [Fintype ι] {φ : ι → F → ℝ}
    (h : ∀ i, DifferentiableAt ℝ (φ i) x) :
    fderiv ℝ (fun y ↦ ∑ i, φ i y) x v = ∑ i, fderiv ℝ (φ i) x v := by
  rw [(HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ (h i).hasFDerivAt).fderiv]
  simp

theorem fderiv_div_apply' (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x)
    (h0 : ψ x ≠ 0) :
    fderiv ℝ (fun y ↦ φ y / ψ y) x v =
      fderiv ℝ φ x v / ψ x - φ x * fderiv ℝ ψ x v / ψ x ^ 2 := by
  have h1 := hφ.hasFDerivAt.mul ((hasFDerivAt_inv h0).comp x hψ.hasFDerivAt)
  simp only [div_eq_mul_inv]
  rw [show (fun y ↦ φ y * (ψ y)⁻¹) = φ * ((fun t : ℝ ↦ t⁻¹) ∘ ψ) from rfl, h1.fderiv]
  simp
  ring

theorem fderiv_sqrt_apply' (hφ : DifferentiableAt ℝ φ x) (h0 : φ x ≠ 0) :
    fderiv ℝ (fun y ↦ √(φ y)) x v = fderiv ℝ φ x v / (2 * √(φ x)) := by
  rw [(hφ.hasFDerivAt.sqrt h0).fderiv]
  simp only [smul_apply, smul_eq_mul]
  field_simp

theorem fderiv_rpow_apply' (hφ : DifferentiableAt ℝ φ x) (h0 : φ x ≠ 0) (r : ℝ) :
    fderiv ℝ (fun y ↦ φ y ^ r) x v = r * φ x ^ (r - 1) * fderiv ℝ φ x v := by
  rw [(hφ.hasFDerivAt.rpow_const (Or.inl h0)).fderiv]
  simp

theorem fderiv_sq_apply' (hφ : DifferentiableAt ℝ φ x) :
    fderiv ℝ (fun y ↦ φ y ^ 2) x v = 2 * φ x * fderiv ℝ φ x v := by
  simp only [sq]
  rw [fderiv_mul_apply' hφ hφ]
  ring

theorem fderiv_sq2_apply' {m : ℕ} {Φ : F → Gen.Ten2 m}
    (hd : ∀ i j, DifferentiableAt ℝ (fun y ↦ Φ y i j) x) :
    fderiv ℝ (fun y ↦ Gen.sq2 (Φ y)) x v =
      2 * ∑ i, ∑ j, Φ x i j * fderiv ℝ (fun y ↦ Φ y i j) x v := by
  unfold Gen.sq2
  have hd2 : ∀ i j, DifferentiableAt ℝ (fun y ↦ Φ y i j ^ 2) x := fun i j ↦ (hd i j).pow 2
  rw [fderiv_sum_apply' (φ := fun i y ↦ ∑ j, Φ y i j ^ 2)
    fun i ↦ DifferentiableAt.fun_sum fun j _ ↦ hd2 i j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_sum_apply' (φ := fun j y ↦ Φ y i j ^ 2) fun j ↦ hd2 i j, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [fderiv_sq_apply' (hd i j)]
  ring

theorem differentiableAt_fun_div (hφ : DifferentiableAt ℝ φ x) (hψ : DifferentiableAt ℝ ψ x)
    (h0 : ψ x ≠ 0) : DifferentiableAt ℝ (fun y ↦ φ y / ψ y) x := by
  simp only [div_eq_mul_inv]
  exact hφ.mul (hψ.inv h0)

end Rules

/-! ### The generator rules -/

namespace ConeJets.IsConeJet

variable {n : ℕ} {u : E n → ℝ} {J : ConeJets n} (h : IsConeJet u J) (hu : ContDiffAt ℝ ∞ u J.x₀)
include h hu

omit hu in
theorem transTData_self : Gen.transTData u J.x₀ J.ι J.x₀ = J.T := by
  funext i j
  exact h.transT_self i j

omit hu in
theorem transBData_self : Gen.transBData u J.x₀ J.ι J.x₀ = J.B := by
  funext i j k
  exact h.transB_self i j k

omit hu in
theorem transPData_self : Gen.transPData u J.x₀ J.ι J.x₀ = J.p := by
  funext i
  exact h.transP_self i

omit hu in
theorem x₀_ne_zero : J.x₀ ≠ 0 := by
  intro h0
  have := h.norm_x₀
  rw [h0, norm_zero] at this
  exact zero_ne_one this

omit hu in
theorem inner_radialProj_x₀ : ⟪J.x₀, radialProj J.x₀⟫ ≠ -1 := by
  rw [radialProj_of_norm_eq_one h.norm_x₀, real_inner_self_eq_norm_sq, h.norm_x₀]
  norm_num

theorem contDiffAt_transData_self :
    ContDiffAt ℝ ∞ (fun x ↦ (Gen.transTData u J.x₀ J.ι x, Gen.transBData u J.x₀ J.ι x,
      Gen.transPData u J.x₀ J.ι x, transG u x)) J.x₀ :=
  Gen.contDiffAt_transData (by rwa [radialProj_of_norm_eq_one h.norm_x₀]) h.x₀_ne_zero
    h.inner_radialProj_x₀

theorem differentiableAt_transT (i j : Fin (n - 1)) :
    DifferentiableAt ℝ (fun x ↦ Gen.transTData u J.x₀ J.ι x i j) J.x₀ := by
  have h1 := contDiffAt_pi.1 (contDiffAt_pi.1 (h.contDiffAt_transData_self hu).fst i) j
  exact h1.differentiableAt (by simp)

theorem differentiableAt_transB (i j k : Fin (n - 1)) :
    DifferentiableAt ℝ (fun x ↦ Gen.transBData u J.x₀ J.ι x i j k) J.x₀ := by
  have h1 := contDiffAt_pi.1 (contDiffAt_pi.1 (contDiffAt_pi.1
    (h.contDiffAt_transData_self hu).snd.fst i) j) k
  exact h1.differentiableAt (by simp)

theorem differentiableAt_transP (i : Fin (n - 1)) :
    DifferentiableAt ℝ (fun x ↦ Gen.transPData u J.x₀ J.ι x i) J.x₀ := by
  have h1 := contDiffAt_pi.1 (h.contDiffAt_transData_self hu).snd.snd.fst i
  exact h1.differentiableAt (by simp)

theorem differentiableAt_transG : DifferentiableAt ℝ (transG u) J.x₀ :=
  (h.contDiffAt_transData_self hu).snd.snd.snd.differentiableAt (by simp)

/-! #### Values and differentiability of the normalized data -/

variable (hw : Gen.sq2 J.T ≠ 0)
include hw

omit h hu in
theorem normW_ne_zero : Gen.normW J.T ≠ 0 := (Gen.normW_pos_iff.2 hw).ne'

omit hu in
theorem sq2_transTData_ne_zero : Gen.sq2 (Gen.transTData u J.x₀ J.ι J.x₀) ≠ 0 := by
  rwa [h.transTData_self]

theorem differentiableAt_transW :
    DifferentiableAt ℝ (fun x ↦ Gen.normW (Gen.transTData u J.x₀ J.ι x)) J.x₀ := by
  have hS : DifferentiableAt ℝ (fun x ↦ Gen.sq2 (Gen.transTData u J.x₀ J.ι x)) J.x₀ := by
    unfold Gen.sq2
    exact DifferentiableAt.fun_sum fun i _ ↦ DifferentiableAt.fun_sum fun j _ ↦
      (h.differentiableAt_transT hu i j).pow 2
  exact hS.sqrt (h.sq2_transTData_ne_zero hw)

omit hu hw in
theorem transW_self : Gen.normW (Gen.transTData u J.x₀ J.ι J.x₀) = Gen.normW J.T := by
  rw [h.transTData_self]

omit hu in
theorem transW_self_ne_zero : Gen.normW (Gen.transTData u J.x₀ J.ι J.x₀) ≠ 0 := by
  rw [h.transW_self]
  exact normW_ne_zero hw

theorem differentiableAt_transA (i j : Fin (n - 1)) :
    DifferentiableAt ℝ (fun x ↦ Gen.normalizedA (Gen.transTData u J.x₀ J.ι x) i j) J.x₀ :=
  show DifferentiableAt ℝ (fun x ↦ Gen.transTData u J.x₀ J.ι x i j / Gen.normW (Gen.transTData u
      J.x₀ J.ι x))
    J.x₀ from differentiableAt_fun_div (h.differentiableAt_transT hu i j)
      (h.differentiableAt_transW hu hw)
    (h.transW_self_ne_zero hw)

theorem differentiableAt_transX (i j k : Fin (n - 1)) :
    DifferentiableAt ℝ
      (fun x ↦ Gen.normalizedX (Gen.transTData u J.x₀ J.ι x) (Gen.transBData u J.x₀ J.ι x) i j k)
          J.x₀ :=
  show DifferentiableAt ℝ (fun x ↦ Gen.transBData u J.x₀ J.ι x i j k / Gen.normW (Gen.transTData u
      J.x₀ J.ι x))
    J.x₀ from differentiableAt_fun_div (h.differentiableAt_transB hu i j k)
      (h.differentiableAt_transW hu hw)
    (h.transW_self_ne_zero hw)

/-- The normalized data `x ↦ (A(x), p(x), g(x))` near `x₀`. -/
theorem differentiableAt_normalizedData :
    DifferentiableAt ℝ (fun x ↦ (Gen.normalizedA (Gen.transTData u J.x₀ J.ι x), Gen.transPData u
        J.x₀ J.ι x,
      transG u x)) J.x₀ := by
  refine DifferentiableAt.prodMk ?_ (DifferentiableAt.prodMk ?_ (h.differentiableAt_transG hu))
  · exact differentiableAt_pi.2 fun i ↦ differentiableAt_pi.2 fun j ↦
      h.differentiableAt_transA hu hw i j
  · exact differentiableAt_pi.2 fun i ↦ h.differentiableAt_transP hu i

omit hu hw in
theorem normalizedData_self : (Gen.normalizedA (Gen.transTData u J.x₀ J.ι J.x₀), Gen.transPData u
    J.x₀ J.ι J.x₀,
    transG u J.x₀) = (Gen.normalizedA J.T, J.p, J.g) := by
  rw [h.transTData_self, h.transPData_self, h.transG_self]

/-! #### The generator rules -/

/-- **`∇_l w = w q_l`.** -/
theorem fderiv_transW (l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ Gen.normW (Gen.transTData u J.x₀ J.ι x)) J.x₀ (frameVec J.ι l) =
      Gen.normW J.T * Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l := by
  have hS : DifferentiableAt ℝ (fun x ↦ Gen.sq2 (Gen.transTData u J.x₀ J.ι x)) J.x₀ := by
    unfold Gen.sq2
    exact DifferentiableAt.fun_sum fun i _ ↦ DifferentiableAt.fun_sum fun j _ ↦
      (h.differentiableAt_transT hu i j).pow 2
  have hT : ∀ i j, fderiv ℝ (fun x ↦ Gen.transTData u J.x₀ J.ι x i j) J.x₀ (frameVec J.ι l) =
      J.B l i j := fun i j ↦ h.transported_T (hu.of_le (by simp)) i j l
  have hw0 := normW_ne_zero hw
  unfold Gen.normW
  rw [fderiv_sqrt_apply' hS (h.sq2_transTData_ne_zero hw),
    fderiv_sq2_apply' (h.differentiableAt_transT hu)]
  simp only [hT, h.transTData_self]
  unfold Gen.normW at hw0
  unfold Gen.qVec Gen.normalizedX Gen.normalizedA
  rw [show Gen.normW J.T = √(Gen.sq2 J.T) from rfl,
    mul_div_mul_left _ _ two_ne_zero, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  field_simp

/-- **`∇_l A_{ij} = X_{lij} - q_l A_{ij}`.** -/
theorem fderiv_transA (i j l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ Gen.normalizedA (Gen.transTData u J.x₀ J.ι x) i j) J.x₀ (frameVec J.ι l) =
      Gen.normalizedX J.T J.B l i j -
        Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l * Gen.normalizedA J.T i j := by
  have hw0 := normW_ne_zero hw
  have hT : fderiv ℝ (fun x ↦ Gen.transTData u J.x₀ J.ι x i j) J.x₀ (frameVec J.ι l) = J.B l i j :=
    h.transported_T (hu.of_le (by simp)) i j l
  rw [show (fun x ↦ Gen.normalizedA (Gen.transTData u J.x₀ J.ι x) i j) = fun x ↦
      Gen.transTData u J.x₀ J.ι x i j / Gen.normW (Gen.transTData u J.x₀ J.ι x) from rfl,
    fderiv_div_apply' (h.differentiableAt_transT hu i j) (h.differentiableAt_transW hu hw)
    (h.transW_self_ne_zero hw), hT, h.fderiv_transW hu hw l, h.transW_self,
    h.transTData_self]
  generalize Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l = q
  unfold Gen.normalizedX Gen.normalizedA
  field_simp

/-- **`∇_l X_{ijk} = w⁻¹ (∇B)_{lijk} - q_l X_{ijk}`.** -/
theorem fderiv_transX (i j k l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ Gen.normalizedX (Gen.transTData u J.x₀ J.ι x) (Gen.transBData u J.x₀ J.ι x) i
        j k) J.x₀
        (frameVec J.ι l) =
      J.DB l i j k / Gen.normW J.T -
        Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l * Gen.normalizedX J.T J.B i j
            k := by
  have hw0 := normW_ne_zero hw
  have hB : fderiv ℝ (fun x ↦ Gen.transBData u J.x₀ J.ι x i j k) J.x₀ (frameVec J.ι l) =
      J.DB l i j k := h.transported_B (hu.of_le (by simp)) i j k l
  rw [show (fun x ↦ Gen.normalizedX (Gen.transTData u J.x₀ J.ι x) (Gen.transBData u J.x₀ J.ι x) i j
      k) =
      fun x ↦ Gen.transBData u J.x₀ J.ι x i j k / Gen.normW (Gen.transTData u J.x₀ J.ι x) from rfl,
    fderiv_div_apply' (h.differentiableAt_transB hu i j k) (h.differentiableAt_transW hu hw)
    (h.transW_self_ne_zero hw), hB, h.fderiv_transW hu hw l, h.transW_self,
    h.transBData_self]
  generalize Gen.qVec (Gen.normalizedX J.T J.B) (Gen.normalizedA J.T) l = q
  unfold Gen.normalizedX
  field_simp

/-- **`∇_l pᵢ = w A_{li} - g δ_{li}`.** -/
theorem fderiv_transP (i l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ Gen.transPData u J.x₀ J.ι x i) J.x₀ (frameVec J.ι l) =
      Gen.normW J.T * Gen.normalizedA J.T l i - J.g * Gen.kron l i := by
  have hw0 := normW_ne_zero hw
  rw [show (fun x ↦ Gen.transPData u J.x₀ J.ι x i) = fun x ↦ transP u J.x₀ J.ι x i from rfl,
    h.transported_p (hu.of_le (by simp)) i l]
  unfold Gen.normalizedA Gen.kron
  field_simp
  split_ifs <;> ring

omit hw in
/-- **`∇_l g = p_l`.** -/
theorem fderiv_transG (l : Fin (n - 1)) :
    fderiv ℝ (transG u) J.x₀ (frameVec J.ι l) = J.p l :=
  h.transported_g (hu.differentiableAt (by simp)) l

/-- **The generator.** Along `τ_l`, the normalized data `(A, p, g)` have derivative
`(D_l A, D_l p, D_l g)` at `z = 1`. -/
theorem fderiv_normalizedData (l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ (Gen.normalizedA (Gen.transTData u J.x₀ J.ι x), Gen.transPData u J.x₀ J.ι x,
      transG u x)) J.x₀ (frameVec J.ι l) =
      Gen.gen (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T) 1 l := by
  have hA : DifferentiableAt ℝ (fun x ↦ Gen.normalizedA (Gen.transTData u J.x₀ J.ι x)) J.x₀ :=
    differentiableAt_pi.2 fun i ↦ differentiableAt_pi.2 fun j ↦
      h.differentiableAt_transA hu hw i j
  have hp : DifferentiableAt ℝ (fun x ↦ Gen.transPData u J.x₀ J.ι x) J.x₀ :=
    differentiableAt_pi.2 fun i ↦ h.differentiableAt_transP hu i
  rw [fderiv_dataTriple_apply hA hp (h.differentiableAt_transG hu)]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only
  · funext i j
    rw [fderiv_ten2_apply hA]
    exact h.fderiv_transA hu hw i j l
  · funext i
    rw [fderiv_ten1_apply hp]
    simp only [Gen.gen, mul_one]
    exact h.fderiv_transP hu hw i l
  · simp only [Gen.gen, one_mul]
    exact h.fderiv_transG hu l

/-- **Normalized differentiation.** For every map `Φ` of the data `(A, p, g)` differentiable at
the data of `x₀`, the derivative of `x ↦ Φ(A(x), p(x), g(x))` along `τ_l` is `D_l Φ` at
`z = 1`. -/
theorem fderiv_certPoly_eq_Dl {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (Φ : Gen.Ten2 (n - 1) × Gen.Ten1 (n - 1) × ℝ → W) (hΦ : DifferentiableAt ℝ Φ (Gen.normalizedA
        J.T, J.p, J.g))
    (l : Fin (n - 1)) :
    fderiv ℝ (fun x ↦ Φ (Gen.normalizedA (Gen.transTData u J.x₀ J.ι x), Gen.transPData u J.x₀ J.ι x,
      transG u x)) J.x₀ (frameVec J.ι l) =
      Gen.Dl Φ (Gen.normalizedA J.T) (Gen.normalizedX J.T J.B) J.p J.g (Gen.normW J.T) 1 l :=
  equivariant_chain_rule Φ hΦ (h.differentiableAt_normalizedData hu hw)
    (h.normalizedData_self) (h.fderiv_normalizedData hu hw l)

end ConeJets.IsConeJet

end OnePhaseDimension
