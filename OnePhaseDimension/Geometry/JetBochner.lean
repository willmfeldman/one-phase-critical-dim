/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.Jets

/-!
# Bochner identities and gradient bounds at a point

Let `u` be `C⁴`, one-homogeneous and harmonic near the unit vector `x₀`, with jet record `J`.
Put `s² = |∇u|²` and `w̃² = r²|D²u|²`; both are zero-homogeneous, and at `x₀` they restrict to
`s² = g² + |p|²` and `w² = |T|²`. We prove, in ambient Euclidean form at `x₀`:

* `Δ|∇u|² = 2|D²u|²`, so `Δs²(x₀) = 2w²` (`laplacian_normSq_gradient`);
* `Δ(r²|D²u|²)(x₀) = 2m w² + 2|B|²` with `m = n - 1` (`laplacian_rsq_jetNormSq_two`);
* `D(|∇u|²)(x₀)[τ_l] = 2(Tp)_l` and `D(|∇u|²)(x₀)[x₀] = 0` (`fderiv_normSq_gradient_frame`,
  `fderiv_normSq_gradient_self`);
* `D(r²|D²u|²)(x₀)[τ_l] = 2⟨T, B_{l··}⟩` and `D(r²|D²u|²)(x₀)[x₀] = 0`;
* `|∇(r²|D²u|²)(x₀)|² ≤ 4 w² |B|²` (`norm_gradient_rsq_jetNormSq_two_sq_le`), and the algebraic
  form `|w⁻¹⟨T, B⟩|² ≤ |B|²` of `|∇w| ≤ |B|` on `{w > 0}`.

The Euclidean Laplacian of a zero-homogeneous function at `|x| = 1` is its spherical Laplacian;
that identification is made elsewhere.

## Differences from the source

The 2026-09-24 version derives `Δw² = 2mw² + 2|B|²` from `ΔT = mT` and the product rule on the
sphere. We compute `Δ(r²|D²u|²) = (2n - 8)|D²u|² + 2r²|D³u|²` in `ℝⁿ` and use
`|D³u(x₀)|² = |B|² + 3w²`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Function Filter Topology Set Laplacian EllipticBernoulli
open scoped ContDiff RealInnerProductSpace Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

/-! ### Cauchy–Schwarz for the contraction `⟨T, B_{l··}⟩` -/

section Algebra

variable {m : ℕ}

/-- `∑_l (∑_{jk} T_{jk} B_{ljk})² ≤ |T|² |B|²`. -/
theorem sum_sq_contract_le (T : Fin m → Fin m → ℝ) (B : Fin m → Fin m → Fin m → ℝ) :
    ∑ l, (∑ j, ∑ k, T j k * B l j k) ^ 2 ≤
      (∑ j, ∑ k, T j k ^ 2) * ∑ l, ∑ j, ∑ k, B l j k ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun l _ ↦ ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin m))
    (fun p ↦ T p.1 p.2) (fun p ↦ B l p.1 p.2)
  simpa only [Fintype.sum_prod_type] using h

/-- On `{w > 0}`, with `w = |T|`: `∑_l (w⁻¹ ∑_{jk} T_{jk}B_{ljk})² ≤ |B|²`. This is the algebraic
content of `|∇w| ≤ |B|`. -/
theorem sum_sq_inv_mul_contract_le (T : Fin m → Fin m → ℝ) (B : Fin m → Fin m → Fin m → ℝ)
    (hw : 0 < ∑ j, ∑ k, T j k ^ 2) :
    ∑ l, ((√(∑ j, ∑ k, T j k ^ 2))⁻¹ * ∑ j, ∑ k, T j k * B l j k) ^ 2 ≤
      ∑ l, ∑ j, ∑ k, B l j k ^ 2 := by
  simp_rw [mul_pow, inv_pow, Real.sq_sqrt hw.le, ← Finset.mul_sum]
  rw [inv_mul_le_iff₀ hw]
  exact sum_sq_contract_le T B

end Algebra

/-! ### Laplacians and gradients at a point -/

variable {n : ℕ} {u : E n → ℝ}

/-- `Δ|∇u|² = 2|D²u|²` for `u` harmonic and `C³` near `x`. -/
theorem laplacian_normSq_gradient_eq {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n))
    {x : E n} (hu : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 3 u y) (hΔ : ∀ᶠ y in 𝓝 x, Δ u y = 0) :
    Δ (fun y ↦ ‖∇ u y‖ ^ 2) x = 2 * jetNormSq e 2 u x := by
  have hfun : (fun y ↦ ‖∇ u y‖ ^ 2) = jetNormSq e 1 u := funext fun y ↦ (jetNormSq_one e u y).symm
  rw [hfun, laplacian_jetNormSq e (k := 1) (by exact_mod_cast hu) hΔ]

namespace ConeJets.IsConeJet

variable {J : ConeJets n} (h : IsConeJet u J)
include h

/-- **`Δs² = 2w²`** at `x₀`, in ambient form: `Δ|∇u|²(x₀) = 2|T|²`. -/
theorem laplacian_normSq_gradient (hu : ∀ᶠ y in 𝓝 J.x₀, ContDiffAt ℝ 3 u y)
    (hΔ : ∀ᶠ y in 𝓝 J.x₀, Δ u y = 0) :
    Δ (fun y ↦ ‖∇ u y‖ ^ 2) J.x₀ = 2 * ∑ i, ∑ j, J.T i j ^ 2 := by
  rw [laplacian_normSq_gradient_eq h.basis hu hΔ, h.jetNormSq_two_eq]

/-- **Bochner identity `Δw² = 2mw² + 2|B|²`** at `x₀`, in ambient form, for the
zero-homogeneous extension `w̃² = r²|D²u|²` (computed in any orthonormal basis `e`). -/
theorem laplacian_rsq_jetNormSq_two {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n))
    (hhom : IsOneHomogeneous u) (hu : ∀ᶠ y in 𝓝 J.x₀, ContDiffAt ℝ 4 u y)
    (hΔ : ∀ᶠ y in 𝓝 J.x₀, Δ u y = 0) :
    Δ (fun y ↦ ‖y‖ ^ 2 * jetNormSq e 2 u y) J.x₀ =
      2 * ((n - 1 : ℕ) : ℝ) * ∑ i, ∑ j, J.T i j ^ 2 + 2 * ∑ i, ∑ j, ∑ k, J.B i j k ^ 2 := by
  have hn : 1 ≤ n := pos_of_norm_eq_one h.norm_x₀
  rw [laplacian_normSq_mul_jetNormSq_two e hhom hu hΔ, h.jetNormSq_two_eq, h.jetNormSq_three_eq,
    h.norm_x₀, finrank_euclideanSpace_fin, Nat.cast_sub hn]
  push_cast
  ring

/-- The form used for the weighted Bochner estimate: `Δw̃²(x₀) ≥ 2|B|²`. -/
theorem two_sum_sq_B_le_laplacian {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n))
    (hhom : IsOneHomogeneous u) (hu : ∀ᶠ y in 𝓝 J.x₀, ContDiffAt ℝ 4 u y)
    (hΔ : ∀ᶠ y in 𝓝 J.x₀, Δ u y = 0) :
    2 * ∑ i, ∑ j, ∑ k, J.B i j k ^ 2 ≤ Δ (fun y ↦ ‖y‖ ^ 2 * jetNormSq e 2 u y) J.x₀ := by
  rw [h.laplacian_rsq_jetNormSq_two e hhom hu hΔ]
  have : 0 ≤ 2 * ((n - 1 : ℕ) : ℝ) * ∑ i, ∑ j, J.T i j ^ 2 := by positivity
  linarith

/-- `D|∇u|²(x₀)[a] = 2 ∑_A D¹u(x₀)[e_A] D²u(x₀)[a, e_A]` in the adapted basis. -/
theorem fderiv_normSq_gradient_apply (hu : ContDiffAt ℝ 2 u J.x₀) (a : E n) :
    fderiv ℝ (fun y ↦ ‖∇ u y‖ ^ 2) J.x₀ a =
      2 * (iteratedFDeriv ℝ 1 u J.x₀ ![J.x₀] * iteratedFDeriv ℝ 2 u J.x₀ ![a, J.x₀] +
        ∑ i, J.p i * iteratedFDeriv ℝ 2 u J.x₀ ![a, frameVec J.ι i]) := by
  have hfun : (fun y ↦ ‖∇ u y‖ ^ 2) = jetNormSq h.basis 1 u :=
    funext fun y ↦ (jetNormSq_one h.basis u y).symm
  rw [hfun, fderiv_jetNormSq_one_apply h.basis hu, Fintype.sum_option]
  simp only [basis_none, basis_some, h.p_eq']

/-- **`∇s² = 2Tp`**: `D|∇u|²(x₀)[τ_l] = 2 ∑ᵢ T_{li} pᵢ`. -/
theorem fderiv_normSq_gradient_frame (hu : ContDiffAt ℝ 2 u J.x₀) (l : Fin (n - 1)) :
    fderiv ℝ (fun y ↦ ‖∇ u y‖ ^ 2) J.x₀ (frameVec J.ι l) = 2 * ∑ i, J.T l i * J.p i := by
  rw [h.fderiv_normSq_gradient_apply hu, h.facts.D2_self_right, mul_zero, zero_add]
  simp_rw [← h.T_eq, mul_comm (J.p _)]

/-- The radial derivative of `|∇u|²` vanishes at `x₀`. -/
theorem fderiv_normSq_gradient_self (hu : ContDiffAt ℝ 2 u J.x₀) :
    fderiv ℝ (fun y ↦ ‖∇ u y‖ ^ 2) J.x₀ J.x₀ = 0 := by
  rw [h.fderiv_normSq_gradient_apply hu, h.facts.D2_self_right]
  simp [h.facts.D2_self_left]

/-- The derivative of `w̃² = r²|D²u|²` at `x₀`. -/
theorem fderiv_rsq_jetNormSq_two_apply {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n))
    (hu : ContDiffAt ℝ 3 u J.x₀) (a : E n) :
    fderiv ℝ (fun y ↦ ‖y‖ ^ 2 * jetNormSq e 2 u y) J.x₀ a =
      2 * ⟪J.x₀, a⟫ * jetNormSq e 2 u J.x₀ + fderiv ℝ (jetNormSq e 2 u) J.x₀ a := by
  have hh : DifferentiableAt ℝ (jetNormSq e 2 u) J.x₀ := by
    have : jetNormSq e 2 u =
        fun y ↦ ∑ I : Fin 2 → κ, iteratedFDeriv ℝ 2 u y (fun j ↦ e (I j)) ^ 2 := rfl
    rw [this]
    exact DifferentiableAt.fun_sum fun I _ ↦ ((contDiffAt_iteratedFDeriv_apply (k := 2) (m := 1)
      (by exact_mod_cast hu) _).differentiableAt one_ne_zero).pow 2
  have H := (hasStrictFDerivAt_norm_sq J.x₀).hasFDerivAt.mul hh.hasFDerivAt
  rw [show (fun y ↦ ‖y‖ ^ 2 * jetNormSq e 2 u y) = (fun y : E n ↦ ‖y‖ ^ 2) * jetNormSq e 2 u
    from rfl, H.fderiv]
  simp [h.norm_x₀]
  ring

/-- **`∇w² = 2⟨T, B⟩`**: `D(r²|D²u|²)(x₀)[τ_l] = 2 ∑_{jk} T_{jk} B_{ljk}`. -/
theorem fderiv_rsq_jetNormSq_two_frame {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n))
    (hu : ContDiffAt ℝ 3 u J.x₀) (l : Fin (n - 1)) :
    fderiv ℝ (fun y ↦ ‖y‖ ^ 2 * jetNormSq e 2 u y) J.x₀ (frameVec J.ι l) =
      2 * ∑ j, ∑ k, J.T j k * J.B l j k := by
  rw [h.fderiv_rsq_jetNormSq_two_apply e hu, show ⟪J.x₀, frameVec J.ι l⟫ = 0 by
    rw [real_inner_comm]; exact h.inner_ι _, mul_zero, zero_mul, zero_add,
    jetNormSq_eq e h.basis, fderiv_jetNormSq_two_apply h.basis hu]
  simp only [Fintype.sum_option, basis_none, basis_some, h.facts.D2_self_left,
    h.facts.D2_self_right, zero_mul, Finset.sum_const_zero, zero_add, ← h.T_eq, ← h.B_eq]

/-- The radial derivative of `w̃² = r²|D²u|²` vanishes at `x₀`. -/
theorem fderiv_rsq_jetNormSq_two_self {κ : Type*} [Fintype κ] (e : OrthonormalBasis κ ℝ (E n))
    (hhom : IsOneHomogeneous u) (hu : ContDiffAt ℝ 3 u J.x₀) :
    fderiv ℝ (fun y ↦ ‖y‖ ^ 2 * jetNormSq e 2 u y) J.x₀ J.x₀ = 0 := by
  rw [h.fderiv_rsq_jetNormSq_two_apply e hu, real_inner_self_eq_norm_sq, h.norm_x₀,
    fderiv_jetNormSq_apply_self e hhom (k := 2) (by exact_mod_cast hu)]
  push_cast
  ring

/-- **`|∇w̃²|² ≤ 4 w̃² |B|²`** at `x₀`, where `w̃²(x₀) = |x₀|²|D²u(x₀)|² = |T|²`. -/
theorem norm_gradient_rsq_jetNormSq_two_sq_le {κ : Type*} [Fintype κ]
    (e : OrthonormalBasis κ ℝ (E n)) (hhom : IsOneHomogeneous u) (hu : ContDiffAt ℝ 3 u J.x₀) :
    ‖∇ (fun y ↦ ‖y‖ ^ 2 * jetNormSq e 2 u y) J.x₀‖ ^ 2 ≤
      4 * (‖J.x₀‖ ^ 2 * jetNormSq e 2 u J.x₀) * ∑ i, ∑ j, ∑ k, J.B i j k ^ 2 := by
  rw [gradient, ← sum_sq_apply_orthonormalBasis h.basis, Fintype.sum_option, basis_none,
    h.fderiv_rsq_jetNormSq_two_self e hhom hu, h.norm_x₀, h.jetNormSq_two_eq]
  simp only [basis_some, h.fderiv_rsq_jetNormSq_two_frame e hu, mul_pow]
  rw [← Finset.mul_sum]
  have := sum_sq_contract_le J.T J.B
  norm_num
  nlinarith

end ConeJets.IsConeJet

end OnePhaseDimension
