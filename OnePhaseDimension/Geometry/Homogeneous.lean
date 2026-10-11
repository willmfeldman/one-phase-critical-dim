/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.Transport
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Calculus of `0`-homogeneous fields

Spherical quantities are represented by `0`-homogeneous functions and vector fields on (a cone
in) `ℝⁿ`, evaluated at unit vectors. This file records how the Euclidean operators act on them.

* **Euler relation.** If `f(r x) = f(x)` for `r > 0`, then `Df(x)[x] = 0`, and
  `Df(x̂) = |x| Df(x)` with `x̂ = x/|x|`.
* **Divergence.** For a `0`-homogeneous field `Z` and a unit vector `x₀` with tangent frame
  `τ_l`, `div Z(x₀) = ∑_l ⟪τ_l, DZ(x₀) τ_l⟫` (the radial term vanishes by the Euler relation).
  If moreover `Z` is tangential, this is the transported trace `∑_l ∇_l Z_l` (the spherical
  divergence).
* **Scalings.** For `Y(x) = a(|x|) Z(x)` with `Z` tangential and `0`-homogeneous,
  `div Y(x) = a(|x|) |x|⁻¹ (div Z)(x̂)`. For `φ(x) = ζ(|x|) f(x)` with `f` `0`-homogeneous,
  `|∇φ(x)|² = ζ'(|x|)² f(x)² + ζ(|x|)² |x|⁻² |∇f(x̂)|²`.
* **Laplacian.** For a `0`-homogeneous scalar `f` and a unit vector `x₀`,
  `Δf(x₀) = ∑_l D²f(x₀)[τ_l, τ_l] = ∑_l ∇_l ∇_l f`, the spherical Laplacian computed by transport.
-/

open Function Filter Topology Set
open scoped RealInnerProductSpace ContDiff Gradient Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### Homogeneity and the Euler relation -/

section General

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {f : F → G} {x : F}

/-- `f` is `0`-homogeneous: `f(r x) = f(x)` for all `r > 0`. -/
def IsZeroHomogeneous (f : F → G) : Prop := ∀ r : ℝ, 0 < r → ∀ x, f (r • x) = f x

/-- `Z` is a tangential field: `⟪x, Z(x)⟫ = 0` for all `x`. -/
def IsTangentialField (Z : F → F) : Prop := ∀ x, ⟪x, Z x⟫ = 0

omit [NormedAddCommGroup G] [NormedSpace ℝ G] in
theorem IsZeroHomogeneous.apply_radialProj (hf : IsZeroHomogeneous f) (hx : x ≠ 0) :
    f (radialProj x) = f x :=
  hf _ (inv_pos.2 (norm_pos_iff.2 hx)) x

/-- The derivative of the norm away from the origin: `D|x|[v] = ⟪x̂, v⟫`. -/
theorem hasFDerivAt_norm (hx : x ≠ 0) :
    HasFDerivAt (fun y : F ↦ ‖y‖) (realInnerCLM (radialProj x)) x := by
  have h2 : HasFDerivAt (fun y : F ↦ ‖y‖ ^ 2) (2 • realInnerCLM x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hs := h2.sqrt (by simp [hx])
  have heq : (fun y : F ↦ √(‖y‖ ^ 2)) = fun y ↦ ‖y‖ :=
    funext fun y ↦ Real.sqrt_sq (norm_nonneg y)
  rw [heq] at hs
  refine hs.congr_fderiv ?_
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  ext v
  simp only [smul_apply, realInnerCLM_apply, radialProj, smul_eq_mul,
    nsmul_eq_mul, Real.sqrt_sq (norm_nonneg x), real_inner_smul_left]
  field_simp
  push_cast
  ring

/-- **Euler relation for `0`-homogeneous maps**: `Df(x)[x] = 0`. -/
theorem IsZeroHomogeneous.fderiv_apply_self (hf : IsZeroHomogeneous f)
    (hd : DifferentiableAt ℝ f x) : fderiv ℝ f x x = 0 := by
  have hline : HasDerivAt (fun t : ℝ ↦ t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hdh : HasFDerivAt f (fderiv ℝ f x) ((1 : ℝ) • x) := by
    rw [one_smul]
    exact hd.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ ↦ f (t • x)) (fderiv ℝ f x x) 1 :=
    hdh.comp_hasDerivAt (1 : ℝ) hline
  have h2 : (fun t : ℝ ↦ f (t • x)) =ᶠ[𝓝 1] fun _ ↦ f x := by
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with t ht
    exact hf t ht x
  exact (h1.congr_of_eventuallyEq h2.symm).unique (hasDerivAt_const _ _)

/-- `Df(x) = r Df(r x)` for a `0`-homogeneous `f` and `r > 0`. -/
theorem IsZeroHomogeneous.fderiv_eq_smul_fderiv_smul (hf : IsZeroHomogeneous f) {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableAt ℝ f (r • x)) :
    fderiv ℝ f x = r • fderiv ℝ f (r • x) := by
  have hfun : f = fun y ↦ f (r • y) := funext fun y ↦ (hf r hr y).symm
  have h : HasFDerivAt (fun y ↦ f (r • y))
      ((fderiv ℝ f (r • x)).comp (r • ContinuousLinearMap.id ℝ F)) x :=
    hd.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)
  conv_lhs => rw [hfun]
  rw [h.fderiv]
  ext v
  simp

/-- `Df(x̂) = |x| Df(x)` for a `0`-homogeneous `f`. -/
theorem IsZeroHomogeneous.fderiv_radialProj (hf : IsZeroHomogeneous f) (hx : x ≠ 0)
    (hd : DifferentiableAt ℝ f x) : fderiv ℝ f (radialProj x) = ‖x‖ • fderiv ℝ f x := by
  have hr : 0 < ‖x‖ := norm_pos_iff.2 hx
  have hxr : ‖x‖ • radialProj x = x := by
    rw [radialProj, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [hf.fderiv_eq_smul_fderiv_smul hr (by rwa [hxr]), hxr]

theorem IsZeroHomogeneous.differentiableAt_radialProj (hf : IsZeroHomogeneous f) (hx : x ≠ 0)
    (hd : DifferentiableAt ℝ f x) : DifferentiableAt ℝ f (radialProj x) := by
  have hr : 0 < ‖x‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hx)
  have hfun : f = fun y ↦ f (‖x‖ • y) := funext fun y ↦ by
    rw [hf _ (norm_pos_iff.2 hx)]
  have hxr : ‖x‖ • radialProj x = x := by
    rw [radialProj, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]
  rw [hfun]
  exact (hxr ▸ hd).comp _ ((differentiableAt_id).const_smul _)

end General

/-! ### Divergence -/

variable {n : ℕ}

/-- The divergence as a sum over any orthonormal basis. -/
theorem divergence_eq_sum_inner {κ : Type*} [Fintype κ] (b : OrthonormalBasis κ ℝ (E n))
    (Z : E n → E n) (x : E n) : divergence Z x = ∑ i, ⟪b i, fderiv ℝ Z x (b i)⟫ := by
  rw [divergence, LinearMap.trace_eq_sum_inner _ b]
  rfl

/-- **Divergence of a `0`-homogeneous field at a unit vector**: the radial term vanishes, so
`div Z(x₀) = ∑_l ⟪τ_l, DZ(x₀) τ_l⟫`. -/
theorem IsZeroHomogeneous.divergence_eq_sum_frame {Z : E n → E n} (hZ : IsZeroHomogeneous Z)
    {x₀ : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hx : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0)
    (hd : DifferentiableAt ℝ Z x₀) :
    divergence Z x₀ = ∑ l, ⟪frameVec ι l, fderiv ℝ Z x₀ (frameVec ι l)⟫ := by
  rw [divergence_eq_sum_inner (adaptedBasis hx hι), Fintype.sum_option]
  simp [hZ.fderiv_apply_self hd]

/-- **Spherical divergence.** For a tangential `0`-homogeneous field, the divergence at a unit
vector is the transported trace `∑_l ∇_l Z_l`, with `Z_l(x) = ⟪τ_l(x), Z(x)⟫`. -/
theorem IsZeroHomogeneous.divergence_eq_transported_trace {Z : E n → E n}
    (hZ : IsZeroHomogeneous Z) (hZt : IsTangentialField Z) {x₀ : E n}
    {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hx : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0)
    (hd : DifferentiableAt ℝ Z x₀) :
    divergence Z x₀ =
      ∑ l, fderiv ℝ (fun x ↦ ⟪transFrame x₀ ι x l, Z x⟫) x₀ (frameVec ι l) := by
  rw [hZ.divergence_eq_sum_frame hx hι hd]
  exact Finset.sum_congr rfl fun l _ ↦
    (fderiv_inner_transFrame_of_tangential hd hx hι (hZt x₀) l _).symm

/-- `div Z(x̂) = |x| div Z(x)` for a `0`-homogeneous field. -/
theorem IsZeroHomogeneous.divergence_radialProj {Z : E n → E n} (hZ : IsZeroHomogeneous Z)
    {x : E n} (hx : x ≠ 0) (hd : DifferentiableAt ℝ Z x) :
    divergence Z (radialProj x) = ‖x‖ * divergence Z x := by
  rw [divergence, divergence, hZ.fderiv_radialProj hx hd, ContinuousLinearMap.toLinearMap_smul,
    map_smul, smul_eq_mul]

/-- **Scaling of the divergence.** For `Y(x) = a(|x|) Z(x)` with `Z` tangential and
`0`-homogeneous, `div Y(x) = a(|x|) |x|⁻¹ (div Z)(x̂)`. -/
theorem divergence_scaled_tangential {Z : E n → E n} (hZ : IsZeroHomogeneous Z)
    (hZt : IsTangentialField Z) {a : ℝ → ℝ} {x : E n} (hx : x ≠ 0)
    (ha : DifferentiableAt ℝ a ‖x‖) (hd : DifferentiableAt ℝ Z x) :
    divergence (fun y ↦ a ‖y‖ • Z y) x = a ‖x‖ * ‖x‖⁻¹ * divergence Z (radialProj x) := by
  have hA : HasFDerivAt (fun y : E n ↦ a ‖y‖)
      ((fderiv ℝ a ‖x‖).comp (realInnerCLM (radialProj x))) x :=
    ha.hasFDerivAt.comp x (hasFDerivAt_norm hx)
  have hprod : HasFDerivAt (fun y ↦ a ‖y‖ • Z y) _ x := hA.smul hd.hasFDerivAt
  have hrad : ⟪radialProj x, Z x⟫ = 0 := by
    rw [radialProj, real_inner_smul_left, hZt x, mul_zero]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  set c : E n →L[ℝ] ℝ := (fderiv ℝ a ‖x‖).comp (realInnerCLM (radialProj x))
  have htr :
      LinearMap.trace ℝ (E n) (c.smulRight (Z x) : E n →ₗ[ℝ] E n) = 0 := by
    have h := LinearMap.trace_smulRight (c : E n →ₗ[ℝ] ℝ) (Z x)
    refine (Eq.trans ?_ h).trans ?_
    · rfl
    · simp [c, hrad]
  rw [hZ.divergence_radialProj hx hd, divergence, hprod.fderiv,
    ContinuousLinearMap.toLinearMap_add, map_add, ContinuousLinearMap.toLinearMap_smul, map_smul,
    ← divergence, htr, smul_eq_mul, add_zero]
  field_simp

/-! ### Gradients -/

theorem inner_gradient_left {f : E n → ℝ} (x v : E n) : ⟪∇ f x, v⟫ = fderiv ℝ f x v := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

/-- `∇f(x̂) = |x| ∇f(x)` for a `0`-homogeneous scalar. -/
theorem IsZeroHomogeneous.gradient_radialProj {f : E n → ℝ} (hf : IsZeroHomogeneous f)
    {x : E n} (hx : x ≠ 0) (hd : DifferentiableAt ℝ f x) :
    ∇ f (radialProj x) = ‖x‖ • ∇ f x := by
  refine ext_inner_right ℝ fun v ↦ ?_
  rw [inner_gradient_left, hf.fderiv_radialProj hx hd, real_inner_smul_left,
    inner_gradient_left]
  rfl

/-- The gradient of a `0`-homogeneous scalar is tangential. -/
theorem IsZeroHomogeneous.inner_gradient_self {f : E n → ℝ} (hf : IsZeroHomogeneous f)
    {x : E n} (hd : DifferentiableAt ℝ f x) : ⟪x, ∇ f x⟫ = 0 := by
  rw [real_inner_comm, inner_gradient_left, hf.fderiv_apply_self hd]

/-- **Gradient of a separated function.** For `φ(x) = ζ(|x|) f(x)` with `f` `0`-homogeneous,
`|∇φ(x)|² = ζ'(|x|)² f(x)² + ζ(|x|)² |x|⁻² |∇f(x̂)|²`. -/
theorem normSq_grad_radial_times_zeroHom {f : E n → ℝ} (hf : IsZeroHomogeneous f)
    {ζ : ℝ → ℝ} {x : E n} (hx : x ≠ 0) (hζ : DifferentiableAt ℝ ζ ‖x‖)
    (hd : DifferentiableAt ℝ f x) :
    ‖∇ (fun y ↦ ζ ‖y‖ * f y) x‖ ^ 2 =
      deriv ζ ‖x‖ ^ 2 * f x ^ 2 + ζ ‖x‖ ^ 2 * ‖x‖⁻¹ ^ 2 * ‖∇ f (radialProj x)‖ ^ 2 := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hZ : HasFDerivAt (fun y : E n ↦ ζ ‖y‖) (deriv ζ ‖x‖ • realInnerCLM (radialProj x)) x :=
    hζ.hasDerivAt.comp_hasFDerivAt x (hasFDerivAt_norm hx)
  have hprod : HasFDerivAt (fun y ↦ ζ ‖y‖ * f y) _ x := hZ.mul hd.hasFDerivAt
  have hgrad : ∇ (fun y ↦ ζ ‖y‖ * f y) x =
      (deriv ζ ‖x‖ * f x) • radialProj x + ζ ‖x‖ • ∇ f x := by
    refine ext_inner_right ℝ fun v ↦ ?_
    rw [inner_gradient_left, hprod.fderiv, inner_add_left, real_inner_smul_left,
      real_inner_smul_left, inner_gradient_left]
    simp only [add_apply, smul_apply,
      realInnerCLM_apply, smul_eq_mul]
    ring
  have horth : ⟪radialProj x, ∇ f x⟫ = 0 := by
    rw [radialProj, real_inner_smul_left, hf.inner_gradient_self hd, mul_zero]
  rw [hgrad, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right, horth,
    norm_smul, norm_smul, norm_radialProj hx, hf.gradient_radialProj hx hd, norm_smul,
    norm_norm]
  simp only [Real.norm_eq_abs, mul_one, mul_zero, add_zero, mul_pow, sq_abs]
  field_simp

/-! ### The Laplacian of a `0`-homogeneous scalar -/

/-- The radial second derivative of a `0`-homogeneous scalar vanishes:
`D²f(x₀)[x₀, x₀] = 0`. -/
theorem IsZeroHomogeneous.iteratedFDeriv_two_self {f : E n → ℝ} (hf : IsZeroHomogeneous f)
    {x₀ : E n} (hd : ContDiffAt ℝ 2 f x₀) : iteratedFDeriv ℝ 2 f x₀ ![x₀, x₀] = 0 := by
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x₀ :=
    (hd.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hline : HasDerivAt (fun t : ℝ ↦ t • x₀) x₀ 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x₀
  have hdh : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x₀) ((1 : ℝ) • x₀) := by
    rw [one_smul]
    exact hD.hasFDerivAt
  have h1 : HasDerivAt (fun t : ℝ ↦ fderiv ℝ f (t • x₀) x₀) (fderiv ℝ (fderiv ℝ f) x₀ x₀ x₀) 1 :=
    (hdh.comp_hasDerivAt (1 : ℝ) hline).clm_apply (hasDerivAt_const _ x₀)
      |>.congr_deriv (by simp)
  have hev : ∀ᶠ y in 𝓝 x₀, DifferentiableAt ℝ f y :=
    (hd.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by norm_num)
  have hev' : ∀ᶠ t in 𝓝 (1 : ℝ), DifferentiableAt ℝ f (t • x₀) := by
    have hc : ContinuousAt (fun t : ℝ ↦ t • x₀) 1 := hline.continuousAt
    exact hc.eventually (p := fun y ↦ DifferentiableAt ℝ f y) (by simpa using hev)
  have h2 : (fun t : ℝ ↦ fderiv ℝ f (t • x₀) x₀) =ᶠ[𝓝 1] fun _ ↦ 0 := by
    filter_upwards [hev', lt_mem_nhds (zero_lt_one' ℝ)] with t ht htpos
    have h := hf.fderiv_apply_self ht
    rw [map_smul, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left htpos.ne'
  exact (h1.congr_of_eventuallyEq h2.symm).unique (hasDerivAt_const _ _)

/-- **Laplacian of a `0`-homogeneous scalar at a unit vector**:
`Δf(x₀) = ∑_l D²f(x₀)[τ_l, τ_l]`. -/
theorem IsZeroHomogeneous.laplacian_eq_sum_frame {f : E n → ℝ} (hf : IsZeroHomogeneous f)
    {x₀ : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hx : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0)
    (hd : ContDiffAt ℝ 2 f x₀) :
    Δ f x₀ = ∑ l, iteratedFDeriv ℝ 2 f x₀ ![frameVec ι l, frameVec ι l] := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (adaptedBasis hx hι)]
  dsimp only
  rw [Fintype.sum_option]
  simp [hf.iteratedFDeriv_two_self hd]

/-- **`Δ_E f = Δ_S f`.** For a `0`-homogeneous scalar, the Euclidean Laplacian at a unit vector is
the spherical Laplacian `∑_l ∇_l ∇_l f`, computed by transport: `∇_l f(x) = Df(x̂)[τ_l(x)]`. -/
theorem laplacian_zeroHom_eq_spherical {f : E n → ℝ} (hf : IsZeroHomogeneous f) {x₀ : E n}
    {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hx : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0)
    (hd : ContDiffAt ℝ 2 f x₀) :
    Δ f x₀ = ∑ l, fderiv ℝ (transJet f x₀ ι 1 ![l]) x₀ (frameVec ι l) := by
  have hD : DifferentiableAt ℝ (iteratedFDeriv ℝ 1 f) x₀ :=
    hd.differentiableAt_iteratedFDeriv (by norm_num)
  rw [hf.laplacian_eq_sum_frame hx hι hd]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [fderiv_transJet_frame hD hx hι, Fin.sum_univ_one]
  have e1 : (Fin.cons (frameVec ι l) fun s ↦ frameVec ι (![l] s) : Fin 2 → E n) =
      ![frameVec ι l, frameVec ι l] := by
    funext s; fin_cases s <;> rfl
  have e2 : update (fun s ↦ frameVec ι (![l] s)) 0 x₀ = ![x₀] := by
    funext s; fin_cases s; simp
  have h0 : iteratedFDeriv ℝ 1 f x₀ ![x₀] = 0 := by
    rw [iteratedFDeriv_one_apply]
    exact hf.fderiv_apply_self (hd.differentiableAt (by norm_num))
  rw [e1, e2, h0, mul_zero, sub_zero]

end OnePhaseDimension
