/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap

/-!
# The pointwise density of a domain variation

Let `Φ_t = id + t ξ` be a domain variation and `v_t = u ∘ Φ_t⁻¹`. At a point `y` where `u` and
`ξ` are differentiable, with `A = Dξ(y)` and `p = ∇u(y)`, the change of variables `x = Φ_t(y)`
turns the energy density of `v_t` at `x` into

`Θ(t, A, p, c) = (|(I + tA)^{-T} p|² + c) det(I + tA)`,

where `c = 1_{u > 0}(y)`. This file studies `Θ` as a function of its four arguments:

* `domainVariationDensity_zero`: `Θ(0, A, p, c) = |p|² + c`;
* `hasDerivAt_domainVariationDensity`: `∂_t Θ(0, A, p, c) = (|p|² + c) tr A − 2 p · A p`, the
  integrand of the inner variation;
* `exists_lipschitzOnWith_domainVariationDensity`: `t ↦ Θ(t, A, p, c)` is Lipschitz on a fixed
  interval around `0`, uniformly for bounded `A`, `p` and `c ∈ [0, 1]`;
* `domainVariationDensity_nonneg`: `Θ ≥ 0` for `c ≥ 0` and `‖t A‖ < 1`;
* `measurable_domainVariationDensityProd`: `Θ` is Borel measurable in all its arguments.

The squared norm `|M^T p|²` is written `∑ᵢ (p · M eᵢ)²` in the standard basis, which is visibly
smooth in `(M, p)`, and `det` is the determinant of the underlying linear map.
-/

open Set Filter Topology Metric
open scoped RealInnerProductSpace NNReal

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ}

/-- `∑ᵢ (p · M eᵢ)² = |M^T p|²`, in the standard basis `eᵢ` of `ℝᵈ`. -/
def pullbackSq (M : E d →L[ℝ] E d) (p : E d) : ℝ :=
  ∑ i, ⟪p, M (EuclideanSpace.single i 1)⟫ ^ 2

/-- The determinant of a continuous linear endomorphism of `ℝᵈ`. -/
def opDet (A : E d →L[ℝ] E d) : ℝ :=
  LinearMap.det (A : E d →ₗ[ℝ] E d)

/-- The energy density of the domain variation `u ∘ (id + t ξ)⁻¹`, pulled back to the reference
configuration: `Θ(t, A, p, c) = (|(I + tA)^{-T} p|² + c) det(I + tA)`. -/
def domainVariationDensity (t : ℝ) (A : E d →L[ℝ] E d) (p : E d) (c : ℝ) : ℝ :=
  (pullbackSq (Ring.inverse (1 + t • A)) p + c) * opDet (1 + t • A)

/-! ### Basic identities -/

/-- `0 • A = 0`, stated with the scalar action used in `1 + t • A`. -/
theorem zero_smul_op (A : E d →L[ℝ] E d) : (0 : ℝ) • A = 0 :=
  zero_smul ℝ A

theorem one_apply_op (v : E d) : (1 : E d →L[ℝ] E d) v = v := rfl

theorem one_add_zero_smul (A : E d →L[ℝ] E d) : (1 : E d →L[ℝ] E d) + (0 : ℝ) • A = 1 := by
  rw [zero_smul_op, add_zero]

theorem inner_single_eq (p : E d) (i : Fin d) : ⟪p, EuclideanSpace.single i (1 : ℝ)⟫ = p i := by
  simp [EuclideanSpace.inner_single_right]

theorem pullbackSq_one (p : E d) : pullbackSq 1 p = ‖p‖ ^ 2 := by
  simp [pullbackSq, inner_single_eq, EuclideanSpace.norm_sq_eq]

/-- `∑ᵢ (p · eᵢ)(p · A eᵢ) = p · A p`. -/
theorem sum_inner_single_mul_inner (A : E d →L[ℝ] E d) (p : E d) :
    ∑ i, ⟪p, EuclideanSpace.single i (1 : ℝ)⟫ * ⟪p, A (EuclideanSpace.single i 1)⟫ =
      ⟪p, A p⟫ := by
  have hp : ∑ i, p i • EuclideanSpace.single i (1 : ℝ) = p := by
    simpa using (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr p
  calc ∑ i, ⟪p, EuclideanSpace.single i (1 : ℝ)⟫ * ⟪p, A (EuclideanSpace.single i 1)⟫
      = ⟪p, A (∑ i, p i • EuclideanSpace.single i (1 : ℝ))⟫ := by
        simp [map_sum, inner_sum, inner_smul_right, inner_single_eq]
    _ = ⟪p, A p⟫ := by rw [hp]

theorem opDet_one : opDet (1 : E d →L[ℝ] E d) = 1 := by
  simp [opDet]

/-- The determinant as a polynomial in the matrix entries `A(eⱼ)ᵢ`. -/
theorem opDet_eq_sum (A : E d →L[ℝ] E d) :
    opDet A = ∑ σ : Equiv.Perm (Fin d),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (EuclideanSpace.single i 1) (σ i) := by
  rw [opDet, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
    Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Units.smul_def, zsmul_eq_mul]
  simp [LinearMap.toMatrix_apply]

theorem contDiff_opDet {n : WithTop ℕ∞} : ContDiff ℝ n (opDet : (E d →L[ℝ] E d) → ℝ) := by
  have hentry : ∀ i j : Fin d, ContDiff ℝ n
      fun A : E d →L[ℝ] E d ↦ A (EuclideanSpace.single j 1) i := fun i j ↦
    (EuclideanSpace.proj i : E d →L[ℝ] ℝ).contDiff.comp (contDiff_id.clm_apply contDiff_const)
  rw [show (opDet : (E d →L[ℝ] E d) → ℝ) = fun A ↦ ∑ σ : Equiv.Perm (Fin d),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (EuclideanSpace.single i 1) (σ i) from
    funext opDet_eq_sum]
  exact ContDiff.sum fun σ _ ↦ contDiff_const.mul (contDiff_prod fun i _ ↦ hentry _ _)

theorem continuous_opDet : Continuous (opDet : (E d →L[ℝ] E d) → ℝ) :=
  (contDiff_opDet (n := 0)).continuous

/-- `t ↦ det(I + tA)` has derivative `tr A` at `0`. -/
theorem hasDerivAt_opDet_one_add_smul (A : E d →L[ℝ] E d) :
    HasDerivAt (fun t : ℝ ↦ opDet (1 + t • A))
      (LinearMap.trace ℝ (E d) (A : E d →ₗ[ℝ] E d)) 0 := by
  set b := (EuclideanSpace.basisFun (Fin d) ℝ).toBasis
  set M := LinearMap.toMatrix b b (A : E d →ₗ[ℝ] E d)
  set P := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)).divX.divX
  have hform : (fun t : ℝ ↦ opDet (1 + t • A)) =
      fun t ↦ 1 + M.trace * t + P.eval t * t ^ 2 := by
    funext t
    rw [opDet, ← LinearMap.det_toMatrix b, ← Matrix.det_one_add_smul]
    congr 1
    simp [M, map_add, map_smul, LinearMap.toMatrix_one]
  rw [hform, LinearMap.trace_eq_matrix_trace ℝ b]
  have h1 : HasDerivAt (fun t : ℝ ↦ M.trace * t) M.trace 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul M.trace
  have h2 : HasDerivAt (fun t : ℝ ↦ P.eval t * t ^ 2)
      (P.derivative.eval 0 * 0 ^ 2 + P.eval 0 * (2 * 0 ^ 1 * 1)) 0 :=
    (P.hasDerivAt 0).mul (by simpa using (hasDerivAt_pow 2 (0 : ℝ)))
  convert (h1.const_add 1).add h2 using 1
  simp [M]

/-! ### Invertibility -/

theorem isUnit_one_add {B : E d →L[ℝ] E d} (hB : ‖B‖ < 1) : IsUnit (1 + B) := by
  have h : ‖-B‖ < 1 := by rwa [norm_neg]
  simpa [sub_eq_add_neg] using (Units.oneSub (-B) h).isUnit

theorem opDet_ne_zero_of_isUnit {B : E d →L[ℝ] E d} (hB : IsUnit B) : opDet B ≠ 0 := by
  have hl : IsUnit (B : E d →ₗ[ℝ] E d) := hB.map ContinuousLinearMap.toLinearMapRingHom
  exact (LinearMap.isUnit_iff_isUnit_det _).1 hl |>.ne_zero

/-- `det(I + B) > 0` when `‖B‖ < 1`: along `s ↦ I + sB`, `s ∈ [0, 1]`, the determinant starts
at `1` and never vanishes. -/
theorem opDet_one_add_pos {B : E d →L[ℝ] E d} (hB : ‖B‖ < 1) : 0 < opDet (1 + B) := by
  by_contra hneg
  push Not at hneg
  set f : ℝ → ℝ := fun s ↦ opDet (1 + s • B)
  have hf : ContinuousOn f (Icc 0 1) :=
    (continuous_opDet.comp
      (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
  have hf0 : f 0 = 1 := by
    simp only [f]
    rw [one_add_zero_smul, opDet_one]
  have hmem : (0 : ℝ) ∈ Icc (f 1) (f 0) :=
    ⟨by simpa [f] using hneg, hf0 ▸ zero_le_one⟩
  obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc' zero_le_one hf hmem
  have hsB : ‖s • B‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    calc s * ‖B‖ ≤ 1 * ‖B‖ := by gcongr; exact hs.2
      _ < 1 := by simpa using hB
  exact opDet_ne_zero_of_isUnit (isUnit_one_add hsB) hfs

/-! ### The density at `t = 0` and its derivative -/

theorem domainVariationDensity_zero (A : E d →L[ℝ] E d) (p : E d) (c : ℝ) :
    domainVariationDensity 0 A p c = ‖p‖ ^ 2 + c := by
  rw [domainVariationDensity, one_add_zero_smul, Ring.inverse_one, pullbackSq_one, opDet_one,
    mul_one]

theorem domainVariationDensity_nonneg {t : ℝ} {A : E d →L[ℝ] E d} (htA : ‖t • A‖ < 1)
    (p : E d) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ domainVariationDensity t A p c :=
  mul_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hc)
    (opDet_one_add_pos htA).le

/-- `t ↦ (I + tA)⁻¹` has derivative `−A` at `0`. -/
theorem hasDerivAt_inverse_one_add_smul (A : E d →L[ℝ] E d) :
    HasDerivAt (fun t : ℝ ↦ Ring.inverse (1 + t • A)) (-A) 0 := by
  have hlin : HasDerivAt (fun t : ℝ ↦ 1 + t • A) ((1 : ℝ) • A) 0 :=
    ((hasDerivAt_id (0 : ℝ)).smul_const A).const_add 1
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (E d →L[ℝ] E d)ˣ)
  have h0 : (1 : E d →L[ℝ] E d) + (0 : ℝ) • A = ((1 : (E d →L[ℝ] E d)ˣ) : E d →L[ℝ] E d) := by
    rw [one_add_zero_smul, Units.val_one]
  rw [← h0] at hinv
  convert hinv.comp_hasDerivAt (0 : ℝ) hlin using 1
  · rfl
  · rw [show (1 : ℝ) • A = A from one_smul ℝ A]
    simp

/-- **The first variation of the density**: `∂_t Θ(0, A, p, c) = (|p|² + c) tr A − 2 p · A p`. -/
theorem hasDerivAt_domainVariationDensity (A : E d →L[ℝ] E d) (p : E d) (c : ℝ) :
    HasDerivAt (fun t ↦ domainVariationDensity t A p c)
      ((‖p‖ ^ 2 + c) * LinearMap.trace ℝ (E d) (A : E d →ₗ[ℝ] E d) - 2 * ⟪p, A p⟫) 0 := by
  have hM := hasDerivAt_inverse_one_add_smul A
  have hi : ∀ i : Fin d, HasDerivAt
      (fun t : ℝ ↦ ⟪p, Ring.inverse (1 + t • A) (EuclideanSpace.single i 1)⟫ ^ 2)
      (2 * ⟪p, EuclideanSpace.single i (1 : ℝ)⟫ * ⟪p, -A (EuclideanSpace.single i 1)⟫) 0 := by
    intro i
    have hval : Ring.inverse (1 + (0 : ℝ) • A) = 1 := by rw [one_add_zero_smul, Ring.inverse_one]
    have happ := hM.clm_apply (hasDerivAt_const (0 : ℝ) (EuclideanSpace.single i (1 : ℝ)))
    rw [hval, map_zero, add_zero] at happ
    have hinner := ((innerSL ℝ p).hasFDerivAt).comp_hasDerivAt (0 : ℝ) happ
    have hsq := hinner.pow 2
    convert hsq using 1
    · funext t
      rfl
    · simp only [Function.comp_apply, hval, innerSL_apply_apply, one_apply_op,
        neg_apply]
      push_cast
      ring
  have hsum : HasDerivAt (fun t : ℝ ↦ pullbackSq (Ring.inverse (1 + t • A)) p + c)
      (∑ i, 2 * ⟪p, EuclideanSpace.single i (1 : ℝ)⟫ * ⟪p, -A (EuclideanSpace.single i 1)⟫) 0 :=
    (HasDerivAt.fun_sum fun i _ ↦ hi i).add_const c
  have hprod := hsum.mul (hasDerivAt_opDet_one_add_smul A)
  have hsum' : ∑ i, 2 * ⟪p, EuclideanSpace.single i (1 : ℝ)⟫ *
      ⟪p, -A (EuclideanSpace.single i 1)⟫ = -(2 * ⟪p, A p⟫) := by
    rw [← sum_inner_single_mul_inner, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_neg_right]
    ring
  have h0 : pullbackSq (Ring.inverse (1 + (0 : ℝ) • A)) p + c = ‖p‖ ^ 2 + c := by
    rw [one_add_zero_smul, Ring.inverse_one, pullbackSq_one]
  have hd0 : opDet (1 + (0 : ℝ) • A) = 1 := by rw [one_add_zero_smul, opDet_one]
  rw [hsum', h0, hd0] at hprod
  have hfun : (fun t ↦ domainVariationDensity t A p c) =
      (fun t ↦ pullbackSq (Ring.inverse (1 + t • A)) p + c) * fun t ↦ opDet (1 + t • A) := rfl
  rw [hfun]
  convert hprod using 1
  ring

/-! ### Smoothness and a uniform Lipschitz bound in `t` -/

/-- `Θ` as a function of `(t, A, p, c)`. -/
def domainVariationDensityProd (z : ℝ × (E d →L[ℝ] E d) × E d × ℝ) : ℝ :=
  domainVariationDensity z.1 z.2.1 z.2.2.1 z.2.2.2

theorem contDiffAt_domainVariationDensityProd {z : ℝ × (E d →L[ℝ] E d) × E d × ℝ}
    (hz : IsUnit (1 + z.1 • z.2.1)) : ContDiffAt ℝ 1 domainVariationDensityProd z := by
  have hlin : ContDiff ℝ 1 fun z : ℝ × (E d →L[ℝ] E d) × E d × ℝ ↦ 1 + z.1 • z.2.1 :=
    contDiff_const.add (contDiff_fst.smul (contDiff_fst.comp contDiff_snd))
  have hinv : ContDiffAt ℝ 1
      (fun z : ℝ × (E d →L[ℝ] E d) × E d × ℝ ↦ Ring.inverse (1 + z.1 • z.2.1)) z := by
    have h := contDiffAt_ringInverse (𝕜 := ℝ) (n := 1) hz.unit
    rw [hz.unit_spec] at h
    exact h.comp z hlin.contDiffAt
  have hp : ContDiff ℝ 1 fun z : ℝ × (E d →L[ℝ] E d) × E d × ℝ ↦ z.2.2.1 :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have hc : ContDiff ℝ 1 fun z : ℝ × (E d →L[ℝ] E d) × E d × ℝ ↦ z.2.2.2 :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have hsum : ContDiffAt ℝ 1 (fun z : ℝ × (E d →L[ℝ] E d) × E d × ℝ ↦
      pullbackSq (Ring.inverse (1 + z.1 • z.2.1)) z.2.2.1) z := by
    unfold pullbackSq
    refine ContDiffAt.sum fun i _ ↦ ?_
    exact (ContDiffAt.inner ℝ hp.contDiffAt (hinv.clm_apply contDiffAt_const)).pow 2
  exact (hsum.add hc.contDiffAt).mul (contDiff_opDet.contDiffAt.comp z hlin.contDiffAt)

/-- **Uniform Lipschitz bound.** For `L, M ≥ 0` there are `δ > 0` and `K` such that
`t ↦ Θ(t, A, p, c)` is `K`-Lipschitz on `[-δ, δ]` whenever `‖A‖ ≤ L`, `‖p‖ ≤ M` and
`c ∈ [0, 1]`; moreover `‖t A‖ < 1` there. -/
theorem exists_lipschitzOnWith_domainVariationDensity (L M : ℝ) :
    ∃ δ > 0, ∃ K : ℝ≥0, ∀ A : E d →L[ℝ] E d, ∀ p : E d, ∀ c : ℝ, ‖A‖ ≤ L → ‖p‖ ≤ M →
      c ∈ Icc (0 : ℝ) 1 →
        LipschitzOnWith K (fun t ↦ domainVariationDensity t A p c) (closedBall 0 δ) ∧
        ∀ t ∈ closedBall (0 : ℝ) δ, ‖t • A‖ < 1 := by
  set δ : ℝ := 1 / (2 * (|L| + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hsmall : ∀ t ∈ closedBall (0 : ℝ) δ, ∀ A : E d →L[ℝ] E d, ‖A‖ ≤ L → ‖t • A‖ < 1 := by
    intro t ht A hA
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at ht
    rw [norm_smul, Real.norm_eq_abs]
    have hL : ‖A‖ ≤ |L| + 1 := hA.trans ((le_abs_self L).trans (le_add_of_nonneg_right zero_le_one))
    calc |t| * ‖A‖ ≤ δ * (|L| + 1) := mul_le_mul ht hL (norm_nonneg _) hδ.le
      _ = 1 / 2 := by rw [hδdef]; field_simp
      _ < 1 := by norm_num
  set S : Set (ℝ × (E d →L[ℝ] E d) × E d × ℝ) :=
    closedBall (0 : ℝ) δ ×ˢ (closedBall (0 : E d →L[ℝ] E d) L ×ˢ
      (closedBall (0 : E d) M ×ˢ Icc (0 : ℝ) 1))
  have hconv : Convex ℝ S :=
    (convex_closedBall _ _).prod ((convex_closedBall _ _).prod
      ((convex_closedBall _ _).prod (convex_Icc _ _)))
  have hcpt : IsCompact S :=
    (isCompact_closedBall _ _).prod ((isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod isCompact_Icc))
  have hcd : ContDiffOn ℝ 1 domainVariationDensityProd S := by
    intro z hz
    refine (contDiffAt_domainVariationDensityProd (isUnit_one_add ?_)).contDiffWithinAt
    exact hsmall _ hz.1 _ (by simpa using hz.2.1)
  obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith one_ne_zero hconv hcpt
  refine ⟨δ, hδ, K, fun A p c hA hp hc ↦ ⟨?_, fun t ht ↦ hsmall t ht A hA⟩⟩
  have hemb : LipschitzWith 1 fun t : ℝ ↦ (t, (A, (p, c))) :=
    LipschitzWith.prodMk_right (A, (p, c))
  have hmaps : MapsTo (fun t : ℝ ↦ (t, (A, (p, c)))) (closedBall 0 δ) S := fun t ht ↦
    ⟨ht, by simpa using hA, by simpa using hp, hc⟩
  simpa [domainVariationDensityProd, Function.comp_def] using
    hK.comp hemb.lipschitzOnWith hmaps

/-! ### Measurability -/

/-- Inversion of continuous linear endomorphisms of `ℝᵈ` (`0` at non-invertible maps) is Borel
measurable. -/
theorem measurable_ringInverse :
    Measurable (Ring.inverse : (E d →L[ℝ] E d) → (E d →L[ℝ] E d)) := by
  classical
  have hs : IsOpen {x : E d →L[ℝ] E d | IsUnit x} := Units.isOpen
  have heq : (Ring.inverse : (E d →L[ℝ] E d) → (E d →L[ℝ] E d)) =
      {x : E d →L[ℝ] E d | IsUnit x}.piecewise Ring.inverse (fun _ ↦ 0) := by
    funext x
    by_cases hx : IsUnit x
    · simp [Set.piecewise, hx]
    · simp [Set.piecewise, hx, Ring.inverse_non_unit]
  rw [heq]
  exact ContinuousOn.measurable_piecewise (differentiableOn_inverse (𝕜 := ℝ)).continuousOn
    continuousOn_const hs.measurableSet

theorem measurable_domainVariationDensityProd :
    Measurable (domainVariationDensityProd : ℝ × (E d →L[ℝ] E d) × E d × ℝ → ℝ) := by
  have hlin : Measurable fun z : ℝ × (E d →L[ℝ] E d) × E d × ℝ ↦ 1 + z.1 • z.2.1 :=
    (continuous_const.add (continuous_fst.smul (continuous_fst.comp continuous_snd))).measurable
  have hinv := measurable_ringInverse.comp hlin
  have hp : Measurable fun z : ℝ × (E d →L[ℝ] E d) × E d × ℝ ↦ z.2.2.1 :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hc : Measurable fun z : ℝ × (E d →L[ℝ] E d) × E d × ℝ ↦ z.2.2.2 :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hsum : Measurable fun z : ℝ × (E d →L[ℝ] E d) × E d × ℝ ↦
      pullbackSq (Ring.inverse (1 + z.1 • z.2.1)) z.2.2.1 := by
    unfold pullbackSq
    refine Finset.measurable_sum _ fun i _ ↦ ?_
    have happ : Measurable fun z : ℝ × (E d →L[ℝ] E d) × E d × ℝ ↦
        Ring.inverse (1 + z.1 • z.2.1) (EuclideanSpace.single i (1 : ℝ)) :=
      (ContinuousLinearMap.apply ℝ (E d)
        (EuclideanSpace.single i (1 : ℝ))).continuous.measurable.comp hinv
    exact (hp.inner happ).pow_const 2
  exact (hsum.add hc).mul (continuous_opDet.measurable.comp hlin)

/-- The trace in the standard basis: `tr A = ∑ᵢ (A eᵢ)ᵢ`. -/
theorem trace_eq_sum (A : E d →L[ℝ] E d) :
    LinearMap.trace ℝ (E d) (A : E d →ₗ[ℝ] E d) = ∑ i, A (EuclideanSpace.single i 1) i := by
  rw [LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun (Fin d) ℝ).toBasis,
    Matrix.trace]
  simp [LinearMap.toMatrix_apply]

theorem continuous_trace :
    Continuous fun A : E d →L[ℝ] E d ↦ LinearMap.trace ℝ (E d) (A : E d →ₗ[ℝ] E d) := by
  simp_rw [trace_eq_sum]
  exact continuous_finsetSum _ fun i _ ↦ (EuclideanSpace.proj i : E d →L[ℝ] ℝ).continuous.comp
    (continuous_id.clm_apply continuous_const)

end OnePhaseDimension
