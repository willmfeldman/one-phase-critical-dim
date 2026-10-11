/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.JetBochner
public import Mathlib.Analysis.Calculus.Implicit
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Jets at the free boundary

At a regular point `x₀` of the free boundary, `u = max F 0` near `x₀` with `F` smooth,
`|∇F| = 1` on `{F = 0}` and `F` harmonic on `{F > 0}`.

* `fderiv_apply_eq_zero_of_eq_zero_on_levelSet`: a function vanishing on a regular level set of
  `F` has zero derivative along the kernel of `DF` (implicit function theorem).
* `mem_closure_pos_of_fderiv_ne_zero`: a regular zero of `F` lies in the closure of `{F > 0}`.
* `JetFacts.of_mem_closure`: the jet facts are closed conditions, so they pass from `{F > 0}`,
  where `F = u` is one-homogeneous and harmonic, to the boundary point (`jetFacts_of_chart`).

## Differences from the source

The 2026-09-24 version differentiates the boundary relations along the boundary using the
Levi-Civita connection of the boundary and its second fundamental form. We use a single lemma
instead: if `ψ` vanishes on `{F = 0}`, then `Dψ` vanishes on `ker DF`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Function Filter Topology Set Laplacian EllipticBernoulli
open scoped ContDiff RealInnerProductSpace Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

/-! ### Lemma (L): derivatives along a regular level set -/

section LevelSet

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Lemma (L).** Let `F` be strictly differentiable at `z` with `DF(z) ≠ 0`, and let `ψ`
vanish on the level set `{F = F(z)}` near `z`. Then `Dψ(z)v = 0` whenever `DF(z)v = 0`. -/
theorem fderiv_apply_eq_zero_of_eq_zero_on_levelSet {F : E → ℝ} {F' : E →L[ℝ] ℝ} {ψ : E → G}
    {ψ' : E →L[ℝ] G} {z : E} {U : Set E} (hU : U ∈ 𝓝 z) (hF : HasStrictFDerivAt F F' z)
    (hF' : F' ≠ 0) (hψ : HasFDerivAt ψ ψ' z) (hzero : ∀ y ∈ U, F y = F z → ψ y = 0) {v : E}
    (hv : F' v = 0) : ψ' v = 0 := by
  have hrange : LinearMap.range (F' : E →ₗ[ℝ] ℝ) = ⊤ :=
    Module.Dual.range_eq_top_of_ne_zero (f := (F' : E →ₗ[ℝ] ℝ)) fun h ↦
      hF' (ContinuousLinearMap.coe_injective (by simpa using h))
  set g : LinearMap.ker (F' : E →ₗ[ℝ] ℝ) → E := hF.implicitFunction F F' hrange (F z) with hg_def
  have hg : HasStrictFDerivAt g (LinearMap.ker (F' : E →ₗ[ℝ] ℝ)).subtypeL 0 :=
    hF.to_implicitFunction hrange
  have hg0 : g 0 = z := hF.implicitFunction_apply_image hrange
  have hlevel : ∀ᶠ y in 𝓝 (0 : LinearMap.ker (F' : E →ₗ[ℝ] ℝ)), F (g y) = F z :=
    (tendsto_const_nhds.prodMk_nhds tendsto_id).eventually
      (hF.map_implicitFunction_eq hrange)
  have hmem : ∀ᶠ y in 𝓝 (0 : LinearMap.ker (F' : E →ₗ[ℝ] ℝ)), g y ∈ U :=
    hg.continuousAt.preimage_mem_nhds (by rwa [hg0])
  have hcomp : HasFDerivAt (ψ ∘ g) (ψ'.comp (LinearMap.ker (F' : E →ₗ[ℝ] ℝ)).subtypeL) 0 := by
    rw [← hg0] at hψ
    exact hψ.comp 0 hg.hasFDerivAt
  have hzero' : HasFDerivAt (ψ ∘ g) (0 : _ →L[ℝ] G) 0 := by
    refine (hasFDerivAt_const (0 : G) _).congr_of_eventuallyEq ?_
    filter_upwards [hlevel, hmem] with y hy hyU
    exact hzero _ hyU hy
  have := congrArg (fun L ↦ L ⟨v, hv⟩) (hcomp.unique hzero')
  simpa using this

end LevelSet

/-! ### Regular zeros lie in the closure of the positive set -/

section Closure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A zero of `F` at which `DF ≠ 0` lies in the closure of `{F > 0} ∩ U` for every
neighborhood `U`. -/
theorem mem_closure_pos_of_fderiv_ne_zero {F : E → ℝ} {F' : E →L[ℝ] ℝ} {x₀ : E} {U : Set E}
    (hU : U ∈ 𝓝 x₀) (hF : HasFDerivAt F F' x₀) (hF0 : F x₀ = 0) (hF' : F' ≠ 0) :
    x₀ ∈ closure {y | y ∈ U ∧ 0 < F y} := by
  obtain ⟨w₀, hw₀⟩ : ∃ w, F' w ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hF' (ContinuousLinearMap.ext h)
  set w := (F' w₀)⁻¹ • w₀
  have hw : F' w = 1 := by simp [w, hw₀]
  have hline : HasDerivAt (fun t : ℝ ↦ x₀ + t • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x₀
  have hcomp : HasDerivAt (fun t : ℝ ↦ F (x₀ + t • w)) 1 0 := by
    have h1 : HasFDerivAt F F' (x₀ + (0 : ℝ) • w) := by simpa using hF
    have h2 := h1.comp_hasDerivAt (0 : ℝ) hline
    rw [hw] at h2
    exact h2
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos (f := fun t : ℝ ↦ F (x₀ + t • w))
    (x₀ := 0) (by rw [hcomp.deriv]; norm_num) (by simpa using hF0)
  have htend : Tendsto (fun t : ℝ ↦ x₀ + t • w) (𝓝[>] 0) (𝓝 x₀) := by
    have : Tendsto (fun t : ℝ ↦ x₀ + t • w) (𝓝 0) (𝓝 (x₀ + (0 : ℝ) • w)) :=
      hline.continuousAt.tendsto
    simpa using this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto htend ?_
  filter_upwards [htend.eventually hU, nhdsWithin_le_nhds hsign, self_mem_nhdsWithin]
    with t htU hts ht
  refine ⟨htU, ?_⟩
  rw [sub_zero, sign_pos (show (0 : ℝ) < t from ht)] at hts
  exact sign_eq_one_iff.1 hts

/-- A function continuous at `x₀` and vanishing on `S` vanishes at points of `closure S`. -/
theorem eq_zero_of_mem_closure {X : Type*} [TopologicalSpace X] {φ : X → ℝ} {S : Set X}
    {x₀ : X} (hφ : ContinuousAt φ x₀) (hx : x₀ ∈ closure S) (h : ∀ y ∈ S, φ y = 0) :
    φ x₀ = 0 := by
  have := hφ.continuousWithinAt.mem_closure_image hx
  have hsub : φ '' S ⊆ {0} := by
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  simpa using closure_mono hsub this

end Closure

end OnePhaseDimension

namespace OnePhaseDimension

/-! ### Jet facts at boundary points -/

section Chart

variable {n : ℕ}

/-- A natural number is below the smoothness exponent `∞`. -/
theorem natCast_le_infty (k : ℕ) : ((k : ℕ) : ℕ∞ω) ≤ ∞ :=
  WithTop.coe_le_coe.2 le_top

/-- Continuity of `y ↦ Dᵏf(y)[v(y)]`. -/
theorem continuousAt_iteratedFDeriv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {k : ℕ} {x₀ : E} (hf : ContDiffAt ℝ k f x₀) {v : E → Fin k → E}
    (hv : ContinuousAt v x₀) : ContinuousAt (fun y ↦ iteratedFDeriv ℝ k f y (v y)) x₀ :=
  (hf.iteratedFDeriv_right (m := 0) (by simp)).continuousAt.eval hv

/-- The jet facts transfer along functions agreeing near the point. -/
theorem JetFacts.congr {u F : E n → ℝ} {y : E n} (h : JetFacts u y) (huF : u =ᶠ[𝓝 y] F) :
    JetFacts F y := by
  have hk : ∀ k, iteratedFDeriv ℝ k u y = iteratedFDeriv ℝ k F y := fun k ↦
    (huF.iteratedFDeriv ℝ k).self_of_nhds
  exact
    { symm := fun k hk' σ v ↦ by simpa only [hk] using h.symm k hk' σ v
      euler := fun k hk' v ↦ by simpa only [hk] using h.euler k hk' v
      trace := fun k hk' κ _ e v ↦ by simpa only [hk] using h.trace k hk' κ e v }

/-- The jet facts are closed conditions: if `u` is `C⁴` at `x₀` and the jet facts hold on a set
whose closure contains `x₀`, they hold at `x₀`. -/
theorem JetFacts.of_mem_closure {u : E n → ℝ} {x₀ : E n} {S : Set (E n)}
    (hu : ContDiffAt ℝ 4 u x₀) (hx : x₀ ∈ closure S) (hS : ∀ y ∈ S, JetFacts u y) :
    JetFacts u x₀ where
  symm k hk σ v := by
    have hk' : ContDiffAt ℝ k u x₀ := hu.of_le (by exact_mod_cast hk)
    refine sub_eq_zero.1 (eq_zero_of_mem_closure (φ := fun y ↦
      iteratedFDeriv ℝ k u y (v ∘ σ) - iteratedFDeriv ℝ k u y v) ?_ hx
      fun y hy ↦ sub_eq_zero.2 ((hS y hy).symm k hk σ v))
    exact (continuousAt_iteratedFDeriv_apply hk' continuousAt_const).sub
      (continuousAt_iteratedFDeriv_apply hk' continuousAt_const)
  euler k hk v := by
    have hk1 : ContDiffAt ℝ (k + 1 : ℕ) u x₀ := hu.of_le (by exact_mod_cast (by omega : k + 1 ≤ 4))
    have hk0 : ContDiffAt ℝ k u x₀ := hu.of_le (by exact_mod_cast (by omega : k ≤ 4))
    refine sub_eq_zero.1 (eq_zero_of_mem_closure (φ := fun y ↦
      iteratedFDeriv ℝ (k + 1) u y (Fin.cons y v) - (1 - k : ℝ) * iteratedFDeriv ℝ k u y v) ?_ hx
      fun y hy ↦ sub_eq_zero.2 ((hS y hy).euler k hk v))
    exact (continuousAt_iteratedFDeriv_apply hk1 (continuousAt_id.finCons continuousAt_const)).sub
      (continuousAt_const.mul (continuousAt_iteratedFDeriv_apply hk0 continuousAt_const))
  trace k hk κ _ e v := by
    have hk2 : ContDiffAt ℝ (k + 2 : ℕ) u x₀ := hu.of_le (by exact_mod_cast (by omega : k + 2 ≤ 4))
    refine eq_zero_of_mem_closure (φ := fun y ↦
      ∑ i, iteratedFDeriv ℝ (k + 2) u y (Fin.cons (e i) (Fin.cons (e i) v))) ?_ hx
      fun y hy ↦ (hS y hy).trace k hk κ e v
    exact tendsto_finsetSum _ fun i _ ↦
      continuousAt_iteratedFDeriv_apply hk2 continuousAt_const

/-- **Jets at a regular boundary point.** Let `u` be one-homogeneous, and near `x₀` let
`u = max F 0` with `F` smooth on an open set `U`, harmonic on `{F > 0}`, `F(x₀) = 0` and
`DF(x₀) ≠ 0`. Then the jets of `F` at `x₀` satisfy the jet facts: they are limits of the jets of
`u` from the positive side. -/
theorem jetFacts_of_chart {u F : E n → ℝ} {U : Set (E n)} {x₀ : E n} (hU : IsOpen U)
    (hx₀ : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hF0 : F x₀ = 0) (hDF : fderiv ℝ F x₀ ≠ 0)
    (hhom : IsOneHomogeneous u) (huF : ∀ x ∈ U, u x = max (F x) 0)
    (hΔ : ∀ x ∈ U, 0 < F x → Δ F x = 0) : JetFacts F x₀ := by
  have hFat : ∀ y ∈ U, ContDiffAt ℝ 4 F y := fun y hy ↦
    (hF.contDiffAt (hU.mem_nhds hy)).of_le (natCast_le_infty 4)
  set S : Set (E n) := {y | y ∈ U ∧ 0 < F y}
  have hSopen : IsOpen S := hF.continuousOn.isOpen_inter_preimage hU isOpen_Ioi
  have hev : ∀ y ∈ S, u =ᶠ[𝓝 y] F := fun y hy ↦ by
    filter_upwards [hSopen.mem_nhds hy] with z hz
    rw [huF z hz.1, max_eq_left hz.2.le]
  refine JetFacts.of_mem_closure (hFat x₀ hx₀)
    (mem_closure_pos_of_fderiv_ne_zero (hU.mem_nhds hx₀)
      ((hFat x₀ hx₀).differentiableAt (by norm_num)).hasFDerivAt hF0 hDF) fun y hy ↦ ?_
  refine (jetFacts_of_harmonic hhom ?_ ?_).congr (hev y hy)
  · filter_upwards [hSopen.mem_nhds hy] with z hz
    exact (hFat z hz.1).congr_of_eventuallyEq (hev z hz)
  · filter_upwards [hSopen.mem_nhds hy] with z hz
    rw [(InnerProductSpace.laplacian_congr_nhds (hev z hz)).self_of_nhds]
    exact hΔ z hz.1 hz.2

end Chart

end OnePhaseDimension

namespace OnePhaseDimension

/-! ### The Hessian along the normal -/

section Normal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem fderiv_apply_eq_inner_gradient (f : E → ℝ) (x v : E) : fderiv ℝ f x v = ⟪∇ f x, v⟫ := by
  rw [gradient, InnerProductSpace.toDual_symm_apply]

/-- `∑_A ∂_A f(x) L(e_A) = L(∇f(x))` for a linear form `L`. -/
theorem sum_fderiv_mul_apply {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E) (f : E → ℝ)
    (x : E) (L : E →L[ℝ] ℝ) : ∑ a, fderiv ℝ f x (e a) * L (e a) = L (∇ f x) := by
  conv_rhs => rw [← e.sum_repr' (∇ f x)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, smul_eq_mul, fderiv_apply_eq_inner_gradient, real_inner_comm]

omit [FiniteDimensional ℝ E] in
theorem differentiableAt_jetNormSq {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E) {k : ℕ}
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ (k + 1 : ℕ) u x) :
    DifferentiableAt ℝ (jetNormSq e k u) x := by
  have : jetNormSq e k u =
      fun y ↦ ∑ I : Fin k → ι, iteratedFDeriv ℝ k u y (fun j ↦ e (I j)) ^ 2 := rfl
  rw [this]
  exact DifferentiableAt.fun_sum fun I _ ↦ ((contDiffAt_iteratedFDeriv_apply (m := 1) hu
    _).differentiableAt one_ne_zero).pow 2

/-- **The Hessian along the normal.** If `|∇F| = 1` on `{F = 0}` near a zero `z` of a `C²`
function `F`, then `D²F(z)[v, ∇F(z)] = 0` for every `v ⊥ ∇F(z)`: tangential differentiation of
`|∇F|² = 1`. -/
theorem iteratedFDeriv_two_gradient_eq_zero {F : E → ℝ} {U : Set E} {z : E} (hU : U ∈ 𝓝 z)
    (hF : ContDiffAt ℝ 2 F z) (hz : F z = 0) (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) {v : E}
    (hv : ⟪∇ F z, v⟫ = 0) : iteratedFDeriv ℝ 2 F z ![v, ∇ F z] = 0 := by
  set e := stdOrthonormalBasis ℝ E
  have hd : DifferentiableAt ℝ (jetNormSq e 1 F) z := differentiableAt_jetNormSq e (k := 1) hF
  have hψ : HasFDerivAt (fun y ↦ ‖∇ F y‖ ^ 2 - 1) (fderiv ℝ (jetNormSq e 1 F) z) z := by
    have hfun : (fun y ↦ ‖∇ F y‖ ^ 2 - 1) = fun y ↦ jetNormSq e 1 F y - 1 :=
      funext fun y ↦ by rw [jetNormSq_one]
    rw [hfun]
    exact hd.hasFDerivAt.sub_const 1
  have hF' : fderiv ℝ F z ≠ 0 := by
    intro h0
    have h1 := hgrad z (mem_of_mem_nhds hU) hz
    rw [gradient, h0, map_zero, norm_zero] at h1
    norm_num at h1
  have key := fderiv_apply_eq_zero_of_eq_zero_on_levelSet hU (hF.hasStrictFDerivAt (by norm_num))
    hF' hψ (fun y hy hy0 ↦ by rw [hgrad y hy (hz ▸ hy0)]; norm_num) (v := v)
    (by rwa [fderiv_apply_eq_inner_gradient])
  rw [fderiv_jetNormSq_one_apply e hF] at key
  simp only [iteratedFDeriv_one_apply, iteratedFDeriv_two_apply] at key ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at key ⊢
  rw [sum_fderiv_mul_apply e F z (fderiv ℝ (fderiv ℝ F) z v)] at key
  linarith

/-- The linear form `a ↦ M(a, v)` of a multilinear form `M`. -/
def consCLM {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ E) ℝ)
    (v : Fin k → E) : E →L[ℝ] ℝ :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) ℝ v).comp M.curryLeft

omit [FiniteDimensional ℝ E] in
@[simp] theorem consCLM_apply {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ E) ℝ)
    (v : Fin k → E) (a : E) : consCLM M v a = M (Fin.cons a v) := by
  simp [consCLM, ContinuousMultilinearMap.curryLeft_apply]

/-- `∑_A ∂_A f(x) M(e_A, v) = M(∇f(x), v)`. -/
theorem sum_fderiv_mul_cons {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E) (f : E → ℝ)
    (x : E) {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ E) ℝ) (v : Fin k → E) :
    ∑ a, fderiv ℝ f x (e a) * M (Fin.cons (e a) v) = M (Fin.cons (∇ f x) v) := by
  simpa using sum_fderiv_mul_apply e f x (consCLM M v)

omit [FiniteDimensional ℝ E] in
/-- The derivative of `y ↦ Dᵏf(y)[w]` in the direction `v`. -/
theorem fderiv_iteratedFDeriv_apply {f : E → ℝ} {x : E} {k : ℕ}
    (hf : ContDiffAt ℝ (k + 1 : ℕ) f x) (w : Fin k → E) (v : E) :
    fderiv ℝ (fun y ↦ iteratedFDeriv ℝ k f y w) x v = iteratedFDeriv ℝ (k + 1) f x (Fin.cons v w) :=
  (iteratedFDeriv_succ_apply_cons_of_contDiffAt hf v w).symm

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_iteratedFDeriv_apply {f : E → ℝ} {x : E} {k : ℕ}
    (hf : ContDiffAt ℝ (k + 1 : ℕ) f x) (w : Fin k → E) :
    HasFDerivAt (fun y ↦ iteratedFDeriv ℝ k f y w)
      (fderiv ℝ (fun y ↦ iteratedFDeriv ℝ k f y w) x) x :=
  ((contDiffAt_iteratedFDeriv_apply (m := 1) hf w).differentiableAt one_ne_zero).hasFDerivAt

/-- On the level set, `D²F[∇F, w] = D²F[∇F, ∇F]⟨∇F, w⟩` (from the normal Hessian lemma). -/
theorem hess_gradient_eq {F : E → ℝ} {U : Set E} {y : E} (hU : U ∈ 𝓝 y)
    (hF : ContDiffAt ℝ 2 F y) (hy : F y = 0) (hgrad : ∀ z ∈ U, F z = 0 → ‖∇ F z‖ = 1) (w : E) :
    iteratedFDeriv ℝ 2 F y ![∇ F y, w] =
      iteratedFDeriv ℝ 2 F y ![∇ F y, ∇ F y] * ⟪∇ F y, w⟫ := by
  have hN : ‖∇ F y‖ = 1 := hgrad y (mem_of_mem_nhds hU) hy
  set N := ∇ F y
  have horth : ⟪N, w - ⟪N, w⟫ • N⟫ = 0 := by
    rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hN]
    ring
  have h0 := iteratedFDeriv_two_gradient_eq_zero hU hF hy hgrad horth
  have hsym : ∀ a b, iteratedFDeriv ℝ 2 F y ![a, b] = iteratedFDeriv ℝ 2 F y ![b, a] :=
    fun a b ↦ iteratedFDeriv_cons_cons_comm (k := 0) hF a b ![]
  rw [hsym] at h0
  have hlin : iteratedFDeriv ℝ 2 F y ![N, w - ⟪N, w⟫ • N] =
      iteratedFDeriv ℝ 2 F y ![N, w] - ⟪N, w⟫ * iteratedFDeriv ℝ 2 F y ![N, N] := by
    rw [hsym N, hsym N w, hsym N N]
    have := consCLM (iteratedFDeriv ℝ 2 F y) ![N] |>.map_sub w (⟪N, w⟫ • N)
    simp only [consCLM_apply, map_smul, smul_eq_mul] at this
    exact this
  rw [hlin] at h0
  linarith

omit [FiniteDimensional ℝ E] in
/-- `∑_A ⟨w, e_A⟩ L(e_A) = L(w)`. -/
theorem sum_inner_mul_apply {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E) (w : E)
    (L : E →L[ℝ] ℝ) : ∑ a, ⟪w, e a⟫ * L (e a) = L w := by
  conv_rhs => rw [← e.sum_repr' w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, smul_eq_mul, real_inner_comm]

/-- **Odd normal component of `D³F` on the boundary.** If `|∇F| = 1` on `{F = 0}` near a zero
`z` of a `C³` function `F`, with `N = ∇F(z)`, then for `v, w ⊥ N`:
`D³F[v, N, w] = D²F[N, N] D²F[v, w] - ∑_A D²F[v, e_A] D²F[e_A, w]`.
This is tangential differentiation of `D²F ∇F - D²F(∇F, ∇F) ∇F = 0` on `{F = 0}`. -/
theorem iteratedFDeriv_three_normal {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ E)
    {F : E → ℝ} {U : Set E} {z : E} (hU : U ∈ 𝓝 z) (hF : ∀ y ∈ U, ContDiffAt ℝ 3 F y)
    (hz : F z = 0) (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) {v w : E} (hv : ⟪∇ F z, v⟫ = 0)
    (hw : ⟪∇ F z, w⟫ = 0) :
    iteratedFDeriv ℝ 3 F z ![v, ∇ F z, w] =
      iteratedFDeriv ℝ 2 F z ![∇ F z, ∇ F z] * iteratedFDeriv ℝ 2 F z ![v, w] -
        ∑ A, iteratedFDeriv ℝ 2 F z ![v, e A] * iteratedFDeriv ℝ 2 F z ![e A, w] := by
  obtain ⟨V, hVU, hVo, hzV⟩ := mem_nhds_iff.1 hU
  have hz3 : ContDiffAt ℝ 3 F z := hF z (hVU hzV)
  have hz2 : ContDiffAt ℝ 2 F z := hz3.of_le (by norm_num)
  -- the three identities that hold at every point
  have e1 : ∀ y, ContDiffAt ℝ 2 F y → ∀ a : E,
      ∑ A, iteratedFDeriv ℝ 1 F y ![e A] * iteratedFDeriv ℝ 2 F y ![e A, a] =
        iteratedFDeriv ℝ 2 F y ![∇ F y, a] := fun y _ a ↦ by
    have := sum_fderiv_mul_cons e F y (iteratedFDeriv ℝ 2 F y) ![a]
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
    exact this
  have hsym2 : ∀ y, ContDiffAt ℝ 2 F y → ∀ a b : E,
      iteratedFDeriv ℝ 2 F y ![a, b] = iteratedFDeriv ℝ 2 F y ![b, a] :=
    fun y hy a b ↦ iteratedFDeriv_cons_cons_comm (k := 0) hy a b ![]
  have e2 : ∀ y, ContDiffAt ℝ 2 F y →
      ∑ A, ∑ B, iteratedFDeriv ℝ 1 F y ![e A] * iteratedFDeriv ℝ 1 F y ![e B] *
        iteratedFDeriv ℝ 2 F y ![e A, e B] = iteratedFDeriv ℝ 2 F y ![∇ F y, ∇ F y] := by
    intro y hy
    have : ∀ A, ∑ B, iteratedFDeriv ℝ 1 F y ![e A] * iteratedFDeriv ℝ 1 F y ![e B] *
        iteratedFDeriv ℝ 2 F y ![e A, e B] =
          iteratedFDeriv ℝ 1 F y ![e A] * iteratedFDeriv ℝ 2 F y ![e A, ∇ F y] := by
      intro A
      rw [hsym2 y hy _ (∇ F y), ← e1 y hy, Finset.mul_sum]
      refine Finset.sum_congr rfl fun B _ ↦ ?_
      rw [hsym2 y hy (e A) (e B)]
      ring
    simp_rw [this]
    exact e1 y hy _
  have e3 : ∀ y, ∑ A, iteratedFDeriv ℝ 1 F y ![e A] * ⟪e A, w⟫ = ⟪∇ F y, w⟫ := fun y ↦ by
    have := sum_fderiv_mul_apply e F y (innerSL ℝ w)
    simp only [innerSL_apply_apply] at this
    simp only [iteratedFDeriv_one_apply, Matrix.cons_val_zero]
    rw [real_inner_comm, ← this]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [real_inner_comm]
  -- the function vanishing on the level set
  set ψ : E → ℝ := fun y ↦
    ∑ A, iteratedFDeriv ℝ 1 F y ![e A] * iteratedFDeriv ℝ 2 F y ![e A, w] -
      (∑ A, ∑ B, iteratedFDeriv ℝ 1 F y ![e A] * iteratedFDeriv ℝ 1 F y ![e B] *
        iteratedFDeriv ℝ 2 F y ![e A, e B]) *
      ∑ A, iteratedFDeriv ℝ 1 F y ![e A] * ⟪e A, w⟫ with hψ_def
  have hvanish : ∀ y ∈ V, F y = F z → ψ y = 0 := by
    intro y hy hy0
    have hyU : U ∈ 𝓝 y := mem_of_superset (hVo.mem_nhds hy) hVU
    have hy2 : ContDiffAt ℝ 2 F y := (hF y (hVU hy)).of_le (by norm_num)
    rw [hz] at hy0
    simp only [hψ_def]
    rw [e1 y hy2, e2 y hy2, e3 y, hess_gradient_eq hyU hy2 hy0 hgrad w, sub_self]
  -- its derivative
  have hd : ∀ A, HasFDerivAt (fun y ↦ iteratedFDeriv ℝ 1 F y ![e A])
      (fderiv ℝ (fun y ↦ iteratedFDeriv ℝ 1 F y ![e A]) z) z := fun A ↦
    hasFDerivAt_iteratedFDeriv_apply (k := 1) hz2 _
  have hH : ∀ (a b : E), HasFDerivAt (fun y ↦ iteratedFDeriv ℝ 2 F y ![a, b])
      (fderiv ℝ (fun y ↦ iteratedFDeriv ℝ 2 F y ![a, b]) z) z := fun a b ↦
    hasFDerivAt_iteratedFDeriv_apply (k := 2) hz3 _
  have hψ : HasFDerivAt ψ _ z :=
    (HasFDerivAt.fun_sum fun A _ ↦ (hd A).mul (hH (e A) w)).sub
      ((HasFDerivAt.fun_sum fun A _ ↦ HasFDerivAt.fun_sum fun B _ ↦
        ((hd A).mul (hd B)).mul (hH (e A) (e B))).mul
        (HasFDerivAt.fun_sum fun A _ ↦ (hd A).mul_const ⟪e A, w⟫))
  have hF' : fderiv ℝ F z ≠ 0 := by
    intro h0
    have h1 := hgrad z (hVU hzV) hz
    rw [gradient, h0, map_zero, norm_zero] at h1
    norm_num at h1
  have key := fderiv_apply_eq_zero_of_eq_zero_on_levelSet (hVo.mem_nhds hzV)
    (hz3.hasStrictFDerivAt (by norm_num)) hF' hψ hvanish (v := v)
    (by rwa [fderiv_apply_eq_inner_gradient])
  simp only [Pi.mul_apply] at key
  rw [e2 z hz2, e3 z, hw, zero_smul, add_zero] at key
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply,
    fderiv_iteratedFDeriv_apply (k := 1) hz2, fderiv_iteratedFDeriv_apply (k := 2) hz3] at key
  have hc3 : ∀ a : E, iteratedFDeriv ℝ 3 F z (Fin.cons v ![a, w]) =
      iteratedFDeriv ℝ 3 F z (Fin.cons a ![v, w]) := fun a ↦
    iteratedFDeriv_cons_cons_comm (k := 1) hz3 v a ![w]
  have hc2 : ∀ a : E, iteratedFDeriv ℝ 2 F z (Fin.cons v ![a]) =
      iteratedFDeriv ℝ 2 F z (Fin.cons a ![v]) := fun a ↦
    iteratedFDeriv_cons_cons_comm (k := 0) hz2 v a ![]
  have h1 : ∑ A, iteratedFDeriv ℝ 1 F z ![e A] *
      iteratedFDeriv ℝ 3 F z (Fin.cons v ![e A, w]) = iteratedFDeriv ℝ 3 F z ![v, ∇ F z, w] := by
    have := sum_fderiv_mul_cons e F z (iteratedFDeriv ℝ 3 F z) ![v, w]
    calc _ = ∑ A, fderiv ℝ F z (e A) * iteratedFDeriv ℝ 3 F z (Fin.cons (e A) ![v, w]) :=
          Finset.sum_congr rfl fun A _ ↦ by rw [iteratedFDeriv_one_apply, hc3]; rfl
      _ = iteratedFDeriv ℝ 3 F z (Fin.cons (∇ F z) ![v, w]) := this
      _ = _ := (hc3 _).symm
  have h2 : ∑ A, ⟪e A, w⟫ * iteratedFDeriv ℝ 2 F z (Fin.cons v ![e A]) =
      iteratedFDeriv ℝ 2 F z ![v, w] := by
    have := sum_inner_mul_apply e w (consCLM (iteratedFDeriv ℝ 2 F z) ![v])
    simp only [consCLM_apply] at this
    calc _ = ∑ A, ⟪w, e A⟫ * iteratedFDeriv ℝ 2 F z (Fin.cons (e A) ![v]) :=
          Finset.sum_congr rfl fun A _ ↦ by rw [real_inner_comm, hc2]
      _ = iteratedFDeriv ℝ 2 F z (Fin.cons w ![v]) := this
      _ = _ := (hc2 _).symm
  have h3 : ∑ A, iteratedFDeriv ℝ 2 F z ![e A, w] * iteratedFDeriv ℝ 2 F z (Fin.cons v ![e A]) =
      ∑ A, iteratedFDeriv ℝ 2 F z ![v, e A] * iteratedFDeriv ℝ 2 F z ![e A, w] :=
    Finset.sum_congr rfl fun A _ ↦ mul_comm _ _
  rw [Finset.sum_add_distrib, h1, h3, h2] at key
  linarith

end Normal

end OnePhaseDimension

namespace OnePhaseDimension

/-! ### The normal-normal-normal component -/

section NNN

variable {n : ℕ}

/-- **`D³F[N, N, N] = |D²F|²`** at a regular boundary point where the jet facts hold: the trace
of `D³F[·, ·, N]` vanishes, and its tangential part is given by the odd normal component. -/
theorem iteratedFDeriv_three_normal_normal_normal {F : E n → ℝ} {U : Set (E n)} {z : E n}
    (hU : U ∈ 𝓝 z) (hF : ∀ y ∈ U, ContDiffAt ℝ 3 F y) (hz : F z = 0)
    (hgrad : ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1) (hJ : JetFacts F z) {κ : Type*} [Fintype κ]
    (e : OrthonormalBasis κ ℝ (E n)) :
    iteratedFDeriv ℝ 3 F z ![∇ F z, ∇ F z, ∇ F z] = jetNormSq e 2 F z := by
  have hN : ‖∇ F z‖ = 1 := hgrad z (mem_of_mem_nhds hU) hz
  have hz2 : ContDiffAt ℝ 2 F z := (hF z (mem_of_mem_nhds hU)).of_le (by norm_num)
  set N := ∇ F z with hN_def
  set f := adaptedBasis hN (inner_stdFrame hN) with hf_def
  set σ : Fin (n - 1) → E n := frameVec (stdFrame N hN)
  have hfN : f none = N := by simp [f]
  have hfσ : ∀ i, f (some i) = σ i := fun i ↦ by simp [f, σ]
  have hσN : ∀ i, ⟪N, σ i⟫ = 0 := fun i ↦ by
    rw [real_inner_comm]; exact inner_stdFrame hN _
  set Q := iteratedFDeriv ℝ 2 F z ![N, N]
  -- the normal Hessian vanishes on tangent vectors
  have ha : ∀ i, iteratedFDeriv ℝ 2 F z ![σ i, N] = 0 := fun i ↦
    iteratedFDeriv_two_gradient_eq_zero hU hz2 hz hgrad (hσN i)
  have ha' : ∀ i, iteratedFDeriv ℝ 2 F z ![N, σ i] = 0 := fun i ↦ by
    rw [hJ.D2_comm]; exact ha i
  -- traces
  have htr2 := hJ.sum_D2 f
  rw [Fintype.sum_option, hfN] at htr2
  simp only [hfσ] at htr2
  have htr3 := hJ.sum_D3 f N
  rw [Fintype.sum_option, hfN] at htr3
  simp only [hfσ] at htr3
  -- the odd component on tangent vectors
  have hb : ∀ i, iteratedFDeriv ℝ 3 F z ![σ i, σ i, N] =
      Q * iteratedFDeriv ℝ 2 F z ![σ i, σ i] -
        ∑ o, iteratedFDeriv ℝ 2 F z ![σ i, f o] ^ 2 := fun i ↦ by
    rw [hJ.D3_comm₂₃, iteratedFDeriv_three_normal f hU hF hz hgrad (hσN i) (hσN i)]
    congr 1
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    rw [hJ.D2_comm (f o), sq]
  -- the squared norm
  have hnorm : jetNormSq e 2 F z =
      Q ^ 2 + ∑ i, ∑ o, iteratedFDeriv ℝ 2 F z ![σ i, f o] ^ 2 := by
    rw [jetNormSq_eq e f, jetNormSq, multilinearNormSq_two, Fintype.sum_option, hfN]
    simp only [hfσ]
    rw [Fintype.sum_option, hfN]
    simp only [hfσ, ha', ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, add_zero]
    rfl
  simp_rw [hb, Finset.sum_sub_distrib, ← Finset.mul_sum] at htr3
  rw [hnorm]
  have htr2' : ∑ i, iteratedFDeriv ℝ 2 F z ![σ i, σ i] = -Q := by linarith
  rw [htr2'] at htr3
  nlinarith

end NNN

end OnePhaseDimension

namespace OnePhaseDimension

/-! ### Boundary jets in frame coordinates -/

section Frame

variable {n : ℕ}

/-- If `aᵀTp = 0` for every `a ⊥ p` and `|p| = 1`, then `Tp = (pᵀTp) p`. -/
theorem mulVec_eq_smul_of_orth {m : ℕ} (T : Fin m → Fin m → ℝ) (p : Fin m → ℝ)
    (hp : ∑ i, p i ^ 2 = 1)
    (hT : ∀ a : Fin m → ℝ, ∑ i, a i * p i = 0 → ∑ i, ∑ j, a i * p j * T i j = 0) (i : Fin m) :
    ∑ j, T i j * p j = (∑ j, ∑ k, p j * T j k * p k) * p i := by
  set t := ∑ j, ∑ k, p j * T j k * p k
  set q : Fin m → ℝ := fun i ↦ ∑ j, T i j * p j - t * p i with hq
  have hqi : ∀ i, q i = ∑ j, T i j * p j - t * p i := fun i ↦ rfl
  have hqp : ∑ i, q i * p i = 0 := by
    have : ∑ i, q i * p i = ∑ i, ∑ j, p i * T i j * p j - t * ∑ i, p i ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hqi, sub_mul, Finset.sum_mul]
      congr 1
      · exact Finset.sum_congr rfl fun j _ ↦ by ring
      · ring
    rw [this, hp, mul_one]
    exact sub_self _
  have h1 := hT q hqp
  have hqq : ∑ i, q i ^ 2 = 0 := by
    have : ∑ i, q i ^ 2 = ∑ i, ∑ j, q i * p j * T i j - t * ∑ i, q i * p i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [sq]
      nth_rewrite 2 [hqi]
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun j _ ↦ by ring
      · ring
    rw [this, h1, hqp]
    ring
  have hq0 : q i = 0 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ sq_nonneg (q j)).1 hqq i
      (Finset.mem_univ i)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  simp only [hq] at hq0
  linarith

end Frame

end OnePhaseDimension

namespace OnePhaseDimension.ConeJets

variable {n : ℕ}

/-- `J` is the jet record of a chart `F` at a regular free-boundary point: `F(x₀) = 0`, and near
`x₀`, `F` is `C³` and `|∇F| = 1` on `{F = 0}`. -/
structure IsBoundaryJet (F : E n → ℝ) (J : ConeJets n) : Prop where
  isConeJet : IsConeJet F J
  zero : F J.x₀ = 0
  nhds : ∃ U ∈ 𝓝 J.x₀, (∀ y ∈ U, ContDiffAt ℝ 3 F y) ∧ ∀ y ∈ U, F y = 0 → ‖∇ F y‖ = 1

/-- `T(p, p)`, the normal-normal entry of `T` (equal to `-H` at boundary points). -/
def Tpp (J : ConeJets n) : ℝ := ∑ i, ∑ j, J.p i * J.p j * J.T i j

namespace IsBoundaryJet

variable {F : E n → ℝ} {J : ConeJets n} (h : IsBoundaryJet F J)
include h

theorem g_eq_zero : J.g = 0 := h.isConeJet.g_eq.trans h.zero

/-- At a boundary point `∇F(x₀) = ∑ pᵢ τᵢ`: the normal is tangent to the sphere. -/
theorem gradient_eq : ∇ F J.x₀ = frameMap J.ι J.p := by
  rw [h.isConeJet.gradient_eq, h.g_eq_zero, zero_smul, zero_add]

theorem norm_gradient : ‖∇ F J.x₀‖ = 1 := by
  obtain ⟨U, hU, -, hg⟩ := h.nhds
  exact hg _ (mem_of_mem_nhds hU) h.zero

/-- `|p| = 1` at a boundary point. -/
theorem sum_p_sq : ∑ i, J.p i ^ 2 = 1 := by
  have := h.isConeJet.normSq_gradient_eq
  rw [h.norm_gradient, h.g_eq_zero] at this
  linarith

theorem inner_gradient_frameMap (a : Fin (n - 1) → ℝ) :
    ⟪∇ F J.x₀, frameMap J.ι a⟫ = ∑ i, a i * J.p i := by
  rw [h.gradient_eq, inner_frameMap_frameMap]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

/-- **`T_{Nα} = 0`**: `T p = T(p, p) p`, i.e. `T N = -H N` with `H = -T(N, N)`. -/
theorem T_mulVec_p (i : Fin (n - 1)) : ∑ j, J.T i j * J.p j = J.Tpp * J.p i := by
  obtain ⟨U, hU, hF, hg⟩ := h.nhds
  have hTpp : J.Tpp = ∑ j, ∑ k, J.p j * J.T j k * J.p k :=
    Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hTpp]
  refine mulVec_eq_smul_of_orth J.T J.p h.sum_p_sq (fun a ha ↦ ?_) i
  have hv : ⟪∇ F J.x₀, frameMap J.ι a⟫ = 0 := by rw [h.inner_gradient_frameMap, ha]
  have := iteratedFDeriv_two_gradient_eq_zero hU ((hF _ (mem_of_mem_nhds hU)).of_le
    (by norm_num)) h.zero hg hv
  rwa [h.gradient_eq, h.isConeJet.D2_frameMap] at this

/-- **Odd boundary jets, `B_{Nαβ} = T_{NN}T_{αβ} - (T²)_{αβ}`**: for `a, c ⊥ p`,
`B(p, a, c) = T(p, p) T(a, c) - (T²)(a, c)`. -/
theorem B_odd (a c : Fin (n - 1) → ℝ) (ha : ∑ i, a i * J.p i = 0)
    (hc : ∑ i, c i * J.p i = 0) :
    ∑ i, ∑ j, ∑ k, J.p i * a j * c k * J.B i j k =
      J.Tpp * (∑ i, ∑ k, a i * c k * J.T i k) -
        ∑ l, (∑ i, a i * J.T i l) * (∑ k, c k * J.T l k) := by
  obtain ⟨U, hU, hF, hg⟩ := h.nhds
  have hJ := h.isConeJet
  have hv : ⟪∇ F J.x₀, frameMap J.ι a⟫ = 0 := by rw [h.inner_gradient_frameMap, ha]
  have hw : ⟪∇ F J.x₀, frameMap J.ι c⟫ = 0 := by rw [h.inner_gradient_frameMap, hc]
  have key := iteratedFDeriv_three_normal hJ.basis hU hF h.zero hg hv hw
  rw [h.gradient_eq, hJ.D3_frameMap, hJ.D2_frameMap, hJ.D2_frameMap, Fintype.sum_option,
    IsConeJet.basis_none, hJ.facts.D2_self_right, zero_mul, zero_add] at key
  simp only [IsConeJet.basis_some, hJ.D2_frameMap_frameVec, hJ.D2_frameVec_frameMap] at key
  refine Eq.trans ?_ key
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦
    Finset.sum_congr rfl fun k _ ↦ ?_
  rw [hJ.B_symm₁₂]
  ring

/-- **`B_{NNN} = w²`**: `B(p, p, p) = |T|²`. -/
theorem B_NNN : ∑ i, ∑ j, ∑ k, J.p i * J.p j * J.p k * J.B i j k = ∑ i, ∑ j, J.T i j ^ 2 := by
  obtain ⟨U, hU, hF, hg⟩ := h.nhds
  have hJ := h.isConeJet
  have key := iteratedFDeriv_three_normal_normal_normal hU hF h.zero hg hJ.facts hJ.basis
  rwa [h.gradient_eq, hJ.D3_frameMap, hJ.jetNormSq_two_eq] at key

end IsBoundaryJet

end OnePhaseDimension.ConeJets

namespace OnePhaseDimension.ConeJets

variable {n : ℕ}

/-- **Boundary jet records from a chart.** If `u` is one-homogeneous, `u = max F 0` on an open
set `U ∋ x₀` with `F` smooth on `U`, harmonic on `{F > 0}`, `|∇F| = 1` on `{F = 0}`, and
`F(x₀) = 0` with `|x₀| = 1`, then the jet record of `F` at `x₀` (in any frame of `x₀^⊥`) is a
boundary jet record. -/
theorem isBoundaryJet_of_chart {u F : E n → ℝ} {U : Set (E n)} {x₀ : E n}
    {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hx : ‖x₀‖ = 1) (hι : ∀ v, ⟪ι v, x₀⟫ = 0) (hU : IsOpen U)
    (hx₀ : x₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U) (hF0 : F x₀ = 0) (hhom : IsOneHomogeneous u)
    (huF : ∀ x ∈ U, u x = max (F x) 0) (hΔ : ∀ x ∈ U, 0 < F x → Δ F x = 0)
    (hgrad : ∀ x ∈ U, F x = 0 → ‖∇ F x‖ = 1) : IsBoundaryJet F (ofFun F x₀ ι) := by
  have hDF : fderiv ℝ F x₀ ≠ 0 := by
    intro h0
    have h1 := hgrad x₀ hx₀ hF0
    rw [gradient, h0, map_zero, norm_zero] at h1
    norm_num at h1
  exact
    { isConeJet := isConeJet_ofFun hx hι
        (jetFacts_of_chart hU hx₀ hF hF0 hDF hhom huF hΔ)
      zero := hF0
      nhds := ⟨U, hU.mem_nhds hx₀, fun y hy ↦
        (hF.contDiffAt (hU.mem_nhds hy)).of_le (natCast_le_infty 3), hgrad⟩ }

end OnePhaseDimension.ConeJets
