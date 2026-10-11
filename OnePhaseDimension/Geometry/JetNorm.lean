/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.Euler
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Squared norms of jets and their Laplacians

For an orthonormal basis `(e_A)` of a finite-dimensional real inner product space and a
continuous multilinear form `M` of order `k`, `multilinearNormSq e M = ∑_I M(e_{I₁}, …, e_{I_k})²`
is the squared Hilbert–Schmidt norm of `M`. It does not depend on the basis
(`multilinearNormSq_eq`). For a function `u`, `jetNormSq e k u x` is this norm of `Dᵏu(x)`;
for `k = 1` it is `|∇u(x)|²`.

## Main results

* `laplacian_mul`: the product rule `Δ(φψ) = (Δφ)ψ + 2⟨∇φ, ∇ψ⟩ + φΔψ`.
* `laplacian_jetNormSq`: for `u` harmonic, `Δ|Dᵏu|² = 2|D^{k+1}u|²`.
* `laplacian_normSq_mul_jetNormSq_two`: for `u` harmonic and one-homogeneous,
  `Δ(r²|D²u|²) = (2n - 8)|D²u|² + 2r²|D³u|²`, where `n` is the dimension.
-/

open Function Filter Topology Set Laplacian
open scoped ContDiff RealInnerProductSpace Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-! ### Hilbert–Schmidt norms of multilinear forms -/

/-- The squared Hilbert–Schmidt norm `∑_I M(e_{I₁}, …, e_{I_k})²` of a multilinear form,
computed in the orthonormal basis `e`. -/
def multilinearNormSq (e : OrthonormalBasis ι ℝ E) {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ) : ℝ :=
  ∑ I : Fin k → ι, M (fun j ↦ e (I j)) ^ 2

omit [FiniteDimensional ℝ E] in
theorem multilinearNormSq_nonneg (e : OrthonormalBasis ι ℝ E) {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ) : 0 ≤ multilinearNormSq e M :=
  Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

omit [FiniteDimensional ℝ E] in
/-- Splitting off the first index. -/
theorem multilinearNormSq_succ (e : OrthonormalBasis ι ℝ E) {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ E) ℝ) :
    multilinearNormSq e M =
      ∑ a, ∑ J : Fin k → ι, M (Fin.cons (e a) fun j ↦ e (J j)) ^ 2 := by
  unfold multilinearNormSq
  rw [← (Fin.consEquiv fun _ ↦ ι).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun J _ ↦ ?_
  congr 2
  funext j
  refine Fin.cases ?_ (fun j ↦ ?_) j <;> rfl

omit [FiniteDimensional ℝ E] in
/-- Splitting a sum over `Fin (k + 1) → ι` along the first index. -/
theorem sum_fin_succ_pi {M : Type*} [AddCommMonoid M] {k : ℕ} (f : (Fin (k + 1) → ι) → M) :
    ∑ I, f I = ∑ a, ∑ J : Fin k → ι, f (Fin.cons a J) := by
  rw [← (Fin.consEquiv fun _ ↦ ι).sum_comp, Fintype.sum_prod_type]
  rfl

omit [FiniteDimensional ℝ E] in
theorem sum_fin_zero_pi {M : Type*} [AddCommMonoid M] (f : (Fin 0 → ι) → M) :
    ∑ I, f I = f ![] := by
  rw [Fintype.sum_unique]
  congr 1

omit [FiniteDimensional ℝ E] in
theorem multilinearNormSq_one (e : OrthonormalBasis ι ℝ E)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 1 ↦ E) ℝ) :
    multilinearNormSq e M = ∑ a, M ![e a] ^ 2 := by
  unfold multilinearNormSq
  simp_rw [sum_fin_succ_pi (k := 0), sum_fin_zero_pi]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 2
  funext j
  fin_cases j
  rfl

omit [FiniteDimensional ℝ E] in
/-- Linearity of a multilinear form in its first slot. -/
theorem cons_sum_smul_apply {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) ↦ E) ℝ)
    {κ : Type*} (s : Finset κ) (a : κ → ℝ) (x : κ → E) (v : Fin k → E) :
    M (Fin.cons (∑ i ∈ s, a i • x i) v) = ∑ i ∈ s, a i * M (Fin.cons (x i) v) := by
  simp_rw [← M.curryLeft_apply, map_sum, map_smul, sum_apply,
    smul_apply, smul_eq_mul]

omit [FiniteDimensional ℝ E] in
theorem multilinearNormSq_two (e : OrthonormalBasis ι ℝ E)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E) ℝ) :
    multilinearNormSq e M = ∑ a, ∑ b, M ![e a, e b] ^ 2 := by
  unfold multilinearNormSq
  simp_rw [sum_fin_succ_pi (k := 1), sum_fin_succ_pi (k := 0), sum_fin_zero_pi]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  congr 2
  funext j
  fin_cases j <;> rfl

omit [FiniteDimensional ℝ E] in
theorem multilinearNormSq_three (e : OrthonormalBasis ι ℝ E)
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin 3 ↦ E) ℝ) :
    multilinearNormSq e M = ∑ a, ∑ b, ∑ c, M ![e a, e b, e c] ^ 2 := by
  unfold multilinearNormSq
  simp_rw [sum_fin_succ_pi (k := 2), sum_fin_succ_pi (k := 1), sum_fin_succ_pi (k := 0),
    sum_fin_zero_pi]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
    Finset.sum_congr rfl fun c _ ↦ ?_
  congr 2
  funext j
  fin_cases j <;> rfl

/-- For a linear form `L`, `∑_A L(e_A)²` is the squared norm of its Riesz representative. -/
theorem sum_sq_apply_orthonormalBasis (e : OrthonormalBasis ι ℝ E) (L : E →L[ℝ] ℝ) :
    ∑ a, L (e a) ^ 2 = ‖(InnerProductSpace.toDual ℝ E).symm L‖ ^ 2 := by
  simp_rw [← InnerProductSpace.toDual_symm_apply (x := e _) (y := L)]
  exact e.sum_sq_inner_left _

/-- The Hilbert–Schmidt norm does not depend on the orthonormal basis. -/
theorem multilinearNormSq_eq (e : OrthonormalBasis ι ℝ E) (e' : OrthonormalBasis ι' ℝ E) :
    ∀ {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) ℝ),
      multilinearNormSq e M = multilinearNormSq e' M
  | 0, M => by
    unfold multilinearNormSq
    rw [Fintype.sum_unique, Fintype.sum_unique]
    congr 2
    funext j
    exact j.elim0
  | k + 1, M => by
    have hIH : ∀ a, ∑ J : Fin k → ι, M (Fin.cons (e a) fun j ↦ e (J j)) ^ 2 =
        ∑ J : Fin k → ι', M (Fin.cons (e a) fun j ↦ e' (J j)) ^ 2 := fun a ↦
      multilinearNormSq_eq e e' (M.curryLeft (e a))
    -- the linear forms `y ↦ M(y, e'_J)`
    let L : (Fin k → ι') → E →L[ℝ] ℝ := fun J ↦
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) ℝ (fun j ↦ e' (J j))).comp
        M.curryLeft
    have hL : ∀ J y, L J y = M (Fin.cons y fun j ↦ e' (J j)) := fun J y ↦ by
      simp [L, ContinuousMultilinearMap.curryLeft_apply]
    rw [multilinearNormSq_succ, multilinearNormSq_succ]
    simp_rw [hIH, ← hL]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun a J ↦ L J (e' a) ^ 2)]
    refine Finset.sum_congr rfl fun J _ ↦ ?_
    rw [sum_sq_apply_orthonormalBasis, sum_sq_apply_orthonormalBasis]

/-! ### Squared norms of jets -/

/-- `|Dᵏu(x)|²`, computed in the orthonormal basis `e` (it does not depend on `e`). -/
def jetNormSq (e : OrthonormalBasis ι ℝ E) (k : ℕ) (u : E → ℝ) (x : E) : ℝ :=
  multilinearNormSq e (iteratedFDeriv ℝ k u x)

theorem jetNormSq_eq (e : OrthonormalBasis ι ℝ E) (e' : OrthonormalBasis ι' ℝ E) (k : ℕ)
    (u : E → ℝ) : jetNormSq e k u = jetNormSq e' k u :=
  funext fun _ ↦ multilinearNormSq_eq e e' _

omit [FiniteDimensional ℝ E] in
theorem jetNormSq_nonneg (e : OrthonormalBasis ι ℝ E) (k : ℕ) (u : E → ℝ) (x : E) :
    0 ≤ jetNormSq e k u x :=
  multilinearNormSq_nonneg e _

/-- `|D¹u|² = |∇u|²`. -/
theorem jetNormSq_one (e : OrthonormalBasis ι ℝ E) (u : E → ℝ) (x : E) :
    jetNormSq e 1 u x = ‖∇ u x‖ ^ 2 := by
  rw [jetNormSq, multilinearNormSq_succ, gradient, ← sum_sq_apply_orthonormalBasis e]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Fintype.sum_unique, iteratedFDeriv_one_apply]
  rfl

/-! ### Second derivatives and the Laplacian -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {x : E}

omit [FiniteDimensional ℝ E] in
/-- `D²f(x)[a, b]` as an iterated directional derivative. -/
theorem iteratedFDeriv_two_apply_eq_fderiv {f : E → F}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) (a b : E) :
    iteratedFDeriv ℝ 2 f x ![a, b] = fderiv ℝ (fun y ↦ fderiv ℝ f y b) x a := by
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hf (differentiableAt_const b)]
  simp

/-- The Laplacian as a sum of second directional derivatives. -/
theorem laplacian_eq_sum_fderiv (e : OrthonormalBasis ι ℝ E) {f : E → F}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    Δ f x = ∑ a, fderiv ℝ (fun y ↦ fderiv ℝ f y (e a)) x (e a) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f e]
  exact Finset.sum_congr rfl fun a _ ↦ iteratedFDeriv_two_apply_eq_fderiv hf _ _

omit [FiniteDimensional ℝ E] in
/-- The second derivative of `y ↦ Dᵏf(y)[w]` is `D^{k+2}f` with `w` in the last slots. -/
theorem iteratedFDeriv_two_iteratedFDeriv_apply {f : E → F} {k : ℕ}
    (hf : ContDiffAt ℝ (k + 2 : ℕ) f x) (w : Fin k → E) (a b : E) :
    iteratedFDeriv ℝ 2 (fun y ↦ iteratedFDeriv ℝ k f y w) x ![a, b] =
      iteratedFDeriv ℝ (k + 2) f x (Fin.cons a (Fin.cons b w)) := by
  have hφ : ContDiffAt ℝ 2 (fun y ↦ iteratedFDeriv ℝ k f y w) x :=
    contDiffAt_iteratedFDeriv_apply (m := 2) hf w
  rw [iteratedFDeriv_two_apply_eq_fderiv
      ((hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero),
    iteratedFDeriv_succ_apply_cons_of_contDiffAt (k := k + 1) hf]
  have hev : (fun y ↦ iteratedFDeriv ℝ (k + 1) f y (Fin.cons b w)) =ᶠ[𝓝 x]
      fun y ↦ fderiv ℝ (fun z ↦ iteratedFDeriv ℝ k f z w) y b := by
    filter_upwards [hf.eventually (natCast_ne_infty _)] with y hy
    exact iteratedFDeriv_succ_apply_cons_of_contDiffAt (hy.of_le (by norm_cast; omega)) b w
  rw [hev.fderiv_eq]

/-- **Product rule for the Laplacian.** -/
theorem laplacian_mul (e : OrthonormalBasis ι ℝ E) {φ ψ : E → ℝ} (hφ : ContDiffAt ℝ 2 φ x)
    (hψ : ContDiffAt ℝ 2 ψ x) :
    Δ (fun y ↦ φ y * ψ y) x =
      Δ φ x * ψ x + 2 * ∑ a, fderiv ℝ φ x (e a) * fderiv ℝ ψ x (e a) + φ x * Δ ψ x := by
  have hd2 : ∀ {g : E → ℝ}, ContDiffAt ℝ 2 g x → DifferentiableAt ℝ (fderiv ℝ g) x :=
    fun hg ↦ (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdd : ∀ {g : E → ℝ}, ContDiffAt ℝ 2 g x → ∀ a : E,
      HasFDerivAt (fun y ↦ fderiv ℝ g y a) (fderiv ℝ (fun y ↦ fderiv ℝ g y a) x) x :=
    fun hg a ↦ ((hd2 hg).clm_apply (differentiableAt_const a)).hasFDerivAt
  have hprod : ContDiffAt ℝ 2 (fun y ↦ φ y * ψ y) x := hφ.mul hψ
  rw [laplacian_eq_sum_fderiv e (hd2 hprod), laplacian_eq_sum_fderiv e (hd2 hφ),
    laplacian_eq_sum_fderiv e (hd2 hψ), Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  have hev : (fun y ↦ fderiv ℝ (fun y ↦ φ y * ψ y) y (e a)) =ᶠ[𝓝 x]
      fun y ↦ φ y * fderiv ℝ ψ y (e a) + ψ y * fderiv ℝ φ y (e a) := by
    filter_upwards [hφ.eventually (natCast_ne_infty 2), hψ.eventually (natCast_ne_infty 2)]
      with y hφy hψy
    rw [fderiv_fun_mul (hφy.differentiableAt two_ne_zero) (hψy.differentiableAt two_ne_zero)]
    simp
  have hφ1 : HasFDerivAt φ (fderiv ℝ φ x) x := (hφ.differentiableAt two_ne_zero).hasFDerivAt
  have hψ1 : HasFDerivAt ψ (fderiv ℝ ψ x) x := (hψ.differentiableAt two_ne_zero).hasFDerivAt
  have H : HasFDerivAt (fun y ↦ φ y * fderiv ℝ ψ y (e a) + ψ y * fderiv ℝ φ y (e a)) _ x :=
    (hφ1.mul (hdd hψ (e a))).add (hψ1.mul (hdd hφ (e a)))
  rw [hev.fderiv_eq, H.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The Laplacian of a finite sum. -/
theorem laplacian_finsetSum {κ : Type*} (s : Finset κ) {f : κ → E → F}
    (hf : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x) :
    Δ (fun y ↦ ∑ i ∈ s, f i y) x = ∑ i ∈ s, Δ (f i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (stdOrthonormalBasis ℝ E)]
    simp
  | insert j s hj ih =>
    have hs : ∀ i ∈ s, ContDiffAt ℝ 2 (f i) x := fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    have hsum : ContDiffAt ℝ 2 (fun y ↦ ∑ i ∈ s, f i y) x := ContDiffAt.sum fun i hi ↦ hs i hi
    have : (fun y ↦ ∑ i ∈ insert j s, f i y) = f j + fun y ↦ ∑ i ∈ s, f i y := by
      funext y
      simp [Finset.sum_insert hj]
    rw [this, (hf j (Finset.mem_insert_self j s)).laplacian_add hsum, ih hs,
      Finset.sum_insert hj]

/-- `Δ|y|² = 2n`. -/
theorem laplacian_normSq (x : E) :
    Δ (fun y : E ↦ ‖y‖ ^ 2) x = 2 * Module.finrank ℝ E := by
  have hfd : ∀ y : E, fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2) y = 2 • innerSL ℝ y := fun y ↦
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.fderiv
  have hd : DifferentiableAt ℝ (fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2)) x := by
    rw [show fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2) = fun y ↦ 2 • innerSL ℝ y from funext hfd]
    exact (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).differentiableAt.const_smul (2 : ℕ)
  set e := stdOrthonormalBasis ℝ E
  rw [laplacian_eq_sum_fderiv e hd]
  have : ∀ a, fderiv ℝ (fun y ↦ fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2) y (e a)) x (e a) = 2 := by
    intro a
    have h2 : (fun y ↦ fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2) y (e a)) =
        fun y ↦ (2 • innerSL ℝ (e a)) y := by
      funext y
      rw [hfd]
      simp [real_inner_comm]
    rw [h2, ContinuousLinearMap.fderiv]
    simp [e.orthonormal.1 a]
  simp_rw [this]
  simp [mul_comm]

/-! ### Laplacians of squared jet norms -/

omit [FiniteDimensional ℝ E] in
/-- The derivative of `|Dᵏu|²`. -/
theorem fderiv_jetNormSq_apply (e : OrthonormalBasis ι ℝ E) {k : ℕ} {u : E → ℝ}
    (hu : ContDiffAt ℝ (k + 1 : ℕ) u x) (a : E) :
    fderiv ℝ (jetNormSq e k u) x a = 2 * ∑ I : Fin k → ι,
      iteratedFDeriv ℝ k u x (fun j ↦ e (I j)) *
        iteratedFDeriv ℝ (k + 1) u x (Fin.cons a fun j ↦ e (I j)) := by
  have hdI : ∀ I : Fin k → ι, HasFDerivAt (fun y ↦ iteratedFDeriv ℝ k u y (fun j ↦ e (I j)))
      (fderiv ℝ (fun y ↦ iteratedFDeriv ℝ k u y (fun j ↦ e (I j))) x) x := fun I ↦
    ((contDiffAt_iteratedFDeriv_apply (m := 1) hu _).differentiableAt one_ne_zero).hasFDerivAt
  have H := HasFDerivAt.fun_sum (u := Finset.univ) fun I _ ↦ (hdI I).pow 2
  have hfun : jetNormSq e k u =
      fun y ↦ ∑ I : Fin k → ι, iteratedFDeriv ℝ k u y (fun j ↦ e (I j)) ^ 2 := rfl
  rw [hfun, H.fderiv, Finset.mul_sum]
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  rw [iteratedFDeriv_succ_apply_cons_of_contDiffAt hu]
  simp
  ring

omit [FiniteDimensional ℝ E] in
/-- The derivative of `|∇u|²` in basis form. -/
theorem fderiv_jetNormSq_one_apply (e : OrthonormalBasis ι ℝ E) {u : E → ℝ}
    (hu : ContDiffAt ℝ 2 u x) (a : E) :
    fderiv ℝ (jetNormSq e 1 u) x a =
      2 * ∑ o, iteratedFDeriv ℝ 1 u x ![e o] * iteratedFDeriv ℝ 2 u x ![a, e o] := by
  rw [fderiv_jetNormSq_apply e (k := 1) (by exact_mod_cast hu), sum_fin_succ_pi]
  simp only [sum_fin_zero_pi]
  congr 1
  refine Finset.sum_congr rfl fun o _ ↦ ?_
  congr 2 <;> · funext j; fin_cases j <;> rfl

omit [FiniteDimensional ℝ E] in
/-- The derivative of `|D²u|²` in basis form. -/
theorem fderiv_jetNormSq_two_apply (e : OrthonormalBasis ι ℝ E) {u : E → ℝ}
    (hu : ContDiffAt ℝ 3 u x) (c : E) :
    fderiv ℝ (jetNormSq e 2 u) x c =
      2 * ∑ a, ∑ b, iteratedFDeriv ℝ 2 u x ![e a, e b] * iteratedFDeriv ℝ 3 u x ![c, e a, e b] := by
  rw [fderiv_jetNormSq_apply e (k := 2) (by exact_mod_cast hu)]
  simp_rw [sum_fin_succ_pi (k := 1), sum_fin_succ_pi (k := 0), sum_fin_zero_pi]
  congr 1
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  congr 2 <;> · funext j; fin_cases j <;> rfl

/-- **Bochner identity for harmonic jets.** If `u` is harmonic and `C^{k+2}` near `x`, then
`Δ|Dᵏu|²(x) = 2|D^{k+1}u(x)|²`. -/
theorem laplacian_jetNormSq (e : OrthonormalBasis ι ℝ E) {k : ℕ} {u : E → ℝ}
    (hu : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (k + 2 : ℕ) u y) (hΔ : ∀ᶠ y in 𝓝 x, Δ u y = 0) :
    Δ (jetNormSq e k u) x = 2 * jetNormSq e (k + 1) u x := by
  have hx : ContDiffAt ℝ (k + 2 : ℕ) u x := hu.self_of_nhds
  set φ : (Fin k → ι) → E → ℝ := fun I y ↦ iteratedFDeriv ℝ k u y (fun j ↦ e (I j))
  have hφ2 : ∀ I, ContDiffAt ℝ 2 (φ I) x := fun I ↦
    contDiffAt_iteratedFDeriv_apply (m := 2) hx _
  have hfun : jetNormSq e k u = fun y ↦ ∑ I, φ I y * φ I y := by
    funext y
    simp only [jetNormSq, multilinearNormSq, φ, sq]
  have hΔφ : ∀ I, Δ (φ I) x = 0 := by
    intro I
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ e]
    simp only [φ]
    simp_rw [iteratedFDeriv_two_iteratedFDeriv_apply hx]
    exact sum_iteratedFDeriv_cons_cons_eq_zero e hu hΔ _
  have hdφ : ∀ I a, fderiv ℝ (φ I) x (e a) =
      iteratedFDeriv ℝ (k + 1) u x (Fin.cons (e a) fun j ↦ e (I j)) := fun I a ↦
    (iteratedFDeriv_succ_apply_cons_of_contDiffAt (hx.of_le (by norm_cast; omega)) _ _).symm
  rw [hfun, laplacian_finsetSum _ fun I _ ↦ (hφ2 I).mul (hφ2 I)]
  simp_rw [laplacian_mul e (hφ2 _) (hφ2 _), hΔφ, hdφ]
  rw [jetNormSq, multilinearNormSq_succ, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  simp [sq]

omit [FiniteDimensional ℝ E] in
/-- If `u` is one-homogeneous, then `D_x|Dᵏu|²(x) = 2(1 - k)|Dᵏu(x)|²`. -/
theorem fderiv_jetNormSq_apply_self (e : OrthonormalBasis ι ℝ E) {k : ℕ} {u : E → ℝ}
    (hhom : IsOneHomogeneous u) (hu : ContDiffAt ℝ (k + 1 : ℕ) u x) :
    fderiv ℝ (jetNormSq e k u) x x = 2 * (1 - k) * jetNormSq e k u x := by
  rw [fderiv_jetNormSq_apply e hu, jetNormSq, multilinearNormSq, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ ↦ ?_
  rw [hhom.iteratedFDeriv_succ_apply_cons_self hu, smul_eq_mul]
  ring

/-- `Δ(|y|² h)(x) = 2n h(x) + 4 Dh(x)[x] + |x|² Δh(x)`. -/
theorem laplacian_normSq_mul {h : E → ℝ} (hh : ContDiffAt ℝ 2 h x) :
    Δ (fun y ↦ ‖y‖ ^ 2 * h y) x =
      2 * Module.finrank ℝ E * h x + 4 * fderiv ℝ h x x + ‖x‖ ^ 2 * Δ h x := by
  set e := stdOrthonormalBasis ℝ E
  have hn : ContDiffAt ℝ 2 (fun y : E ↦ ‖y‖ ^ 2) x := by
    exact (contDiff_norm_sq ℝ).contDiffAt
  rw [laplacian_mul e hn hh, laplacian_normSq]
  have : ∑ a, fderiv ℝ (fun y : E ↦ ‖y‖ ^ 2) x (e a) * fderiv ℝ h x (e a) =
      2 * fderiv ℝ h x x := by
    simp_rw [(hasStrictFDerivAt_norm_sq x).hasFDerivAt.fderiv]
    simp only [smul_apply, innerSL_apply_apply, nsmul_eq_mul,
      Nat.cast_ofNat, mul_assoc, ← Finset.mul_sum]
    congr 1
    have hx : fderiv ℝ h x x = fderiv ℝ h x (∑ i, ⟪e i, x⟫ • e i) := by rw [e.sum_repr']
    rw [hx, map_sum]
    simp [real_inner_comm]
  rw [this]
  ring

/-- **Euclidean Bochner identity for `r²|D²u|²`.** If `u` is harmonic and one-homogeneous and
`C⁴` near `x`, then
`Δ(r²|D²u|²)(x) = (2n - 8)|D²u(x)|² + 2|x|²|D³u(x)|²`. -/
theorem laplacian_normSq_mul_jetNormSq_two (e : OrthonormalBasis ι ℝ E) {u : E → ℝ}
    (hhom : IsOneHomogeneous u) (hu : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ 4 u y)
    (hΔ : ∀ᶠ y in 𝓝 x, Δ u y = 0) :
    Δ (fun y ↦ ‖y‖ ^ 2 * jetNormSq e 2 u y) x =
      (2 * Module.finrank ℝ E - 8) * jetNormSq e 2 u x + 2 * ‖x‖ ^ 2 * jetNormSq e 3 u x := by
  have hx : ContDiffAt ℝ 4 u x := hu.self_of_nhds
  have hh : ContDiffAt ℝ 2 (jetNormSq e 2 u) x := by
    have : jetNormSq e 2 u =
        fun y ↦ ∑ I : Fin 2 → ι, iteratedFDeriv ℝ 2 u y (fun j ↦ e (I j)) ^ 2 := rfl
    rw [this]
    exact ContDiffAt.sum fun I _ ↦ (contDiffAt_iteratedFDeriv_apply (k := 2) (m := 2)
      (by exact_mod_cast hx) _).pow 2
  rw [laplacian_normSq_mul hh, laplacian_jetNormSq e (k := 2) (by exact_mod_cast hu) hΔ,
    fderiv_jetNormSq_apply_self e hhom (k := 2) (hx.of_le (by norm_num))]
  push_cast
  ring

end OnePhaseDimension
