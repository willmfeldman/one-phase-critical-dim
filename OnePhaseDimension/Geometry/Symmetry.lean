/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Symmetry of higher derivatives and traces of harmonic jets

Mathlib proves that the second derivative of a `C²` function is symmetric, and that all iterated
derivatives of an analytic function are symmetric. We prove the symmetry of the `k`-th iterated
Fréchet derivative of a real `Cᵏ` function for every `k`, by induction on `k`: the adjacent
transpositions generate the symmetric group, the transposition of the first two slots is the
symmetry of the second derivative of `y ↦ Dᵏ⁻²f(y)[v]`, and the other adjacent transpositions
come from the inductive hypothesis at nearby points.

We also record the commutation of the Laplacian with derivatives in the form used for harmonic
functions: if `Δf = 0` near `x`, then for every orthonormal basis `(eᵢ)` and every `v`,
`∑ᵢ D^{k+2}f(x)[eᵢ, eᵢ, v₁, …, v_k] = 0`.

## Main results

* `iteratedFDeriv_succ_apply_cons`: `D^{k+1}f(x)[a, v] = D(y ↦ Dᵏf(y)[v])(x)[a]`.
* `iteratedFDeriv_comp_perm_of_contDiffAt`: `Dᵏf(x)[v ∘ σ] = Dᵏf(x)[v]` for `f` of class `Cᵏ`
  at `x`; the cases `k = 3, 4` are `iteratedFDeriv_three_perm`, `iteratedFDeriv_four_perm`.
* `sum_iteratedFDeriv_cons_cons_eq_zero`: the traces of the derivatives of a harmonic function
  vanish (the Laplacian commutes with derivatives).
-/

open Function Equiv Filter Topology Set Laplacian
open scoped ContDiff

@[expose] public section

namespace OnePhaseDimension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : E → F} {x : E}

/-! ### Peeling off the first slot -/

/-- A natural number is a finite smoothness exponent. -/
theorem natCast_ne_infty (k : ℕ) : ((k : ℕ) : ℕ∞ω) ≠ ∞ := by
  exact_mod_cast ENat.natCast_ne_top k

/-- The `(k+1)`-st derivative with first argument `a` is the derivative in the direction `a` of
the `k`-th derivative applied to the remaining arguments. -/
theorem iteratedFDeriv_succ_apply_cons {k : ℕ}
    (hf : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x) (a : E) (v : Fin k → E) :
    iteratedFDeriv ℝ (k + 1) f x (Fin.cons a v) =
      fderiv ℝ (fun y ↦ iteratedFDeriv ℝ k f y v) x a := by
  rw [hf.iteratedFDeriv_succ_apply_left']
  simp

/-- Version of `iteratedFDeriv_succ_apply_cons` under a `C^{k+1}` hypothesis. -/
theorem iteratedFDeriv_succ_apply_cons_of_contDiffAt {k : ℕ}
    (hf : ContDiffAt ℝ (k + 1 : ℕ) f x) (a : E) (v : Fin k → E) :
    iteratedFDeriv ℝ (k + 1) f x (Fin.cons a v) =
      fderiv ℝ (fun y ↦ iteratedFDeriv ℝ k f y v) x a :=
  iteratedFDeriv_succ_apply_cons
    (hf.differentiableAt_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self k)) a v

/-- If `f` is `C^{k+m}` at `x`, then `y ↦ Dᵏf(y)[v]` is `Cᵐ` at `x`. -/
theorem contDiffAt_iteratedFDeriv_apply {k m : ℕ} (hf : ContDiffAt ℝ (k + m : ℕ) f x)
    (v : Fin k → E) : ContDiffAt ℝ m (fun y ↦ iteratedFDeriv ℝ k f y v) x :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ E) F v).contDiff.contDiffAt.comp x
    (hf.iteratedFDeriv_right (by push_cast; rw [add_comm]))

/-! ### Symmetry -/

/-- The first two slots of `D^{k+2}f(x)` commute when `f` is `C^{k+2}` at `x`. -/
theorem iteratedFDeriv_cons_cons_comm {k : ℕ} (hf : ContDiffAt ℝ (k + 2 : ℕ) f x) (a b : E)
    (v : Fin k → E) :
    iteratedFDeriv ℝ (k + 2) f x (Fin.cons a (Fin.cons b v)) =
      iteratedFDeriv ℝ (k + 2) f x (Fin.cons b (Fin.cons a v)) := by
  set h : E → F := fun y ↦ iteratedFDeriv ℝ k f y v with hh_def
  have hh : ContDiffAt ℝ 2 h x := contDiffAt_iteratedFDeriv_apply (m := 2) hf v
  have hev : ∀ᶠ y in 𝓝 x, ∀ c,
      iteratedFDeriv ℝ (k + 1) f y (Fin.cons c v) = fderiv ℝ h y c := by
    filter_upwards [hf.eventually (natCast_ne_infty _)] with y hy c
    exact iteratedFDeriv_succ_apply_cons_of_contDiffAt (hy.of_le (by norm_cast; omega)) c v
  have hdiff : DifferentiableAt ℝ (fderiv ℝ h) x :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have key : ∀ c d, iteratedFDeriv ℝ (k + 2) f x (Fin.cons c (Fin.cons d v)) =
      fderiv ℝ (fderiv ℝ h) x c d := by
    intro c d
    rw [iteratedFDeriv_succ_apply_cons_of_contDiffAt (k := k + 1) hf c]
    have hd : (fun y ↦ iteratedFDeriv ℝ (k + 1) f y (Fin.cons d v)) =ᶠ[𝓝 x]
        fun y ↦ fderiv ℝ h y d := hev.mono fun y hy ↦ hy d
    rw [hd.fderiv_eq, fderiv_clm_apply hdiff (differentiableAt_const d)]
    simp
  rw [key, key, (hh.isSymmSndFDerivAt (by simp)).eq]

/-- If `Dᵏf(y)` is invariant under `σ` for all `y` near `x`, then `D^{k+1}f(x)` is invariant
under `σ` acting on the last `k` slots. -/
theorem iteratedFDeriv_cons_comp_perm {k : ℕ} (hf : ContDiffAt ℝ (k + 1 : ℕ) f x)
    (σ : Perm (Fin k))
    (hσ : ∀ᶠ y in 𝓝 x, ∀ v : Fin k → E,
      iteratedFDeriv ℝ k f y (v ∘ σ) = iteratedFDeriv ℝ k f y v)
    (a : E) (v : Fin k → E) :
    iteratedFDeriv ℝ (k + 1) f x (Fin.cons a (v ∘ σ)) =
      iteratedFDeriv ℝ (k + 1) f x (Fin.cons a v) := by
  rw [iteratedFDeriv_succ_apply_cons_of_contDiffAt hf,
    iteratedFDeriv_succ_apply_cons_of_contDiffAt hf]
  have hv : (fun y ↦ iteratedFDeriv ℝ k f y (v ∘ σ)) =ᶠ[𝓝 x]
      fun y ↦ iteratedFDeriv ℝ k f y v := hσ.mono fun y hy ↦ hy v
  rw [hv.fderiv_eq]

/-- **Symmetry of iterated derivatives.** If `f` is `Cᵏ` at `x`, then `Dᵏf(x)` is a symmetric
multilinear map. -/
theorem iteratedFDeriv_comp_perm_of_contDiffAt {k : ℕ} (hf : ContDiffAt ℝ k f x)
    (σ : Perm (Fin k)) (v : Fin k → E) :
    iteratedFDeriv ℝ k f x (v ∘ σ) = iteratedFDeriv ℝ k f x v := by
  induction k generalizing x with
  | zero => congr 1; exact Subsingleton.elim _ _
  | succ k ih =>
    let S : Submonoid (Perm (Fin (k + 1))) :=
      { carrier := {σ | ∀ v : Fin (k + 1) → E,
          iteratedFDeriv ℝ (k + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (k + 1) f x v}
        one_mem' := fun v ↦ rfl
        mul_mem' := by
          intro σ τ hσ hτ v
          rw [Perm.coe_mul, ← Function.comp_assoc, hτ, hσ] }
    have hle : Submonoid.closure (Set.range fun i : Fin k ↦ swap i.castSucc i.succ) ≤ S := by
      rw [Submonoid.closure_le]
      rintro _ ⟨i, rfl⟩ w
      cases k with
      | zero => exact i.elim0
      | succ j =>
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · have hw : w ∘ swap (Fin.castSucc (0 : Fin (j + 1))) (Fin.succ 0) =
              Fin.cons (w 1) (Fin.cons (w 0) fun l ↦ w l.succ.succ) := by
            funext l
            refine Fin.cases ?_ (fun l ↦ Fin.cases ?_ (fun l ↦ ?_) l) l
            · simp
            · simp
            · simp only [comp_apply, Fin.cons_succ]
              exact congrArg w (swap_apply_of_ne_of_ne (by simp [Fin.ext_iff])
                (by simp [Fin.ext_iff]))
          have hw' : w = Fin.cons (w 0) (Fin.cons (w 1) fun l ↦ w l.succ.succ) := by
            funext l
            refine Fin.cases ?_ (fun l ↦ Fin.cases ?_ (fun l ↦ ?_) l) l <;> simp
          change iteratedFDeriv ℝ (j + 2) f x _ = iteratedFDeriv ℝ (j + 2) f x _
          rw [hw]
          conv_rhs => rw [hw']
          exact iteratedFDeriv_cons_cons_comm hf _ _ _
        · have hw : w ∘ swap (Fin.castSucc i.succ) i.succ.succ =
              Fin.cons (w 0) (Fin.tail w ∘ swap i.castSucc i.succ) := by
            funext l
            refine Fin.cases ?_ (fun l ↦ ?_) l
            · simp only [comp_apply, Fin.cons_zero]
              exact congrArg w (swap_apply_of_ne_of_ne (by simp [Fin.ext_iff])
                (by simp [Fin.ext_iff]))
            · simp only [comp_apply, Fin.cons_succ, Fin.tail]
              rw [← Fin.succ_castSucc, (Fin.succ_injective _).swap_apply]
          have hσ : ∀ᶠ y in 𝓝 x, ∀ v : Fin (j + 1) → E,
              iteratedFDeriv ℝ (j + 1) f y (v ∘ swap i.castSucc i.succ) =
                iteratedFDeriv ℝ (j + 1) f y v := by
            filter_upwards [hf.eventually (natCast_ne_infty _)] with y hy v
            exact ih (hy.of_le (by norm_cast; omega)) _ v
          change iteratedFDeriv ℝ (j + 1 + 1) f x _ = iteratedFDeriv ℝ (j + 1 + 1) f x _
          rw [hw, iteratedFDeriv_cons_comp_perm hf _ hσ, Fin.cons_self_tail]
    have hσ : σ ∈ S := hle (by rw [Perm.mclosure_swap_castSucc_succ]; exact Submonoid.mem_top σ)
    exact hσ v

/-- Symmetry of the third derivative of a `C³` function. -/
theorem iteratedFDeriv_three_perm (hf : ContDiffAt ℝ 3 f x) (σ : Perm (Fin 3))
    (v : Fin 3 → E) : iteratedFDeriv ℝ 3 f x (v ∘ σ) = iteratedFDeriv ℝ 3 f x v :=
  iteratedFDeriv_comp_perm_of_contDiffAt (k := 3) (by exact_mod_cast hf) σ v

/-- Symmetry of the fourth derivative of a `C⁴` function. -/
theorem iteratedFDeriv_four_perm (hf : ContDiffAt ℝ 4 f x) (σ : Perm (Fin 4))
    (v : Fin 4 → E) : iteratedFDeriv ℝ 4 f x (v ∘ σ) = iteratedFDeriv ℝ 4 f x v :=
  iteratedFDeriv_comp_perm_of_contDiffAt (k := 4) (by exact_mod_cast hf) σ v

/-- Slots two and three of `D^{k+3}f(x)` commute when `f` is `C^{k+3}` at `x`. -/
theorem iteratedFDeriv_cons_cons_cons_comm {k : ℕ} (hf : ContDiffAt ℝ (k + 3 : ℕ) f x)
    (a b c : E) (v : Fin k → E) :
    iteratedFDeriv ℝ (k + 3) f x (Fin.cons a (Fin.cons b (Fin.cons c v))) =
      iteratedFDeriv ℝ (k + 3) f x (Fin.cons a (Fin.cons c (Fin.cons b v))) := by
  rw [iteratedFDeriv_succ_apply_cons_of_contDiffAt (k := k + 2) hf,
    iteratedFDeriv_succ_apply_cons_of_contDiffAt (k := k + 2) hf]
  have hv : (fun y ↦ iteratedFDeriv ℝ (k + 2) f y (Fin.cons b (Fin.cons c v))) =ᶠ[𝓝 x]
      fun y ↦ iteratedFDeriv ℝ (k + 2) f y (Fin.cons c (Fin.cons b v)) := by
    filter_upwards [hf.eventually (natCast_ne_infty _)] with y hy
    exact iteratedFDeriv_cons_cons_comm (hy.of_le (by norm_cast; omega)) b c v
  rw [hv.fderiv_eq]

/-! ### The Laplacian commutes with derivatives -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → F} {x : E}

/-- **Traces of harmonic jets.** If `f` is `C^{k+2}` and harmonic near `x`, then for every
orthonormal basis `(eᵢ)` and all `v`, `∑ᵢ D^{k+2}f(x)[eᵢ, eᵢ, v] = 0`. This is the statement
`Dᵏ(Δf) = 0` with the trace taken in the first two slots. -/
theorem sum_iteratedFDeriv_cons_cons_eq_zero {ι : Type*} [Fintype ι]
    (e : OrthonormalBasis ι ℝ E) {k : ℕ} (hf : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ (k + 2 : ℕ) f y)
    (hΔ : ∀ᶠ y in 𝓝 x, Δ f y = 0) (v : Fin k → E) :
    ∑ i, iteratedFDeriv ℝ (k + 2) f x (Fin.cons (e i) (Fin.cons (e i) v)) = 0 := by
  induction k generalizing x with
  | zero =>
    have h := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f e) x
    rw [hΔ.self_of_nhds] at h
    rw [h]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 1
    funext l
    refine Fin.cases ?_ (fun l ↦ Fin.cases ?_ (fun l ↦ l.elim0) l) l <;> rfl
  | succ k ih =>
    have hx : ContDiffAt ℝ (k + 3 : ℕ) f x := hf.self_of_nhds
    have hev : (fun y ↦ ∑ i, iteratedFDeriv ℝ (k + 2) f y
        (Fin.cons (e i) (Fin.cons (e i) (Fin.tail v)))) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [hf.eventually_nhds, hΔ.eventually_nhds] with y hy hy'
      exact ih (hy.mono fun z hz ↦ hz.of_le (by norm_cast; omega)) hy' _
    have hmove : ∀ i, iteratedFDeriv ℝ (k + 1 + 2) f x (Fin.cons (e i) (Fin.cons (e i) v)) =
        fderiv ℝ (fun y ↦ iteratedFDeriv ℝ (k + 2) f y
          (Fin.cons (e i) (Fin.cons (e i) (Fin.tail v)))) x (v 0) := by
      intro i
      rw [← Fin.cons_self_tail v]
      change iteratedFDeriv ℝ (k + 3) f x _ = _
      rw [iteratedFDeriv_cons_cons_cons_comm hx, iteratedFDeriv_cons_cons_comm (k := k + 1) hx,
        iteratedFDeriv_succ_apply_cons_of_contDiffAt (k := k + 2) hx]
      simp
    simp_rw [hmove]
    have hd : ∀ i ∈ (Finset.univ : Finset ι), DifferentiableAt ℝ (fun y ↦
        iteratedFDeriv ℝ (k + 2) f y (Fin.cons (e i) (Fin.cons (e i) (Fin.tail v)))) x :=
      fun i _ ↦ (contDiffAt_iteratedFDeriv_apply (m := 1) hx _).differentiableAt one_ne_zero
    rw [← sum_apply, ← fderiv_fun_sum hd, hev.fderiv_eq]
    simp

end OnePhaseDimension
