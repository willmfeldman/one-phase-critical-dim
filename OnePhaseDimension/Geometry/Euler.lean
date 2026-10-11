/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.Symmetry

/-!
# Euler relations for one-homogeneous functions

If `u(r x) = r u(x)` for all `r > 0`, then the `k`-th derivative is `(1 - k)`-homogeneous,
`r^k Dᵏu(r x) = r Dᵏu(x)`, and differentiating in `r` at `r = 1` gives the Euler relation

  `D^{k+1}u(x)[x, v₁, …, v_k] = (1 - k) Dᵏu(x)[v₁, …, v_k]`.

Only differentiability at the single point `x` is used: the homogeneity of `Dᵏu` is obtained by
composing with the linear equivalence `y ↦ r y`, which needs no smoothness.
-/

open Function Filter Topology Set
open scoped ContDiff

@[expose] public section

namespace OnePhaseDimension

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {u : E → F} {x : E}

/-- One-homogeneity on rays: `u (r • x) = r • u x` for all `r > 0`. -/
def IsOneHomogeneous (u : E → F) : Prop :=
  ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r • u x

/-- The `k`-th derivative of a one-homogeneous function is `(1 - k)`-homogeneous:
`r^k Dᵏu(r x)[v] = r Dᵏu(x)[v]`. -/
theorem IsOneHomogeneous.pow_smul_iteratedFDeriv_smul (hu : IsOneHomogeneous u) {r : ℝ}
    (hr : 0 < r) {k : ℕ} (hk : ContDiffAt ℝ k u x) (v : Fin k → E) :
    r ^ k • iteratedFDeriv ℝ k u (r • x) v = r • iteratedFDeriv ℝ k u x v := by
  set g : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 r hr.ne') with hg
  have hgx : ∀ y, g y = r • y := fun y ↦ rfl
  have hcomp : u ∘ g = r • u := by
    funext y
    simp [hgx, hu r hr y]
  have h1 := g.iteratedFDerivWithin_comp_right u uniqueDiffOn_univ (mem_univ (g x)) k
  simp only [preimage_univ, iteratedFDerivWithin_univ] at h1
  rw [hcomp, iteratedFDeriv_const_smul_apply hk] at h1
  have h2 := congrArg (fun M ↦ M v) h1
  simp only [smul_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply] at h2
  change r • _ = iteratedFDeriv ℝ k u (r • x) (fun i ↦ r • v i) at h2
  rw [h2, (iteratedFDeriv ℝ k u (r • x)).map_smul_univ (fun _ ↦ r) v]
  simp

/-- **Euler relation for derivatives.** For a one-homogeneous `u` with `Dᵏu` differentiable at
`x`: `D^{k+1}u(x)[x, v] = (1 - k) Dᵏu(x)[v]`. -/
theorem IsOneHomogeneous.iteratedFDeriv_succ_apply_cons_self (hu : IsOneHomogeneous u) {k : ℕ}
    (hk : ContDiffAt ℝ (k + 1 : ℕ) u x) (v : Fin k → E) :
    iteratedFDeriv ℝ (k + 1) u x (Fin.cons x v) =
      (1 - k : ℝ) • iteratedFDeriv ℝ k u x v := by
  set h : E → F := fun y ↦ iteratedFDeriv ℝ k u y v
  have hk' : ContDiffAt ℝ k u x := hk.of_le (by exact_mod_cast Nat.le_succ k)
  have hdh : HasFDerivAt h (fderiv ℝ h x) (((1 : ℝ)) • x) := by
    rw [one_smul]
    exact (contDiffAt_iteratedFDeriv_apply (m := 1) hk v).differentiableAt one_ne_zero
      |>.hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ ↦ t • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hcomp : HasDerivAt (fun t : ℝ ↦ h (t • x)) (fderiv ℝ h x x) 1 := by
    have := hdh.comp_hasDerivAt (1 : ℝ) hline
    exact this
  have hφ : HasDerivAt (fun t : ℝ ↦ t ^ k • h (t • x))
      ((1 : ℝ) ^ k • fderiv ℝ h x x + ((k : ℝ) * 1 ^ (k - 1)) • h ((1 : ℝ) • x)) 1 :=
    (hasDerivAt_pow k (1 : ℝ)).smul hcomp
  have hψ : HasDerivAt (fun t : ℝ ↦ t • h x) (h x) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const (h x)
  have heq : (fun t : ℝ ↦ t ^ k • h (t • x)) =ᶠ[𝓝 1] fun t ↦ t • h x := by
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with t ht
    exact hu.pow_smul_iteratedFDeriv_smul ht hk' v
  have key : fderiv ℝ h x x + (k : ℝ) • h x = h x := by
    simpa using (hφ.congr_of_eventuallyEq heq.symm).unique hψ
  rw [iteratedFDeriv_succ_apply_cons_of_contDiffAt hk, sub_smul, one_smul]
  exact eq_sub_of_add_eq key

end OnePhaseDimension
