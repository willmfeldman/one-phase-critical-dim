/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Statements.CertificateGen
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# The coefficient maps of the certificate in `ℝ³`

We define the coefficient data `certThreeCoeffs : Gen.Coeffs 3` of the certificate in dimension
three (exponent `a = 29/50`, interior constant `ε = 1/50`, boundary constant `δ = 1/100`):
`f = 1`, `K = 0`, `P = 0`, and, writing `Ap` for the vector `(Ap)_i = A_{ia} p_a`,

  `U_{jk} = 197/1000 p_j p_k − 27/200 p_j (Ap)_k + 429/1000 (Ap)_j (Ap)_k + 527/1000 A_{jk}`
    `− 173/500 (p·Ap) A_{jk} − 1/1000 |p|² A_{jk} + 49/250 (A²)_{jk} − 17/40 |p|² (A²)_{jk}`,

  `M_l = 39/500 p_l + 69/500 (Ap)_l`.

`U` is not symmetric; only its symmetric trace-free part enters the inequalities.

We prove the structural properties of the certificate: smoothness, orthogonal equivariance
(with `f` invariant), evenness of `U` and `K` in `p`, `P = 0` at `g = 0`, and `f ≥ 1/50`.
The tensor algebra (matrix–vector products, matrix products, outer products, quadratic forms and
their behaviour under orthogonal changes of variables) is stated for every `m`.

## Main definitions

* `Gen.CertThree.matVec`, `Gen.CertThree.matMul`, `Gen.CertThree.outer`,
  `Gen.CertThree.quadForm`: the tensor operations.
* `Gen.CertThree.coeffU`, `Gen.CertThree.coeffM`: the coefficients `U` and `M`.
* `Gen.certThreeCoeffs`: the certificate data.

## Main statements

* `Gen.certThree_smooth_U`, `Gen.certThree_equiv_U`, … : the structural fields of
  `Gen.CertificateHolds 3 (1/50) (1/100) Gen.certThreeCoeffs` other than the interior and
  boundary inequalities.
-/

open scoped ContDiff

@[expose] public noncomputable section

namespace OnePhaseDimension.Gen

namespace CertThree

variable {m : ℕ}

/-! ### Tensor operations -/

/-- The matrix–vector product `(Ap)_i = ∑ₐ A_{ia} p_a`. -/
def matVec (A : Ten2 m) (p : Ten1 m) : Ten1 m := fun i ↦ ∑ a, A i a * p a

/-- The matrix product `(AB)_{ij} = ∑ₐ A_{ia} B_{aj}`. -/
def matMul (A B : Ten2 m) : Ten2 m := fun i j ↦ ∑ a, A i a * B a j

/-- The outer product `(u ⊗ v)_{jk} = u_j v_k`. -/
def outer (u v : Ten1 m) : Ten2 m := fun j k ↦ u j * v k

/-- The Euclidean inner product `u · v = ∑ᵢ uᵢ vᵢ`. -/
def dot (u v : Ten1 m) : ℝ := ∑ i, u i * v i

/-- The quadratic form `p · Ap`. -/
def quadForm (A : Ten2 m) (p : Ten1 m) : ℝ := dot p (matVec A p)

theorem sq1_eq_dot (p : Ten1 m) : sq1 p = dot p p := by
  simp only [sq1, dot, sq]

/-! ### Linearity of the actions -/

theorem act1_add (O : Ten2 m) (u v : Ten1 m) : act1 O (u + v) = act1 O u + act1 O v := by
  funext i
  simp [act1, mul_add, Finset.sum_add_distrib]

theorem act1_smul (O : Ten2 m) (c : ℝ) (u : Ten1 m) : act1 O (c • u) = c • act1 O u := by
  funext i
  simp [act1, Finset.mul_sum, mul_left_comm]

theorem act2_add (O : Ten2 m) (B C : Ten2 m) : act2 O (B + C) = act2 O B + act2 O C := by
  funext i j
  simp [act2, mul_add, Finset.sum_add_distrib]

theorem act2_sub (O : Ten2 m) (B C : Ten2 m) : act2 O (B - C) = act2 O B - act2 O C := by
  funext i j
  simp [act2, mul_sub, Finset.sum_sub_distrib]

theorem act2_smul (O : Ten2 m) (c : ℝ) (B : Ten2 m) : act2 O (c • B) = c • act2 O B := by
  funext i j
  simp [act2, Finset.mul_sum, mul_left_comm]

theorem act2_outer (O : Ten2 m) (u v : Ten1 m) :
    act2 O (outer u v) = outer (act1 O u) (act1 O v) := by
  funext i j
  simp only [act2, outer, act1, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  ring

/-! ### Orthogonal invariance of the contractions -/

/-- `∑ₐ O_{ad} (Op)_a = p_d` for orthogonal `O`. -/
theorem sum_mul_act1 {O : Ten2 m} (hO : IsOrth O) (p : Ten1 m) (d : Fin m) :
    ∑ a, O a d * act1 O p a = p d := by
  simp only [act1, Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ e, ∑ a, O a d * (O a e * p e) = kron d e * p e := fun e ↦ by
    rw [← hO d e, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  simp only [this, kron, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true]

theorem dot_act1 {O : Ten2 m} (hO : IsOrth O) (u v : Ten1 m) :
    dot (act1 O u) (act1 O v) = dot u v := by
  have h : ∀ i, act1 O u i * act1 O v i = ∑ d, u d * (O i d * act1 O v i) := fun i ↦ by
    rw [show act1 O u i = ∑ d, O i d * u d from rfl, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d _ ↦ by ring
  simp only [dot, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← Finset.mul_sum, sum_mul_act1 hO v d]

theorem sq1_act1 {O : Ten2 m} (hO : IsOrth O) (p : Ten1 m) : sq1 (act1 O p) = sq1 p := by
  rw [sq1_eq_dot, sq1_eq_dot, dot_act1 hO]

theorem matVec_act {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) (p : Ten1 m) :
    matVec (act2 O A) (act1 O p) = act1 O (matVec A p) := by
  funext i
  have h : ∀ a, act2 O A i a * act1 O p a
      = ∑ c, ∑ d, O i c * A c d * (O a d * act1 O p a) := fun a ↦ by
    simp only [act2, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun d _ ↦ by ring
  simp only [matVec, h]
  change _ = ∑ c, O i c * ∑ d, A c d * p d
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [← Finset.mul_sum, sum_mul_act1 hO p d]
  ring

theorem quadForm_act {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) (p : Ten1 m) :
    quadForm (act2 O A) (act1 O p) = quadForm A p := by
  rw [quadForm, matVec_act hO, dot_act1 hO, quadForm]

theorem matMul_act {O : Ten2 m} (hO : IsOrth O) (A B : Ten2 m) :
    matMul (act2 O A) (act2 O B) = act2 O (matMul A B) := by
  funext i j
  -- the `j`-th column of `act2 O B` is `act1 O` of `e ↦ ∑_f O_{jf} B_{ef}`
  have hcol : (fun a ↦ act2 O B a j) = act1 O (fun e ↦ ∑ f, O j f * B e f) := by
    funext a
    simp only [act2, act1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ ↦ Finset.sum_congr rfl fun f _ ↦ ?_
    ring
  have h := congrFun (matVec_act hO A (fun e ↦ ∑ f, O j f * B e f)) i
  rw [← hcol] at h
  change ∑ a, act2 O A i a * act2 O B a j = _
  rw [show ∑ a, act2 O A i a * act2 O B a j = matVec (act2 O A) (fun a ↦ act2 O B a j) i from
    rfl, h]
  simp only [act1, matVec, act2, matMul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  ring

/-! ### Evenness -/

theorem matVec_neg (A : Ten2 m) (p : Ten1 m) : matVec A (-p) = -matVec A p := by
  funext i
  simp [matVec]

theorem outer_neg_neg (u v : Ten1 m) : outer (-u) (-v) = outer u v := by
  funext j k
  simp [outer]

theorem quadForm_neg (A : Ten2 m) (p : Ten1 m) : quadForm A (-p) = quadForm A p := by
  simp [quadForm, dot, matVec_neg]

theorem sq1_neg (p : Ten1 m) : sq1 (-p) = sq1 p := by
  simp [sq1]

/-! ### The coefficients -/

/-- The coefficient `U`:
`U = 197/1000 p⊗p − 27/200 p⊗Ap + 429/1000 Ap⊗Ap + (527/1000 − 173/500 p·Ap − 1/1000 |p|²) A`
`+ (49/250 − 17/40 |p|²) A²`. -/
def coeffU (A : Ten2 m) (p : Ten1 m) : Ten2 m :=
  (197 / 1000 : ℝ) • outer p p - (27 / 200 : ℝ) • outer p (matVec A p)
    + (429 / 1000 : ℝ) • outer (matVec A p) (matVec A p)
    + (527 / 1000 - 173 / 500 * quadForm A p - 1 / 1000 * sq1 p) • A
    + (49 / 250 - 17 / 40 * sq1 p) • matMul A A

/-- The coefficient `M = 39/500 p + 69/500 Ap`. -/
def coeffM (A : Ten2 m) (p : Ten1 m) : Ten1 m :=
  (39 / 500 : ℝ) • p + (69 / 500 : ℝ) • matVec A p

theorem coeffU_apply (A : Ten2 m) (p : Ten1 m) (j k : Fin m) :
    coeffU A p j k = 197 / 1000 * (p j * p k) - 27 / 200 * (p j * matVec A p k)
      + 429 / 1000 * (matVec A p j * matVec A p k)
      + (527 / 1000 - 173 / 500 * quadForm A p - 1 / 1000 * sq1 p) * A j k
      + (49 / 250 - 17 / 40 * sq1 p) * matMul A A j k := by
  simp [coeffU, outer]

theorem coeffM_apply (A : Ten2 m) (p : Ten1 m) (l : Fin m) :
    coeffM A p l = 39 / 500 * p l + 69 / 500 * matVec A p l := by
  simp [coeffM]

theorem coeffU_act {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) (p : Ten1 m) :
    coeffU (act2 O A) (act1 O p) = act2 O (coeffU A p) := by
  simp only [coeffU, act2_add, act2_sub, act2_smul, act2_outer, matVec_act hO, quadForm_act hO,
    sq1_act1 hO, matMul_act hO]

theorem coeffM_act {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) (p : Ten1 m) :
    coeffM (act2 O A) (act1 O p) = act1 O (coeffM A p) := by
  simp only [coeffM, act1_add, act1_smul, matVec_act hO]

theorem coeffU_neg (A : Ten2 m) (p : Ten1 m) : coeffU A (-p) = coeffU A p := by
  simp only [coeffU, matVec_neg, outer_neg_neg, quadForm_neg, sq1_neg]

/-! ### Smoothness -/

theorem contDiff_entry2 (a b : Fin m) :
    ContDiff ℝ ∞ fun x : Ten2 m × Ten1 m × ℝ ↦ x.1 a b := by
  fun_prop

theorem contDiff_entry1 (a : Fin m) :
    ContDiff ℝ ∞ fun x : Ten2 m × Ten1 m × ℝ ↦ x.2.1 a := by
  fun_prop

theorem contDiff_coeffU_apply (j k : Fin m) :
    ContDiff ℝ ∞ fun x : Ten2 m × Ten1 m × ℝ ↦ coeffU x.1 x.2.1 j k := by
  simp only [coeffU_apply, matVec, matMul, quadForm, dot, sq1]
  fun_prop

theorem contDiff_coeffM_apply (l : Fin m) :
    ContDiff ℝ ∞ fun x : Ten2 m × Ten1 m × ℝ ↦ coeffM x.1 x.2.1 l := by
  simp only [coeffM_apply, matVec]
  fun_prop

end CertThree

open CertThree

/-- The certificate data in `ℝ³`: `f = 1`, `U = coeffU`, `K = 0`, `M = coeffM`, `P = 0`. -/
def certThreeCoeffs : Coeffs 3 where
  f _ := 1
  U x := coeffU x.1 x.2.1
  K _ := 0
  M x := coeffM x.1 x.2.1
  P _ := 0

theorem certThree_smooth_f : ContDiff ℝ ∞ certThreeCoeffs.f := contDiff_const

theorem certThree_smooth_U : ContDiff ℝ ∞ certThreeCoeffs.U :=
  contDiff_pi.2 fun j ↦ contDiff_pi.2 fun k ↦ contDiff_coeffU_apply j k

theorem certThree_smooth_K : ContDiff ℝ ∞ certThreeCoeffs.K := contDiff_const

theorem certThree_smooth_M : ContDiff ℝ ∞ certThreeCoeffs.M :=
  contDiff_pi.2 fun l ↦ contDiff_coeffM_apply l

theorem certThree_smooth_P : ContDiff ℝ ∞ certThreeCoeffs.P := contDiff_const

theorem certThree_equiv_f (O : Ten2 3) (_ : IsOrth O) (A : Ten2 3) (p : Ten1 3) (g : ℝ) :
    certThreeCoeffs.f (act2 O A, act1 O p, g) = certThreeCoeffs.f (A, p, g) := rfl

theorem certThree_equiv_U (O : Ten2 3) (hO : IsOrth O) (A : Ten2 3) (p : Ten1 3) (g : ℝ) :
    certThreeCoeffs.U (act2 O A, act1 O p, g) = act2 O (certThreeCoeffs.U (A, p, g)) :=
  coeffU_act hO A p

theorem certThree_equiv_K (O : Ten2 3) (_ : IsOrth O) (A : Ten2 3) (p : Ten1 3) (g : ℝ) :
    certThreeCoeffs.K (act2 O A, act1 O p, g) = act4 O (certThreeCoeffs.K (A, p, g)) := by
  funext i j k l
  simp [certThreeCoeffs, act4]

theorem certThree_equiv_M (O : Ten2 3) (hO : IsOrth O) (A : Ten2 3) (p : Ten1 3) (g : ℝ) :
    certThreeCoeffs.M (act2 O A, act1 O p, g) = act1 O (certThreeCoeffs.M (A, p, g)) :=
  coeffM_act hO A p

theorem certThree_equiv_P (O : Ten2 3) (_ : IsOrth O) (A : Ten2 3) (p : Ten1 3) (g : ℝ) :
    certThreeCoeffs.P (act2 O A, act1 O p, g) = act1 O (certThreeCoeffs.P (A, p, g)) := by
  funext i
  simp [certThreeCoeffs, act1]

theorem certThree_even_U (A : Ten2 3) (p : Ten1 3) (g : ℝ) :
    certThreeCoeffs.U (A, -p, g) = certThreeCoeffs.U (A, p, g) :=
  coeffU_neg A p

theorem certThree_even_K (A : Ten2 3) (p : Ten1 3) (g : ℝ) :
    certThreeCoeffs.K (A, -p, g) = certThreeCoeffs.K (A, p, g) := rfl

theorem certThree_P_g_zero (A : Ten2 3) (p : Ten1 3) : certThreeCoeffs.P (A, p, 0) = 0 := rfl

theorem certThree_f_ge (A : Ten2 3) (p : Ten1 3) (g : ℝ) :
    (1 / 50 : ℝ) ≤ certThreeCoeffs.f (A, p, g) := by
  change (1 / 50 : ℝ) ≤ 1
  norm_num

end OnePhaseDimension.Gen
