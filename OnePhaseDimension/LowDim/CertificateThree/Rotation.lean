/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.CertificateThree.Explicit
public import OnePhaseDimension.Flux.Algebra
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Reduction of the certificate inequalities in `ℝ³` to diagonal `A`

The interior polynomial `interiorPolyThree` and the boundary polynomial `boundaryPolyThree` are
full contractions of orthogonally equivariant tensors, hence invariant under
`(A, X, p, ℓ) ↦ (O A Oᵀ, O·X, O p, O ℓ)` for orthogonal `O`. Every symmetric `A` on `ℝ³` is
diagonalised by an orthogonal change of variables, and when `A p = λ p` with `|p| = 1` the frame
can be chosen with `O p = e₂` and `O A Oᵀ = diag(μ₀, μ₁, λ)`. Hence both inequalities required by
`certThree_holds_of` reduce to diagonal `A`.

## Main definitions

* `Gen.CertThree.diag3`: the diagonal matrix `diag(a, b, c)` on `ℝ³`.

## Main statements

* `Gen.interiorPolyThree_act`, `Gen.boundaryPolyThree_act`: orthogonal invariance.
* `Gen.CertThree.exists_orth_diag`, `Gen.CertThree.exists_orth_diag_of_eigen`: eigenframes.
* `Gen.certThree_interior_of_diag`, `Gen.certThree_boundary_of_diag`: the reductions.
-/

open scoped Matrix

@[expose] public noncomputable section

namespace OnePhaseDimension.Gen

namespace CertThree

variable {m : ℕ}

/-! ### Orthogonal matrices -/

/-- The pairing `⟨B, C⟩ = ∑_{jk} B_{jk} C_{jk}` of two-tensors. -/
def frob (B C : Ten2 m) : ℝ := ∑ j, ∑ k, B j k * C j k

/-- The contraction `(X : B)_l = ∑_{jk} X_{ljk} B_{jk}`. -/
def contr3 (X : Ten3 m) (B : Ten2 m) : Ten1 m := fun l ↦ frob (X l) B

/-- The transpose of a two-tensor. -/
def transp (O : Ten2 m) : Ten2 m := fun i j ↦ O j i

theorem matrix_of_one_apply (i j : Fin m) : (1 : Matrix (Fin m) (Fin m) ℝ) i j = kron i j := by
  simp [Matrix.one_apply, kron]

/-- An orthogonal matrix has orthonormal rows. -/
theorem isOrth_rows {O : Ten2 m} (hO : IsOrth O) (i j : Fin m) :
    ∑ k, O i k * O j k = kron i j := by
  have h : (Matrix.of O)ᵀ * Matrix.of O = 1 := by
    ext a b
    rw [matrix_of_one_apply, ← hO a b]
    simp [Matrix.mul_apply]
  have h₂ : Matrix.of O * (Matrix.of O)ᵀ = 1 := mul_eq_one_comm.1 h
  have h' := congrFun (congrFun h₂ i) j
  rw [matrix_of_one_apply] at h'
  rw [← h']
  simp [Matrix.mul_apply]

/-- A matrix with orthonormal rows is orthogonal. -/
theorem isOrth_of_rows {O : Ten2 m} (h : ∀ i j, ∑ k, O i k * O j k = kron i j) : IsOrth O := by
  have h₁ : Matrix.of O * (Matrix.of O)ᵀ = 1 := by
    ext a b
    rw [matrix_of_one_apply, ← h a b]
    simp [Matrix.mul_apply]
  intro i j
  have h₂ : (Matrix.of O)ᵀ * Matrix.of O = 1 := mul_eq_one_comm.1 h₁
  have h' := congrFun (congrFun h₂ i) j
  rw [matrix_of_one_apply] at h'
  rw [← h']
  simp [Matrix.mul_apply]

theorem isOrth_transp {O : Ten2 m} (hO : IsOrth O) : IsOrth (transp O) :=
  fun i j ↦ isOrth_rows hO i j

theorem act1_transp_act1 {O : Ten2 m} (hO : IsOrth O) (p : Ten1 m) :
    act1 (transp O) (act1 O p) = p :=
  funext fun d ↦ sum_mul_act1 hO p d

theorem act2_apply_eq_act1 (O B : Ten2 m) (j k : Fin m) :
    act2 O B j k = act1 O (fun a ↦ act1 O (B a) k) j := by
  simp only [act2, act1, Finset.mul_sum, mul_assoc]

theorem act2_transp_act2 {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) :
    act2 (transp O) (act2 O A) = A := by
  funext i j
  have h : ∀ a b, transp O i a * transp O j b * act2 O A a b
      = O b j * (O a i * act1 O (fun c ↦ act1 O (A c) b) a) := fun a b ↦ by
    rw [act2_apply_eq_act1]; simp only [transp]; ring
  change ∑ a, ∑ b, transp O i a * transp O j b * act2 O A a b = A i j
  simp only [h]
  rw [Finset.sum_comm]
  have h₂ : ∀ b, ∑ a, O b j * (O a i * act1 O (fun c ↦ act1 O (A c) b) a)
      = O b j * act1 O (A i) b := fun b ↦ by
    rw [← Finset.mul_sum, sum_mul_act1 hO]
  simp only [h₂]
  exact sum_mul_act1 hO (A i) j

/-! ### Linearity of the pairing and of the contraction -/

theorem frob_comm (B C : Ten2 m) : frob B C = frob C B := by
  simp only [frob, mul_comm]

theorem frob_sum_smul_left (a : Fin m → ℝ) (B : Fin m → Ten2 m) (C : Ten2 m) :
    frob (∑ c, a c • B c) C = ∑ c, a c * frob (B c) C := by
  simp only [frob, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
  ring

theorem frob_sum_smul_right (a : Fin m → ℝ) (B : Ten2 m) (C : Fin m → Ten2 m) :
    frob B (∑ c, a c • C c) = ∑ c, a c * frob B (C c) := by
  rw [frob_comm, frob_sum_smul_left]
  simp only [frob_comm]

/-- `⟨O B Oᵀ, O C Oᵀ⟩ = ⟨B, C⟩`. -/
theorem frob_act2 {O : Ten2 m} (hO : IsOrth O) (B C : Ten2 m) :
    frob (act2 O B) (act2 O C) = frob B C := by
  have h₁ : ∀ k, ∑ j, act2 O B j k * act2 O C j k
      = ∑ a, act1 O (B a) k * act1 O (C a) k := fun k ↦ by
    simp only [act2_apply_eq_act1]
    exact dot_act1 hO (fun a ↦ act1 O (B a) k) (fun a ↦ act1 O (C a) k)
  simp only [frob]
  rw [Finset.sum_comm]
  simp only [h₁]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ ↦ dot_act1 hO (B a) (C a)

/-- The slice `(O·X)_l = ∑_c O_{lc} O X_c Oᵀ`. -/
theorem act3_slice (O : Ten2 m) (X : Ten3 m) (l : Fin m) :
    act3 O X l = ∑ c, O l c • act2 O (X c) := by
  funext j k
  simp only [act3, act2, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ Finset.sum_congr rfl fun a _ ↦
    Finset.sum_congr rfl fun b _ ↦ ?_
  ring

theorem contr3_act {O : Ten2 m} (hO : IsOrth O) (X : Ten3 m) (B : Ten2 m) :
    contr3 (act3 O X) (act2 O B) = act1 O (contr3 X B) := by
  funext l
  simp only [contr3, act3_slice, frob_sum_smul_left, frob_act2 hO, act1]

theorem qVec_eq_contr3 (X : Ten3 m) (A : Ten2 m) : qVec X A = contr3 X A := rfl

theorem qVec_act {O : Ten2 m} (hO : IsOrth O) (X : Ten3 m) (A : Ten2 m) :
    qVec (act3 O X) (act2 O A) = act1 O (qVec X A) :=
  contr3_act hO X A

/-! ### Contractions with a linear map of the direction -/

/-- The action of `O` on a direction `(E, v)`. -/
def actDir (O : Ten2 m) (d : Ten2 m × Ten1 m) : Ten2 m × Ten1 m := (act2 O d.1, act1 O d.2)

theorem sum_sum_orth {O : Ten2 m} (hO : IsOrth O) (Φ : Fin m → Fin m → ℝ) :
    ∑ l, ∑ c, O l c * ∑ e, O l e * Φ c e = ∑ c, Φ c c := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Finset.sum_comm]
  have : ∀ e, ∑ l, O l c * (O l e * Φ c e) = kron c e * Φ c e := fun e ↦ by
    rw [← hO c e, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  simp only [this]
  exact sum_kron_mul c (Φ c)

/-- For a linear map `F` of the direction with values in two-tensors, equivariant from `F` to
`F'`, the contraction `∑_l ⟨F(d_l), Y_l⟩` is invariant. -/
theorem sum_frob_linear_act {O : Ten2 m} (hO : IsOrth O)
    (F F' : Ten2 m × Ten1 m →ₗ[ℝ] Ten2 m) (hF : ∀ d, F' (actDir O d) = act2 O (F d))
    (d : Fin m → Ten2 m × Ten1 m) (Y : Fin m → Ten2 m) :
    ∑ l, frob (F' (∑ c, O l c • actDir O (d c))) (∑ c, O l c • act2 O (Y c))
      = ∑ l, frob (F (d l)) (Y l) := by
  simp only [map_sum, map_smul, hF, frob_sum_smul_left, frob_sum_smul_right, frob_act2 hO]
  exact sum_sum_orth hO fun c e ↦ frob (F (d e)) (Y c)

/-- For a linear map `G` of the direction with values in vectors, equivariant from `G` to `G'`,
the trace `∑_l G(d_l)_l` is invariant. -/
theorem sum_trace_linear_act {O : Ten2 m} (hO : IsOrth O)
    (G G' : Ten2 m × Ten1 m →ₗ[ℝ] Ten1 m) (hG : ∀ d, G' (actDir O d) = act1 O (G d))
    (d : Fin m → Ten2 m × Ten1 m) :
    ∑ l, G' (∑ c, O l c • actDir O (d c)) l = ∑ l, G (d l) l := by
  simp only [map_sum, map_smul, hG, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, act1]
  exact sum_sum_orth hO fun c e ↦ G (d c) e

/-! ### Linearity of the directional derivatives -/

theorem matVec_add_left (E E' : Ten2 m) (p : Ten1 m) :
    matVec (E + E') p = matVec E p + matVec E' p := by
  funext i
  simp [matVec, add_mul, Finset.sum_add_distrib]

theorem matVec_smul_left (c : ℝ) (E : Ten2 m) (p : Ten1 m) :
    matVec (c • E) p = c • matVec E p := by
  funext i
  simp [matVec, Finset.mul_sum, mul_assoc]

theorem matVec_add_right (A : Ten2 m) (v v' : Ten1 m) :
    matVec A (v + v') = matVec A v + matVec A v' := by
  funext i
  simp [matVec, mul_add, Finset.sum_add_distrib]

theorem matVec_smul_right (c : ℝ) (A : Ten2 m) (v : Ten1 m) :
    matVec A (c • v) = c • matVec A v := by
  funext i
  simp [matVec, Finset.mul_sum, mul_left_comm]

theorem matMul_add_left (E E' A : Ten2 m) : matMul (E + E') A = matMul E A + matMul E' A := by
  funext i j
  simp [matMul, add_mul, Finset.sum_add_distrib]

theorem matMul_smul_left (c : ℝ) (E A : Ten2 m) : matMul (c • E) A = c • matMul E A := by
  funext i j
  simp [matMul, Finset.mul_sum, mul_assoc]

theorem matMul_add_right (A E E' : Ten2 m) : matMul A (E + E') = matMul A E + matMul A E' := by
  funext i j
  simp [matMul, mul_add, Finset.sum_add_distrib]

theorem matMul_smul_right (c : ℝ) (A E : Ten2 m) : matMul A (c • E) = c • matMul A E := by
  funext i j
  simp [matMul, Finset.mul_sum, mul_left_comm]

theorem outer_add_left (u u' v : Ten1 m) : outer (u + u') v = outer u v + outer u' v := by
  funext j k
  simp [outer, add_mul]

theorem outer_smul_left (c : ℝ) (u v : Ten1 m) : outer (c • u) v = c • outer u v := by
  funext j k
  simp [outer, mul_assoc]

theorem outer_add_right (u v v' : Ten1 m) : outer u (v + v') = outer u v + outer u v' := by
  funext j k
  simp [outer, mul_add]

theorem outer_smul_right (c : ℝ) (u v : Ten1 m) : outer u (c • v) = c • outer u v := by
  funext j k
  simp [outer, mul_left_comm]

theorem dot_add_left (u u' v : Ten1 m) : dot (u + u') v = dot u v + dot u' v := by
  simp [dot, add_mul, Finset.sum_add_distrib]

theorem dot_smul_left (c : ℝ) (u v : Ten1 m) : dot (c • u) v = c * dot u v := by
  simp [dot, Finset.mul_sum, mul_assoc]

theorem dot_add_right (u v v' : Ten1 m) : dot u (v + v') = dot u v + dot u v' := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem dot_smul_right (c : ℝ) (u v : Ten1 m) : dot u (c • v) = c * dot u v := by
  simp [dot, Finset.mul_sum, mul_left_comm]

theorem matVecDir_add (A : Ten2 m) (p : Ten1 m) (E E' : Ten2 m) (v v' : Ten1 m) :
    matVecDir A p (E + E') (v + v') = matVecDir A p E v + matVecDir A p E' v' := by
  simp only [matVecDir, matVec_add_left, matVec_add_right]
  abel

theorem matVecDir_smul (c : ℝ) (A : Ten2 m) (p : Ten1 m) (E : Ten2 m) (v : Ten1 m) :
    matVecDir A p (c • E) (c • v) = c • matVecDir A p E v := by
  simp only [matVecDir, matVec_smul_left, matVec_smul_right, smul_add]

theorem quadFormDir_add (A : Ten2 m) (p : Ten1 m) (E E' : Ten2 m) (v v' : Ten1 m) :
    quadFormDir A p (E + E') (v + v') = quadFormDir A p E v + quadFormDir A p E' v' := by
  simp only [quadFormDir, matVecDir_add, dot_add_left, dot_add_right]
  ring

theorem quadFormDir_smul (c : ℝ) (A : Ten2 m) (p : Ten1 m) (E : Ten2 m) (v : Ten1 m) :
    quadFormDir A p (c • E) (c • v) = c * quadFormDir A p E v := by
  simp only [quadFormDir, matVecDir_smul, dot_smul_left, dot_smul_right]
  ring

theorem coeffUDir_add (A : Ten2 m) (p : Ten1 m) (E E' : Ten2 m) (v v' : Ten1 m) :
    coeffUDir A p (E + E') (v + v') = coeffUDir A p E v + coeffUDir A p E' v' := by
  simp only [coeffUDir, matVecDir_add, quadFormDir_add, outer_add_left, outer_add_right,
    dot_add_right, matMul_add_left, matMul_add_right]
  module

theorem coeffUDir_smul (c : ℝ) (A : Ten2 m) (p : Ten1 m) (E : Ten2 m) (v : Ten1 m) :
    coeffUDir A p (c • E) (c • v) = c • coeffUDir A p E v := by
  simp only [coeffUDir, matVecDir_smul, quadFormDir_smul, outer_smul_left, outer_smul_right,
    dot_smul_right, matMul_smul_left, matMul_smul_right]
  module

theorem coeffMDir_add (A : Ten2 m) (p : Ten1 m) (E E' : Ten2 m) (v v' : Ten1 m) :
    coeffMDir A p (E + E') (v + v') = coeffMDir A p E v + coeffMDir A p E' v' := by
  simp only [coeffMDir, matVecDir_add]
  module

theorem coeffMDir_smul (c : ℝ) (A : Ten2 m) (p : Ten1 m) (E : Ten2 m) (v : Ten1 m) :
    coeffMDir A p (c • E) (c • v) = c • coeffMDir A p E v := by
  simp only [coeffMDir, matVecDir_smul]
  module

/-- The derivative of `U` at `(A, p)` as a linear map of the direction `(E, v)`. -/
def coeffUDirLin (A : Ten2 m) (p : Ten1 m) : Ten2 m × Ten1 m →ₗ[ℝ] Ten2 m where
  toFun d := coeffUDir A p d.1 d.2
  map_add' d d' := coeffUDir_add A p d.1 d'.1 d.2 d'.2
  map_smul' c d := coeffUDir_smul c A p d.1 d.2

/-- The derivative of `M` at `(A, p)` as a linear map of the direction `(E, v)`. -/
def coeffMDirLin (A : Ten2 m) (p : Ten1 m) : Ten2 m × Ten1 m →ₗ[ℝ] Ten1 m where
  toFun d := coeffMDir A p d.1 d.2
  map_add' d d' := coeffMDir_add A p d.1 d'.1 d.2 d'.2
  map_smul' c d := coeffMDir_smul c A p d.1 d.2

theorem coeffUDirLin_apply (A : Ten2 m) (p : Ten1 m) (d : Ten2 m × Ten1 m) :
    coeffUDirLin A p d = coeffUDir A p d.1 d.2 := rfl

theorem coeffMDirLin_apply (A : Ten2 m) (p : Ten1 m) (d : Ten2 m × Ten1 m) :
    coeffMDirLin A p d = coeffMDir A p d.1 d.2 := rfl

/-! ### Equivariance of the directional derivatives -/

theorem matVecDir_act {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) (p : Ten1 m) (E : Ten2 m)
    (v : Ten1 m) :
    matVecDir (act2 O A) (act1 O p) (act2 O E) (act1 O v) = act1 O (matVecDir A p E v) := by
  simp only [matVecDir, matVec_act hO, act1_add]

theorem quadFormDir_act {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) (p : Ten1 m) (E : Ten2 m)
    (v : Ten1 m) :
    quadFormDir (act2 O A) (act1 O p) (act2 O E) (act1 O v) = quadFormDir A p E v := by
  simp only [quadFormDir, matVecDir_act hO, matVec_act hO, dot_act1 hO]

theorem coeffUDir_act {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) (p : Ten1 m) (E : Ten2 m)
    (v : Ten1 m) :
    coeffUDir (act2 O A) (act1 O p) (act2 O E) (act1 O v) = act2 O (coeffUDir A p E v) := by
  simp only [coeffUDir, act2_add, act2_sub, act2_smul, act2_outer, matVec_act hO,
    matVecDir_act hO, quadForm_act hO, quadFormDir_act hO, sq1_act1 hO, dot_act1 hO,
    matMul_act hO]

theorem coeffMDir_act {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) (p : Ten1 m) (E : Ten2 m)
    (v : Ten1 m) :
    coeffMDir (act2 O A) (act1 O p) (act2 O E) (act1 O v) = act1 O (coeffMDir A p E v) := by
  simp only [coeffMDir, act1_add, act1_smul, matVecDir_act hO]

theorem coeffUDirLin_act {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) (p : Ten1 m)
    (d : Ten2 m × Ten1 m) :
    coeffUDirLin (act2 O A) (act1 O p) (actDir O d) = act2 O (coeffUDirLin A p d) :=
  coeffUDir_act hO A p d.1 d.2

theorem coeffMDirLin_act {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) (p : Ten1 m)
    (d : Ten2 m × Ten1 m) :
    coeffMDirLin (act2 O A) (act1 O p) (actDir O d) = act1 O (coeffMDirLin A p d) :=
  coeffMDir_act hO A p d.1 d.2

/-! ### The generator directions -/

/-- The direction `(X_l − q_l A, w A_{l·} − g z δ_{l·})` of `D_l` in the `(A, p)` variables. -/
def dirOf (X : Ten3 m) (A : Ten2 m) (g w z : ℝ) (l : Fin m) : Ten2 m × Ten1 m :=
  (fun a b ↦ X l a b - qVec X A l * A a b, fun a ↦ w * A l a - g * z * kron l a)

/-- The directions of the rotated data are the rotated directions, mixed by `O`. -/
theorem dirOf_act {O : Ten2 m} (hO : IsOrth O) (X : Ten3 m) (A : Ten2 m) (g w z : ℝ)
    (l : Fin m) :
    dirOf (act3 O X) (act2 O A) g w z l = ∑ c, O l c • actDir O (dirOf X A g w z c) := by
  refine Prod.ext ?_ ?_
  · funext a b
    have hE : ∀ c, act2 O (fun a b ↦ X c a b - qVec X A c * A a b)
        = act2 O (X c) - qVec X A c • act2 O A := fun c ↦ by
      rw [← act2_smul, ← act2_sub]
      rfl
    have h1 : act3 O X l a b = ∑ c, O l c * act2 O (X c) a b := by
      rw [act3_slice]
      simp [Finset.sum_apply]
    have h2 : qVec (act3 O X) (act2 O A) l = ∑ c, O l c * qVec X A c := by
      rw [qVec_act hO]
      rfl
    simp only [dirOf, actDir, Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, hE, Pi.sub_apply]
    rw [h1, h2, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ ↦ by ring
  · funext a
    have h1 : ∀ c, ∑ d, O a d * (w * A c d - g * z * kron c d)
        = w * ∑ d, O a d * A c d - g * z * O a c := fun c ↦ by
      have : ∑ d, kron c d * O a d = O a c := sum_kron_mul c (O a)
      rw [Finset.mul_sum, ← this, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun d _ ↦ by ring
    have h2 : ∑ c, O l c * O a c = kron l a := isOrth_rows hO l a
    simp only [dirOf, actDir, Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, act1, h1, act2]
    rw [← h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ ↦ ?_
    have h3 : ∑ b, O l c * O a b * A c b = O l c * ∑ d, O a d * A c d := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [h3]
    ring


/-! ### Preservation of the hypotheses -/

theorem trace_act2 {O : Ten2 m} (hO : IsOrth O) (A : Ten2 m) :
    ∑ i, act2 O A i i = ∑ i, A i i := by
  simp only [act2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.sum_comm]
  have : ∀ b, ∑ i, O i a * O i b * A a b = kron a b * A a b := fun b ↦ by
    rw [← hO a b, Finset.sum_mul]
  simp only [this]
  exact sum_kron_mul a (A a)

theorem isSymm2_act2 (O : Ten2 m) {A : Ten2 m} (hA : IsSymm2 A) : IsSymm2 (act2 O A) := by
  intro i j
  simp only [act2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  rw [hA b a]
  ring

theorem isSTF2_act2 {O : Ten2 m} (hO : IsOrth O) {A : Ten2 m} (hA : IsSTF2 A) :
    IsSTF2 (act2 O A) :=
  ⟨isSymm2_act2 O hA.1, (trace_act2 hO A).trans hA.2⟩

theorem sq2_eq_frob (A : Ten2 m) : sq2 A = frob A A := by
  simp only [sq2, frob, sq]

theorem isSTF3_act3 {O : Ten2 m} (hO : IsOrth O) {X : Ten3 m} (hX : IsSTF3 X) :
    IsSTF3 (act3 O X) := by
  obtain ⟨h₁, h₂, h₃⟩ := hX
  have s₁ : ∀ i j k, act3 O X i j k = act3 O X j i k := fun i j k ↦ by
    simp only [act3]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦
      Finset.sum_congr rfl fun c _ ↦ ?_
    rw [h₁ b a c]
    ring
  have s₂ : ∀ i j k, act3 O X i j k = act3 O X i k j := fun i j k ↦ by
    simp only [act3]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ Finset.sum_congr rfl fun c _ ↦ ?_
    rw [h₂ a c b]
    ring
  refine ⟨s₁, s₂, fun k ↦ ?_⟩
  have e : ∀ i, act3 O X i i k = act3 O X k i i := fun i ↦ by rw [s₂, s₁]
  simp only [e, act3_slice, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun c _ ↦ ?_
  rw [← Finset.mul_sum, trace_act2 hO]
  have : ∑ i, X c i i = ∑ i, X i i c := Finset.sum_congr rfl fun i _ ↦ by rw [h₁ c i i, h₂ i c i]
  rw [this, h₃ c, mul_zero]

/-! ### Eigenframes -/

/-- If the rows of `O` are orthonormal eigenvectors of `A`, then `O A Oᵀ` is diagonal. -/
theorem act2_eq_of_eigen {O A : Ten2 m} {ν : Fin m → ℝ}
    (hrows : ∀ i j, ∑ k, O i k * O j k = kron i j)
    (hev : ∀ j a, ∑ b, A a b * O j b = ν j * O j a) (i j : Fin m) :
    act2 O A i j = kron i j * ν j := by
  have h : ∀ a, ∑ b, O i a * O j b * A a b = O i a * (ν j * O j a) := fun a ↦ by
    rw [← hev j a, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ ↦ by ring
  simp only [act2, h]
  rw [← hrows i j, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ ↦ by ring

/-- The linear map of a two-tensor on `ℝ^m`. -/
def ten2Lin (A : Ten2 m) : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanLin (Matrix.of A)

theorem ten2Lin_apply (A : Ten2 m) (v : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    ten2Lin A v i = ∑ j, A i j * v j := by
  simp [ten2Lin, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]

theorem inner_euclidean (v w : EuclideanSpace ℝ (Fin m)) : inner ℝ v w = ∑ j, v j * w j := by
  simp [PiLp.inner_apply, mul_comm]

theorem ten2Lin_isSymmetric {A : Ten2 m} (hA : IsSymm2 A) : (ten2Lin A).IsSymmetric :=
  fun v w ↦ by
    rw [inner_euclidean, inner_euclidean]
    simp only [ten2Lin_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [hA j i]; ring

/-- **Spectral theorem.** Every symmetric `A` is diagonalised by an orthogonal change of
variables: `O A Oᵀ = diag(ν)`. -/
theorem exists_orth_diag {A : Ten2 m} (hA : IsSymm2 A) :
    ∃ O : Ten2 m, IsOrth O ∧ ∃ ν : Fin m → ℝ, ∀ i j, act2 O A i j = kron i j * ν j := by
  have hT := ten2Lin_isSymmetric hA
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp
  have hrows : ∀ i j, ∑ k, hT.eigenvectorBasis hn i k * hT.eigenvectorBasis hn j k
      = kron i j := fun i j ↦ by
    have h := (hT.eigenvectorBasis hn).orthonormal
    rw [orthonormal_iff_ite] at h
    rw [← inner_euclidean, h i j, kron]
  refine ⟨fun i k ↦ hT.eigenvectorBasis hn i k, isOrth_of_rows hrows, hT.eigenvalues hn,
    act2_eq_of_eigen hrows fun j a ↦ ?_⟩
  have h := congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v a) (hT.apply_eigenvectorBasis hn j)
  simp only [ten2Lin_apply] at h
  rw [h]
  simp

/-- A symmetric `A` with a unit eigenvector `p` has two orthonormal eigenvectors orthogonal to
`p` (the spectral theorem on the invariant subspace `p^⊥`). -/
theorem exists_eigenframe {A : Ten2 3} {p : Ten1 3} {lam : ℝ} (hA : IsSymm2 A) (hp : sq1 p = 1)
    (hAp : ∀ i, ∑ j, A i j * p j = lam * p i) :
    ∃ (v : Fin 2 → Fin 3 → ℝ) (μ : Fin 2 → ℝ),
      (∀ i k, ∑ j, v i j * v k j = if i = k then 1 else 0) ∧ (∀ i, ∑ j, v i j * p j = 0) ∧
      (∀ i j, ∑ b, A j b * v i b = μ i * v i j) := by
  have hTs := ten2Lin_isSymmetric hA
  have hp0 : (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 3)) ≠ 0 := by
    intro h
    have h' : ∀ j, p j = 0 := fun j ↦ by
      simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 3) ↦ v j) h
    simp [sq1, h'] at hp
  have hK : ∀ v ∈ (ℝ ∙ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 3)))ᗮ,
      ten2Lin A v ∈ (ℝ ∙ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 3)))ᗮ := fun v hv ↦ by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hv ⊢
    rw [← hTs, inner_euclidean]
    rw [inner_euclidean] at hv
    simp only [ten2Lin_apply]
    have : ∀ j, ∑ b, A j b * (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 3)) b =
        lam * (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 3)) j := hAp
    simp only [this, mul_assoc, ← Finset.mul_sum, hv, mul_zero]
  have hTK := hTs.restrict_invariant hK
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  have hn : Module.finrank ℝ (ℝ ∙ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 3)))ᗮ = 2 :=
    Submodule.finrank_orthogonal_span_singleton hp0
  refine ⟨fun i j ↦ ((hTK.eigenvectorBasis hn i : (ℝ ∙ (WithLp.toLp 2 p :
    EuclideanSpace ℝ (Fin 3)))ᗮ) : EuclideanSpace ℝ (Fin 3)) j, hTK.eigenvalues hn, ?_, ?_, ?_⟩
  · intro i k
    have h := (hTK.eigenvectorBasis hn).orthonormal
    rw [orthonormal_iff_ite] at h
    rw [← h i k, Submodule.coe_inner, inner_euclidean]
  · intro i
    have h := (hTK.eigenvectorBasis hn i).2
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_euclidean] at h
    rw [← h]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  · intro i j
    have h := hTK.apply_eigenvectorBasis hn i
    have h2 := congrArg (fun w : (ℝ ∙ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 3)))ᗮ ↦
      (w : EuclideanSpace ℝ (Fin 3)) j) h
    simp only [LinearMap.coe_restrict_apply, ten2Lin_apply] at h2
    rw [h2]
    simp

/-- The diagonal matrix `diag(a, b, c)` on `ℝ³`. -/
def diag3 (a b c : ℝ) : Ten2 3 := ![![a, 0, 0], ![0, b, 0], ![0, 0, c]]

/-- The unit vector `e₂ = (0, 0, 1)`. -/
def e₂ : Ten1 3 := ![0, 0, 1]

theorem eq_diag3_of_kron {B : Ten2 3} {ν : Fin 3 → ℝ} (h : ∀ i j, B i j = kron i j * ν j) :
    B = diag3 (ν 0) (ν 1) (ν 2) := by
  funext i j
  rw [h]
  fin_cases i <;> fin_cases j <;> simp [kron, diag3]

theorem trace_diag3 (a b c : ℝ) : ∑ i, diag3 a b c i i = a + b + c := by
  simp [diag3, Fin.sum_univ_three]

theorem sq2_diag3 (a b c : ℝ) : sq2 (diag3 a b c) = a ^ 2 + b ^ 2 + c ^ 2 := by
  simp [sq2, diag3, Fin.sum_univ_three]

/-- **Eigenframe with a prescribed eigenvector.** If `A` is symmetric, `A p = λ p` and
`|p| = 1`, there is an orthogonal `O` with `O A Oᵀ = diag(μ₀, μ₁, λ)` and `O p = e₂`. -/
theorem exists_orth_diag_of_eigen {A : Ten2 3} {p : Ten1 3} {lam : ℝ} (hA : IsSymm2 A)
    (hp : sq1 p = 1) (hAp : ∀ i, ∑ j, A i j * p j = lam * p i) :
    ∃ O : Ten2 3, IsOrth O ∧ ∃ μ₀ μ₁ : ℝ,
      act2 O A = diag3 μ₀ μ₁ lam ∧ act1 O p = e₂ := by
  obtain ⟨v, μ, hvv, hvp, hev⟩ := exists_eigenframe hA hp hAp
  have hpp : ∑ j, p j * p j = 1 := by rw [← hp, sq1_eq_dot, dot]
  have hpv : ∀ i, ∑ j, p j * v i j = 0 := fun i ↦ by
    rw [← hvp i]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  let O : Ten2 3 := ![v 0, v 1, p]
  have hrows : ∀ i j, ∑ k, O i k * O j k = kron i j := fun i j ↦ by
    fin_cases i <;> fin_cases j <;>
      simp [O, kron, hvv, hvp, hpv, hpp]
  have hev' : ∀ j a, ∑ b, A a b * O j b = ![μ 0, μ 1, lam] j * O j a := fun j a ↦ by
    fin_cases j
    · exact hev 0 a
    · exact hev 1 a
    · exact hAp a
  refine ⟨O, isOrth_of_rows hrows, μ 0, μ 1, ?_, ?_⟩
  · exact eq_diag3_of_kron (act2_eq_of_eigen hrows hev')
  · funext i
    fin_cases i <;> simp [act1, O, e₂, hvp, hpp]

end CertThree

open CertThree

/-! ### Invariance of the explicit polynomials -/

/-- `interiorPolyThree` written with the pairings `⟨·,·⟩`, the dot product and the linear maps
`coeffUDirLin`, `coeffMDirLin`. -/
theorem interiorPolyThree_eq (A : Ten2 3) (X : Ten3 3) (p : Ten1 3) (g w z : ℝ) (ℓ : Ten1 3) :
    interiorPolyThree A X p g w z ℓ =
      z ^ 2 * (3 * frob (coeffU A p) A - 1)
        + (∑ l, frob (coeffUDirLin A p (dirOf X A g w z l)) (X l)
          + 4 / 25 * dot (qVec X A) (contr3 X (coeffU A p)))
        + w * (∑ l, coeffMDirLin A p (dirOf X A g w z l) l
          + 54 / 25 * dot (qVec X A) (coeffM A p))
        + sq1 ℓ - 29 / 25 * dot (qVec X A) ℓ := by
  have hG : ∑ l, ∑ j, ∑ k,
      (coeffUDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
          (fun a ↦ w * A l a - g * z * kron l a) j k
        + 4 / 25 * qVec X A l * coeffU A p j k) * X l j k
      = ∑ l, frob (coeffUDirLin A p (dirOf X A g w z l)) (X l)
        + 4 / 25 * dot (qVec X A) (contr3 X (coeffU A p)) := by
    simp only [add_mul, Finset.sum_add_distrib, dot, contr3, frob, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun j _ ↦
      Finset.sum_congr rfl fun k _ ↦ by ring
  have hM : ∑ l, (coeffMDir A p (fun a b ↦ X l a b - qVec X A l * A a b)
          (fun a ↦ w * A l a - g * z * kron l a) l
        + 54 / 25 * qVec X A l * coeffM A p l)
      = ∑ l, coeffMDirLin A p (dirOf X A g w z l) l
        + 54 / 25 * dot (qVec X A) (coeffM A p) := by
    simp only [Finset.sum_add_distrib, dot, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  have hF : ∑ l, 29 / 25 * qVec X A l * ℓ l = 29 / 25 * dot (qVec X A) ℓ := by
    simp only [dot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  rw [interiorPolyThree, hG, hM, hF]
  rfl

/-- **Orthogonal invariance of the interior polynomial.** -/
theorem interiorPolyThree_act {O : Ten2 3} (hO : IsOrth O) (A : Ten2 3) (X : Ten3 3)
    (p : Ten1 3) (g w z : ℝ) (ℓ : Ten1 3) :
    interiorPolyThree (act2 O A) (act3 O X) (act1 O p) g w z (act1 O ℓ)
      = interiorPolyThree A X p g w z ℓ := by
  have hG : ∑ l, frob (coeffUDirLin (act2 O A) (act1 O p) (dirOf (act3 O X) (act2 O A) g w z l))
      (act3 O X l) = ∑ l, frob (coeffUDirLin A p (dirOf X A g w z l)) (X l) := by
    simp only [dirOf_act hO, act3_slice]
    exact sum_frob_linear_act hO _ _ (coeffUDirLin_act hO A p) _ _
  have hM : ∑ l, coeffMDirLin (act2 O A) (act1 O p) (dirOf (act3 O X) (act2 O A) g w z l) l
      = ∑ l, coeffMDirLin A p (dirOf X A g w z l) l := by
    simp only [dirOf_act hO]
    exact sum_trace_linear_act hO _ _ (coeffMDirLin_act hO A p) _
  rw [interiorPolyThree_eq, interiorPolyThree_eq, hG, hM, coeffU_act hO, coeffM_act hO,
    qVec_act hO, frob_act2 hO, contr3_act hO, dot_act1 hO, dot_act1 hO, dot_act1 hO,
    sq1_act1 hO]

/-- `boundaryPolyThree` written with the pairing `⟨·,·⟩` and the dot product. -/
theorem boundaryPolyThree_eq (A : Ten2 3) (p : Ten1 3) (lam : ℝ) :
    boundaryPolyThree A p lam
      = -lam + frob (coeffU A p) (lam • A - matMul A A + outer p p) + dot p (coeffM A p) := rfl

/-- **Orthogonal invariance of the boundary polynomial.** -/
theorem boundaryPolyThree_act {O : Ten2 3} (hO : IsOrth O) (A : Ten2 3) (p : Ten1 3)
    (lam : ℝ) :
    boundaryPolyThree (act2 O A) (act1 O p) lam = boundaryPolyThree A p lam := by
  have h : lam • act2 O A - matMul (act2 O A) (act2 O A) + outer (act1 O p) (act1 O p)
      = act2 O (lam • A - matMul A A + outer p p) := by
    rw [act2_add, act2_sub, act2_smul, matMul_act hO, act2_outer]
  rw [boundaryPolyThree_eq, boundaryPolyThree_eq, h, coeffU_act hO, coeffM_act hO, frob_act2 hO,
    dot_act1 hO]

/-! ### The reductions -/

/-- **Reduction of the interior inequality to diagonal `A`.** If the interior inequality holds
for `A = diag(α₀, α₁, −α₀−α₁)` with `α₀² + α₁² + (α₀+α₁)² = 1`, it holds for every symmetric
trace-free `A` with `|A| = 1`. -/
theorem certThree_interior_of_diag
    (H : ∀ α₀ α₁ : ℝ, α₀ ^ 2 + α₁ ^ 2 + (α₀ + α₁) ^ 2 = 1 → ∀ X p g w z ℓ, IsSTF3 X →
      g ^ 2 + sq1 p ≤ 1 →
        1 / 50 * (z ^ 2 + sq1 ℓ) ≤ interiorPolyThree (diag3 α₀ α₁ (-α₀ - α₁)) X p g w z ℓ) :
    ∀ A X p g w z ℓ, IsSTF2 A → sq2 A = 1 → IsSTF3 X → g ^ 2 + sq1 p ≤ 1 →
      1 / 50 * (z ^ 2 + sq1 ℓ) ≤ interiorPolyThree A X p g w z ℓ := by
  intro A X p g w z ℓ hA hA1 hX hpg
  obtain ⟨O, hO, ν, hν⟩ := exists_orth_diag hA.1
  have hD := eq_diag3_of_kron hν
  have htr : ν 0 + ν 1 + ν 2 = 0 := by
    rw [← trace_diag3, ← hD, trace_act2 hO, hA.2]
  have hsq : ν 0 ^ 2 + ν 1 ^ 2 + ν 2 ^ 2 = 1 := by
    rw [← sq2_diag3, ← hD, sq2_act2 hO, hA1]
  have h2 : ν 2 = -ν 0 - ν 1 := by linarith
  rw [← interiorPolyThree_act hO, hD, h2, ← sq1_act1 hO ℓ]
  refine H (ν 0) (ν 1) ?_ _ _ _ _ _ _ (isSTF3_act3 hO hX) (by rwa [sq1_act1 hO])
  rw [h2] at hsq
  linarith

/-- **Reduction of the boundary inequality to diagonal `A` and `p = e₂`.** If the boundary
inequality holds for `A = diag(x₀, x₁, λ)`, `p = e₂` with `x₀ + x₁ + λ = 0`,
`x₀² + x₁² + λ² = 1` and `λ < 0`, it holds for every symmetric trace-free `A` with `|A| = 1` and
every unit eigenvector `p` of `A` with eigenvalue `λ < 0`. -/
theorem certThree_boundary_of_diag
    (H : ∀ x₀ x₁ lam : ℝ, x₀ + x₁ + lam = 0 → x₀ ^ 2 + x₁ ^ 2 + lam ^ 2 = 1 → lam < 0 →
      1 / 100 ≤ boundaryPolyThree (diag3 x₀ x₁ lam) e₂ lam) :
    ∀ A p (lam : ℝ), IsSTF2 A → sq2 A = 1 → sq1 p = 1 →
      (∀ i, ∑ j, A i j * p j = lam * p i) → lam < 0 → 1 / 100 ≤ boundaryPolyThree A p lam := by
  intro A p lam hA hA1 hp hAp hlam
  obtain ⟨O, hO, μ₀, μ₁, hD, hOp⟩ := exists_orth_diag_of_eigen hA.1 hp hAp
  have htr : μ₀ + μ₁ + lam = 0 := by
    rw [← trace_diag3, ← hD, trace_act2 hO, hA.2]
  have hsq : μ₀ ^ 2 + μ₁ ^ 2 + lam ^ 2 = 1 := by
    rw [← sq2_diag3, ← hD, sq2_act2 hO, hA1]
  rw [← boundaryPolyThree_act hO, hD, hOp]
  exact H μ₀ μ₁ lam htr hsq hlam


/-- The certificate properties of `certThreeCoeffs` with `ε = 1/50`, `δ = 1/100` follow from the
interior inequality at diagonal `A` and the boundary inequality at diagonal `A` and `p = e₂`. -/
theorem certThree_holds_of_diag
    (hI : ∀ α₀ α₁ : ℝ, α₀ ^ 2 + α₁ ^ 2 + (α₀ + α₁) ^ 2 = 1 → ∀ X p g w z ℓ, IsSTF3 X →
      g ^ 2 + sq1 p ≤ 1 →
        1 / 50 * (z ^ 2 + sq1 ℓ) ≤ interiorPolyThree (diag3 α₀ α₁ (-α₀ - α₁)) X p g w z ℓ)
    (hB : ∀ x₀ x₁ lam : ℝ, x₀ + x₁ + lam = 0 → x₀ ^ 2 + x₁ ^ 2 + lam ^ 2 = 1 → lam < 0 →
      1 / 100 ≤ boundaryPolyThree (diag3 x₀ x₁ lam) e₂ lam) :
    CertificateHolds 3 (1 / 50) (1 / 100) certThreeCoeffs :=
  certThree_holds_of (certThree_interior_of_diag hI) (certThree_boundary_of_diag hB)

end OnePhaseDimension.Gen
