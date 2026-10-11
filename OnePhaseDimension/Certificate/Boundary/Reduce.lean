/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Boundary.DiagBound
public import OnePhaseDimension.Flux.Algebra
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Reduction of the boundary inequality to diagonal data

* `boundaryExpr_act`: the boundary expression `𝓢` of orthogonally equivariant coefficients is
  invariant under `(A, p) ↦ (O A Oᵀ, O p)`; it is a full contraction of equivariant tensors.
* `exists_eigenframe`: for a symmetric `A` with a unit eigenvector `p`, there are orthonormal
  eigenvectors `v₁, …, v₄` of `A` spanning `p^⊥` (the spectral theorem for the restriction of
  `A` to the invariant subspace `p^⊥`).
* `exists_orth_diag`: with `O` the orthogonal matrix of rows `v₁, …, v₄, p`, `O A Oᵀ` is
  `diag(x₁, …, x₄, λ)` and `O p = e₅`; for trace-free `A`, `λ = -∑ xᵢ`.
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate.Boundary

open Finset
open scoped Matrix

/-! ### Invariance of the boundary expression -/

section Invariance

variable {O : Ten2} (hO : IsOrth5 O)

theorem of_bdryS0 (A : Ten2) (lam : ℝ) :
    Matrix.of (Coeffs.bdryS0 A lam) = lam • Matrix.of A - Matrix.of A * Matrix.of A := by
  ext i j
  simp [Coeffs.bdryS0, Matrix.mul_apply]

include hO in
theorem bdryS0_act (A : Ten2) (lam : ℝ) :
    Coeffs.bdryS0 (act2 O A) lam = act2 O (Coeffs.bdryS0 A lam) := by
  have h := transpose_mul_self_of_isOrth5 hO
  apply Matrix.of.symm.injective
  change Matrix.of _ = Matrix.of _
  rw [of_bdryS0, act2_eq, act2_eq, of_bdryS0]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [show (omat O)ᵀ * (omat O * (Matrix.of A * (omat O)ᵀ)) = Matrix.of A * (omat O)ᵀ by
    rw [← Matrix.mul_assoc, h, Matrix.one_mul]]

theorem pp_act (p : Ten1) :
    (fun j k => act1 O p j * act1 O p k) = act2 O (fun j k => p j * p k) := by
  funext j k
  simp only [act1, act2, sum_mul_sum]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

theorem act2_add (X Y : Ten2) : act2 O (fun j k => X j k + Y j k) =
    fun j k => act2 O X j k + act2 O Y j k := by
  funext j k
  simp only [act2, mul_add, sum_add_distrib]

theorem act3_add (X Y : Ten3) : act3 O (fun i j k => X i j k + Y i j k) =
    fun i j k => act3 O X i j k + act3 O Y i j k := by
  funext i j k
  simp only [act3, mul_add, sum_add_distrib]

theorem act3_vec_ten2 (u : Ten1) (S : Ten2) :
    act3 O (fun i j k => u i * S j k) = fun i j k => act1 O u i * act2 O S j k := by
  funext i j k
  simp only [act3, act1, act2]
  rw [Finset.sum_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  exact sum_congr rfl fun c _ => by ring

theorem act3_cyc (Y : Ten3) :
    act3 O (fun i j k => Y j k i) = fun i j k => act3 O Y j k i := by
  funext i j k
  simp only [act3]
  rw [← sum3_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ => by ring

theorem act3_vec_ten2_apply (u : Ten1) (S : Ten2) (i j k : Fin 5) :
    act3 O (fun i j k => u i * S j k) i j k = act1 O u i * act2 O S j k :=
  congrFun (congrFun (congrFun (act3_vec_ten2 u S) i) j) k

theorem act3_cyc_apply (Y : Ten3) (i j k : Fin 5) :
    act3 O (fun i j k => Y j k i) i j k = act3 O Y j k i :=
  congrFun (congrFun (congrFun (act3_cyc Y) i) j) k

theorem act3_vec_ten2_apply₁ (u : Ten1) (S : Ten2) (i j k : Fin 5) :
    act3 O (fun i j k => u j * S k i) i j k = act1 O u j * act2 O S k i :=
  (act3_cyc_apply (fun i j k => u i * S j k) i j k).trans (act3_vec_ten2_apply u S j k i)

theorem act3_vec_ten2_apply₂ (u : Ten1) (S : Ten2) (i j k : Fin 5) :
    act3 O (fun i j k => u k * S i j) i j k = act1 O u k * act2 O S i j :=
  (act3_cyc_apply (fun i j k => u j * S k i) i j k).trans (act3_vec_ten2_apply₁ u S j k i)

theorem act3_add4_apply (W₁ W₂ W₃ W₄ : Ten3) (i j k : Fin 5) :
    act3 O (fun i j k => W₁ i j k + W₂ i j k + W₃ i j k + W₄ i j k) i j k =
      act3 O W₁ i j k + act3 O W₂ i j k + act3 O W₃ i j k + act3 O W₄ i j k := by
  simp only [act3, mul_add, sum_add_distrib]

include hO in
theorem bdryV_act (A : Ten2) (p : Ten1) (lam : ℝ) :
    Coeffs.bdryV (act2 O A) (act1 O p) lam = act3 O (Coeffs.bdryV A p lam) := by
  funext i j k
  have hpp := congrFun (congrFun (pp_act (O := O) p) j) k
  have h4 := act3_add4_apply (O := O) (fun i j k => p i * Coeffs.bdryS0 A lam j k)
    (fun i j k => p j * Coeffs.bdryS0 A lam k i) (fun i j k => p k * Coeffs.bdryS0 A lam i j)
    (fun i j k => p i * (fun j k => p j * p k) j k) i j k
  rw [act3_vec_ten2_apply, act3_vec_ten2_apply₁, act3_vec_ten2_apply₂, act3_vec_ten2_apply,
    ← hpp, ← bdryS0_act hO] at h4
  have hV : Coeffs.bdryV A p lam = fun i j k => p i * Coeffs.bdryS0 A lam j k +
      p j * Coeffs.bdryS0 A lam k i + p k * Coeffs.bdryS0 A lam i j +
      p i * (fun j k => p j * p k) j k := by
    funext i j k
    simp only [Coeffs.bdryV]
    ring
  rw [hV, h4]
  simp only [Coeffs.bdryV]
  ring

/-- The `C` term of `𝓢` as `p_l (K_{lijk} V_{ijk} - K_{iljk} V_{ijk})`. -/
theorem sum_C_mul (c : Coeffs) (x : Ten2 × Ten1 × ℝ) (p : Ten1) (V : Ten3) :
    ∑ l, ∑ i, ∑ j, ∑ k, c.C x l i j k * p l * V i j k =
      ∑ l, p l * ((fun a => ∑ i, ∑ j, ∑ k, c.K x a i j k * V i j k) l -
        (fun b => ∑ i, ∑ j, ∑ k, c.K x i b j k * V i j k) l) := by
  simp only [Coeffs.C, mul_sub, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun l _ => sum_congr rfl fun i _ => sum_congr rfl fun j _ =>
    sum_congr rfl fun k _ => by ring

include hO in
/-- **Orthogonal invariance of `𝓢`** for equivariant coefficients. -/
theorem boundaryExpr_act (c : Coeffs)
    (hf : ∀ A p, c.f (act2 O A, act1 O p, 0) = c.f (A, p, 0))
    (hU : ∀ A p, c.U (act2 O A, act1 O p, 0) = act2 O (c.U (A, p, 0)))
    (hK : ∀ A p, c.K (act2 O A, act1 O p, 0) = act4 O (c.K (A, p, 0)))
    (hM : ∀ A p, c.M (act2 O A, act1 O p, 0) = act1 O (c.M (A, p, 0)))
    (A : Ten2) (p : Ten1) (lam : ℝ) :
    c.boundaryExpr (act2 O A) (act1 O p) lam = c.boundaryExpr A p lam := by
  have hS : (fun j k => Coeffs.bdryS0 (act2 O A) lam j k + act1 O p j * act1 O p k) =
      act2 O (fun j k => Coeffs.bdryS0 A lam j k + p j * p k) := by
    rw [act2_add, bdryS0_act hO, ← pp_act]
  have hUterm : ∑ j, ∑ k, c.U (act2 O A, act1 O p, 0) j k *
      (Coeffs.bdryS0 (act2 O A) lam j k + act1 O p j * act1 O p k) =
      ∑ j, ∑ k, c.U (A, p, 0) j k * (Coeffs.bdryS0 A lam j k + p j * p k) := by
    have := congrFun₂ hS
    simp only [this, hU]
    exact sum_act2_mul_act2 hO _ _
  have hCterm : ∑ l, ∑ i, ∑ j, ∑ k, c.C (act2 O A, act1 O p, 0) l i j k * act1 O p l *
      Coeffs.bdryV (act2 O A) (act1 O p) lam i j k =
      ∑ l, ∑ i, ∑ j, ∑ k, c.C (A, p, 0) l i j k * p l * Coeffs.bdryV A p lam i j k := by
    rw [sum_C_mul, sum_C_mul, bdryV_act hO, hK]
    simp only [sum_act4_mul_act3 hO, sum_act4_swap_mul_act3 hO]
    have : ∀ (F G : Ten1) (l : Fin 5), act1 O F l - act1 O G l =
        act1 O (fun a => F a - G a) l := fun F G l => by
      simp only [act1, mul_sub, sum_sub_distrib]
    simp only [this]
    exact sum_act1_mul_act1 hO _ _
  have hMterm : ∑ l, act1 O p l * c.M (act2 O A, act1 O p, 0) l = ∑ l, p l * c.M (A, p, 0) l := by
    rw [hM]; exact sum_act1_mul_act1 hO _ _
  simp only [Coeffs.boundaryExpr, hf, hUterm, hCterm, hMterm]

end Invariance

/-! ### An orthonormal eigenframe containing `p` -/

/-- The linear map of a two-tensor on `ℝ⁵`. -/
def ten2Lin (A : Ten2) : EuclideanSpace ℝ (Fin 5) →ₗ[ℝ] EuclideanSpace ℝ (Fin 5) :=
  Matrix.toEuclideanLin (Matrix.of A)

theorem ten2Lin_apply (A : Ten2) (v : EuclideanSpace ℝ (Fin 5)) (i : Fin 5) :
    ten2Lin A v i = ∑ j, A i j * v j := by
  simp [ten2Lin, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]

theorem inner_euclidean_five (v w : EuclideanSpace ℝ (Fin 5)) :
    inner ℝ v w = ∑ j, v j * w j := by
  simp [PiLp.inner_apply, mul_comm]

theorem ten2Lin_isSymmetric {A : Ten2} (hA : IsSymm2 A) : (ten2Lin A).IsSymmetric := fun v w => by
  rw [inner_euclidean_five, inner_euclidean_five]
  simp only [ten2Lin_apply, sum_mul, mul_sum]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hA j i]; ring

/-- **Eigenframe.** A symmetric `A` with a unit eigenvector `p` has four orthonormal eigenvectors
orthogonal to `p` (spectral theorem on the invariant subspace `p^⊥`). -/
theorem exists_eigenframe {A : Ten2} {p : Ten1} {lam : ℝ} (hA : IsSymm2 A) (hp : sq1 p = 1)
    (hAp : ∀ i, ∑ j, A i j * p j = lam * p i) :
    ∃ (v : Fin 4 → Fin 5 → ℝ) (μ : Fin 4 → ℝ),
      (∀ i k, ∑ j, v i j * v k j = if i = k then 1 else 0) ∧ (∀ i, ∑ j, v i j * p j = 0) ∧
      (∀ i j, ∑ b, A j b * v i b = μ i * v i j) := by
  have hTs := ten2Lin_isSymmetric hA
  have hp0 : (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 5)) ≠ 0 := by
    intro h
    have h' : ∀ j, p j = 0 := fun j => by
      simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 5) => v j) h
    simp [sq1, h'] at hp
  have hK : ∀ v ∈ (ℝ ∙ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 5)))ᗮ,
      ten2Lin A v ∈ (ℝ ∙ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 5)))ᗮ := fun v hv => by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hv ⊢
    rw [← hTs, inner_euclidean_five]
    rw [inner_euclidean_five] at hv
    simp only [ten2Lin_apply]
    have : ∀ j, ∑ b, A j b * (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 5)) b =
        lam * (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 5)) j := hAp
    simp only [this, mul_assoc, ← mul_sum, hv, mul_zero]
  have hTK := hTs.restrict_invariant hK
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 5)) = 4 + 1) := ⟨by simp⟩
  have hn : Module.finrank ℝ (ℝ ∙ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 5)))ᗮ = 4 :=
    Submodule.finrank_orthogonal_span_singleton hp0
  refine ⟨fun i j => ((hTK.eigenvectorBasis hn i : (ℝ ∙ (WithLp.toLp 2 p :
    EuclideanSpace ℝ (Fin 5)))ᗮ) : EuclideanSpace ℝ (Fin 5)) j, hTK.eigenvalues hn, ?_, ?_, ?_⟩
  · intro i k
    have h := (hTK.eigenvectorBasis hn).orthonormal
    rw [orthonormal_iff_ite] at h
    rw [← h i k, Submodule.coe_inner, inner_euclidean_five]
  · intro i
    have h := (hTK.eigenvectorBasis hn i).2
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_euclidean_five] at h
    rw [← h]
    exact sum_congr rfl fun j _ => mul_comm _ _
  · intro i j
    have h := hTK.apply_eigenvectorBasis hn i
    have h2 := congrArg (fun w : (ℝ ∙ (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin 5)))ᗮ =>
      (w : EuclideanSpace ℝ (Fin 5)) j) h
    simp only [LinearMap.coe_restrict_apply, ten2Lin_apply] at h2
    rw [h2]
    simp

/-! ### The orthogonal matrix of the frame -/

/-- The matrix with rows `v₁, …, v₄, p`. -/
def frameMat (v : Fin 4 → Fin 5 → ℝ) (p : Ten1) : Ten2 :=
  fun r j => if h : r.val < 4 then v ⟨r.val, h⟩ j else p j

theorem frameMat_four (v : Fin 4 → Fin 5 → ℝ) (p : Ten1) (j : Fin 5) :
    frameMat v p 4 j = p j := by
  simp [frameMat]

theorem frameMat_lt (v : Fin 4 → Fin 5 → ℝ) (p : Ten1) (i : Fin 4) (j : Fin 5) :
    frameMat v p i.castSucc j = v i j := by
  simp [frameMat]

/-- Every index of `Fin 5` is `i.castSucc` for some `i : Fin 4`, or `4`. -/
theorem fin5_cases (r : Fin 5) : (∃ i : Fin 4, r = i.castSucc) ∨ r = 4 := by
  rcases Fin.eq_castSucc_or_eq_last r with ⟨i, rfl⟩ | rfl
  · exact Or.inl ⟨i, rfl⟩
  · exact Or.inr rfl

end OnePhaseDimension.Certificate.Boundary
