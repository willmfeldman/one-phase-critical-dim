/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Boundary.Reduce

/-!
# The boundary inequality

For the coefficient maps of the first table (`tableCoeffs`), every symmetric trace-free `A` with
`|A|² = 1` and every unit eigenvector `p` of `A` with eigenvalue `λ < 0` satisfy

  `𝓢 = -λ f + U_{jk}(S₀ + p ⊗ p)_{jk} + C_{lijk} p_l V_{ijk} + p_l M_l ≥ δ*`

(`boundary_inequality`), in the form required by the boundary field of
`OnePhaseDimension.CertificateHolds`.

The proof follows the source: by orthogonal invariance we move to the frame of rows
`v₁, …, v₄, p` (orthonormal eigenvectors of `A` on `p^⊥`, then `p`), where `p = e₅` and
`A = diag(x₁, …, x₄, λ)` with `λ = -∑ xᵢ`, `R(x) = |A|² = 1` and `∑ xᵢ = -λ > 0`; there the
inequality is `boundaryExpr_diag_ge`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate

open Finset Boundary Boundary.Poly4
open scoped Matrix

namespace Boundary

section Frame

variable {v : Fin 4 → Fin 5 → ℝ} {p : Ten1}
  (hv : ∀ i k, ∑ j, v i j * v k j = if i = k then 1 else 0) (hvp : ∀ i, ∑ j, v i j * p j = 0)
  (hp : sq1 p = 1)

theorem castSucc_ne_four (i : Fin 4) : (i.castSucc : Fin 5) ≠ 4 :=
  (Fin.castSucc_lt_last i).ne

include hv hvp hp in
/-- The rows of the frame matrix are orthonormal. -/
theorem frameMat_rows (r s : Fin 5) : ∑ j, frameMat v p r j * frameMat v p s j = kron r s := by
  have hpp : ∑ j, p j * p j = 1 := by simpa [sq1, sq] using hp
  have hpv : ∀ k, ∑ j, p j * v k j = 0 := fun k => by
    rw [← hvp k]; exact sum_congr rfl fun j _ => mul_comm _ _
  rcases fin5_cases r with ⟨i, rfl⟩ | rfl <;> rcases fin5_cases s with ⟨k, rfl⟩ | rfl
  · simp only [frameMat_lt, hv, kron, Fin.castSucc_inj]
  · simp only [frameMat_lt, frameMat_four, hvp, kron, castSucc_ne_four, ite_false]
  · simp only [frameMat_lt, frameMat_four, hpv, kron, (castSucc_ne_four k).symm, ite_false]
  · simp only [frameMat_four, hpp, kron, ite_true]

include hv hvp hp in
/-- The frame matrix is orthogonal. -/
theorem isOrth5_frameMat : IsOrth5 (frameMat v p) := by
  have h1 : omat (frameMat v p) * (omat (frameMat v p))ᵀ = 1 := by
    ext r s
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [kron] using frameMat_rows hv hvp hp r s
  have h2 := mul_eq_one_comm.mp h1
  intro i j
  have := congrFun (congrFun h2 i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [kron] using this

include hvp hp in
/-- `O p = e₅`. -/
theorem act1_frameMat : act1 (frameMat v p) p = e5 := by
  have hpp : ∑ j, p j * p j = 1 := by simpa [sq1, sq] using hp
  funext r
  rcases fin5_cases r with ⟨i, rfl⟩ | rfl
  · simp only [act1, frameMat_lt, hvp, e5, castSucc_ne_four, ite_false]
  · simp only [act1, frameMat_four, hpp, e5, ite_true]

/-- The eigenvalue of the row `r` of the frame. -/
def frameEig (μ : Fin 4 → ℝ) (lam : ℝ) (r : Fin 5) : ℝ :=
  if h : r.val < 4 then μ ⟨r.val, h⟩ else lam

include hv hvp hp in
theorem act2_frameMat {A : Ten2} {μ : Fin 4 → ℝ} {lam : ℝ}
    (hAp : ∀ i, ∑ j, A i j * p j = lam * p i) (hve : ∀ i j, ∑ b, A j b * v i b = μ i * v i j)
    (r s : Fin 5) :
    act2 (frameMat v p) A r s = if r = s then frameEig μ lam r else 0 := by
  have heig : ∀ a, ∑ b, frameMat v p s b * A a b = frameEig μ lam s * frameMat v p s a :=
    fun a => by
      simp only [mul_comm (frameMat v p s _)]
      rcases fin5_cases s with ⟨i, rfl⟩ | rfl
      · simp only [frameMat_lt, hve, frameEig, Fin.val_castSucc, i.isLt, ↓reduceDIte]
      · simp only [frameMat_four, hAp, frameEig]; simp
  have : act2 (frameMat v p) A r s =
      frameEig μ lam s * ∑ a, frameMat v p r a * frameMat v p s a := by
    simp only [act2, mul_sum]
    refine sum_congr rfl fun a _ => ?_
    simp only [mul_assoc, ← mul_sum, heig]
    ring
  rw [this, frameMat_rows hv hvp hp, kron]
  split_ifs with h
  · rw [h, mul_one]
  · rw [mul_zero]

end Frame

theorem trace_act2 {O : Ten2} (hO : IsOrth5 O) (A : Ten2) :
    ∑ r, act2 O A r r = ∑ a, A a a := by
  simp only [act2]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  have : ∀ b, ∑ r, O r a * O r b * A a b = kron a b * A a b := fun b => by
    rw [← sum_mul, hO a b]
  simp only [this, kron, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

theorem sq2_diagA (x : Fin 4 → ℝ) : sq2 (diagA x) = rQuad x := by
  simp only [sq2, diagA, ite_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    sum_ite_eq, mem_univ, ite_true, rQuad]
  rw [Fin.sum_univ_castSucc]
  simp [dvec, Fin.val_castSucc]

/-- The coefficient maps of the first table are orthogonally equivariant. -/
theorem tableCoeffs_equiv {O : Ten2} (hO : IsOrth5 O) (A : Ten2) (p : Ten1) (g : ℝ) :
    tableCoeffs.f (act2 O A, act1 O p, g) = tableCoeffs.f (A, p, g) ∧
      tableCoeffs.U (act2 O A, act1 O p, g) = act2 O (tableCoeffs.U (A, p, g)) ∧
      tableCoeffs.K (act2 O A, act1 O p, g) = act4 O (tableCoeffs.K (A, p, g)) ∧
      tableCoeffs.M (act2 O A, act1 O p, g) = act1 O (tableCoeffs.M (A, p, g)) ∧
      tableCoeffs.P (act2 O A, act1 O p, g) = act1 O (tableCoeffs.P (A, p, g)) :=
  rowsCoeffs_equiv Data.rowsOfRank_famEntries_f Data.rowsOfRank_famEntries_U
    Data.rowsOfRank_famEntries_K Data.rowsOfRank_famEntries_M Data.rowsOfRank_famEntries_P O hO A p
    g

end Boundary

/-- **The boundary inequality** `𝓢 ≥ δ*` for the coefficient maps of the first table: for every
symmetric trace-free `A` with `|A|² = 1` and unit vector `p` with `Ap = λp`, `λ < 0`. -/
theorem boundary_inequality (A : Ten2) (p : Ten1) (lam : ℝ) (hA : IsSTF2 A) (hA1 : sq2 A = 1)
    (hp : sq1 p = 1) (hAp : ∀ i, ∑ j, A i j * p j = lam * p i) (hlam : lam < 0) :
    δStar ≤ tableCoeffs.boundaryExpr A p lam := by
  obtain ⟨v, μ, hv, hvp, hve⟩ := exists_eigenframe hA.1 hp hAp
  have hO := isOrth5_frameMat hv hvp hp
  have h2 := act2_frameMat hv hvp hp hAp hve
  -- the trace condition gives `λ = -∑ μᵢ`
  have hsum : ∑ i, μ i = -lam := by
    have h := trace_act2 hO A
    rw [hA.2] at h
    simp only [h2, ite_true] at h
    rw [Fin.sum_univ_castSucc] at h
    simp only [frameEig, Fin.val_castSucc, Fin.is_lt, ↓reduceDIte, Fin.val_last, lt_irrefl] at h
    linarith
  have hdiag : act2 (frameMat v p) A = diagA μ := by
    funext r s
    rw [h2, diagA]
    split_ifs with h
    · subst h
      rcases fin5_cases r with ⟨i, rfl⟩ | rfl
      · simp [frameEig, dvec]
      · simp [frameEig, dvec, hsum]
    · rfl
  have hR : rQuad μ = 1 := by rw [← sq2_diagA, ← hdiag, sq2_act2 hO, hA1]
  have h4 : dvec μ 4 = lam := by rw [dvec_four, hsum, neg_neg]
  have heq := boundaryExpr_act hO tableCoeffs (fun A p => (tableCoeffs_equiv hO A p 0).1)
    (fun A p => (tableCoeffs_equiv hO A p 0).2.1) (fun A p => (tableCoeffs_equiv hO A p 0).2.2.1)
    (fun A p => (tableCoeffs_equiv hO A p 0).2.2.2.1) A p lam
  rw [← heq, hdiag, act1_frameMat hvp hp, ← h4]
  exact boundaryExpr_diag_ge μ hR (by rw [hsum]; linarith)

end OnePhaseDimension.Certificate
