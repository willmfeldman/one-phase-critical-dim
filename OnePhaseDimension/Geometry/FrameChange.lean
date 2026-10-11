/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.Jets
public import OnePhaseDimension.Statements.CertificateGen

/-!
# Change of tangent frame

Let `y ∈ ℝⁿ` be a unit vector and let `ι, ι' : ℝ^{n-1} → y^⊥` be two linear isometries, with frames
`τₐ = ι eₐ` and `σᵢ = ι' eᵢ`. The change-of-frame matrix `O_{ia} = ⟪σᵢ, τₐ⟫` is orthogonal,
`σᵢ = ∑ₐ O_{ia} τₐ` and `τₐ = ∑ᵢ O_{ia} σᵢ`. Tensors read off in the two frames are related by
`O`: for a `k`-linear form `M`, `M[σ_{i₁}, …, σ_{i_k}] = ∑ O_{i₁a₁} ⋯ O_{i_k a_k} M[τ_{a₁}, …]`.

Consequently, if `Φ` is an orthogonally equivariant vector-valued map of the data `(A, p, g)`, the
ambient vector `∑ᵢ Φ(A, p, g)ᵢ τᵢ` does not depend on the frame in which `A` and `p` are read
(`sum_smul_frameVec_equivariant`), and an invariant scalar map takes the same value in both frames
(`invariant_frame_eq`). This is what makes the ambient fields built from the certificate
coefficients well defined, independently of the frame chosen at each point.
-/

open Function
open scoped RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ} {y : E n} {ι ι' : E (n - 1) →ₗᵢ[ℝ] E n}

/-- Expansion of a vector of `y^⊥` in a frame of `y^⊥`: `v = ∑ᵢ ⟪τᵢ, v⟫ τᵢ`. -/
theorem eq_sum_inner_frameVec (hy : ‖y‖ = 1) (hι : ∀ v, ⟪ι v, y⟫ = 0) {v : E n}
    (hv : ⟪y, v⟫ = 0) : v = ∑ i, ⟪frameVec ι i, v⟫ • frameVec ι i := by
  have h := (adaptedBasis hy hι).sum_repr' v
  rw [Fintype.sum_option] at h
  simp only [adaptedBasis_apply, adaptedVec_none, adaptedVec_some, hv, zero_smul,
    zero_add] at h
  exact h.symm

/-- The change-of-frame matrix `O_{ia} = ⟪σᵢ, τₐ⟫` from the frame of `ι` to the frame of `ι'`. -/
def frameChange (ι ι' : E (n - 1) →ₗᵢ[ℝ] E n) (i a : Fin (n - 1)) : ℝ :=
  ⟪frameVec ι' i, frameVec ι a⟫

section

variable (hy : ‖y‖ = 1) (hι : ∀ v, ⟪ι v, y⟫ = 0) (hι' : ∀ v, ⟪ι' v, y⟫ = 0)
include hy hι hι'

/-- `σᵢ = ∑ₐ O_{ia} τₐ`. -/
theorem frameVec_eq_sum_frameChange (i : Fin (n - 1)) :
    frameVec ι' i = ∑ a, frameChange ι ι' i a • frameVec ι a := by
  have hv : ⟪y, frameVec ι' i⟫ = 0 := by rw [real_inner_comm]; exact hι' _
  conv_lhs => rw [eq_sum_inner_frameVec hy hι hv]
  simp only [frameChange, real_inner_comm (frameVec ι' i)]

/-- `τₐ = ∑ᵢ O_{ia} σᵢ`. -/
theorem frameVec_eq_sum_frameChange' (a : Fin (n - 1)) :
    frameVec ι a = ∑ i, frameChange ι ι' i a • frameVec ι' i := by
  have hv : ⟪y, frameVec ι a⟫ = 0 := by rw [real_inner_comm]; exact hι _
  conv_lhs => rw [eq_sum_inner_frameVec hy hι' hv]
  simp only [frameChange, real_inner_comm (frameVec ι a)]

/-- The change-of-frame matrix is orthogonal: `∑ₖ O_{ki} O_{kj} = δ_{ij}`. -/
theorem sum_frameChange_mul (i j : Fin (n - 1)) :
    ∑ k, frameChange ι ι' k i * frameChange ι ι' k j = if i = j then 1 else 0 := by
  rw [← inner_frameVec_frameVec ι i j]
  conv_rhs => rw [frameVec_eq_sum_frameChange' hy hι hι' i]
  simp only [sum_inner, real_inner_smul_left, frameChange]

/-- Reading a linear form in the new frame: `L(σᵢ) = ∑ₐ O_{ia} L(τₐ)`. -/
theorem apply_frameVec_frameChange (L : E n →L[ℝ] ℝ) (i : Fin (n - 1)) :
    L (frameVec ι' i) = ∑ a, frameChange ι ι' i a * L (frameVec ι a) := by
  rw [frameVec_eq_sum_frameChange hy hι hι' i, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- Reading a `k`-linear form in the new frame:
`M[σ_{i₁}, …, σ_{i_k}] = ∑_a O_{i₁a₁} ⋯ O_{i_k a_k} M[τ_{a₁}, …, τ_{a_k}]`. -/
theorem multilinear_frameVec_frameChange {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E n) ℝ) (idx : Fin k → Fin (n - 1)) :
    M (fun s ↦ frameVec ι' (idx s)) =
      ∑ a : Fin k → Fin (n - 1), (∏ s, frameChange ι ι' (idx s) (a s)) *
        M (fun s ↦ frameVec ι (a s)) := by
  simp_rw [frameVec_eq_sum_frameChange hy hι hι', M.map_sum, M.map_smul_univ, smul_eq_mul]

/-- Reading a bilinear form in the new frame:
`Q[σᵢ, σⱼ] = ∑ₐ ∑_b O_{ia} O_{jb} Q[τₐ, τ_b]`. -/
theorem bilinear_frameVec_frameChange
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E n) ℝ) (i j : Fin (n - 1)) :
    Q ![frameVec ι' i, frameVec ι' j] =
      ∑ a, ∑ b, frameChange ι ι' i a * frameChange ι ι' j b * Q ![frameVec ι a, frameVec ι b] := by
  have h1 : Q ![frameVec ι' i, frameVec ι' j] =
      ∑ a, frameChange ι ι' i a * Q ![frameVec ι a, frameVec ι' j] := by
    rw [frameVec_eq_sum_frameChange hy hι hι' i]
    exact cons_sum_smul_apply Q Finset.univ _ _ _
  have h2 : ∀ w : E n, Q ![w, frameVec ι' j] =
      ∑ b, frameChange ι ι' j b * Q ![w, frameVec ι b] := by
    intro w
    rw [frameVec_eq_sum_frameChange hy hι hι' j]
    exact cons_sum_smul_apply (Q.curryLeft w) Finset.univ _ _ ![]
  rw [h1]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  ring

/-- **Frame independence of the ambient vector.** If `z'ᵢ = ∑ₐ O_{ia} zₐ`, then
`∑ᵢ z'ᵢ σᵢ = ∑ₐ zₐ τₐ`. -/
theorem sum_smul_frameVec_eq (z z' : Fin (n - 1) → ℝ)
    (hz : ∀ i, z' i = ∑ a, frameChange ι ι' i a * z a) :
    ∑ i, z' i • frameVec ι' i = ∑ a, z a • frameVec ι a := by
  simp_rw [hz, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [frameVec_eq_sum_frameChange' hy hι hι' a, Finset.smul_sum]
  simp only [smul_comm (z a)]

end

/-! ### Certificate data read in a frame -/

section Data

/-- The change-of-frame matrix is orthogonal in the sense of the certificate statement. -/
theorem isOrth_frameChange (hy : ‖y‖ = 1) (hι : ∀ v, ⟪ι v, y⟫ = 0)
    (hι' : ∀ v, ⟪ι' v, y⟫ = 0) : Gen.IsOrth (frameChange ι ι') := fun i j ↦
  sum_frameChange_mul hy hι hι' i j

/-- The data `(A, p)` read off a bilinear form `Q` and a linear form `L` in the frame of `ι`. -/
def frameData (ι : E (n - 1) →ₗᵢ[ℝ] E n)
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E n) ℝ) (L : E n →L[ℝ] ℝ) :
    Gen.Ten2 (n - 1) × Gen.Ten1 (n - 1) :=
  (fun i j ↦ Q ![frameVec ι i, frameVec ι j], fun i ↦ L (frameVec ι i))

theorem frameData_frameChange (hy : ‖y‖ = 1) (hι : ∀ v, ⟪ι v, y⟫ = 0)
    (hι' : ∀ v, ⟪ι' v, y⟫ = 0) (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E n) ℝ)
    (L : E n →L[ℝ] ℝ) :
    frameData ι' Q L =
      (Gen.act2 (frameChange ι ι') (frameData ι Q L).1,
        Gen.act1 (frameChange ι ι') (frameData ι Q L).2) := by
  refine Prod.ext (funext fun i ↦ funext fun j ↦ ?_) (funext fun i ↦ ?_)
  · exact bilinear_frameVec_frameChange hy hι hι' Q i j
  · exact apply_frameVec_frameChange hy hι hι' L i

/-- **Frame independence for equivariant maps.** For an orthogonally equivariant
`Φ : (A, p, g) ↦ Φ(A, p, g) ∈ ℝ^{n-1}`, the ambient vector `∑ᵢ Φ(A, p, g)ᵢ τᵢ`, with `A, p` read
off `Q, L` in the frame `τ`, is the same for every frame of `y^⊥`. -/
theorem sum_smul_frameVec_equivariant (hy : ‖y‖ = 1) (hι : ∀ v, ⟪ι v, y⟫ = 0)
    (hι' : ∀ v, ⟪ι' v, y⟫ = 0)
    (Φ : Gen.Ten2 (n - 1) × Gen.Ten1 (n - 1) × ℝ → Gen.Ten1 (n - 1))
    (hΦ : ∀ O, Gen.IsOrth O → ∀ A p g,
      Φ (Gen.act2 O A, Gen.act1 O p, g) = Gen.act1 O (Φ (A, p, g)))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E n) ℝ) (L : E n →L[ℝ] ℝ) (g : ℝ) :
    ∑ i, Φ ((frameData ι' Q L).1, (frameData ι' Q L).2, g) i • frameVec ι' i =
      ∑ i, Φ ((frameData ι Q L).1, (frameData ι Q L).2, g) i • frameVec ι i := by
  refine sum_smul_frameVec_eq hy hι hι' _ _ fun i ↦ ?_
  rw [frameData_frameChange hy hι hι', hΦ _ (isOrth_frameChange hy hι hι')]
  rfl

/-- **Frame independence for invariant maps.** -/
theorem invariant_frame_eq (hy : ‖y‖ = 1) (hι : ∀ v, ⟪ι v, y⟫ = 0)
    (hι' : ∀ v, ⟪ι' v, y⟫ = 0) {W : Type*} (f : Gen.Ten2 (n - 1) × Gen.Ten1 (n - 1) × ℝ → W)
    (hf : ∀ O, Gen.IsOrth O → ∀ A p g, f (Gen.act2 O A, Gen.act1 O p, g) = f (A, p, g))
    (Q : ContinuousMultilinearMap ℝ (fun _ : Fin 2 ↦ E n) ℝ) (L : E n →L[ℝ] ℝ) (g : ℝ) :
    f ((frameData ι' Q L).1, (frameData ι' Q L).2, g) =
      f ((frameData ι Q L).1, (frameData ι Q L).2, g) := by
  rw [frameData_frameChange hy hι hι', hf _ (isOrth_frameChange hy hι hι')]

end Data

end OnePhaseDimension
