/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Statements.Certificate
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.MeanInequalities

/-!
# Tensor bounds for the certificate

Let `A` be a symmetric trace-free `5 × 5` matrix with `tr A² = 1`, and put `θ = 4/5`. We prove
the estimates of the lemma "tensor bounds" in the section "Bounds for scalar graphs" of the
2026-09-24 version:

* `sq1_pow_mulVec_le`: `|A^k v|² ≤ θ^k |v|²` (the operator bound `‖A‖² ≤ θ`, iterated);
* `sumSq_pow_succ_le`: `|A^{k+1}|² ≤ θ^k`;
* `trace_pow_sq_le`: `(tr A^{k+2})² ≤ θ^k`;
* `trace_cube_sq_le`: `(tr A³)² ≤ 9/20`;
* `sq1_contract_le_five_sevenths`: `|X:A|² ≤ (5/7)|X|²` for a symmetric trace-free `X`;
* `sq1_contract_pow_le`: `|X:A^{k+2}|² ≤ θ^{k+1} |X|²`;
* `mixed_pow_le`: `s^h t^b ≤ (h/(h+b))^h (b/(h+b))^b` for `s, t ≥ 0`, `s + t ≤ 1`.

The proofs diagonalize `A` by an orthogonal matrix (Mathlib's spectral theorem). The
eigenvalues `α` satisfy `∑ α = 0` and `∑ α² = 1`, hence `α_i² = (∑_{j ≠ i} α_j)² ≤ 4(1 − α_i²)`.

The cubic bound: the 2026-09-24 version maximizes `∑ α³` by Lagrange multipliers; we use instead
the inequality `∑ (α_i − M)(α_i + 1/(5M))² ≤ 0` with `M = √(4/5) ≥ α_i`, which expands to
`∑ α³ ≤ M − 1/(5M) = 3/(5M)`. The bound `5/7` follows the 2026-09-24 version: `|X:A|²` is the
pairing of `X` with the symmetric trace-free part `F` of `(X:A) ⊗ A`, and
`|F|² = |ζ|²/3 + (10/21)|Aζ|²` for `ζ = X:A`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate

open Matrix Finset

/-! ### Orthogonal diagonalization -/

/-- A real symmetric matrix is orthogonally diagonalizable. -/
theorem exists_orthogonal_diag {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}
    (hA : A.IsSymm) :
    ∃ (U : Matrix n n ℝ) (α : n → ℝ), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧ A = U * diagonal α * Uᵀ := by
  have hH : A.IsHermitian := Matrix.isHermitian_iff_isSymm.mpr hA
  refine ⟨hH.eigenvectorUnitary, hH.eigenvalues, ?_, ?_, ?_⟩
  · have := Unitary.coe_star_mul_self hH.eigenvectorUnitary
    simpa only [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using this
  · have := Unitary.coe_mul_star_self hH.eigenvectorUnitary
    simpa only [Unitary.coe_star, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
      using this
  · conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id, Function.id_comp]

theorem pow_eq_conj_diagonal {n : Type*} [Fintype n] [DecidableEq n] {A U : Matrix n n ℝ}
    {α : n → ℝ} (hU : Uᵀ * U = 1) (hA : A = U * diagonal α * Uᵀ) (k : ℕ) :
    A ^ k = U * diagonal (fun i => α i ^ k) * Uᵀ := by
  induction k with
  | zero =>
    simp only [pow_zero]
    rw [diagonal_one, Matrix.mul_one, mul_eq_one_comm.mp hU]
  | succ k ih =>
    rw [pow_succ, ih, hA]
    calc U * diagonal (fun i => α i ^ k) * Uᵀ * (U * diagonal α * Uᵀ)
        = U * (diagonal (fun i => α i ^ k) * (Uᵀ * U) * diagonal α) * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, Matrix.mul_one, diagonal_mul_diagonal]; simp only [pow_succ]

theorem trace_conj_diagonal {n : Type*} [Fintype n] [DecidableEq n] {U : Matrix n n ℝ}
    (hU : Uᵀ * U = 1) (α : n → ℝ) : (U * diagonal α * Uᵀ).trace = ∑ i, α i := by
  rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, trace_diagonal]

theorem sq1_eq_dotProduct (v : Fin 5 → ℝ) : sq1 v = v ⬝ᵥ v := by
  simp only [sq1, dotProduct, sq]

theorem sq1_mulVec_of_orth {U : Matrix (Fin 5) (Fin 5) ℝ} (hU : Uᵀ * U = 1) (v : Fin 5 → ℝ) :
    sq1 (U *ᵥ v) = sq1 v := by
  rw [sq1_eq_dotProduct, sq1_eq_dotProduct, dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec,
    hU, one_mulVec]

/-! ### Eigenvalues of a unit symmetric trace-free matrix -/

/-- Five reals with sum `0` and sum of squares `1`: the first has square at most `4/5`. -/
theorem sq_le_four_fifths_of_sum {a b c d e : ℝ} (hs : a + b + c + d + e = 0)
    (hq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = 1) : a ^ 2 ≤ 4 / 5 := by
  have ha : a = -(b + c + d + e) := by linarith
  subst ha
  nlinarith [sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (c - d),
    sq_nonneg (c - e), sq_nonneg (d - e)]

/-- Spectral data of a unit symmetric trace-free `5 × 5` matrix: an orthogonal `U` and
eigenvalues `α` with `A^k = U diag(α^k) Uᵀ`, `∑ α = 0`, `∑ α² = 1` and `α_i² ≤ 4/5`. -/
theorem exists_spectral_data {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsSymm) (h0 : A.trace = 0)
    (h1 : (A ^ 2).trace = 1) :
    ∃ (U : Matrix (Fin 5) (Fin 5) ℝ) (α : Fin 5 → ℝ), Uᵀ * U = 1 ∧ U * Uᵀ = 1 ∧
      (∀ k, A ^ k = U * diagonal (fun i => α i ^ k) * Uᵀ) ∧ ∑ i, α i = 0 ∧
      ∑ i, α i ^ 2 = 1 ∧ ∀ i, α i ^ 2 ≤ 4 / 5 := by
  obtain ⟨U, α, hU, hU', hAU⟩ := exists_orthogonal_diag hA
  have hk := pow_eq_conj_diagonal hU hAU
  have hs : ∑ i, α i = 0 := by
    have := hk 1
    simp only [pow_one] at this
    rw [← h0, this, trace_conj_diagonal hU]
  have hq : ∑ i, α i ^ 2 = 1 := by rw [← h1, hk 2, trace_conj_diagonal hU]
  refine ⟨U, α, hU, hU', hk, hs, hq, ?_⟩
  rw [Fin.sum_univ_five] at hs hq
  intro i
  fin_cases i
  · exact sq_le_four_fifths_of_sum hs hq
  · exact show α 1 ^ 2 ≤ 4 / 5 from
      sq_le_four_fifths_of_sum (b := α 0) (c := α 2) (d := α 3) (e := α 4) (by linarith)
        (by linarith)
  · exact show α 2 ^ 2 ≤ 4 / 5 from
      sq_le_four_fifths_of_sum (b := α 0) (c := α 1) (d := α 3) (e := α 4) (by linarith)
        (by linarith)
  · exact show α 3 ^ 2 ≤ 4 / 5 from
      sq_le_four_fifths_of_sum (b := α 0) (c := α 1) (d := α 2) (e := α 4) (by linarith)
        (by linarith)
  · exact show α 4 ^ 2 ≤ 4 / 5 from
      sq_le_four_fifths_of_sum (b := α 0) (c := α 1) (d := α 2) (e := α 3) (by linarith)
        (by linarith)

/-! ### Matrix bounds -/

section MatrixBounds

variable {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsSymm) (h0 : A.trace = 0)
  (h1 : (A ^ 2).trace = 1)
include hA h0 h1

/-- The operator bound `‖A‖² ≤ 4/5`, iterated: `|A^k v|² ≤ (4/5)^k |v|²`. -/
theorem sq1_pow_mulVec_le (k : ℕ) (v : Fin 5 → ℝ) :
    sq1 (A ^ k *ᵥ v) ≤ (4 / 5) ^ k * sq1 v := by
  obtain ⟨U, α, hU, hU', hk, -, -, hα⟩ := exists_spectral_data hA h0 h1
  have hUt : Uᵀᵀ * Uᵀ = 1 := by rw [transpose_transpose]; exact hU'
  rw [hk k, ← mulVec_mulVec, ← mulVec_mulVec, sq1_mulVec_of_orth hU,
    ← sq1_mulVec_of_orth hUt v]
  simp only [sq1, mulVec_diagonal, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) (hα i) k) (sq_nonneg _)

/-- The sum of `α_i^{2k+2}` over the eigenvalues, which is `|A^{k+1}|²`, is at most
`(4/5)^k`. -/
theorem trace_pow_two_mul_le (k : ℕ) : (A ^ (2 * k + 2)).trace ≤ (4 / 5) ^ k := by
  obtain ⟨U, α, hU, -, hk, -, hq, hα⟩ := exists_spectral_data hA h0 h1
  rw [hk, trace_conj_diagonal hU]
  calc ∑ i, α i ^ (2 * k + 2) ≤ ∑ i, (4 / 5) ^ k * α i ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [pow_add, pow_mul]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (sq_nonneg _) (hα i) k)
          (sq_nonneg _)
    _ = (4 / 5) ^ k := by rw [← Finset.mul_sum, hq, mul_one]

/-- The Frobenius bound `|A^{k+1}|² ≤ (4/5)^k`. -/
theorem sumSq_pow_succ_le (k : ℕ) : ∑ i, ∑ j, (A ^ (k + 1)) i j ^ 2 ≤ (4 / 5) ^ k := by
  have hS := hA.pow (k + 1)
  have : ∑ i, ∑ j, (A ^ (k + 1)) i j ^ 2 = (A ^ (2 * k + 2)).trace := by
    rw [show A ^ (2 * k + 2) = A ^ (k + 1) * A ^ (k + 1) by rw [← pow_add]; ring_nf]
    simp only [Matrix.trace, Matrix.diag, mul_apply, sq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hS.apply i j]
  rw [this]
  exact trace_pow_two_mul_le hA h0 h1 k

/-- The trace bound `(tr A^{k+2})² ≤ (4/5)^k`. -/
theorem trace_pow_sq_le (k : ℕ) : (A ^ (k + 2)).trace ^ 2 ≤ (4 / 5) ^ k := by
  obtain ⟨U, α, hU, -, hk, -, hq, hα⟩ := exists_spectral_data hA h0 h1
  have h2 := trace_pow_two_mul_le hA h0 h1 k
  rw [hk, trace_conj_diagonal hU] at h2 ⊢
  calc (∑ i, α i ^ (k + 2)) ^ 2 = (∑ i, α i * α i ^ (k + 1)) ^ 2 := by
        congr 1; refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ (∑ i, α i ^ 2) * ∑ i, (α i ^ (k + 1)) ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = ∑ i, α i ^ (2 * k + 2) := by
        rw [hq, one_mul]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ (4 / 5) ^ k := h2

/-- The cubic trace bound `(tr A³)² ≤ 9/20`. -/
theorem trace_cube_sq_le : (A ^ 3).trace ^ 2 ≤ 9 / 20 := by
  obtain ⟨U, α, hU, -, hk, hs, hq, hα⟩ := exists_spectral_data hA h0 h1
  rw [hk, trace_conj_diagonal hU]
  set M := Real.sqrt (4 / 5) with hM
  have hM0 : 0 < M := Real.sqrt_pos.2 (by norm_num)
  have hM2 : M ^ 2 = 4 / 5 := Real.sq_sqrt (by norm_num)
  set c := 1 / (5 * M) with hc
  have hMc : M * c = 1 / 5 := by rw [hc]; field_simp
  have hc2 : c ^ 2 = 1 / 20 := by
    have : (M * c) ^ 2 = 1 / 25 := by rw [hMc]; norm_num
    rw [mul_pow, hM2] at this; linarith
  have habs : ∀ i, |α i| ≤ M := fun i => Real.abs_le_sqrt (hα i)
  clear_value M c
  -- `∑ (α_i − M)(α_i + c)² ≤ 0` and the same for `−α`.
  have hup : ∑ i, (α i - M) * (α i + c) ^ 2 ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg
      (by linarith [le_abs_self (α i), habs i]) (sq_nonneg _)
  have hlo : ∑ i, (-α i - M) * (-α i + c) ^ 2 ≤ 0 :=
    Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg
      (by linarith [neg_abs_le (α i), habs i]) (sq_nonneg _)
  rw [Fin.sum_univ_five] at hs hq hup hlo ⊢
  have h₁ : α 0 ^ 3 + α 1 ^ 3 + α 2 ^ 3 + α 3 ^ 3 + α 4 ^ 3 ≤ M - c := by
    linear_combination hup - (2 * c - M) * hq - (c ^ 2 - 2 * M * c) * hs + 5 * c * hMc
  have h₂ : -(α 0 ^ 3 + α 1 ^ 3 + α 2 ^ 3 + α 3 ^ 3 + α 4 ^ 3) ≤ M - c := by
    linear_combination hlo - (2 * c - M) * hq + (c ^ 2 - 2 * M * c) * hs + 5 * c * hMc
  have h₃ : (M - c) ^ 2 = 9 / 20 := by
    linear_combination hM2 - 2 * hMc + hc2
  rw [← h₃]
  exact sq_le_sq' (by linarith) h₁

end MatrixBounds

/-! ### Cubic tensors -/

/-- Squared norm of a three-tensor, `|X|² = ∑ X_{abc}²`. -/
def sq3 (X : Fin 5 → Fin 5 → Fin 5 → ℝ) : ℝ := ∑ a, ∑ b, ∑ c, X a b c ^ 2

/-- The vector `(X:M)_c = ∑_{a,b} X_{abc} M_{ab}`. -/
def contractX (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ) : Fin 5 → ℝ :=
  fun c => ∑ a, ∑ b, X a b c * M a b

theorem sq3_nonneg (X : Fin 5 → Fin 5 → Fin 5 → ℝ) : 0 ≤ sq3 X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    sq_nonneg _

theorem sq1_nonneg (v : Fin 5 → ℝ) : 0 ≤ sq1 v := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Cauchy–Schwarz for triple sums. -/
theorem sum3_mul_sq_le (f g : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    (∑ a, ∑ b, ∑ c, f a b c * g a b c) ^ 2 ≤
      (∑ a, ∑ b, ∑ c, f a b c ^ 2) * ∑ a, ∑ b, ∑ c, g a b c ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 5 × Fin 5 × Fin 5))
    (fun x => f x.1 x.2.1 x.2.2) (fun x => g x.1 x.2.1 x.2.2)
  simpa only [Fintype.sum_prod_type] using h

/-- Cauchy–Schwarz for double sums. -/
theorem sum2_mul_sq_le (f g : Fin 5 → Fin 5 → ℝ) :
    (∑ a, ∑ b, f a b * g a b) ^ 2 ≤ (∑ a, ∑ b, f a b ^ 2) * ∑ a, ∑ b, g a b ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 5 × Fin 5))
    (fun x => f x.1 x.2) (fun x => g x.1 x.2)
  simpa only [Fintype.sum_prod_type] using h

/-- `|X:M|² ≤ |M|² |X|²`. -/
theorem sq1_contractX_le (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ) :
    sq1 (contractX X M) ≤ (∑ a, ∑ b, M a b ^ 2) * sq3 X := by
  have hX : sq3 X = ∑ c, ∑ a, ∑ b, X a b c ^ 2 :=
    calc sq3 X = ∑ a, ∑ c, ∑ b, X a b c ^ 2 :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hX, Finset.mul_sum, sq1]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [mul_comm]
  exact sum2_mul_sq_le (fun a b => X a b c) M

/-- A cubic tensor symmetric under the exchanges of its first two and last two slots. -/
def IsSymm3 (T : Fin 5 → Fin 5 → Fin 5 → ℝ) : Prop :=
  (∀ a b c, T a b c = T b a c) ∧ ∀ a b c, T a b c = T a c b

theorem IsSymm3.cycle {T : Fin 5 → Fin 5 → Fin 5 → ℝ} (hT : IsSymm3 T) (a b c : Fin 5) :
    T a b c = T b c a := by
  rw [hT.1, hT.2]

/-- Pairing a symmetric tensor with `f(a, c, b)` is pairing it with `f(a, b, c)`. -/
theorem IsSymm3.sum_mul_acb {T : Fin 5 → Fin 5 → Fin 5 → ℝ} (hT : IsSymm3 T)
    (f : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * f a c b = ∑ a, ∑ b, ∑ c, T a b c * f a b c := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [hT.2]

/-- Pairing a symmetric tensor with `f(b, c, a)` is pairing it with `f(a, b, c)`. -/
theorem IsSymm3.sum_mul_bca {T : Fin 5 → Fin 5 → Fin 5 → ℝ} (hT : IsSymm3 T)
    (f : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * f b c a = ∑ a, ∑ b, ∑ c, T a b c * f a b c := by
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => by
    rw [hT.cycle a b c]

theorem sum_kron_mul (a : Fin 5) (g : Fin 5 → ℝ) : ∑ b, kron a b * g b = g a := by
  simp only [kron, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem sum3_kron_mul (T : Fin 5 → Fin 5 → Fin 5 → ℝ) (v : Fin 5 → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * (kron a b * v c) = ∑ c, v c * ∑ a, T a a c := by
  calc _ = ∑ a, ∑ b, kron a b * ∑ c, T a b c * v c := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ = ∑ a, ∑ c, T a a c * v c := Finset.sum_congr rfl fun a _ => sum_kron_mul a _
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by ring

/-- Pairing a symmetric tensor with `𝒥v = δ_{ab}v_c + δ_{ac}v_b + δ_{bc}v_a`. -/
theorem IsSymm3.sum_mul_jOp {T : Fin 5 → Fin 5 → Fin 5 → ℝ} (hT : IsSymm3 T) (v : Fin 5 → ℝ) :
    ∑ a, ∑ b, ∑ c, T a b c * (kron a b * v c + kron a c * v b + kron b c * v a) =
      3 * ∑ c, v c * ∑ a, T a a c := by
  have h₂ := hT.sum_mul_acb fun a b c => kron a b * v c
  have h₃ := hT.sum_mul_bca fun a b c => kron a b * v c
  simp only [mul_add, Finset.sum_add_distrib]
  rw [h₂, h₃, sum3_kron_mul]
  ring

section FiveSevenths

variable {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsSymm) (h0 : A.trace = 0)
  (h1 : (A ^ 2).trace = 1)

/-- The symmetrization of `ζ ⊗ A`. -/
def symTensor (A : Matrix (Fin 5) (Fin 5) ℝ) (ζ : Fin 5 → ℝ) (a b c : Fin 5) : ℝ :=
  (ζ a * A b c + ζ b * A a c + ζ c * A a b) / 3

/-- The symmetric trace-free part of `ζ ⊗ A`: `F = B − 𝒥v/7` with `v = (2/3)Aζ`. -/
def stfTensor (A : Matrix (Fin 5) (Fin 5) ℝ) (ζ : Fin 5 → ℝ) (a b c : Fin 5) : ℝ :=
  symTensor A ζ a b c - (kron a b * (2 / 3 * (A *ᵥ ζ) c) + kron a c * (2 / 3 * (A *ᵥ ζ) b) +
    kron b c * (2 / 3 * (A *ᵥ ζ) a)) / 7

include hA in
theorem isSymm3_symTensor (ζ : Fin 5 → ℝ) : IsSymm3 (symTensor A ζ) := by
  refine ⟨fun a b c => ?_, fun a b c => ?_⟩ <;> simp only [symTensor]
  · rw [hA.apply a b]; ring
  · rw [hA.apply b c]; ring

include hA in
theorem isSymm3_stfTensor (ζ : Fin 5 → ℝ) : IsSymm3 (stfTensor A ζ) := by
  have hB := isSymm3_symTensor hA ζ
  have hk : ∀ i j : Fin 5, kron i j = kron j i := fun i j => by
    simp only [kron, eq_comm]
  refine ⟨fun a b c => ?_, fun a b c => ?_⟩ <;> simp only [stfTensor]
  · rw [hB.1 a b c, hk a b]; ring
  · rw [hB.2 a b c, hk b c]; ring

theorem sum_kron_self : ∑ a : Fin 5, kron a a = 5 := by simp [kron]

include hA h0 in
theorem trace_stfTensor (ζ : Fin 5 → ℝ) (c : Fin 5) : ∑ a, stfTensor A ζ a a c = 0 := by
  have h0' : ∑ a, A a a = 0 := h0
  have hAζ : ∑ a, ζ a * A a c = (A *ᵥ ζ) c := by
    simp only [mulVec, dotProduct]
    exact Finset.sum_congr rfl fun a _ => by rw [hA.apply a c]; ring
  simp only [stfTensor, symTensor, Finset.sum_sub_distrib, ← Finset.sum_div,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, sum_kron_self]
  simp only [kron, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [h0', hAζ]
  ring

include hA h1 in
theorem sumSq_eq_one : ∑ a, ∑ b, A a b ^ 2 = 1 := by
  rw [← h1, sq A]
  simp only [Matrix.trace, Matrix.diag, mul_apply, sq]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hA.apply a b]

include hA h1 in
/-- `⟨B, ζ_c A_{ab}⟩ = |ζ|²/3 + 2|Aζ|²/3`. -/
theorem sum_symTensor_mul (ζ : Fin 5 → ℝ) :
    ∑ a, ∑ b, ∑ c, symTensor A ζ a b c * (ζ c * A a b) =
      sq1 ζ / 3 + 2 / 3 * sq1 (A *ᵥ ζ) := by
  have e₁ : ∑ a, ∑ b, ∑ c, ζ a * A b c * (ζ c * A a b) = sq1 (A *ᵥ ζ) := by
    simp only [sq1, mulVec, dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun c _ => ?_
    rw [hA.apply b a]; ring
  have e₂ : ∑ a, ∑ b, ∑ c, ζ b * A a c * (ζ c * A a b) = sq1 (A *ᵥ ζ) := by
    simp only [sq1, mulVec, dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    ring
  have e₃ : ∑ a, ∑ b, ∑ c, ζ c * A a b * (ζ c * A a b) = sq1 ζ := by
    have h := sumSq_eq_one hA h1
    simp only [sq1]
    calc _ = ∑ a, ∑ b, A a b ^ 2 * ∑ c, ζ c ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun c _ => by ring
      _ = (∑ a, ∑ b, A a b ^ 2) * ∑ c, ζ c ^ 2 := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => (Finset.sum_mul _ _ _).symm
      _ = ∑ c, ζ c ^ 2 := by rw [h, one_mul]
  simp only [symTensor, add_div, add_mul, Finset.sum_add_distrib, div_mul_eq_mul_div,
    ← Finset.sum_div, e₁, e₂, e₃]
  ring

/-- Pairing a symmetric tensor with the symmetrization `B` of `ζ ⊗ A` is pairing it with
`ζ_c A_{ab}`. -/
theorem IsSymm3.sum_mul_symTensor {T : Fin 5 → Fin 5 → Fin 5 → ℝ} (hT : IsSymm3 T)
    (ζ : Fin 5 → ℝ) : ∑ a, ∑ b, ∑ c, T a b c * symTensor A ζ a b c =
      ∑ a, ∑ b, ∑ c, T a b c * (ζ c * A a b) := by
  have h₂ := hT.sum_mul_acb fun a b c => ζ c * A a b
  have h₃ := hT.sum_mul_bca fun a b c => ζ c * A a b
  have : ∀ a b c, T a b c * symTensor A ζ a b c = (T a b c * (ζ a * A b c) +
      T a b c * (ζ b * A a c) + T a b c * (ζ c * A a b)) / 3 := fun a b c => by
    simp only [symTensor]; ring
  simp only [this, ← Finset.sum_div, Finset.sum_add_distrib]
  rw [h₂, h₃]
  ring

include hA h0 h1 in
/-- `|F|² = |ζ|²/3 + (10/21)|Aζ|²`. -/
theorem sq3_stfTensor (ζ : Fin 5 → ℝ) :
    sq3 (stfTensor A ζ) = sq1 ζ / 3 + 10 / 21 * sq1 (A *ᵥ ζ) := by
  have hF := isSymm3_stfTensor hA ζ
  have hB := isSymm3_symTensor hA ζ
  set v : Fin 5 → ℝ := fun c => 2 / 3 * (A *ᵥ ζ) c with hv
  -- `⟨F, 𝒥v⟩ = 0` since `F` is trace-free.
  have hFJ : ∑ a, ∑ b, ∑ c, stfTensor A ζ a b c *
      (kron a b * v c + kron a c * v b + kron b c * v a) = 0 := by
    rw [hF.sum_mul_jOp]
    simp only [trace_stfTensor hA h0, mul_zero, Finset.sum_const_zero]
  -- `⟨𝒥v, ζ_c A_{ab}⟩ = 2⟨v, Aζ⟩`.
  have hJ : ∑ a, ∑ b, ∑ c, (kron a b * v c + kron a c * v b + kron b c * v a) * (ζ c * A a b) =
      4 / 3 * sq1 (A *ᵥ ζ) := by
    have h0' : ∑ a, A a a = 0 := h0
    have j₁ : ∑ a, ∑ b, ∑ c, kron a b * v c * (ζ c * A a b) = 0 := by
      calc _ = ∑ a, ∑ b, kron a b * ∑ c, v c * ζ c * A a b := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun c _ => by ring
        _ = ∑ a, ∑ c, v c * ζ c * A a a := Finset.sum_congr rfl fun a _ => sum_kron_mul a _
        _ = ∑ c, v c * ζ c * ∑ a, A a a := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
        _ = 0 := by simp only [h0', mul_zero, Finset.sum_const_zero]
    have j₂ : ∑ a, ∑ b, ∑ c, kron a c * v b * (ζ c * A a b) = ∑ a, v a * (A *ᵥ ζ) a := by
      calc _ = ∑ a, ∑ b, v b * ζ a * A a b := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [← sum_kron_mul a (fun c => v b * ζ c * A a b)]
            exact Finset.sum_congr rfl fun c _ => by ring
        _ = ∑ b, ∑ a, v b * ζ a * A a b := Finset.sum_comm
        _ = _ := by
            refine Finset.sum_congr rfl fun b _ => ?_
            simp only [mulVec, dotProduct, Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by rw [hA.apply a b]; ring
    have j₃ : ∑ a, ∑ b, ∑ c, kron b c * v a * (ζ c * A a b) = ∑ a, v a * (A *ᵥ ζ) a := by
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← sum_kron_mul b (fun c => v a * (A a b * ζ b))]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [kron]
      split_ifs with h
      · subst h; ring
      · ring
    have split : ∑ a, ∑ b, ∑ c, (kron a b * v c + kron a c * v b + kron b c * v a) *
        (ζ c * A a b) = ∑ a, ∑ b, ∑ c, kron a b * v c * (ζ c * A a b) +
          ∑ a, ∑ b, ∑ c, kron a c * v b * (ζ c * A a b) +
          ∑ a, ∑ b, ∑ c, kron b c * v a * (ζ c * A a b) := by
      simp only [add_mul, Finset.sum_add_distrib]
    rw [split, j₁, j₂, j₃, zero_add, sq1, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by simp only [hv]; ring
  have hsq : sq3 (stfTensor A ζ) = ∑ a, ∑ b, ∑ c, stfTensor A ζ a b c * symTensor A ζ a b c := by
    have : ∀ a b c, stfTensor A ζ a b c ^ 2 = stfTensor A ζ a b c * symTensor A ζ a b c -
        stfTensor A ζ a b c * (kron a b * v c + kron a c * v b + kron b c * v a) / 7 :=
      fun a b c => by simp only [stfTensor, hv]; ring
    simp only [sq3, this, Finset.sum_sub_distrib, ← Finset.sum_div, hFJ, zero_div, sub_zero]
  rw [hsq, hF.sum_mul_symTensor]
  have : ∀ a b c, stfTensor A ζ a b c * (ζ c * A a b) = symTensor A ζ a b c * (ζ c * A a b) -
      (kron a b * v c + kron a c * v b + kron b c * v a) * (ζ c * A a b) / 7 :=
    fun a b c => by simp only [stfTensor, hv]; ring
  simp only [this, Finset.sum_sub_distrib, ← Finset.sum_div, hJ, sum_symTensor_mul hA h1]
  ring

/-- For symmetric trace-free `X`, `⟨X, F⟩ = |X:A|²` where `F` is the symmetric trace-free part
of `(X:A) ⊗ A`. -/
theorem sum_mul_stfTensor {X : Fin 5 → Fin 5 → Fin 5 → ℝ} (hX : IsSymm3 X)
    (hXt : ∀ c, ∑ a, X a a c = 0) :
    ∑ a, ∑ b, ∑ c, X a b c * stfTensor A (contractX X A) a b c = sq1 (contractX X A) := by
  set ζ := contractX X A with hζ
  have : ∀ a b c, X a b c * stfTensor A ζ a b c = X a b c * symTensor A ζ a b c -
      X a b c * (kron a b * (2 / 3 * (A *ᵥ ζ) c) + kron a c * (2 / 3 * (A *ᵥ ζ) b) +
        kron b c * (2 / 3 * (A *ᵥ ζ) a)) / 7 := fun a b c => by
    simp only [stfTensor]; ring
  simp only [this, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [hX.sum_mul_jOp, hX.sum_mul_symTensor]
  simp only [hXt, mul_zero, Finset.sum_const_zero, zero_div, sub_zero, sq1]
  rw [Finset.sum_comm]
  calc _ = ∑ b, ∑ c, ∑ a, X a b c * (ζ c * A a b) := Finset.sum_congr rfl fun b _ =>
        Finset.sum_comm
    _ = ∑ c, ∑ b, ∑ a, X a b c * (ζ c * A a b) := Finset.sum_comm
    _ = ∑ c, ζ c * ζ c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hc : ζ c = ∑ a, ∑ b, X a b c * A a b := by rw [hζ]; rfl
        calc ∑ b, ∑ a, X a b c * (ζ c * A a b) = ζ c * ∑ b, ∑ a, X a b c * A a b := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun a _ => by ring
          _ = ζ c * ζ c := by rw [Finset.sum_comm, ← hc]
    _ = _ := Finset.sum_congr rfl fun c _ => by ring

include hA h0 h1 in
/-- The bound `|X:A|² ≤ (5/7)|X|²` for symmetric trace-free `X`. -/
theorem sq1_contract_le_five_sevenths {X : Fin 5 → Fin 5 → Fin 5 → ℝ} (hX : IsSymm3 X)
    (hXt : ∀ c, ∑ a, X a a c = 0) : sq1 (contractX X A) ≤ 5 / 7 * sq3 X := by
  set ζ := contractX X A
  have hCS := sum3_mul_sq_le X (stfTensor A ζ)
  rw [sum_mul_stfTensor hX hXt] at hCS
  change sq1 ζ ^ 2 ≤ sq3 X * sq3 (stfTensor A ζ) at hCS
  have hF : sq3 (stfTensor A ζ) ≤ 5 / 7 * sq1 ζ := by
    rw [sq3_stfTensor hA h0 h1]
    have := sq1_pow_mulVec_le hA h0 h1 1 ζ
    rw [pow_one] at this
    linarith
  have hz := sq1_nonneg ζ
  have hX0 := sq3_nonneg X
  rcases hz.lt_or_eq with hpos | hzero
  · have : sq1 ζ * sq1 ζ ≤ (5 / 7 * sq3 X) * sq1 ζ := by
      nlinarith [mul_le_mul_of_nonneg_left hF hX0]
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]; positivity

end FiveSevenths

section PowContract

variable {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsSymm) (h0 : A.trace = 0)
  (h1 : (A ^ 2).trace = 1)
include hA h0 h1

/-- `|X:A^{k+2}|² ≤ (4/5)^{k+1} |X|²`. -/
theorem sq1_contract_pow_le (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (k : ℕ) :
    sq1 (contractX X (A ^ (k + 2))) ≤ (4 / 5) ^ (k + 1) * sq3 X :=
  (sq1_contractX_le X _).trans
    (mul_le_mul_of_nonneg_right (sumSq_pow_succ_le hA h0 h1 (k + 1)) (sq3_nonneg X))

end PowContract

/-! ### The mixed bound -/

/-- The mixed bound `s^h t^b ≤ (h/(h+b))^h (b/(h+b))^b` for `s, t ≥ 0` with `s + t ≤ 1`
(with `0^0 = 1` and `0/0 = 0`, the right side is `1` when `h = 0` or `b = 0`). -/
theorem mixed_pow_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t ≤ 1) (h b : ℕ) :
    s ^ h * t ^ b ≤ ((h : ℝ) / (h + b)) ^ h * ((b : ℝ) / (h + b)) ^ b := by
  have hs1 : s ≤ 1 := by linarith
  have ht1 : t ≤ 1 := by linarith
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    · have hb' : (b : ℝ) ≠ 0 := by positivity
      simp only [pow_zero, Nat.cast_zero, zero_add, one_mul, div_self hb', one_pow]
      exact pow_le_one₀ ht ht1
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hh' : (h : ℝ) ≠ 0 := by positivity
    simp only [pow_zero, Nat.cast_zero, add_zero, mul_one, div_self hh', one_pow]
    exact pow_le_one₀ hs hs1
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  set n : ℝ := h + b with hn
  have hnpos : 0 < n := by positivity
  set p₁ := s * n / h
  set p₂ := t * n / b
  have hp₁ : 0 ≤ p₁ := by positivity
  have hp₂ : 0 ≤ p₂ := by positivity
  have hAMGM := Real.geom_mean_le_arith_mean2_weighted (w₁ := h / n) (w₂ := b / n)
    (p₁ := p₁) (p₂ := p₂) (by positivity) (by positivity) hp₁ hp₂
    (by rw [hn]; field_simp)
  have hsum : (h : ℝ) / n * p₁ + b / n * p₂ = s + t := by
    simp only [p₁, p₂]; field_simp
  rw [hsum] at hAMGM
  have hle : (p₁ ^ ((h : ℝ) / n) * p₂ ^ ((b : ℝ) / n)) ^ (h + b) ≤ 1 :=
    pow_le_one₀ (by positivity) (hAMGM.trans hst)
  have hpow : ∀ (p : ℝ) (m : ℕ), 0 ≤ p → (p ^ ((m : ℝ) / n)) ^ (h + b) = p ^ m := by
    intro p m hp
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp, show (m : ℝ) / n * ((h + b : ℕ) : ℝ) = m by
      rw [hn]; push_cast; field_simp, Real.rpow_natCast]
  rw [mul_pow, hpow _ _ hp₁, hpow _ _ hp₂] at hle
  have e : p₁ ^ h * p₂ ^ b = s ^ h * t ^ b * ((n / h) ^ h * (n / b) ^ b) := by
    simp only [p₁, p₂]; rw [mul_div_assoc, mul_div_assoc, mul_pow, mul_pow]; ring
  rw [e] at hle
  have hpos : 0 < (n / h) ^ h * (n / b) ^ b := by positivity
  have hinv : ((h : ℝ) / n) ^ h * ((b : ℝ) / n) ^ b = 1 / ((n / h) ^ h * (n / b) ^ b) := by
    rw [one_div, mul_inv, ← inv_pow, ← inv_pow, inv_div, inv_div]
  rw [hinv, le_div_iff₀ hpos]
  linarith

end OnePhaseDimension.Certificate
