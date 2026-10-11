/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Bounds.TensorBounds

/-!
# Norm bounds for contractions of tensors on `ℝ⁵`

Elementary Cauchy–Schwarz and operator-norm estimates for the contractions that occur in the
scalar graphs of the certificate:

* `OpBound M κ`: `|M v|² ≤ κ |v|²` for all `v`; `opBound_pow` gives `κ = (4/5)^k` for `M = A^k`;
* `sq_dot_le`: `⟨P, R⟩² ≤ |P|² |R|²`;
* `sq1_vecX_le`, `sq2_matX_le`: contracting a cubic tensor with vectors;
* `sq2_biOp_le`, `sq3_triOp_le`: applying matrices with operator bounds to the slots of a two- or
  three-tensor (the Kronecker operator bound `‖M₁ ⊗ ⋯ ⊗ M_r‖ ≤ ∏ ‖M_s‖`, proved one slot at a
  time).
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate

open Matrix Finset

/-- `M` has squared operator norm at most `κ`. -/
def OpBound (M : Matrix (Fin 5) (Fin 5) ℝ) (κ : ℝ) : Prop := ∀ v, sq1 (M *ᵥ v) ≤ κ * sq1 v

theorem opBound_pow {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : A.IsSymm) (h0 : A.trace = 0)
    (h1 : (A ^ 2).trace = 1) (k : ℕ) : OpBound (A ^ k) ((4 / 5) ^ k) :=
  sq1_pow_mulVec_le hA h0 h1 k

theorem sq2_nonneg (Q : Fin 5 → Fin 5 → ℝ) : 0 ≤ sq2 Q :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Cauchy–Schwarz for vectors. -/
theorem sq_dot_le (P R : Fin 5 → ℝ) : (∑ a, P a * R a) ^ 2 ≤ sq1 P * sq1 R :=
  Finset.sum_mul_sq_le_sq_mul_sq _ _ _

/-- The vector `(X:(y ⊗ z))_a = ∑_{b,c} X_{abc} y_b z_c`. -/
def vecX (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (y z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun a => ∑ b, ∑ c, X a b c * y b * z c

/-- The matrix `(X·y)_{ab} = ∑_c X_{abc} y_c`. -/
def matX (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (y : Fin 5 → ℝ) : Fin 5 → Fin 5 → ℝ :=
  fun a b => ∑ c, X a b c * y c

theorem sum_sq_mul_sq (y z : Fin 5 → ℝ) : ∑ b, ∑ c, (y b * z c) ^ 2 = sq1 y * sq1 z := by
  simp only [sq1, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

theorem sq1_vecX_le (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (y z : Fin 5 → ℝ) :
    sq1 (vecX X y z) ≤ sq3 X * sq1 y * sq1 z := by
  rw [sq1, sq3, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have h := sum2_mul_sq_le (X a) fun b c => y b * z c
  rw [sum_sq_mul_sq] at h
  calc vecX X y z a ^ 2 = (∑ b, ∑ c, X a b c * (y b * z c)) ^ 2 := by
        simp only [vecX, mul_assoc]
    _ ≤ _ := h
    _ = _ := by ring

theorem sq2_matX_le (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (y : Fin 5 → ℝ) :
    sq2 (matX X y) ≤ sq3 X * sq1 y := by
  rw [sq2, sq3, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun b _ => sq_dot_le (X a b) y

/-- The triple product `∑ X_{abc} y_a z_b u_c` is bounded by `|X| |y| |z| |u|`. -/
theorem sq_sum3_vec_le (X : Fin 5 → Fin 5 → Fin 5 → ℝ) (y z u : Fin 5 → ℝ) :
    (∑ a, ∑ b, ∑ c, X a b c * (y a * z b * u c)) ^ 2 ≤ sq3 X * (sq1 y * sq1 z * sq1 u) := by
  refine (sum3_mul_sq_le X fun a b c => y a * z b * u c).trans (le_of_eq ?_)
  congr 1
  simp only [sq1, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

/-! ### Slot operators -/

section Slots

variable {M₁ M₂ M₃ : Matrix (Fin 5) (Fin 5) ℝ} {κ₁ κ₂ κ₃ : ℝ}

theorem sq2_comm (Q : Fin 5 → Fin 5 → ℝ) : sq2 (fun a b => Q b a) = sq2 Q := by
  simp only [sq2]
  exact Finset.sum_comm

/-- Applying `M` to the second slot of a two-tensor. -/
theorem sq2_op_right_le (hM : OpBound M₁ κ₁) (Q : Fin 5 → Fin 5 → ℝ) :
    sq2 (fun a a' => ∑ b', M₁ a' b' * Q a b') ≤ κ₁ * sq2 Q := by
  rw [sq2, sq2, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => hM (Q a)

/-- Applying `M` to the first slot of a two-tensor. -/
theorem sq2_op_left_le (hM : OpBound M₁ κ₁) (Q : Fin 5 → Fin 5 → ℝ) :
    sq2 (fun a a' => ∑ b, M₁ a b * Q b a') ≤ κ₁ * sq2 Q := by
  have e₁ : sq2 (fun a a' => ∑ b, M₁ a b * Q b a') = ∑ a', sq1 (M₁ *ᵥ fun b => Q b a') := by
    rw [sq2, Finset.sum_comm]; rfl
  have e₂ : sq2 Q = ∑ a', sq1 (fun b => Q b a') := by rw [sq2, Finset.sum_comm]; rfl
  rw [e₁, e₂, Finset.mul_sum]
  exact Finset.sum_le_sum fun a' _ => hM _

/-- The Kronecker bound on two-tensors: `|(M₁ ⊗ M₂)Q|² ≤ κ₁ κ₂ |Q|²`. -/
theorem sq2_biOp_le (hM₁ : OpBound M₁ κ₁) (hM₂ : OpBound M₂ κ₂) (hκ₁ : 0 ≤ κ₁)
    (Q : Fin 5 → Fin 5 → ℝ) :
    sq2 (fun a a' => ∑ b, ∑ b', M₁ a b * M₂ a' b' * Q b b') ≤ κ₁ * κ₂ * sq2 Q := by
  set T : Fin 5 → Fin 5 → ℝ := fun b a' => ∑ b', M₂ a' b' * Q b b'
  have hT : sq2 T ≤ κ₂ * sq2 Q := sq2_op_right_le hM₂ Q
  have h := sq2_op_left_le hM₁ T
  have e : (fun a a' => ∑ b, ∑ b', M₁ a b * M₂ a' b' * Q b b') =
      fun a a' => ∑ b, M₁ a b * T b a' := by
    funext a a'
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [T, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b' _ => by ring
  rw [e]
  calc _ ≤ κ₁ * sq2 T := h
    _ ≤ κ₁ * (κ₂ * sq2 Q) := mul_le_mul_of_nonneg_left hT hκ₁
    _ = _ := by ring

theorem sq3_eq_sum_sq2 (T : Fin 5 → Fin 5 → Fin 5 → ℝ) : sq3 T = ∑ a, sq2 (T a) := rfl

/-- Moving the first slot of a three-tensor to the end does not change its norm. -/
theorem sq3_rotate (T : Fin 5 → Fin 5 → Fin 5 → ℝ) : sq3 (fun a b c => T b c a) = sq3 T := by
  simp only [sq3]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

/-- Applying `M` to the last slot of a three-tensor. -/
theorem sq3_op_last_le (hM : OpBound M₁ κ₁) (T : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    sq3 (fun a b c => ∑ c', M₁ c c' * T a b c') ≤ κ₁ * sq3 T := by
  rw [sq3_eq_sum_sq2, sq3_eq_sum_sq2, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => sq2_op_right_le hM (T a)

/-- Applying `M` to the middle slot of a three-tensor. -/
theorem sq3_op_mid_le (hM : OpBound M₁ κ₁) (T : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    sq3 (fun a b c => ∑ b', M₁ b b' * T a b' c) ≤ κ₁ * sq3 T := by
  rw [sq3_eq_sum_sq2, sq3_eq_sum_sq2, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ => sq2_op_left_le hM (T a)

/-- Applying `M` to the first slot of a three-tensor. -/
theorem sq3_op_first_le (hM : OpBound M₁ κ₁) (T : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    sq3 (fun a b c => ∑ a', M₁ a a' * T a' b c) ≤ κ₁ * sq3 T := by
  have e : ∀ S : Fin 5 → Fin 5 → Fin 5 → ℝ, sq3 S = ∑ b, ∑ c, sq1 (fun a => S a b c) := by
    intro S
    rw [sq3, Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_comm
  rw [e, e T, Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun c _ => hM fun a => T a b c

/-- The Kronecker bound on three-tensors: `|(M₁ ⊗ M₂ ⊗ M₃)T|² ≤ κ₁ κ₂ κ₃ |T|²`. -/
theorem sq3_triOp_le (hM₁ : OpBound M₁ κ₁) (hM₂ : OpBound M₂ κ₂) (hM₃ : OpBound M₃ κ₃)
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (T : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    sq3 (fun a a' a'' => ∑ b, M₁ a b * ∑ b', M₂ a' b' * ∑ b'', M₃ a'' b'' * T b b' b'') ≤
      κ₁ * κ₂ * κ₃ * sq3 T := by
  set T₃ : Fin 5 → Fin 5 → Fin 5 → ℝ := fun a b c => ∑ c', M₃ c c' * T a b c'
  set T₂ : Fin 5 → Fin 5 → Fin 5 → ℝ := fun a b c => ∑ b', M₂ b b' * T₃ a b' c
  have h₃ : sq3 T₃ ≤ κ₃ * sq3 T := sq3_op_last_le hM₃ T
  have h₂ : sq3 T₂ ≤ κ₂ * sq3 T₃ := sq3_op_mid_le hM₂ T₃
  have h₁ := sq3_op_first_le hM₁ T₂
  have e : (fun a a' a'' => ∑ b, M₁ a b * ∑ b', M₂ a' b' * ∑ b'', M₃ a'' b'' * T b b' b'') =
      fun a a' a'' => ∑ b, M₁ a b * T₂ b a' a'' := rfl
  rw [e]
  calc _ ≤ κ₁ * sq3 T₂ := h₁
    _ ≤ κ₁ * (κ₂ * (κ₃ * sq3 T)) :=
        mul_le_mul_of_nonneg_left (h₂.trans (mul_le_mul_of_nonneg_left h₃ hκ₂)) hκ₁
    _ = _ := by ring

end Slots

end OnePhaseDimension.Certificate
