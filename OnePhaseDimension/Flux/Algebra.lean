/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.ToGen
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The flux fields as functions of the frame data

All tensors are over `ℝ^m` (`Gen.Ten1 m`, …) and the certificate data are generic
(`Gen.Coeffs m`); the five-dimensional declarations at the end of the file are the case `m = 5`.

Let `T` be a symmetric two-tensor (the spherical Hessian read in an orthonormal frame), `B` a
three-tensor (its derivative), `p` a vector and `g` a scalar. With `w = |T|`, `A = T/w`,
`X = B/w` and `a = 29/50`, the flux fields of the certificate `c` have frame components

  `h = w^a √f(A, p, g)`,  `Z_l = w^{2a}(G_{lijk}(A, p, g) X_{ijk} + w M_l(A, p, g) + P_l(A, p, g))`.

This file defines these components (`fluxHComp`, `fluxZComp`) and proves that they transform
correctly under an orthogonal change of frame: `h` is invariant and `Z` is a vector
(`fluxHComp_act`, `fluxZComp_act`). This is what makes the ambient fields independent of the frame
in which the data are read.

## Main definitions

* `Gen.act3`: the action of a matrix on three-tensors.
* `Gen.normW`, `Gen.normalizedA`, `Gen.normalizedX`: `w = |T|`, `A = T/w`, `X = B/w`.
* `Gen.Coeffs.contractG`: the contraction `G_{lijk} X_{ijk}`.
* `Gen.Coeffs.fluxZComp`, `Gen.Coeffs.fluxHComp`.
-/

open Finset

@[expose] public noncomputable section

namespace OnePhaseDimension

namespace Gen

variable {m : ℕ}

/-- Action of `O` on three-tensors. -/
def act3 (O : Ten2 m) (X : Ten3 m) : Ten3 m := fun i j k ↦
  ∑ a, ∑ b, ∑ c, O i a * O j b * O k c * X a b c

/-! ### Peeling off one slot -/

theorem act2_eq_act1 (O A : Ten2 m) (i j : Fin m) :
    act2 O A i j = act1 O (fun a ↦ act1 O (A a) j) i := by
  simp only [act2, act1, mul_sum, mul_assoc]

theorem act3_eq_act1 (O : Ten2 m) (X : Ten3 m) (i j k : Fin m) :
    act3 O X i j k = act1 O (fun a ↦ act2 O (X a) j k) i := by
  simp only [act3, act2, act1, mul_sum, mul_assoc]

theorem act4_eq_act1 (O : Ten2 m) (K : Ten4 m) (l i j k : Fin m) :
    act4 O K l i j k = act1 O (fun a ↦ act3 O (K a) i j k) l := by
  simp only [act4, act3, act1, mul_sum, mul_assoc]

theorem act4_swap_eq_act1 (O : Ten2 m) (K : Ten4 m) (l i j k : Fin m) :
    act4 O K i l j k = act1 O (fun b ↦ act3 O (fun a c e ↦ K a b c e) i j k) l := by
  simp only [act4, act3, act1, mul_sum]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun b _ ↦ sum_congr rfl fun a _ ↦ sum_congr rfl fun c _ ↦
    sum_congr rfl fun e _ ↦ ?_
  ring

/-! ### Pulling `act1` out of a contraction -/

theorem sum4_comm (F : Fin m → Fin m → Fin m → Fin m → ℝ) :
    ∑ i, ∑ j, ∑ k, ∑ a, F i j k a = ∑ a, ∑ i, ∑ j, ∑ k, F i j k a := by
  calc ∑ i, ∑ j, ∑ k, ∑ a, F i j k a = ∑ i, ∑ j, ∑ a, ∑ k, F i j k a :=
        sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ Finset.sum_comm
    _ = ∑ i, ∑ a, ∑ j, ∑ k, F i j k a := sum_congr rfl fun i _ ↦ Finset.sum_comm
    _ = ∑ a, ∑ i, ∑ j, ∑ k, F i j k a := Finset.sum_comm

theorem sum3_comm (F : Fin m → Fin m → Fin m → ℝ) :
    ∑ j, ∑ k, ∑ a, F j k a = ∑ a, ∑ j, ∑ k, F j k a := by
  calc ∑ j, ∑ k, ∑ a, F j k a = ∑ j, ∑ a, ∑ k, F j k a :=
        sum_congr rfl fun j _ ↦ Finset.sum_comm
    _ = ∑ a, ∑ j, ∑ k, F j k a := Finset.sum_comm

theorem sum2_act1_mul (O : Ten2 m) (F : Fin m → Ten2 m) (H : Ten2 m) (l : Fin m) :
    ∑ j, ∑ k, act1 O (fun a ↦ F a j k) l * H j k =
      act1 O (fun a ↦ ∑ j, ∑ k, F a j k * H j k) l := by
  simp only [act1, sum_mul, mul_sum]
  rw [sum3_comm]
  refine sum_congr rfl fun a _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ ?_
  ring

theorem sum3_act1_mul (O : Ten2 m) (F : Fin m → Ten3 m) (H : Ten3 m) (l : Fin m) :
    ∑ i, ∑ j, ∑ k, act1 O (fun a ↦ F a i j k) l * H i j k =
      act1 O (fun a ↦ ∑ i, ∑ j, ∑ k, F a i j k * H i j k) l := by
  simp only [act1, sum_mul, mul_sum]
  rw [sum4_comm]
  refine sum_congr rfl fun a _ ↦ sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦
    sum_congr rfl fun k _ ↦ ?_
  ring

/-! ### Orthogonal invariance of contractions -/

section Orth

variable {O : Ten2 m} (hO : IsOrth O)
include hO

theorem sum_act1_mul_act1 (x y : Ten1 m) :
    ∑ i, act1 O x i * act1 O y i = ∑ a, x a * y a := by
  calc ∑ i, act1 O x i * act1 O y i
      = ∑ i, ∑ b, ∑ a, O i a * x a * (O i b * y b) := by simp only [act1, sum_mul, mul_sum]
    _ = ∑ b, ∑ a, ∑ i, O i a * x a * (O i b * y b) :=
        (sum3_comm fun b a i ↦ O i a * x a * (O i b * y b)).symm
    _ = ∑ b, ∑ a, (∑ i, O i a * O i b) * (x a * y b) := by
        simp only [sum_mul]
        refine sum_congr rfl fun b _ ↦ sum_congr rfl fun a _ ↦ sum_congr rfl fun i _ ↦ ?_
        ring
    _ = ∑ a, x a * y a := by
        have hO' : ∀ a b, ∑ k, O k a * O k b = kron a b := hO
        simp only [hO', kron, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]

theorem sum_act2_mul_act2 (U V : Ten2 m) :
    ∑ i, ∑ j, act2 O U i j * act2 O V i j = ∑ a, ∑ b, U a b * V a b := by
  simp only [act2_eq_act1]
  rw [Finset.sum_comm]
  simp only [sum_act1_mul_act1 hO]
  rw [Finset.sum_comm]
  simp only [sum_act1_mul_act1 hO]

theorem sum_act3_mul_act3 (S R : Ten3 m) :
    ∑ i, ∑ j, ∑ k, act3 O S i j k * act3 O R i j k = ∑ a, ∑ b, ∑ c, S a b c * R a b c := by
  simp only [act3_eq_act1]
  have h : ∀ (F : Fin m → Fin m → Fin m → ℝ),
      ∑ i, ∑ j, ∑ k, F i j k = ∑ j, ∑ k, ∑ i, F i j k := fun F ↦ by
    rw [Finset.sum_comm]
    exact sum_congr rfl fun j _ ↦ Finset.sum_comm
  rw [h]
  simp only [sum_act1_mul_act1 hO]
  rw [← h]
  simp only [sum_act2_mul_act2 hO]

theorem sq2_act2 (T : Ten2 m) : sq2 (act2 O T) = sq2 T := by
  simp only [sq2, sq]
  exact sum_act2_mul_act2 hO T T

theorem sq1_act1 (p : Ten1 m) : sq1 (act1 O p) = sq1 p := by
  simp only [sq1, sq]
  exact sum_act1_mul_act1 hO p p

/-- `U'_{jk} X'_{ljk} = O_{la} U_{jk} X_{ajk}`. -/
theorem sum_act2_mul_act3 (U : Ten2 m) (X : Ten3 m) (l : Fin m) :
    ∑ j, ∑ k, act2 O U j k * act3 O X l j k =
      act1 O (fun a ↦ ∑ j, ∑ k, U j k * X a j k) l := by
  simp only [act3_eq_act1 O X l]
  simp only [mul_comm (act2 O U _ _), sum2_act1_mul]
  congr 1
  funext a
  rw [sum_act2_mul_act2 hO]
  exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ mul_comm _ _

/-- `K'_{lijk} X'_{ijk} = O_{la} K_{abce} X_{bce}`. -/
theorem sum_act4_mul_act3 (K : Ten4 m) (X : Ten3 m) (l : Fin m) :
    ∑ i, ∑ j, ∑ k, act4 O K l i j k * act3 O X i j k =
      act1 O (fun a ↦ ∑ i, ∑ j, ∑ k, K a i j k * X i j k) l := by
  simp only [act4_eq_act1 O K l, sum3_act1_mul]
  congr 1
  funext a
  exact sum_act3_mul_act3 hO _ _

/-- `K'_{iljk} X'_{ijk} = O_{lb} K_{abce} X_{ace}`. -/
theorem sum_act4_swap_mul_act3 (K : Ten4 m) (X : Ten3 m) (l : Fin m) :
    ∑ i, ∑ j, ∑ k, act4 O K i l j k * act3 O X i j k =
      act1 O (fun b ↦ ∑ i, ∑ j, ∑ k, K i b j k * X i j k) l := by
  simp only [act4_swap_eq_act1 O K l, sum3_act1_mul]
  congr 1
  funext b
  exact sum_act3_mul_act3 hO _ _

end Orth

/-! ### The normalized data -/

/-- `w = |T|`. -/
def normW (T : Ten2 m) : ℝ := √(sq2 T)

/-- `A = T / w`. -/
def normalizedA (T : Ten2 m) : Ten2 m := fun i j ↦ T i j / normW T

/-- `X = B / w`. -/
def normalizedX (T : Ten2 m) (B : Ten3 m) : Ten3 m := fun i j k ↦ B i j k / normW T

theorem normW_act2 {O : Ten2 m} (hO : IsOrth O) (T : Ten2 m) : normW (act2 O T) = normW T := by
  rw [normW, normW, sq2_act2 hO]

theorem normalizedA_act2 {O : Ten2 m} (hO : IsOrth O) (T : Ten2 m) :
    normalizedA (act2 O T) = act2 O (normalizedA T) := by
  funext i j
  simp only [normalizedA, normW_act2 hO, act2, div_eq_mul_inv, sum_mul, mul_assoc]

theorem normalizedX_act {O : Ten2 m} (hO : IsOrth O) (T : Ten2 m) (B : Ten3 m) :
    normalizedX (act2 O T) (act3 O B) = act3 O (normalizedX T B) := by
  funext i j k
  simp only [normalizedX, normW_act2 hO, act3, div_eq_mul_inv, sum_mul, mul_assoc]

theorem act1_combo (O : Ten2 m) (r s : ℝ) (u v t : Ten1 m) (l : Fin m) :
    act1 O (fun l ↦ r * (u l + s * v l + t l)) l =
      r * (act1 O u l + s * act1 O v l + act1 O t l) := by
  simp only [act1, mul_add, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun a _ ↦ by ring

namespace Coeffs

variable (c : Coeffs m)

/-- The contraction `G_{lijk} X_{ijk}` at the data `x = (A, p, g)`. -/
def contractG (x : Ten2 m × Ten1 m × ℝ) (X : Ten3 m) (l : Fin m) : ℝ :=
  ∑ i, ∑ j, ∑ k, c.G x l i j k * X i j k

/-- `G_{lijk} X_{ijk} = U_{jk} X_{ljk} + K_{lijk} X_{ijk} - K_{iljk} X_{ijk}`. -/
theorem contractG_eq (x : Ten2 m × Ten1 m × ℝ) (X : Ten3 m) (l : Fin m) :
    c.contractG x X l = ∑ j, ∑ k, c.U x j k * X l j k +
      (∑ i, ∑ j, ∑ k, c.K x l i j k * X i j k - ∑ i, ∑ j, ∑ k, c.K x i l j k * X i j k) := by
  simp only [contractG, G, C, add_mul, sub_mul, sum_add_distrib, sum_sub_distrib]
  congr 1
  simp only [kron, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_eq_single l (fun i _ hi ↦ by simp [Ne.symm hi]) (by simp)]
  simp

/-- The frame components `Z_l = w^{2a}(G_{lijk} X_{ijk} + w M_l + P_l)` of the flux field, as
functions of the frame data `(T, B, p, g)`. -/
def fluxZComp (T : Ten2 m) (B : Ten3 m) (p : Ten1 m) (g : ℝ) : Ten1 m := fun l ↦
  normW T ^ (2 * aExp) * (c.contractG (normalizedA T, p, g) (normalizedX T B) l
    + normW T * c.M (normalizedA T, p, g) l + c.P (normalizedA T, p, g) l)

/-- The scalar `h = w^a √f(A, p, g)`, as a function of the frame data `(T, p, g)`. -/
def fluxHComp (T : Ten2 m) (p : Ten1 m) (g : ℝ) : ℝ :=
  normW T ^ aExp * √(c.f (normalizedA T, p, g))

variable {c : Coeffs m} {ε δ : ℝ}

theorem contractG_act (hc : CertificateHolds m ε δ c) {O : Ten2 m} (hO : IsOrth O)
    (A : Ten2 m) (p : Ten1 m) (g : ℝ) (X : Ten3 m) (l : Fin m) :
    c.contractG (act2 O A, act1 O p, g) (act3 O X) l = act1 O (c.contractG (A, p, g) X) l := by
  rw [contractG_eq, hc.equiv_U O hO, hc.equiv_K O hO, sum_act2_mul_act3 hO,
    sum_act4_mul_act3 hO, sum_act4_swap_mul_act3 hO]
  have : c.contractG (A, p, g) X = fun a ↦ c.contractG (A, p, g) X a := rfl
  rw [this]
  simp only [contractG_eq, act1, mul_add, mul_sub, sum_add_distrib, sum_sub_distrib]

/-- **Equivariance of `Z`.** -/
theorem fluxZComp_act (hc : CertificateHolds m ε δ c) {O : Ten2 m} (hO : IsOrth O)
    (T : Ten2 m) (B : Ten3 m) (p : Ten1 m) (g : ℝ) :
    c.fluxZComp (act2 O T) (act3 O B) (act1 O p) g = act1 O (c.fluxZComp T B p g) := by
  funext l
  simp only [fluxZComp, normW_act2 hO, normalizedA_act2 hO, normalizedX_act hO,
    contractG_act hc hO, hc.equiv_M O hO, hc.equiv_P O hO]
  exact (act1_combo O (normW T ^ (2 * aExp)) (normW T)
    (c.contractG (normalizedA T, p, g) (normalizedX T B)) (c.M (normalizedA T, p, g))
    (c.P (normalizedA T, p, g)) l).symm

/-- **Invariance of `h`.** -/
theorem fluxHComp_act (hc : CertificateHolds m ε δ c) {O : Ten2 m} (hO : IsOrth O)
    (T : Ten2 m) (p : Ten1 m) (g : ℝ) :
    c.fluxHComp (act2 O T) (act1 O p) g = c.fluxHComp T p g := by
  simp only [fluxHComp, normW_act2 hO, normalizedA_act2 hO, hc.equiv_f O hO]

end Coeffs

end Gen

/-! ### Dimension five -/

/-- Action of `O` on three-tensors. -/
def act3 (O : Ten2) (X : Ten3) : Ten3 := fun i j k ↦
  ∑ a, ∑ b, ∑ c, O i a * O j b * O k c * X a b c

theorem sum3_comm (F : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ j, ∑ k, ∑ a, F j k a = ∑ a, ∑ j, ∑ k, F j k a :=
  Gen.sum3_comm F

section Orth

variable {O : Ten2} (hO : IsOrth5 O)
include hO

theorem sum_act1_mul_act1 (x y : Ten1) :
    ∑ i, act1 O x i * act1 O y i = ∑ a, x a * y a :=
  Gen.sum_act1_mul_act1 hO x y

theorem sum_act2_mul_act2 (U V : Ten2) :
    ∑ i, ∑ j, act2 O U i j * act2 O V i j = ∑ a, ∑ b, U a b * V a b :=
  Gen.sum_act2_mul_act2 hO U V

theorem sq2_act2 (T : Ten2) : sq2 (act2 O T) = sq2 T :=
  Gen.sq2_act2 hO T

/-- `K'_{lijk} X'_{ijk} = O_{la} K_{abce} X_{bce}`. -/
theorem sum_act4_mul_act3 (K : Ten4) (X : Ten3) (l : Fin 5) :
    ∑ i, ∑ j, ∑ k, act4 O K l i j k * act3 O X i j k =
      act1 O (fun a ↦ ∑ i, ∑ j, ∑ k, K a i j k * X i j k) l :=
  Gen.sum_act4_mul_act3 hO K X l

/-- `K'_{iljk} X'_{ijk} = O_{lb} K_{abce} X_{ace}`. -/
theorem sum_act4_swap_mul_act3 (K : Ten4) (X : Ten3) (l : Fin 5) :
    ∑ i, ∑ j, ∑ k, act4 O K i l j k * act3 O X i j k =
      act1 O (fun b ↦ ∑ i, ∑ j, ∑ k, K i b j k * X i j k) l :=
  Gen.sum_act4_swap_mul_act3 hO K X l

end Orth

/-- `w = |T|`. -/
def normW (T : Ten2) : ℝ := Gen.normW T

/-- `A = T / w`. -/
def normalizedA (T : Ten2) : Ten2 := Gen.normalizedA T

end OnePhaseDimension
