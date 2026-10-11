/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The scaled projection operators of the Gram blocks

Tensors of rank two and three on `ℝ⁵` are written as curried functions. For a rank-`r` tensor
`F`, `F^π` is the slot permutation by `π`, and `Tr_{ab}` contracts the slots `a, b`. Following
the 2026-09-24 version (Section "Scaled projection operators"):

* `none`: `Π F = F`;
* `anti` (rank two): `Π F = F - F^{(12)}`;
* `sym`, rank two: `(Π F)_{ij} = 5 F'_{ij} - δ_{ij} v`, `F' = ∑_{π ∈ S₂} F^π`, `v = Tr₁₂ F'`;
* `sym`, rank three: `(Π F)_{ijk} = 7 F'_{ijk} - (δ_{ij} v_k + δ_{ik} v_j + δ_{jk} v_i)`,
  `F' = ∑_{π ∈ S₃} F^π`, `v = Tr₁₂ F'`;
* `hook`, rank three: `F' = 3 (F + F^{(12)}) - ∑_{π ∈ S₃} F^π`, `v = Tr₁₂ F'` and
  `(Π F)_{ijk} = 8 F'_{ijk} - (2 δ_{ij} v_k - δ_{ik} v_j - δ_{jk} v_i)`.

The six permutations of three slots are written out: `S_{ijk}, S_{ikj}, S_{jik}, S_{jki},
S_{kij}, S_{kji}`.

## Main results: the matching forms

The Gram blocks are expanded with `⟨T, Π S⟩` written through inner products of `T` with
permuted copies of `S` and through partial traces, so that `Π S` itself is never formed:

* `inner_projSym2`: `⟨T, Π S⟩ = 5 (⟨T, S⟩ + ⟨T, S^{(12)}⟩) - 2 tr T · tr S`;
* `inner_projAnti2`: `⟨T, Π S⟩ = ⟨T, S⟩ - ⟨T, S^{(12)}⟩`;
* `inner_projSym3`: `⟨T, Π S⟩ = 7 ∑_{π ∈ S₃} ⟨T, S^π⟩ - 2 ⟨τ T, τ S⟩`,
  with `τ = Tr₁₂ + Tr₁₃ + Tr₂₃`;
* `inner_projHook`: `⟨T, Π S⟩ = 16 (⟨T, S⟩ + ⟨T, S^{(12)}⟩) - 8 ∑_{π ∉ {1, (12)}} ⟨T, S^π⟩
  - 2 ⟨w T, w S⟩`, with `w = 2 Tr₁₂ - Tr₁₃ - Tr₂₃`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Proj

open Finset

/-- The Kronecker delta. -/
def δ (i j : Fin 5) : ℝ := if i = j then 1 else 0

/-! ### Rank one and two -/

/-- The inner product of vectors. -/
def inner1 (v w : Fin 5 → ℝ) : ℝ := ∑ k, v k * w k

/-- The inner product of two-tensors. -/
def inner2 (F G : Fin 5 → Fin 5 → ℝ) : ℝ := ∑ i, ∑ j, F i j * G i j

/-- The trace of a two-tensor. -/
def tr2 (F : Fin 5 → Fin 5 → ℝ) : ℝ := ∑ i, F i i

/-- The transposed two-tensor `F^{(12)}`. -/
def swap2 (F : Fin 5 → Fin 5 → ℝ) : Fin 5 → Fin 5 → ℝ := fun i j => F j i

/-- `∑_{π ∈ S₂} F^π`. -/
def symSum2 (F : Fin 5 → Fin 5 → ℝ) : Fin 5 → Fin 5 → ℝ := fun i j => F i j + F j i

/-- The scaled projection `sym` of rank two. -/
def projSym2 (F : Fin 5 → Fin 5 → ℝ) : Fin 5 → Fin 5 → ℝ :=
  fun i j => 5 * symSum2 F i j - δ i j * tr2 (symSum2 F)

/-- The scaled projection `anti` of rank two. -/
def projAnti2 (F : Fin 5 → Fin 5 → ℝ) : Fin 5 → Fin 5 → ℝ := fun i j => F i j - F j i

theorem sum_δ_mul (i : Fin 5) (f : Fin 5 → ℝ) : ∑ j, δ i j * f j = f i := by
  simp [δ]

theorem sum_mul_δ (i : Fin 5) (f : Fin 5 → ℝ) : ∑ j, f j * δ j i = f i := by
  simp [δ]

theorem inner_projSym2 (T S : Fin 5 → Fin 5 → ℝ) :
    inner2 T (projSym2 S) = 5 * (inner2 T S + inner2 T (swap2 S)) - 2 * tr2 T * tr2 S := by
  have h : ∑ i, ∑ j, T i j * (δ i j * tr2 (symSum2 S)) = tr2 T * tr2 (symSum2 S) := by
    simp only [mul_left_comm _ (δ _ _), sum_δ_mul, tr2, sum_mul]
  have h₂ : tr2 (symSum2 S) = 2 * tr2 S := by
    simp only [tr2, symSum2, ← two_mul, mul_sum]
  simp only [inner2, projSym2, mul_sub, sum_sub_distrib, h]
  rw [h₂, show tr2 T * (2 * tr2 S) = 2 * tr2 T * tr2 S by ring, sub_left_inj]
  simp only [symSum2, swap2, mul_add, sum_add_distrib, mul_sum]
  refine congrArg₂ _ ?_ ?_ <;>
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem inner_projAnti2 (T S : Fin 5 → Fin 5 → ℝ) :
    inner2 T (projAnti2 S) = inner2 T S - inner2 T (swap2 S) := by
  simp only [inner2, projAnti2, swap2, mul_sub, sum_sub_distrib]

/-! ### Rank three -/

/-- The inner product of three-tensors. -/
def inner3 (F G : Fin 5 → Fin 5 → Fin 5 → ℝ) : ℝ := ∑ i, ∑ j, ∑ k, F i j k * G i j k

/-- `Tr₁₂ F`. -/
def tr12 (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : Fin 5 → ℝ := fun k => ∑ a, F a a k
/-- `Tr₁₃ F`. -/
def tr13 (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : Fin 5 → ℝ := fun k => ∑ a, F a k a
/-- `Tr₂₃ F`. -/
def tr23 (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : Fin 5 → ℝ := fun k => ∑ a, F k a a

/-- `τ F = Tr₁₂ F + Tr₁₃ F + Tr₂₃ F`. -/
def tau (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : Fin 5 → ℝ := fun k => tr12 F k + tr13 F k + tr23 F k

/-- `w F = 2 Tr₁₂ F - Tr₁₃ F - Tr₂₃ F`. -/
def hookW (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : Fin 5 → ℝ :=
  fun k => 2 * tr12 F k - tr13 F k - tr23 F k

/-- `∑_{π ∈ S₃} F^π`. -/
def symSum3 (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : Fin 5 → Fin 5 → Fin 5 → ℝ :=
  fun i j k => F i j k + F i k j + F j i k + F j k i + F k i j + F k j i

/-- `(𝒥 v)_{ijk} = δ_{ij} v_k + δ_{ik} v_j + δ_{jk} v_i`. -/
def jOp (v : Fin 5 → ℝ) : Fin 5 → Fin 5 → Fin 5 → ℝ :=
  fun i j k => δ i j * v k + δ i k * v j + δ j k * v i

/-- `(𝓑 v)_{ijk} = 2 δ_{ij} v_k - δ_{ik} v_j - δ_{jk} v_i`. -/
def bOp (v : Fin 5 → ℝ) : Fin 5 → Fin 5 → Fin 5 → ℝ :=
  fun i j k => 2 * δ i j * v k - δ i k * v j - δ j k * v i

/-- The scaled projection `sym` of rank three. -/
def projSym3 (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : Fin 5 → Fin 5 → Fin 5 → ℝ :=
  fun i j k => 7 * symSum3 F i j k - jOp (tr12 (symSum3 F)) i j k

/-- `F' = 3 (F + F^{(12)}) - ∑_{π ∈ S₃} F^π`. -/
def hookPre (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : Fin 5 → Fin 5 → Fin 5 → ℝ :=
  fun i j k => 3 * (F i j k + F j i k) - symSum3 F i j k

/-- The scaled projection `hook` of rank three. -/
def projHook (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : Fin 5 → Fin 5 → Fin 5 → ℝ :=
  fun i j k => 8 * hookPre F i j k - bOp (tr12 (hookPre F)) i j k

theorem inner3_jOp (T : Fin 5 → Fin 5 → Fin 5 → ℝ) (v : Fin 5 → ℝ) :
    inner3 T (jOp v) = inner1 (tau T) v := by
  have h₁ : ∑ i, ∑ j, ∑ k, T i j k * (δ i j * v k) = ∑ k, tr12 T k * v k := by
    simp only [δ, mul_ite, mul_zero, ite_mul, zero_mul, one_mul, sum_ite_irrel,
      sum_const_zero, sum_ite_eq, mem_univ, ite_true, tr12, sum_mul]
    exact sum_comm
  have h₂ : ∑ i, ∑ j, ∑ k, T i j k * (δ i k * v j) = ∑ k, tr13 T k * v k := by
    simp only [δ, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true,
      tr13, sum_mul]
    exact sum_comm
  have h₃ : ∑ i, ∑ j, ∑ k, T i j k * (δ j k * v i) = ∑ k, tr23 T k * v k := by
    simp only [δ, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true,
      tr23, sum_mul]
  simp only [inner3, jOp, inner1, tau, mul_add, sum_add_distrib, add_mul, h₁, h₂, h₃]

theorem inner3_bOp (T : Fin 5 → Fin 5 → Fin 5 → ℝ) (v : Fin 5 → ℝ) :
    inner3 T (bOp v) = inner1 (hookW T) v := by
  have hJ : bOp v = fun i j k => 3 * (δ i j * v k) - jOp v i j k := by
    funext i j k; simp only [bOp, jOp]; ring
  have h₁ : inner3 T (fun i j k => δ i j * v k) = inner1 (tr12 T) v := by
    simp only [inner3, inner1, δ, mul_ite, mul_zero, ite_mul, zero_mul, one_mul,
      sum_ite_irrel, sum_const_zero, sum_ite_eq, mem_univ, ite_true, tr12, sum_mul]
    exact sum_comm
  simp only [hJ, inner3, mul_sub, sum_sub_distrib, mul_left_comm _ (3 : ℝ), ← mul_sum]
  rw [show (∑ i, ∑ j, ∑ k, T i j k * jOp v i j k) = inner3 T (jOp v) from rfl, inner3_jOp,
    show (∑ i, ∑ j, ∑ k, T i j k * (δ i j * v k)) = inner3 T (fun i j k => δ i j * v k)
      from rfl, h₁]
  simp only [inner1, hookW, tau, ← sum_sub_distrib, mul_sum]
  exact sum_congr rfl fun k _ => by ring

theorem tr12_symSum3 (S : Fin 5 → Fin 5 → Fin 5 → ℝ) (k : Fin 5) :
    tr12 (symSum3 S) k = 2 * tau S k := by
  simp only [tr12, symSum3, tau, tr13, tr23, sum_add_distrib]
  ring

theorem tr12_hookPre (S : Fin 5 → Fin 5 → Fin 5 → ℝ) (k : Fin 5) :
    tr12 (hookPre S) k = 2 * hookW S k := by
  have h := tr12_symSum3 S k
  simp only [tr12, hookPre, sum_sub_distrib, ← mul_sum, sum_add_distrib] at h ⊢
  rw [h]
  simp only [hookW, tau, tr12]
  ring

/-- `⟨T, S'⟩` summed over the six permutations `S' = S^π` of the slots of `S`. -/
def innerPerms3 (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) : ℝ :=
  inner3 T S + inner3 T (fun i j k => S i k j) + inner3 T (fun i j k => S j i k) +
    inner3 T (fun i j k => S j k i) + inner3 T (fun i j k => S k i j) +
    inner3 T (fun i j k => S k j i)

theorem inner3_add (T F G : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (fun i j k => F i j k + G i j k) = inner3 T F + inner3 T G := by
  simp only [inner3, mul_add, sum_add_distrib]

theorem inner3_smul_sub (T F G : Fin 5 → Fin 5 → Fin 5 → ℝ) (a : ℝ) :
    inner3 T (fun i j k => a * F i j k - G i j k) = a * inner3 T F - inner3 T G := by
  simp only [inner3, mul_sub, sum_sub_distrib, mul_left_comm _ a, ← mul_sum]

theorem inner1_smul (v w : Fin 5 → ℝ) (a : ℝ) : inner1 v (fun k => a * w k) = a * inner1 v w := by
  simp only [inner1, mul_left_comm _ a, ← mul_sum]

theorem inner3_symSum3 (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (symSum3 S) = innerPerms3 T S := by
  simp only [inner3, symSum3, innerPerms3, mul_add, sum_add_distrib]

/-- The matching form of `sym` at rank three:
`⟨T, Π S⟩ = 7 ∑_{π ∈ S₃} ⟨T, S^π⟩ - 2 ⟨τ T, τ S⟩`. -/
theorem inner_projSym3 (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (projSym3 S) = 7 * innerPerms3 T S - 2 * inner1 (tau T) (tau S) := by
  have h : projSym3 S = fun i j k => 7 * symSum3 S i j k - jOp (fun k => 2 * tau S k) i j k := by
    unfold projSym3
    rw [show tr12 (symSum3 S) = fun k => 2 * tau S k from funext (tr12_symSum3 S)]
  rw [h, inner3_smul_sub, inner3_symSum3, inner3_jOp, inner1_smul]

theorem inner3_hookPre (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (hookPre S) =
      3 * (inner3 T S + inner3 T (fun i j k => S j i k)) - innerPerms3 T S := by
  change inner3 T (fun i j k => 3 * (S i j k + S j i k) - symSum3 S i j k) = _
  rw [inner3_smul_sub (G := symSum3 S) (F := fun i j k => S i j k + S j i k),
    inner3_add, inner3_symSum3]

/-- The matching form of `hook`: `⟨T, Π S⟩ = 16 (⟨T, S⟩ + ⟨T, S^{(12)}⟩) - 8 ∑ ⟨T, S^π⟩` over
the other four permutations, `- 2 ⟨w T, w S⟩`. -/
theorem inner_projHook (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (projHook S) =
      16 * (inner3 T S + inner3 T (fun i j k => S j i k)) -
        8 * (inner3 T (fun i j k => S i k j) + inner3 T (fun i j k => S j k i) +
          inner3 T (fun i j k => S k i j) + inner3 T (fun i j k => S k j i)) -
        2 * inner1 (hookW T) (hookW S) := by
  have h : projHook S = fun i j k =>
      8 * hookPre S i j k - bOp (fun k => 2 * hookW S k) i j k := by
    unfold projHook
    rw [show tr12 (hookPre S) = fun k => 2 * hookW S k from funext (tr12_hookPre S)]
  rw [h, inner3_smul_sub, inner3_hookPre, inner3_bOp, inner1_smul, innerPerms3]
  ring


/-! ### Reindexing under slot permutations -/

theorem sum3_equiv (f : Fin 5 → Fin 5 → Fin 5 → ℝ)
    (σ : (Fin 5 × Fin 5 × Fin 5) ≃ (Fin 5 × Fin 5 × Fin 5)) :
    ∑ i, ∑ j, ∑ k, f i j k =
      ∑ i, ∑ j, ∑ k, f (σ (i, j, k)).1 (σ (i, j, k)).2.1 (σ (i, j, k)).2.2 := by
  simp only [← Fintype.sum_prod_type']
  exact (Equiv.sum_comp σ (fun x => f x.1 x.2.1 x.2.2)).symm

/-- The permutation of index triples `(i, j, k) ↦ (a, b, c)` given by a function of the
triple and its inverse. -/
def triplePerm (f g : Fin 5 × Fin 5 × Fin 5 → Fin 5 × Fin 5 × Fin 5)
    (h₁ : ∀ x, g (f x) = x) (h₂ : ∀ x, f (g x) = x) :
    (Fin 5 × Fin 5 × Fin 5) ≃ (Fin 5 × Fin 5 × Fin 5) :=
  ⟨f, g, h₁, h₂⟩

theorem inner3_comm (F G : Fin 5 → Fin 5 → Fin 5 → ℝ) : inner3 F G = inner3 G F := by
  simp only [inner3, mul_comm]

theorem inner3_swap23 (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (fun i j k => S i k j) = inner3 S (fun i j k => T i k j) := by
  rw [inner3, sum3_equiv _ (triplePerm (fun x => (x.1, x.2.2, x.2.1))
    (fun x => (x.1, x.2.2, x.2.1)) (fun _ => rfl) (fun _ => rfl))]
  simp only [triplePerm, Equiv.coe_fn_mk, inner3, mul_comm]

theorem inner3_swap12 (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (fun i j k => S j i k) = inner3 S (fun i j k => T j i k) := by
  rw [inner3, sum3_equiv _ (triplePerm (fun x => (x.2.1, x.1, x.2.2))
    (fun x => (x.2.1, x.1, x.2.2)) (fun _ => rfl) (fun _ => rfl))]
  simp only [triplePerm, Equiv.coe_fn_mk, inner3, mul_comm]

theorem inner3_swap13 (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (fun i j k => S k j i) = inner3 S (fun i j k => T k j i) := by
  rw [inner3, sum3_equiv _ (triplePerm (fun x => (x.2.2, x.2.1, x.1))
    (fun x => (x.2.2, x.2.1, x.1)) (fun _ => rfl) (fun _ => rfl))]
  simp only [triplePerm, Equiv.coe_fn_mk, inner3, mul_comm]

theorem inner3_cycle (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (fun i j k => S j k i) = inner3 S (fun i j k => T k i j) := by
  rw [inner3, sum3_equiv _ (triplePerm (fun x => (x.2.2, x.1, x.2.1))
    (fun x => (x.2.1, x.2.2, x.1)) (fun _ => rfl) (fun _ => rfl))]
  simp only [triplePerm, Equiv.coe_fn_mk, inner3, mul_comm]

/-- `∑_{π ∈ S₃} ⟨T, S^π⟩` is symmetric in `T, S` (the inverse permutations run over `S₃`). -/
theorem innerPerms3_comm (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    innerPerms3 T S = innerPerms3 S T := by
  have h₁ := inner3_comm T S
  have h₂ := inner3_swap23 T S
  have h₃ := inner3_swap12 T S
  have h₄ := inner3_cycle T S
  have h₅ := inner3_cycle S T
  have h₆ := inner3_swap13 T S
  simp only [innerPerms3]
  rw [h₁, h₂, h₃, h₄, ← h₅, h₆]
  ring

theorem inner2_comm (F G : Fin 5 → Fin 5 → ℝ) : inner2 F G = inner2 G F := by
  simp only [inner2, mul_comm]

theorem inner2_swap2 (T S : Fin 5 → Fin 5 → ℝ) : inner2 T (swap2 S) = inner2 S (swap2 T) := by
  simp only [inner2, swap2]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => mul_comm _ _

theorem inner1_comm (v w : Fin 5 → ℝ) : inner1 v w = inner1 w v := by
  simp only [inner1, mul_comm]

/-! ### Self-adjointness -/

theorem inner_projSym2_comm (T S : Fin 5 → Fin 5 → ℝ) :
    inner2 T (projSym2 S) = inner2 S (projSym2 T) := by
  rw [inner_projSym2, inner_projSym2, inner2_comm T S, inner2_swap2]
  ring

theorem inner_projAnti2_comm (T S : Fin 5 → Fin 5 → ℝ) :
    inner2 T (projAnti2 S) = inner2 S (projAnti2 T) := by
  rw [inner_projAnti2, inner_projAnti2, inner2_comm T S, inner2_swap2]

theorem inner_projSym3_comm (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (projSym3 S) = inner3 S (projSym3 T) := by
  rw [inner_projSym3, inner_projSym3, innerPerms3_comm, inner1_comm]

theorem inner_projHook_comm (T S : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 T (projHook S) = inner3 S (projHook T) := by
  have h₁ := inner3_comm T S
  have h₂ := inner3_swap23 T S
  have h₃ := inner3_swap12 T S
  have h₄ := inner3_cycle T S
  have h₅ := inner3_cycle S T
  have h₆ := inner3_swap13 T S
  rw [inner_projHook, inner_projHook, h₁, h₂, h₃, h₄, ← h₅, h₆, inner1_comm]
  ring

/-! ### Positive semidefiniteness -/

theorem inner2_self_nonneg (F : Fin 5 → Fin 5 → ℝ) : 0 ≤ inner2 F F :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_self_nonneg _

theorem inner3_self_nonneg (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : 0 ≤ inner3 F F :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_self_nonneg _

theorem inner_projAnti2_self (F : Fin 5 → Fin 5 → ℝ) :
    inner2 F (projAnti2 F) = inner2 (projAnti2 F) (projAnti2 F) / 2 := by
  have h : inner2 (projAnti2 F) (projAnti2 F) = 2 * inner2 F F - 2 * inner2 F (swap2 F) := by
    have hs : inner2 (swap2 F) (swap2 F) = inner2 F F := by
      simp only [inner2, swap2]; exact Finset.sum_comm
    have hc : inner2 (swap2 F) F = inner2 F (swap2 F) := inner2_comm _ _
    simp only [inner2, projAnti2, swap2] at hs hc ⊢
    simp only [sub_mul, mul_sub, sum_sub_distrib]
    rw [hs, hc]
    ring
  rw [h, inner_projAnti2]
  ring

theorem inner_projAnti2_nonneg (F : Fin 5 → Fin 5 → ℝ) : 0 ≤ inner2 F (projAnti2 F) := by
  rw [inner_projAnti2_self]
  exact div_nonneg (inner2_self_nonneg _) zero_le_two

theorem sum_δ_self : ∑ i, ∑ j, δ i j * δ i j = 5 := by
  simp [δ]

theorem inner_projSym2_self (F : Fin 5 → Fin 5 → ℝ) :
    inner2 F (projSym2 F) =
      5 / 2 * inner2 (fun i j => symSum2 F i j - δ i j * (tr2 (symSum2 F) / 5))
        (fun i j => symSum2 F i j - δ i j * (tr2 (symSum2 F) / 5)) := by
  set S := symSum2 F
  have hSS : inner2 S S = 2 * inner2 F F + 2 * inner2 F (swap2 F) := by
    have hs : inner2 (swap2 F) (swap2 F) = inner2 F F := by
      simp only [inner2, swap2]; exact Finset.sum_comm
    have hc : inner2 (swap2 F) F = inner2 F (swap2 F) := inner2_comm _ _
    simp only [inner2, S, symSum2, swap2] at hs hc ⊢
    simp only [add_mul, mul_add, sum_add_distrib]
    rw [hs, hc]
    ring
  have htr : tr2 S = 2 * tr2 F := by simp only [tr2, S, symSum2, ← two_mul, mul_sum]
  have hδ : ∀ c : ℝ, inner2 (fun i j => S i j - δ i j * c) (fun i j => S i j - δ i j * c) =
      inner2 S S - 2 * c * tr2 S + 5 * c ^ 2 := by
    intro c
    simp only [inner2, sub_mul, mul_sub, sum_sub_distrib]
    have h₁ : ∑ i, ∑ j, S i j * (δ i j * c) = c * tr2 S := by
      simp only [mul_left_comm _ (δ _ _), sum_δ_mul, tr2, mul_sum]
      exact sum_congr rfl fun i _ => mul_comm _ _
    have h₂ : ∑ i, ∑ j, δ i j * c * S i j = c * tr2 S := by
      rw [← h₁]; exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    have h₃ : ∑ i, ∑ j, δ i j * c * (δ i j * c) = 5 * c ^ 2 := by
      rw [← sum_δ_self]
      simp only [sum_mul]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    rw [h₁, h₂, h₃]
    ring
  rw [hδ, inner_projSym2, hSS, htr]
  ring

theorem inner_projSym2_nonneg (F : Fin 5 → Fin 5 → ℝ) : 0 ≤ inner2 F (projSym2 F) := by
  rw [inner_projSym2_self]
  exact mul_nonneg (by norm_num) (inner2_self_nonneg _)


theorem inner3_sub_smul_self (G B : Fin 5 → Fin 5 → Fin 5 → ℝ) (c : ℝ) :
    inner3 (fun i j k => G i j k - c * B i j k) (fun i j k => G i j k - c * B i j k) =
      inner3 G G - 2 * c * inner3 G B + c ^ 2 * inner3 B B := by
  simp only [inner3, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

theorem sum_const_five (x : ℝ) : ∑ _a : Fin 5, x = 5 * x := by
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

theorem tau_jOp (v : Fin 5 → ℝ) (k : Fin 5) : tau (jOp v) k = 21 * v k := by
  simp only [tau, tr12, tr13, tr23, jOp, δ, sum_add_distrib, ite_mul, one_mul, zero_mul,
    sum_ite_eq, sum_ite_eq', mem_univ, ite_true, sum_const_five]
  ring

theorem hookW_bOp (v : Fin 5 → ℝ) (k : Fin 5) : hookW (bOp v) k = 24 * v k := by
  simp only [hookW, tr12, tr13, tr23, bOp, δ, sum_sub_distrib, mul_ite, mul_one, mul_zero,
    ite_mul, one_mul, zero_mul, sum_ite_eq, sum_ite_eq', mem_univ, ite_true,
    sum_const_five]
  ring

/-- A fully symmetric three-tensor. -/
def IsSym3 (S : Fin 5 → Fin 5 → Fin 5 → ℝ) : Prop :=
  (∀ i j k, S j i k = S i j k) ∧ ∀ i j k, S i k j = S i j k

theorem isSym3_symSum3 (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : IsSym3 (symSum3 F) :=
  ⟨fun i j k => by simp only [symSum3]; ring, fun i j k => by simp only [symSum3]; ring⟩

theorem IsSym3.tau_eq {S : Fin 5 → Fin 5 → Fin 5 → ℝ} (hS : IsSym3 S) (k : Fin 5) :
    tau S k = 3 * tr12 S k := by
  have h₁ : tr13 S k = tr12 S k := sum_congr rfl fun a _ => hS.2 a a k
  have h₂ : tr23 S k = tr12 S k := sum_congr rfl fun a _ => by
    rw [hS.1 a k a, hS.2 a a k]
  simp only [tau, h₁, h₂]
  ring

theorem IsSym3.innerPerms3 {S : Fin 5 → Fin 5 → Fin 5 → ℝ} (hS : IsSym3 S)
    (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : innerPerms3 S F = 6 * inner3 S F := by
  have e₁ : (fun i j k => S i k j) = S := funext fun i => funext fun j => funext fun k => hS.2 i j k
  have e₂ : (fun i j k => S j i k) = S := funext fun i => funext fun j => funext fun k => hS.1 i j k
  have e₃ : (fun i j k => S k j i) = S := funext fun i => funext fun j => funext fun k => by
    rw [← hS.1, hS.2, hS.1]
  have e₄ : (fun i j k => S k i j) = S := funext fun i => funext fun j => funext fun k => by
    rw [← hS.1, hS.2]
  have e₅ : (fun i j k => S j k i) = S := funext fun i => funext fun j => funext fun k => by
    rw [hS.2 j i k, hS.1 i j k]
  have r₂ : inner3 S (fun i j k => F i k j) = inner3 S F := by
    rw [inner3_swap23 S F, e₁, inner3_comm]
  have r₃ : inner3 S (fun i j k => F j i k) = inner3 S F := by
    rw [inner3_swap12 S F, e₂, inner3_comm]
  have r₄ : inner3 S (fun i j k => F j k i) = inner3 S F := by
    rw [inner3_cycle S F, e₄, inner3_comm]
  have r₅ : inner3 S (fun i j k => F k i j) = inner3 S F := by
    rw [← inner3_cycle F S, e₅, inner3_comm]
  have r₆ : inner3 S (fun i j k => F k j i) = inner3 S F := by
    rw [inner3_swap13 S F, e₃, inner3_comm]
  simp only [Proj.innerPerms3, r₂, r₃, r₄, r₅, r₆]
  ring

/-- `⟨F, Π_sym F⟩ = (7/6) |S - 𝒥 v / 7|²` with `S = ∑_π F^π`, `v = Tr₁₂ S` (42 times the
squared norm of the symmetric trace-free projection of `F`). -/
theorem inner_projSym3_self (F : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 F (projSym3 F) = 7 / 6 *
      inner3 (fun i j k => symSum3 F i j k - 1 / 7 * jOp (tr12 (symSum3 F)) i j k)
        (fun i j k => symSum3 F i j k - 1 / 7 * jOp (tr12 (symSum3 F)) i j k) := by
  set S := symSum3 F
  set v := tr12 S
  have hS : IsSym3 S := isSym3_symSum3 F
  have h₁ : inner3 F (projSym3 F) = 7 * inner3 F S - inner1 (tau F) v := by
    rw [show projSym3 F = fun i j k => 7 * S i j k - jOp v i j k from rfl, inner3_smul_sub,
      inner3_jOp]
  have h₂ : inner1 (tau F) v = 1 / 2 * inner1 v v := by
    simp only [inner1, mul_sum]
    exact sum_congr rfl fun k _ => by rw [show v k = 2 * tau F k from tr12_symSum3 F k]; ring
  have h₃ : inner3 S S = 6 * inner3 F S := by
    rw [show inner3 S S = inner3 S (symSum3 F) from rfl, inner3_symSum3, hS.innerPerms3,
      inner3_comm]
  have h₄ : inner3 S (jOp v) = 3 * inner1 v v := by
    rw [inner3_jOp]
    simp only [inner1, mul_sum, hS.tau_eq]
    exact sum_congr rfl fun k _ => by ring
  have h₅ : inner3 (jOp v) (jOp v) = 21 * inner1 v v := by
    rw [inner3_jOp]
    simp only [inner1, mul_sum, tau_jOp]
    exact sum_congr rfl fun k _ => by ring
  rw [inner3_sub_smul_self, h₁, h₂, h₃, h₄, h₅]
  ring

theorem inner_projSym3_nonneg (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : 0 ≤ inner3 F (projSym3 F) := by
  rw [inner_projSym3_self]
  exact mul_nonneg (by norm_num) (inner3_self_nonneg _)

theorem hookPre_swap12 (F : Fin 5 → Fin 5 → Fin 5 → ℝ) (i j k : Fin 5) :
    hookPre F j i k = hookPre F i j k := by
  simp only [hookPre, symSum3]; ring

theorem symSum3_hookPre (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : symSum3 (hookPre F) = fun _ _ _ => 0 := by
  funext i j k; simp only [symSum3, hookPre]; ring

theorem hookW_hookPre (F : Fin 5 → Fin 5 → Fin 5 → ℝ) (k : Fin 5) :
    hookW (hookPre F) k = 3 * tr12 (hookPre F) k := by
  simp only [hookW, tr12, tr13, tr23, hookPre, symSum3, sum_sub_distrib, sum_add_distrib,
    ← mul_sum]
  ring

/-- `⟨F, Π_hook F⟩ = (4/3) |H - 𝓑 v / 8|²` with `H = 3 (F + F^{(12)}) - ∑_π F^π`, `v = Tr₁₂ H`
(this is `48 |Q₀ P₀ F|²`). -/
theorem inner_projHook_self (F : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    inner3 F (projHook F) = 4 / 3 *
      inner3 (fun i j k => hookPre F i j k - 1 / 8 * bOp (tr12 (hookPre F)) i j k)
        (fun i j k => hookPre F i j k - 1 / 8 * bOp (tr12 (hookPre F)) i j k) := by
  set H := hookPre F
  set v := tr12 H
  have h₁ : inner3 F (projHook F) = 8 * inner3 F H - inner1 (hookW F) v := by
    rw [show projHook F = fun i j k => 8 * H i j k - bOp v i j k from rfl, inner3_smul_sub,
      inner3_bOp]
  have h₂ : inner1 (hookW F) v = 1 / 2 * inner1 v v := by
    simp only [inner1, mul_sum]
    exact sum_congr rfl fun k _ => by rw [show v k = 2 * hookW F k from tr12_hookPre F k]; ring
  have h₃ : inner3 H H = 6 * inner3 F H := by
    have e : (fun i j k => H j i k) = H :=
      funext fun i => funext fun j => funext fun k => hookPre_swap12 F i j k
    have hsym : inner3 H (symSum3 F) = 0 := by
      rw [inner3_symSum3, innerPerms3_comm, ← inner3_symSum3, symSum3_hookPre]
      simp [inner3]
    calc inner3 H H = inner3 H (fun i j k => 3 * (F i j k + F j i k) - symSum3 F i j k) := rfl
      _ = 3 * (inner3 H F + inner3 H (fun i j k => F j i k)) - inner3 H (symSum3 F) := by
        rw [inner3_smul_sub (F := fun i j k => F i j k + F j i k), inner3_add]
      _ = 6 * inner3 F H := by
        rw [hsym, inner3_swap12 H F, e, inner3_comm H F]
        ring
  have hW : ∀ k, hookW H k = 3 * v k := hookW_hookPre F
  have h₄ : inner3 H (bOp v) = 3 * inner1 v v := by
    rw [inner3_bOp]
    simp only [inner1, mul_sum, hW]
    exact sum_congr rfl fun k _ => by ring
  have h₅ : inner3 (bOp v) (bOp v) = 24 * inner1 v v := by
    rw [inner3_bOp]
    simp only [inner1, mul_sum, hookW_bOp]
    exact sum_congr rfl fun k _ => by ring
  rw [inner3_sub_smul_self, h₁, h₂, h₃, h₄, h₅]
  ring

theorem inner_projHook_nonneg (F : Fin 5 → Fin 5 → Fin 5 → ℝ) : 0 ≤ inner3 F (projHook F) := by
  rw [inner_projHook_self]
  exact mul_nonneg (by norm_num) (inner3_self_nonneg _)

end OnePhaseDimension.Certificate.Proj
