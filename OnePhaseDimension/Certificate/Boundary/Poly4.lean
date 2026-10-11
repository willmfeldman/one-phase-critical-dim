/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

/-!
# Polynomials in four variables, computed in the kernel

A polynomial in `x = (x₁, x₂, x₃, x₄)` with integer coefficients is an association list from
exponent vectors `(a₁, a₂, a₃, a₄) : ℕ × ℕ × ℕ × ℕ` to integers (`Poly4`). The operations
(sum by merging, product, power, substitution of a permutation of the variables, and the
homogenization `x^α ↦ x^α R^{⌊(5 - |α|)/2⌋}`) are structurally recursive, so that identities
between such polynomials can be checked by `decide +kernel`.

Every operation is proved sound for the evaluation `Poly4.eval`; soundness does not use any
sortedness invariant. Sortedness (lexicographic in the exponent vector, no zero coefficients)
only makes the results canonical, so that two equal polynomials give equal lists.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Boundary

open Finset

/-- An exponent vector in four variables. -/
abbrev Mono := ℕ × ℕ × ℕ × ℕ

namespace Mono

/-- The value `x₁^{a₁} x₂^{a₂} x₃^{a₃} x₄^{a₄}` of a monomial. -/
def eval (a : Mono) (x : Fin 4 → ℝ) : ℝ :=
  x 0 ^ a.1 * x 1 ^ a.2.1 * x 2 ^ a.2.2.1 * x 3 ^ a.2.2.2

/-- The total degree. -/
def deg (a : Mono) : ℕ := a.1 + a.2.1 + a.2.2.1 + a.2.2.2

/-- Strict lexicographic order (Boolean). -/
def lt (a b : Mono) : Bool :=
  Nat.blt a.1 b.1 || (a.1 == b.1 && (Nat.blt a.2.1 b.2.1 || (a.2.1 == b.2.1 &&
    (Nat.blt a.2.2.1 b.2.2.1 || (a.2.2.1 == b.2.2.1 && Nat.blt a.2.2.2 b.2.2.2)))))

/-- The exponent vector `n eᵢ`. -/
def single (i : Fin 4) (n : ℕ) : Mono :=
  if i = 0 then (n, 0, 0, 0) else if i = 1 then (0, n, 0, 0) else if i = 2 then (0, 0, n, 0)
  else (0, 0, 0, n)

/-- The exponent vector of `∏ᵢ x_{σ i}^{aᵢ}`. -/
def subst (σ : Fin 4 → Fin 4) (a : Mono) : Mono :=
  single (σ 0) a.1 + single (σ 1) a.2.1 + single (σ 2) a.2.2.1 + single (σ 3) a.2.2.2

theorem eval_add (a b : Mono) (x : Fin 4 → ℝ) : (a + b).eval x = a.eval x * b.eval x := by
  simp only [eval, Prod.fst_add, Prod.snd_add, pow_add]
  ring

theorem eval_zero (x : Fin 4 → ℝ) : (0 : Mono).eval x = 1 := by
  simp [eval]

theorem eval_single (i : Fin 4) (n : ℕ) (x : Fin 4 → ℝ) : (single i n).eval x = x i ^ n := by
  fin_cases i <;> simp [single, eval]

theorem eval_subst (σ : Fin 4 → Fin 4) (a : Mono) (x : Fin 4 → ℝ) :
    (subst σ a).eval x = a.eval (x ∘ σ) := by
  rw [subst, eval_add, eval_add, eval_add, eval_single, eval_single, eval_single, eval_single]
  rfl

end Mono

/-- A polynomial in four variables: an association list from exponent vectors to integer
coefficients. -/
abbrev Poly4 := List (Mono × ℤ)

namespace Poly4

/-- The value of a polynomial. -/
def eval (P : Poly4) (x : Fin 4 → ℝ) : ℝ := (P.map fun t => (t.2 : ℝ) * t.1.eval x).sum

@[simp] theorem eval_nil (x : Fin 4 → ℝ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (t : Mono × ℤ) (P : Poly4) (x : Fin 4 → ℝ) :
    eval (t :: P) x = t.2 * t.1.eval x + eval P x := by
  simp [eval]

theorem eval_append (P Q : Poly4) (x : Fin 4 → ℝ) : eval (P ++ Q) x = eval P x + eval Q x := by
  simp [eval]

/-- Insert-merge one term into a polynomial, given the merge of the tail. -/
def mergeAux (a : Mono) (c : ℤ) (p : Poly4) (mp : Poly4 → Poly4) : Poly4 → Poly4
  | [] => (a, c) :: p
  | (b, d) :: q =>
    if a = b then (if c + d = 0 then mp q else (a, c + d) :: mp q)
    else if Mono.lt a b then (a, c) :: mp ((b, d) :: q)
    else (b, d) :: mergeAux a c p mp q

/-- Merge (add) two polynomials; on sorted inputs the result is sorted and has no zero
coefficients. -/
def merge : Poly4 → Poly4 → Poly4
  | [], q => q
  | (a, c) :: p, q => mergeAux a c p (merge p) q

theorem eval_mergeAux (a : Mono) (c : ℤ) (P : Poly4) (mp : Poly4 → Poly4) (x : Fin 4 → ℝ)
    (hmp : ∀ Q, eval (mp Q) x = eval P x + eval Q x) :
    ∀ Q, eval (mergeAux a c P mp Q) x = c * a.eval x + eval P x + eval Q x
  | [] => by simp [mergeAux]
  | (b, d) :: Q => by
    unfold mergeAux
    split_ifs with hab hcd hlt
    · subst hab
      rw [hmp, eval_cons]
      have : (c : ℝ) + d = 0 := by exact_mod_cast hcd
      linear_combination (-a.eval x) * this
    · subst hab
      simp only [eval_cons, hmp]; push_cast; ring
    · simp only [eval_cons, hmp]; ring
    · simp only [eval_cons, eval_mergeAux a c P mp x hmp Q]; ring

theorem eval_merge (x : Fin 4 → ℝ) : ∀ P Q : Poly4, eval (merge P Q) x = eval P x + eval Q x
  | [], Q => by simp [merge]
  | (a, c) :: P, Q => by
    rw [merge, eval_mergeAux a c P (merge P) x (eval_merge x P), eval_cons]

/-- Collect a list of terms. -/
def ofList (l : Poly4) : Poly4 :=
  l.foldr (fun t acc => if t.2 = 0 then acc else merge [t] acc) []

theorem eval_ofList (x : Fin 4 → ℝ) : ∀ l : Poly4, eval (ofList l) x = eval l x
  | [] => rfl
  | t :: l => by
    have ih := eval_ofList x l
    simp only [ofList, List.foldr_cons] at ih ⊢
    split_ifs with h
    · rw [ih, eval_cons, h]; simp
    · rw [eval_merge, ih]; simp

/-- Multiply all coefficients by an integer. -/
def smul (c : ℤ) (P : Poly4) : Poly4 :=
  if c = 0 then [] else P.map fun t => (t.1, c * t.2)

theorem eval_smul (c : ℤ) (P : Poly4) (x : Fin 4 → ℝ) : eval (smul c P) x = c * eval P x := by
  unfold smul
  split_ifs with h
  · simp [h]
  · induction P with
    | nil => simp
    | cons t P ih => simp only [List.map_cons, eval_cons, ih]; push_cast; ring

/-- The product of a term with a polynomial (a shift of the exponents). -/
def mulTerm (a : Mono) (c : ℤ) (Q : Poly4) : Poly4 :=
  if c = 0 then [] else Q.map fun t => (a + t.1, c * t.2)

theorem eval_mulTerm (a : Mono) (c : ℤ) (Q : Poly4) (x : Fin 4 → ℝ) :
    eval (mulTerm a c Q) x = c * a.eval x * eval Q x := by
  unfold mulTerm
  split_ifs with h
  · simp [h]
  · induction Q with
    | nil => simp
    | cons t Q ih => simp only [List.map_cons, eval_cons, ih, Mono.eval_add]; push_cast; ring

/-- The product of two polynomials. -/
def mul (P Q : Poly4) : Poly4 :=
  P.foldr (fun t acc => merge (mulTerm t.1 t.2 Q) acc) []

theorem eval_mul (P Q : Poly4) (x : Fin 4 → ℝ) : eval (mul P Q) x = eval P x * eval Q x := by
  induction P with
  | nil => simp [mul]
  | cons t P ih =>
    simp only [mul, List.foldr_cons] at ih ⊢
    rw [eval_merge, eval_mulTerm, ih, eval_cons]; ring

/-- The constant polynomial `c`. -/
def const (c : ℤ) : Poly4 := if c = 0 then [] else [(0, c)]

theorem eval_const (c : ℤ) (x : Fin 4 → ℝ) : eval (const c) x = c := by
  unfold const; split_ifs with h <;> simp [h, Mono.eval_zero]

/-- Powers. -/
def pow (P : Poly4) : ℕ → Poly4
  | 0 => const 1
  | n + 1 => mul P (pow P n)

theorem eval_pow (P : Poly4) (x : Fin 4 → ℝ) : ∀ n, eval (pow P n) x = eval P x ^ n
  | 0 => by simp [pow, eval_const]
  | n + 1 => by rw [pow, eval_mul, eval_pow P x n, pow_succ']

/-- The sum of a list of polynomials. -/
def sum (l : List Poly4) : Poly4 := l.foldr merge []

theorem eval_sum (l : List Poly4) (x : Fin 4 → ℝ) :
    eval (sum l) x = (l.map fun P => eval P x).sum := by
  induction l with
  | nil => rfl
  | cons P l ih => simp only [sum, List.foldr_cons] at ih ⊢; rw [eval_merge, ih]; simp

/-- Substitute `x ↦ x ∘ σ`. -/
def subst (σ : Fin 4 → Fin 4) (P : Poly4) : Poly4 :=
  ofList (P.map fun t => (t.1.subst σ, t.2))

theorem eval_subst (σ : Fin 4 → Fin 4) (P : Poly4) (x : Fin 4 → ℝ) :
    eval (subst σ P) x = eval P (x ∘ σ) := by
  rw [subst, eval_ofList]
  induction P with
  | nil => rfl
  | cons t P ih => simp only [List.map_cons, eval_cons, ih, Mono.eval_subst]

/-! ### Named polynomials -/

/-- The variable `xᵢ`. -/
def var (i : Fin 4) : Poly4 := [(Mono.single i 1, 1)]

theorem eval_var (i : Fin 4) (x : Fin 4 → ℝ) : eval (var i) x = x i := by
  simp [var, Mono.eval_single]

/-- `R(x) = ∑ xᵢ² + (∑ xᵢ)²`. -/
def rPoly : Poly4 :=
  merge (sum ((List.finRange 4).map fun i => pow (var i) 2))
    (pow (sum ((List.finRange 4).map var)) 2)

/-- The quadratic form `R(x) = ∑ xᵢ² + (∑ xᵢ)²`. -/
def rQuad (x : Fin 4 → ℝ) : ℝ := ∑ i, x i ^ 2 + (∑ i, x i) ^ 2

theorem eval_rPoly (x : Fin 4 → ℝ) : eval rPoly x = rQuad x := by
  simp [rPoly, rQuad, eval_merge, eval_sum, eval_pow, eval_var, List.finRange_succ,
    Fin.sum_univ_four]
  ring

/-! ### Homogenization -/

/-- The powers `R⁰, R¹, R²`. -/
def rPowTable : List Poly4 := [pow rPoly 0, pow rPoly 1, pow rPoly 2]

/-- The homogenization `x^α ↦ x^α R^{⌊(5 - |α|)/2⌋}` (truncated subtraction; for degree at
most `5` the exponent of `R` is at most `2`). -/
def homog (P : Poly4) : Poly4 :=
  P.foldr (fun t acc =>
    merge (mulTerm t.1 t.2 (rPowTable.getD ((5 - t.1.deg) / 2) (pow rPoly ((5 - t.1.deg) / 2))))
      acc) []

theorem eval_rPowTable_getD (n : ℕ) (x : Fin 4 → ℝ) (hR : rQuad x = 1) :
    eval (rPowTable.getD n (pow rPoly n)) x = 1 := by
  have h : ∀ m, eval (pow rPoly m) x = 1 := fun m => by rw [eval_pow, eval_rPoly, hR, one_pow]
  rcases n with _ | _ | _ | n <;> simp [rPowTable, h]

/-- Homogenization does not change the value on `R = 1`. -/
theorem eval_homog (P : Poly4) (x : Fin 4 → ℝ) (hR : rQuad x = 1) :
    eval (homog P) x = eval P x := by
  induction P with
  | nil => rfl
  | cons t P ih =>
    simp only [homog, List.foldr_cons] at ih ⊢
    rw [eval_merge, eval_mulTerm, eval_rPowTable_getD _ x hR, ih, eval_cons, mul_one]

end Poly4

end OnePhaseDimension.Certificate.Boundary
