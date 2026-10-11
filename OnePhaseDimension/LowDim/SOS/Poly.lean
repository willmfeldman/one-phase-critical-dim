/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Sparse polynomials for kernel computation

A monomial in the variables `y₀, y₁, …` is its list of exponents `[e₀, e₁, …]`, and a polynomial
with integer coefficients is a list of pairs `(monomial, coefficient)`. The operations (sum,
balanced sum of many polynomials, product, scalar multiple) are written only with the recursors
`List.rec`, `Nat.rec`, `Bool.rec`, `Option.rec`, `Ordering.rec` and the operations on `Nat` and
`Int` literals that the kernel evaluates with arbitrary-precision arithmetic, so that identities
between explicit polynomials can be checked with `decide +kernel`.

The value `Poly.eval y P = ∑ c · ∏ᵢ yᵢ^{eᵢ}` is additive and multiplicative for these operations
without any side condition (`eval_merge`, `eval_mergeAll`, `eval_mul`, `eval_smul`). Ordering
and cancellation only matter for the completeness of an identity check, never for soundness.

## Main definitions

* `LowDim.SOS.Mono`, `LowDim.SOS.Poly`, `LowDim.SOS.Poly.eval`.
* `LowDim.SOS.Poly.merge`, `LowDim.SOS.Poly.mergeAll`, `LowDim.SOS.Poly.mul`,
  `LowDim.SOS.Poly.smul`, `LowDim.SOS.Poly.var`.
-/

@[expose] public section

namespace OnePhaseDimension.LowDim.SOS

/-! ### Monomials -/

/-- A monomial `∏ᵢ yᵢ^{eᵢ}`, as its list of exponents. -/
abbrev Mono := List ℕ

namespace Mono

/-- The value `∏ᵢ y_{n+i}^{eᵢ}` of a monomial whose variables start at index `n`. -/
noncomputable def evalFrom (y : ℕ → ℝ) : Mono → ℕ → ℝ
  | [], _ => 1
  | d :: e, n => y n ^ d * evalFrom y e (n + 1)

/-- The value `∏ᵢ yᵢ^{eᵢ}` of a monomial. -/
noncomputable def eval (y : ℕ → ℝ) (e : Mono) : ℝ := evalFrom y e 0

/-- The product of two monomials: the entrywise sum of the exponent lists. -/
noncomputable def mul (a : Mono) : Mono → Mono :=
  List.rec (motive := fun _ => Mono → Mono) (fun b => b)
    (fun x a' ih b => List.rec (motive := fun _ => Mono) (x :: a')
      (fun y b' _ => Nat.add x y :: ih b') b) a

/-- The variable `yᵢ`. -/
noncomputable def var (i : ℕ) : Mono :=
  Nat.rec (motive := fun _ => Mono) [1] (fun _ ih => 0 :: ih) i

/-- Lexicographic comparison of exponent lists (a shorter list is smaller than its
extensions). -/
noncomputable def cmp (a : Mono) : Mono → Ordering :=
  List.rec (motive := fun _ => Mono → Ordering)
    (fun b => List.rec (motive := fun _ => Ordering) Ordering.eq (fun _ _ _ => Ordering.lt) b)
    (fun x _ ih b => List.rec (motive := fun _ => Ordering) Ordering.gt
      (fun y b' _ => Bool.rec (Bool.rec (ih b') Ordering.gt (Nat.blt y x)) Ordering.lt
        (Nat.blt x y)) b) a

@[simp] theorem mul_nil_left (b : Mono) : mul [] b = b := rfl

@[simp] theorem mul_nil_right (a : Mono) : mul a [] = a := by
  cases a <;> rfl

theorem mul_cons_cons (x y : ℕ) (a b : Mono) : mul (x :: a) (y :: b) = (x + y) :: mul a b := rfl

theorem evalFrom_mul (y : ℕ → ℝ) :
    ∀ (a b : Mono) (n : ℕ), evalFrom y (mul a b) n = evalFrom y a n * evalFrom y b n
  | [], b, n => by simp [evalFrom]
  | x :: a, [], n => by simp [evalFrom]
  | x :: a, z :: b, n => by
    rw [mul_cons_cons, evalFrom, evalFrom, evalFrom, evalFrom_mul y a b, pow_add]
    ring

theorem eval_mul (y : ℕ → ℝ) (a b : Mono) : eval y (mul a b) = eval y a * eval y b :=
  evalFrom_mul y a b 0

theorem evalFrom_var (y : ℕ → ℝ) : ∀ (i n : ℕ), evalFrom y (var i) n = y (n + i)
  | 0, n => by simp [var, evalFrom]
  | i + 1, n => by
    change y n ^ 0 * evalFrom y (var i) (n + 1) = _
    rw [evalFrom_var y i, pow_zero, one_mul]
    congr 1
    omega

@[simp] theorem eval_var (y : ℕ → ℝ) (i : ℕ) : eval y (var i) = y i := by
  rw [eval, evalFrom_var, zero_add]

@[simp] theorem eval_nil (y : ℕ → ℝ) : eval y [] = 1 := rfl

theorem eq_of_cmp_eq : ∀ {a b : Mono}, cmp a b = Ordering.eq → a = b
  | [], [], _ => rfl
  | [], _ :: _, h => Ordering.noConfusion h
  | _ :: _, [], h => Ordering.noConfusion h
  | x :: a, y :: b, h => by
    change Bool.rec (motive := fun _ => Ordering)
      (Bool.rec (motive := fun _ => Ordering) (cmp a b) Ordering.gt (Nat.blt y x)) Ordering.lt
      (Nat.blt x y) = Ordering.eq at h
    cases hxy : Nat.blt x y <;> cases hyx : Nat.blt y x <;> rw [hxy, hyx] at h <;>
      try exact Ordering.noConfusion h
    have h1 : ¬ x < y := by rw [← Nat.blt_eq, hxy]; decide
    have h2 : ¬ y < x := by rw [← Nat.blt_eq, hyx]; decide
    rw [show x = y by omega, eq_of_cmp_eq h]

end Mono

/-! ### Polynomials -/

/-- A polynomial with integer coefficients: a list of `(monomial, coefficient)`. -/
abbrev Poly := List (Mono × ℤ)

namespace Poly

/-- The value `∑ c · ∏ᵢ yᵢ^{eᵢ}`. -/
noncomputable def eval (y : ℕ → ℝ) (P : Poly) : ℝ := (P.map fun t => (t.2 : ℝ) * t.1.eval y).sum

@[simp] theorem eval_nil (y : ℕ → ℝ) : eval y [] = 0 := rfl

@[simp] theorem eval_cons (y : ℕ → ℝ) (e : Mono) (c : ℤ) (P : Poly) :
    eval y ((e, c) :: P) = c * e.eval y + eval y P := by
  simp [eval]

theorem eval_append (y : ℕ → ℝ) (P Q : Poly) : eval y (P ++ Q) = eval y P + eval y Q := by
  simp [eval]

/-- The sum of two polynomials, sorted by `Mono.cmp` if both are, cancelling zero
coefficients. -/
noncomputable def merge (p : Poly) : Poly → Poly :=
  List.rec (motive := fun _ => Poly → Poly) (fun q => q)
    (fun ac p' ihp q =>
      List.rec (motive := fun _ => Poly) (ac :: p')
        (fun bd q' ihq =>
          Ordering.rec (motive := fun _ => Poly) (ac :: ihp (bd :: q'))
            (Bool.rec (motive := fun _ => Poly) ((ac.1, Int.add ac.2 bd.2) :: ihp q') (ihp q')
              (Int.beq' (Int.add ac.2 bd.2) 0))
            (bd :: ihq) (Mono.cmp ac.1 bd.1))
        q)
    p

theorem eval_merge (y : ℕ → ℝ) : ∀ p q : Poly, eval y (merge p q) = eval y p + eval y q
  | [], q => by simp [merge]
  | ac :: p, q => by
    induction q with
    | nil => simp [merge]
    | cons bd q ihq =>
      obtain ⟨a, c⟩ := ac
      obtain ⟨b, d⟩ := bd
      change eval y (Ordering.rec (motive := fun _ => Poly) ((a, c) :: merge p ((b, d) :: q))
        (Bool.rec (motive := fun _ => Poly) ((a, Int.add c d) :: merge p q) (merge p q)
          (Int.beq' (Int.add c d) 0)) ((b, d) :: merge ((a, c) :: p) q) (Mono.cmp a b)) = _
      rcases hab : Mono.cmp a b <;> dsimp only
      · simp only [eval_cons, eval_merge y p]; ring
      · have he : a = b := Mono.eq_of_cmp_eq hab
        subst he
        rcases hz : Int.beq' (Int.add c d) 0 <;> dsimp only
        · simp only [eval_cons, eval_merge y p, Int.add_def, Int.cast_add]; ring
        · have : c + d = 0 := by simpa [Int.beq'_eq] using hz
          have hr : (c : ℝ) + d = 0 := by exact_mod_cast this
          simp only [eval_merge y p, eval_cons]
          linear_combination -hr * a.eval y
      · simp only [eval_cons, ihq]; ring

/-- `List.length` by the recursor. -/
noncomputable def length (l : List Poly) : ℕ := List.rec 0 (fun _ _ ih => Nat.succ ih) l

theorem length_eq (l : List Poly) : length l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg Nat.succ ih

/-- One round of pairwise merging, carrying a pending polynomial. -/
noncomputable def mergePairs (l : List Poly) : Option Poly → List Poly :=
  List.rec (motive := fun _ => Option Poly → List Poly)
    (fun o => Option.rec [] (fun a => [a]) o)
    (fun x _ ih o => Option.rec (ih (some x)) (fun a => merge a x :: ih none) o) l

/-- The sum of a list of polynomials, by a balanced merge tree. -/
noncomputable def mergeAll (l : List Poly) : Poly :=
  List.rec [] (fun a _ _ => a)
    (Nat.rec (motive := fun _ => List Poly → List Poly) (fun l => l)
      (fun _ ih l => ih (mergePairs l none)) (length l) l)

/-- The value of the pending polynomial. -/
noncomputable def evalOpt (y : ℕ → ℝ) (o : Option Poly) : ℝ := (o.map (eval y)).getD 0

/-- The length of the pending list. -/
def lenOpt : Option Poly → ℕ
  | none => 0
  | some _ => 1

theorem eval_mergePairs (y : ℕ → ℝ) :
    ∀ (l : List Poly) (o : Option Poly),
      ((mergePairs l o).map (eval y)).sum = evalOpt y o + (l.map (eval y)).sum
  | [], none => by simp [mergePairs, evalOpt]
  | [], some a => by simp [mergePairs, evalOpt]
  | x :: l, none => by
    change ((mergePairs l (some x)).map (eval y)).sum = _
    rw [eval_mergePairs y l]
    simp [evalOpt]
  | x :: l, some a => by
    change ((merge a x :: mergePairs l none).map (eval y)).sum = _
    rw [List.map_cons, List.sum_cons, eval_merge, eval_mergePairs y l]
    simp [evalOpt]
    ring

theorem length_mergePairs :
    ∀ (l : List Poly) (o : Option Poly),
      2 * (mergePairs l o).length ≤ l.length + lenOpt o + 1
  | [], none => by simp [mergePairs, lenOpt]
  | [], some a => by simp [mergePairs, lenOpt]
  | x :: l, none => by
    change 2 * (mergePairs l (some x)).length ≤ _
    have := length_mergePairs l (some x)
    simp only [lenOpt, List.length_cons] at this ⊢
    omega
  | x :: l, some a => by
    change 2 * (merge a x :: mergePairs l none).length ≤ _
    have := length_mergePairs l none
    simp only [lenOpt, List.length_cons] at this ⊢
    omega

theorem mergeAll_aux (y : ℕ → ℝ) : ∀ (n : ℕ) (l : List Poly), l.length ≤ n + 1 →
    ∃ P : Poly, Nat.rec (motive := fun _ => List Poly → List Poly) (fun l => l)
      (fun _ ih l => ih (mergePairs l none)) n l = [P] ∧ eval y P = (l.map (eval y)).sum ∨
      Nat.rec (motive := fun _ => List Poly → List Poly) (fun l => l)
      (fun _ ih l => ih (mergePairs l none)) n l = [] ∧ l = []
  | 0, l, h => by
    rcases l with _ | ⟨P, _ | ⟨Q, l⟩⟩
    · exact ⟨[], Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨P, Or.inl ⟨rfl, by simp⟩⟩
    · simp at h
  | n + 1, l, h => by
    have hlen := length_mergePairs l none
    simp only [lenOpt] at hlen
    obtain ⟨P, hP⟩ := mergeAll_aux y n (mergePairs l none) (by omega)
    refine ⟨P, ?_⟩
    change _ ∧ _ ∨ _ at hP
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨h1, ?_⟩
      rw [h2, eval_mergePairs]
      simp [evalOpt]
    · right
      refine ⟨h1, ?_⟩
      rcases l with _ | ⟨x, l⟩
      · rfl
      · exfalso
        have := eval_mergePairs (fun _ => 0) (x :: l) none
        have hx : (mergePairs (x :: l) none) = mergePairs l (some x) := rfl
        rcases l with _ | ⟨x', l'⟩
        · rw [hx] at h2; simp [mergePairs] at h2
        · rw [hx] at h2; simp [mergePairs] at h2

theorem eval_mergeAll (y : ℕ → ℝ) (l : List Poly) :
    eval y (mergeAll l) = (l.map (eval y)).sum := by
  obtain ⟨P, hP⟩ := mergeAll_aux y (length l) l (by rw [length_eq]; omega)
  rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [mergeAll, h1]; exact h2
  · rw [mergeAll, h1, h2]; rfl

/-- `List.map` by the recursor. -/
noncomputable def lmap {α β : Type} (f : α → β) (l : List α) : List β :=
  List.rec [] (fun a _ ih => f a :: ih) l

theorem lmap_eq {α β : Type} (f : α → β) (l : List α) : lmap f l = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => exact congrArg (f a :: ·) ih

/-- `List.flatMap` by the recursor. -/
noncomputable def lflatMap {α β : Type} (f : α → List β) (l : List α) : List β :=
  List.rec [] (fun a _ ih => List.rec (motive := fun _ => List β) ih (fun b _ ih' => b :: ih')
    (f a)) l

theorem lflatMap_eq {α β : Type} (f : α → List β) (l : List α) : lflatMap f l = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change List.rec (motive := fun _ => List β) (lflatMap f l) (fun b _ ih' => b :: ih') (f a) = _
    rw [List.flatMap_cons, ih]
    induction f a with
    | nil => rfl
    | cons b l' ih' => exact congrArg (b :: ·) ih'

/-- Multiplication by an integer. -/
noncomputable def smul (c : ℤ) (P : Poly) : Poly := lmap (fun t => (t.1, Int.mul c t.2)) P

theorem eval_smul (y : ℕ → ℝ) (c : ℤ) (P : Poly) : eval y (smul c P) = c * eval y P := by
  rw [smul, lmap_eq]
  induction P with
  | nil => simp
  | cons t P ih =>
    obtain ⟨e, d⟩ := t
    simp only [Int.mul_def] at ih ⊢
    simp only [List.map_cons, eval_cons, ih, Int.cast_mul]
    ring

/-- Multiplication of every term by the monomial `e` and the integer `c`. -/
noncomputable def mulTerm (e : Mono) (c : ℤ) (Q : Poly) : Poly :=
  lmap (fun s => (Mono.mul e s.1, Int.mul c s.2)) Q

theorem eval_mulTerm (y : ℕ → ℝ) (e : Mono) (c : ℤ) (Q : Poly) :
    eval y (mulTerm e c Q) = c * e.eval y * eval y Q := by
  rw [mulTerm, lmap_eq]
  induction Q with
  | nil => simp
  | cons t Q ih =>
    obtain ⟨f, d⟩ := t
    simp only [Int.mul_def] at ih ⊢
    simp only [List.map_cons, eval_cons, ih, Int.cast_mul, Mono.eval_mul]
    ring

/-- The product of two polynomials. -/
noncomputable def mul (P Q : Poly) : Poly := mergeAll (lmap (fun t => mulTerm t.1 t.2 Q) P)

theorem eval_mul (y : ℕ → ℝ) (P Q : Poly) : eval y (mul P Q) = eval y P * eval y Q := by
  rw [mul, eval_mergeAll, lmap_eq, List.map_map]
  induction P with
  | nil => simp
  | cons t P ih =>
    obtain ⟨e, c⟩ := t
    simp only [List.map_cons, List.sum_cons, Function.comp_apply, eval_mulTerm, ih, eval_cons]
    ring

/-- The polynomial `yᵢ`. -/
noncomputable def var (i : ℕ) : Poly := [(Mono.var i, 1)]

@[simp] theorem eval_var (y : ℕ → ℝ) (i : ℕ) : eval y (var i) = y i := by
  simp [var]

/-- The constant polynomial `c` (empty when `c = 0`). -/
noncomputable def const (c : ℤ) : Poly := Bool.rec [([], c)] [] (Int.beq' c 0)

@[simp] theorem eval_const (y : ℕ → ℝ) (c : ℤ) : eval y (const c) = c := by
  rw [const]
  rcases h : Int.beq' c 0
  · simp
  · have : c = 0 := by simpa [Int.beq'_eq] using h
    simp [this]

/-- Whether a polynomial is the empty list. -/
noncomputable def isNil (P : Poly) : Bool := List.rec true (fun _ _ _ => false) P

theorem eq_nil_of_isNil {P : Poly} (h : isNil P = true) : P = [] := by
  cases P with
  | nil => rfl
  | cons _ _ => exact Bool.noConfusion h

end Poly

end OnePhaseDimension.LowDim.SOS
