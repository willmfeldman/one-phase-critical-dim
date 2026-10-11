/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.SOS.Poly
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum

/-!
# Gram blocks, packed data and the residual bound

The certificate is a polynomial identity in the variables `y₀, …, y₁₇`, where
`(y₀, …, y₅) = (α₀, α₁, p₀, p₁, p₂, g)` and `(y₆, …, y₁₇) = v` are the twelve coordinates of the
quadratic form. This module provides:

* the packed data format: a natural number `k = (12 μ + ν) · 16⁶ + ∑ᵢ eᵢ 16ⁱ` stands for the
  monomial `∏ᵢ yᵢ^{eᵢ} · y_{6+μ} y_{6+ν}` (`dataMono`), and a list of pairs `(k, c)` for the
  polynomial `∑ c · dataMono k` (`ofData`);
* Gram blocks given by an integer lower-triangular matrix `L` and a basis `b_r` of monomials:
  `∑_{r,s} (L Lᵀ)_{rs} b_r b_s = ∑_i (∑_r L_{ri} b_r)² ≥ 0` (`eval_blockPoly`,
  `eval_blockPoly_nonneg`);
* the residual bound: on `|yᵢ| ≤ 1` (`i < 6`), a polynomial of packed data with keys below
  `144 · 16⁶` is at least `-(∑ |c|) · ∑_{j<12} y_{6+j}²` (`neg_absSum_mul_le_eval_ofData`).
-/

@[expose] public section

namespace OnePhaseDimension.LowDim.SOS

open Finset

/-! ### Packed monomials -/

/-- `d :: l`, except that a zero exponent is dropped at the end of a monomial, so that monomials
stay without trailing zeros. -/
noncomputable def trimCons (d : ℕ) (l : Mono) : Mono :=
  Bool.rec (d :: l) (List.rec (motive := fun _ => Mono) [] (fun _ _ _ => d :: l) l) (Nat.beq d 0)

theorem evalFrom_trimCons (y : ℕ → ℝ) (d : ℕ) (l : Mono) (n : ℕ) :
    Mono.evalFrom y (trimCons d l) n = y n ^ d * Mono.evalFrom y l (n + 1) := by
  rw [trimCons]
  rcases h : Nat.beq d 0 <;> dsimp only
  · rfl
  · have hd : d = 0 := by simpa using h
    subst hd
    cases l <;> simp [Mono.evalFrom]

/-- The monomial `∏_{i<6} yᵢ^{eᵢ}` of a packed code `c = ∑ᵢ eᵢ 16ⁱ`. -/
noncomputable def xMono (c : ℕ) : Mono :=
  trimCons (Nat.mod c 16) (trimCons (Nat.mod (Nat.div c 16) 16)
    (trimCons (Nat.mod (Nat.div c 256) 16) (trimCons (Nat.mod (Nat.div c 4096) 16)
      (trimCons (Nat.mod (Nat.div c 65536) 16) (trimCons (Nat.mod (Nat.div c 1048576) 16) [])))))

/-- The value of `xMono c`. -/
noncomputable def xVal (y : ℕ → ℝ) (c : ℕ) : ℝ :=
  y 0 ^ (c % 16) * y 1 ^ (c / 16 % 16) * y 2 ^ (c / 256 % 16) * y 3 ^ (c / 4096 % 16) *
    y 4 ^ (c / 65536 % 16) * y 5 ^ (c / 1048576 % 16)

theorem nat_mod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl
theorem nat_div_eq (a b : ℕ) : Nat.div a b = a / b := rfl
theorem nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl

theorem eval_xMono (y : ℕ → ℝ) (c : ℕ) : (xMono c).eval y = xVal y c := by
  simp only [Mono.eval, xMono, evalFrom_trimCons, Mono.evalFrom, xVal, nat_mod_eq, nat_div_eq,
    Nat.reduceAdd, mul_one, zero_add]
  ring

theorem abs_xVal_le_one {y : ℕ → ℝ} (hy : ∀ i < 6, |y i| ≤ 1) (c : ℕ) : |xVal y c| ≤ 1 := by
  have h : ∀ i < 6, ∀ d : ℕ, |y i ^ d| ≤ 1 := fun i hi d => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hy i hi)
  simp only [xVal, abs_mul]
  have := h 0 (by norm_num) (c % 16)
  have := h 1 (by norm_num) (c / 16 % 16)
  have := h 2 (by norm_num) (c / 256 % 16)
  have := h 3 (by norm_num) (c / 4096 % 16)
  have := h 4 (by norm_num) (c / 65536 % 16)
  have := h 5 (by norm_num) (c / 1048576 % 16)
  have hm : ∀ a b : ℝ, a ≤ 1 → 0 ≤ b → b ≤ 1 → a * b ≤ 1 := fun a b ha hb0 hb1 => by
    nlinarith [mul_nonneg (sub_nonneg.2 ha) hb0]
  refine hm _ _ (hm _ _ (hm _ _ (hm _ _ (hm _ _ ?_ (abs_nonneg _) ?_)
    (abs_nonneg _) ?_) (abs_nonneg _) ?_) (abs_nonneg _) ?_) (abs_nonneg _) ?_ <;> assumption

/-- The monomial of a packed key `k = (12 μ + ν) · 16⁶ + c`: `xMono c · y_{6+μ} · y_{6+ν}`. -/
noncomputable def dataMono (k : ℕ) : Mono :=
  Mono.mul (Mono.mul (xMono (Nat.mod k 16777216))
    (Mono.var (Nat.add 6 (Nat.div (Nat.div k 16777216) 12))))
    (Mono.var (Nat.add 6 (Nat.mod (Nat.div k 16777216) 12)))

theorem eval_dataMono (y : ℕ → ℝ) (k : ℕ) :
    (dataMono k).eval y =
      xVal y (k % 16777216) * y (6 + k / 16777216 / 12) * y (6 + k / 16777216 % 12) := by
  simp only [dataMono, Mono.eval_mul, Mono.eval_var, eval_xMono, nat_mod_eq, nat_div_eq,
    nat_add_eq]

/-- The single-term polynomial `c · e`, empty when `c = 0`. -/
noncomputable def term (e : Mono) (c : ℤ) : Poly := Bool.rec [(e, c)] [] (Int.beq' c 0)

theorem eval_term (y : ℕ → ℝ) (e : Mono) (c : ℤ) : (term e c).eval y = c * e.eval y := by
  rw [term]
  rcases h : Int.beq' c 0 <;> dsimp only
  · simp
  · have : c = 0 := by simpa [Int.beq'_eq] using h
    simp [this]

/-- The polynomial `∑ s · c · dataMono k` of packed data `(k, c)`, with a sign `s`, sorted by a
balanced merge of the single terms. -/
noncomputable def ofData (s : ℤ) (l : List (ℕ × ℤ)) : Poly :=
  Poly.mergeAll (Poly.lmap (fun t => term (dataMono t.1) (Int.mul s t.2)) l)

theorem eval_ofData (y : ℕ → ℝ) (s : ℤ) (l : List (ℕ × ℤ)) :
    (ofData s l).eval y = s * (l.map fun t => (t.2 : ℝ) * (dataMono t.1).eval y).sum := by
  rw [ofData, Poly.eval_mergeAll, Poly.lmap_eq, List.map_map]
  induction l with
  | nil => simp
  | cons t l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, Function.comp_apply,
      eval_term, Int.mul_def, Int.cast_mul]
    ring

/-! ### The residual bound -/

/-- `∑ |c|` over packed data. -/
noncomputable def absSum (l : List (ℕ × ℤ)) : ℕ :=
  List.rec 0 (fun t _ ih => Nat.add (Int.natAbs t.2) ih) l

/-- All keys are below `144 · 16⁶`, i.e. both quadratic-form indices are below `12`. -/
noncomputable def keysBelow (l : List (ℕ × ℤ)) : Bool :=
  List.rec true (fun t _ ih => Bool.and (Nat.blt t.1 2415919104) ih) l

/-- The squared norm `∑_{j<12} y_{6+j}²` of the quadratic-form variables. -/
noncomputable def vSq (y : ℕ → ℝ) : ℝ := ∑ j ∈ range 12, y (6 + j) ^ 2

theorem sq_le_vSq (y : ℕ → ℝ) {j : ℕ} (hj : j < 12) : y (6 + j) ^ 2 ≤ vSq y :=
  single_le_sum (f := fun j => y (6 + j) ^ 2) (fun _ _ => sq_nonneg _) (mem_range.2 hj)

theorem abs_eval_dataMono_le {y : ℕ → ℝ} (hy : ∀ i < 6, |y i| ≤ 1) {k : ℕ}
    (hk : k < 2415919104) : |(dataMono k).eval y| ≤ vSq y := by
  rw [eval_dataMono, abs_mul, abs_mul]
  have h1 : k / 16777216 / 12 < 12 := by omega
  have h2 : k / 16777216 % 12 < 12 := by omega
  have ha := sq_le_vSq y h1
  have hb := sq_le_vSq y h2
  have hx := abs_xVal_le_one hy (k % 16777216)
  set a := y (6 + k / 16777216 / 12)
  set b := y (6 + k / 16777216 % 12)
  have hab : |a| * |b| ≤ vSq y := by
    nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|), abs_nonneg a, abs_nonneg b]
  calc |xVal y (k % 16777216)| * |a| * |b| ≤ 1 * (|a| * |b|) := by
        rw [mul_assoc]; gcongr
    _ ≤ vSq y := by linarith

theorem neg_absSum_mul_le_eval_ofData {y : ℕ → ℝ} (hy : ∀ i < 6, |y i| ≤ 1)
    (l : List (ℕ × ℤ)) (hl : keysBelow l = true) :
    -((absSum l : ℝ) * vSq y) ≤ (ofData 1 l).eval y := by
  rw [eval_ofData, Int.cast_one, one_mul]
  induction l with
  | nil => simp [absSum]
  | cons t l ih =>
    change Bool.and (Nat.blt t.1 2415919104) (keysBelow l) = true at hl
    rw [Bool.and_eq_true, Nat.blt_eq] at hl
    change -(((Int.natAbs t.2 + absSum l : ℕ) : ℝ) * vSq y) ≤ _
    rw [List.map_cons, List.sum_cons]
    have h1 := abs_eval_dataMono_le hy hl.1
    have h2 := ih hl.2
    have h3 : -((Int.natAbs t.2 : ℝ) * vSq y) ≤ (t.2 : ℝ) * (dataMono t.1).eval y := by
      have : |(t.2 : ℝ) * (dataMono t.1).eval y| ≤ (Int.natAbs t.2 : ℝ) * vSq y := by
        have hc : ((Int.natAbs t.2 : ℕ) : ℝ) = |(t.2 : ℝ)| := by
          rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
        rw [abs_mul, hc]
        exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      exact neg_le_of_abs_le this
    push_cast
    linarith

/-! ### Gram blocks -/

/-- The dot product of two integer lists (truncated to the shorter one). -/
noncomputable def dot (a : List ℤ) : List ℤ → ℤ :=
  List.rec (motive := fun _ => List ℤ → ℤ) (fun _ => 0)
    (fun x _ ih b => List.rec (motive := fun _ => ℤ) 0 (fun z b' _ => Int.add (Int.mul x z) (ih b'))
      b) a

theorem dot_eq_sum : ∀ (a b : List ℤ) (n : ℕ), a.length ≤ n →
    dot a b = ∑ i ∈ range n, a.getD i 0 * b.getD i 0
  | [], b, n, _ => by simp [dot]
  | x :: a, [], n, _ => by simp [dot]
  | x :: a, z :: b, n + 1, h => by
    change Int.add (Int.mul x z) (dot a b) = _
    rw [sum_range_succ', dot_eq_sum a b n (by simpa using h)]
    simp only [List.getD_cons_succ, List.getD_cons_zero, Int.add_def, Int.mul_def]
    ring

/-- A basis monomial `xMono c · y_{6+μ}`. -/
noncomputable def basisMono (r : ℕ × ℕ × List ℤ) : Mono :=
  Mono.mul (xMono r.1) (Mono.var (Nat.add 6 r.2.1))

/-- The terms `s · (L Lᵀ)_{rs} b_r b_s` of a Gram block with rows `(code, μ, row of L)`. -/
noncomputable def blockTerms (sc : ℤ) (rows : List (ℕ × ℕ × List ℤ)) : List Poly :=
  Poly.lflatMap (fun r => Poly.lmap (fun s => term (Mono.mul (basisMono r) (basisMono s))
    (Int.mul sc (dot r.2.2 s.2.2))) rows) rows

/-- The Gram block polynomial `s · ∑_{r,s} (L Lᵀ)_{rs} b_r b_s`. -/
noncomputable def blockPoly (sc : ℤ) (rows : List (ℕ × ℕ × List ℤ)) : Poly :=
  Poly.mergeAll (blockTerms sc rows)

/-- The value of the linear form `∑_r L_{ri} b_r`. -/
noncomputable def linForm (y : ℕ → ℝ) (rows : List (ℕ × ℕ × List ℤ)) (i : ℕ) : ℝ :=
  (rows.map fun r => ((r.2.2.getD i 0 : ℤ) : ℝ) * (basisMono r).eval y).sum

theorem list_sum_finset_sum {α : Type*} (l : List α) (f : α → ℕ → ℝ) (s : Finset ℕ) :
    (l.map fun a => ∑ i ∈ s, f a i).sum = ∑ i ∈ s, (l.map fun a => f a i).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, sum_add_distrib]

theorem sum_map_flatMap {α β : Type*} (l : List α) (f : α → List β) (g : β → ℝ) :
    ((l.flatMap f).map g).sum = (l.map fun a => ((f a).map g).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem eval_blockPoly (y : ℕ → ℝ) (sc : ℤ) (rows : List (ℕ × ℕ × List ℤ)) :
    (blockPoly sc rows).eval y =
      sc * ∑ i ∈ range (rows.map fun r => r.2.2.length).sum, linForm y rows i ^ 2 := by
  set n := (rows.map fun r => r.2.2.length).sum
  have hn : ∀ r ∈ rows, r.2.2.length ≤ n := fun r hr =>
    List.le_sum_of_mem (List.mem_map.2 ⟨r, hr, rfl⟩)
  set g : ℕ × ℕ × List ℤ → ℕ → ℝ := fun r i => ((r.2.2.getD i 0 : ℤ) : ℝ) * (basisMono r).eval y
  have h : ∀ r ∈ rows, ∀ s ∈ rows, (Poly.eval y (term (Mono.mul (basisMono r) (basisMono s))
      (Int.mul sc (dot r.2.2 s.2.2)))) = sc * ∑ i ∈ range n, g r i * g s i := by
    intro r hr s _
    rw [eval_term, Mono.eval_mul, dot_eq_sum _ _ n (hn r hr), Int.mul_def]
    push_cast
    rw [mul_assoc, Finset.sum_mul]
    congr 1
    exact sum_congr rfl fun i _ => by simp only [g]; ring
  rw [blockPoly, Poly.eval_mergeAll, blockTerms, Poly.lflatMap_eq, sum_map_flatMap]
  simp only [Poly.lmap_eq, List.map_map, Function.comp_def]
  rw [List.map_congr_left (fun r hr => congrArg List.sum
    (List.map_congr_left (fun s hs => h r hr s hs)))]
  simp only [List.sum_map_mul_left, list_sum_finset_sum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [linForm, sq, ← List.sum_map_mul_right]

theorem eval_blockPoly_nonneg (y : ℕ → ℝ) {sc : ℤ} (hsc : 0 ≤ sc)
    (rows : List (ℕ × ℕ × List ℤ)) : 0 ≤ (blockPoly sc rows).eval y := by
  rw [eval_blockPoly]
  exact mul_nonneg (by exact_mod_cast hsc) (sum_nonneg fun _ _ => sq_nonneg _)

end OnePhaseDimension.LowDim.SOS
