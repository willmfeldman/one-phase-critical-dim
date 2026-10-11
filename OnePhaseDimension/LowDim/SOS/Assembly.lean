/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.SOS.Identity
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Tactic.IntervalCases

/-!
# The interior form is bounded below on the domain

From the kernel-checked identity `total_isNil` we deduce the lower bound

  `S · Q(y) ≥ S/50 · (y₇² + y₈² + y₉² + y₁₀²)`

for every `y` with `y₀² + y₁² + (y₀ + y₁)² = 1` and `y₂² + y₃² + y₄² + y₅² ≤ 1`, where `S · Q` is
the scaled interior form `Data.qPoly`. In the identity every Gram block contributes a
nonnegative multiple of a sum of squares (the multiplier `χ = 1 − y₂² − y₃² − y₄² − y₅²` is
nonnegative on the domain), the multiple of `h = 2y₀² + 2y₀y₁ + 2y₁² − 1` vanishes, and the
residual is bounded by `(∑ |c|) · |v|²` with `1000 ∑ |c| ≤ S`, which the term `S/1000 · |v|²`
absorbs.

## Main statements

* `LowDim.SOS.qPoly_lower_bound`.
-/

@[expose] public section

namespace OnePhaseDimension.LowDim.SOS

open Data Finset

/-! ### Values of the auxiliary polynomials -/

theorem eval_sqPoly (y : ℕ → ℝ) (c : ℤ) (js : List ℕ) :
    (sqPoly c js).eval y = c * (js.map fun j => y j ^ 2).sum := by
  rw [sqPoly, Poly.eval_mergeAll, Poly.lmap_eq, List.map_map]
  induction js with
  | nil => simp
  | cons j js ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp_apply, ih, Poly.eval_cons,
      Poly.eval_nil, Mono.eval_mul, Mono.eval_var]
    ring

theorem eval_chiPoly (y : ℕ → ℝ) :
    chiPoly.eval y = 1 - y 2 ^ 2 - y 3 ^ 2 - y 4 ^ 2 - y 5 ^ 2 := by
  simp [chiPoly, Mono.eval, Mono.evalFrom]
  ring

theorem eval_hPoly (y : ℕ → ℝ) :
    hPoly.eval y = 2 * y 0 ^ 2 + 2 * y 0 * y 1 + 2 * y 1 ^ 2 - 1 := by
  simp [hPoly, Mono.eval, Mono.evalFrom]
  ring

theorem eval_blockPoly_nonpos (y : ℕ → ℝ) {sc : ℤ} (hsc : sc ≤ 0)
    (rows : List (ℕ × ℕ × List ℤ)) : (blockPoly sc rows).eval y ≤ 0 := by
  rw [eval_blockPoly]
  exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hsc)
    (sum_nonneg fun _ _ => sq_nonneg _)

theorem eval_blockWithMult_nonpos {y : ℕ → ℝ} (hχ : 0 ≤ chiPoly.eval y) {sc : ℤ} (hsc : sc ≤ 0)
    (b : Bool × List (ℕ × ℕ × List ℤ)) : (blockWithMult sc b).eval y ≤ 0 := by
  obtain ⟨f, rows⟩ := b
  cases f
  · exact eval_blockPoly_nonpos y hsc rows
  · change (Poly.mul chiPoly (blockPoly sc rows)).eval y ≤ 0
    rw [Poly.eval_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hχ (eval_blockPoly_nonpos y hsc rows)

theorem eval_blocks_nonpos {y : ℕ → ℝ} (hχ : 0 ≤ chiPoly.eval y) {sc : ℤ} (hsc : sc ≤ 0)
    (l : List (Bool × List (ℕ × ℕ × List ℤ))) :
    (Poly.mergeAll (Poly.lmap (blockWithMult sc) l)).eval y ≤ 0 := by
  rw [Poly.eval_mergeAll, Poly.lmap_eq, List.map_map]
  induction l with
  | nil => simp
  | cons b l ih =>
    rw [List.map_cons, List.sum_cons]
    exact add_nonpos (eval_blockWithMult_nonpos hχ hsc b) ih

theorem eval_ofData_neg (y : ℕ → ℝ) (l : List (ℕ × ℤ)) :
    (ofData (-1) l).eval y = -(ofData 1 l).eval y := by
  rw [eval_ofData, eval_ofData]
  push_cast
  ring

theorem negSucc_pred (n : ℕ) (hn : 0 < n) : Int.negSucc (Nat.pred n) = -(n : ℤ) := by
  rw [Int.negSucc_eq, ← Nat.cast_succ, Nat.succ_pred_eq_of_pos hn]

/-! ### Kernel-checked facts about the data -/

theorem keysBelow_residualPoly : keysBelow residualPoly = true := by
  decide +kernel

theorem absSum_residualPoly_le : Nat.ble (1000 * absSum residualPoly) scale = true := by
  decide +kernel

theorem scale_div_fifty : ((Nat.div scale 50 : ℕ) : ℝ) = (scale : ℝ) / 50 := by
  rw [show Nat.div scale 50 = scale / 50 from rfl,
    Nat.cast_div (Nat.dvd_of_mod_eq_zero (by decide +kernel)) (by norm_num)]
  norm_num

/-! ### The lower bound -/

/-- The scaled interior form is at least `S/50 · (y₇² + y₈² + y₉² + y₁₀²)` on the domain
`y₀² + y₁² + (y₀ + y₁)² = 1`, `y₂² + y₃² + y₄² + y₅² ≤ 1`. -/
theorem qPoly_lower_bound (y : ℕ → ℝ) (hα : y 0 ^ 2 + y 1 ^ 2 + (y 0 + y 1) ^ 2 = 1)
    (hp : y 2 ^ 2 + y 3 ^ 2 + y 4 ^ 2 + y 5 ^ 2 ≤ 1) :
    (scale : ℝ) / 50 * (y 7 ^ 2 + y 8 ^ 2 + y 9 ^ 2 + y 10 ^ 2) ≤ (ofData 1 qPoly).eval y := by
  have hy : ∀ i < 6, |y i| ≤ 1 := by
    intro i hi
    have h2 : y i ^ 2 ≤ 1 := by
      interval_cases i
      · nlinarith [sq_nonneg (y 1), sq_nonneg (y 0 + y 1)]
      · nlinarith [sq_nonneg (y 0), sq_nonneg (y 0 + y 1)]
      all_goals nlinarith [sq_nonneg (y 2), sq_nonneg (y 3), sq_nonneg (y 4), sq_nonneg (y 5)]
    exact abs_le.2 ⟨by nlinarith [sq_nonneg (y i + 1)], by nlinarith [sq_nonneg (y i - 1)]⟩
  have htot := congrArg (Poly.eval y) (Poly.eq_nil_of_isNil total_isNil)
  rw [total, Poly.eval_mergeAll] at htot
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Poly.eval_nil,
    add_zero, eval_sqPoly, Poly.eval_mul, eval_hPoly] at htot
  have hpos : ∀ n : ℕ, 0 < n → ((Int.negSucc (Nat.pred n) : ℤ) : ℝ) = -(n : ℝ) := fun n hn => by
    rw [negSucc_pred n hn]; push_cast; ring
  rw [hpos _ (by decide +kernel), hpos _ (by decide +kernel)] at htot
  have hχ : 0 ≤ chiPoly.eval y := by rw [eval_chiPoly]; linarith
  have hB := eval_blocks_nonpos hχ (sc := Int.negSucc (Nat.pred gramScale))
    (Int.negSucc_lt_zero _).le blocks
  have hR := neg_absSum_mul_le_eval_ofData hy residualPoly keysBelow_residualPoly
  have hR' := eval_ofData_neg y residualPoly
  have hh : 2 * y 0 ^ 2 + 2 * y 0 * y 1 + 2 * y 1 ^ 2 - 1 = 0 := by linear_combination hα
  have hV : vSq y = y 6 ^ 2 + (y 7 ^ 2 + (y 8 ^ 2 + (y 9 ^ 2 + (y 10 ^ 2 + (y 11 ^ 2 +
      (y 12 ^ 2 + (y 13 ^ 2 + (y 14 ^ 2 + (y 15 ^ 2 + (y 16 ^ 2 + y 17 ^ 2)))))))))) := by
    simp [vSq, sum_range_succ]
    ring
  have hS : (1000 * absSum residualPoly : ℝ) ≤ scale := by
    exact_mod_cast Nat.le_of_ble_eq_true absSum_residualPoly_le
  have hS1000 : ((Nat.div scale 1000 : ℕ) : ℝ) = (scale : ℝ) / 1000 := by
    rw [show Nat.div scale 1000 = scale / 1000 from rfl,
      Nat.cast_div (Nat.dvd_of_mod_eq_zero (by decide +kernel)) (by norm_num)]
    norm_num
  rw [hR', hh, ← hV, hS1000, scale_div_fifty] at htot
  have hVn : 0 ≤ vSq y := sum_nonneg fun _ _ => sq_nonneg _
  have hab : 0 ≤ ((scale : ℝ) / 1000 - absSum residualPoly) * vSq y :=
    mul_nonneg (by linarith) hVn
  generalize (ofData 1 qPoly).eval y = q at htot ⊢
  generalize (ofData 1 residualPoly).eval y = r at htot hR
  generalize Poly.eval y (Poly.mergeAll (Poly.lmap (blockWithMult (Int.negSucc gramScale.pred))
    blocks)) = b at htot hB
  generalize (absSum residualPoly : ℝ) = a at hR hab
  generalize vSq y = v at htot hR hab
  generalize (scale : ℝ) = S at htot hab ⊢
  linarith only [htot, hB, hR, hab]

end OnePhaseDimension.LowDim.SOS
