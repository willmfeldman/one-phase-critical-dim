/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.RoundingA1
public import OnePhaseDimension.Certificate.Collect.RoundingA2
public import OnePhaseDimension.Certificate.Collect.RoundingB1
public import OnePhaseDimension.Certificate.Collect.RoundingB2

/-!
# Graph-bound classification and rounding of all remainder keys

Every remainder key is accepted by the graph-bound classification, and its rounded numerator
satisfies `n_t² ≥ 10¹⁰ L_t²` (checked in four parts).
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data

theorem roundingOK_append (l₁ l₂ : List (ℕ × ℤ × ℕ)) :
    roundingOK (l₁ ++ l₂) = (roundingOK l₁ && roundingOK l₂) := by
  simp only [roundingOK, List.all_append]

theorem roundingOK_remainderData : roundingOK remainderData = true := by
  have hA : roundingOK remainderDataA = true := by
    rw [← List.take_append_drop 429 remainderDataA, roundingOK_append, roundingOK_A1,
      roundingOK_A2, Bool.and_self]
  have hB : roundingOK remainderDataB = true := by
    rw [← List.take_append_drop 429 remainderDataB, roundingOK_append, roundingOK_B1,
      roundingOK_B2, Bool.and_self]
  rw [remainderData, roundingOK_append, hA, hB, Bool.and_self]

end OnePhaseDimension.Certificate.Collect
