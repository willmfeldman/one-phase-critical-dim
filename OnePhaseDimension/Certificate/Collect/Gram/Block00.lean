/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Gram

/-!
# Block 0 of the second table, `@ 0 none I` (1 rows)

The block is expanded in 1 chunk(s) of first rows and merged;
the result agrees with an independently computed reference.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data Expand

/-- The chunks of block 0 (first row, number of first rows). -/
def gramCuts00 : List (ℕ × ℕ) := [(0, 1)]

theorem cutsCover_00 : cutsCover gramCuts00 0 (blockRows block00).length = true := by
  decide +kernel

/-- Block 0 (reference). -/
def gramRef00 : List (ℕ × ℤ) := [
  (281475010265088, .ofNat 144)]

set_option maxRecDepth 100000 in
/-- The chunk `[0, 1)` of block 0 equals `gramRef00`. -/
theorem gramChunk_00_0 :
    gramChunk block00.proj block00.rank.toNat 0 1 (blockRows block00) = gramRef00 := by
  rw [← gramChunk_k_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The collected block 0 before the multiplier. -/
theorem gramPre_00 : gramPre block00 gramCuts00 = gramRef00 := by
  simp only [gramPre, gramCuts00, List.map_cons, List.map_nil]
  rw [gramChunk_00_0, ← Poly.mergeAll_k_eq]
  decide +kernel

/-- The Gram contribution of block 0. -/
theorem gramBlock_00 : gramBlock block00 gramCuts00 = gramRef00 :=
  gramPre_00

end OnePhaseDimension.Certificate.Collect
