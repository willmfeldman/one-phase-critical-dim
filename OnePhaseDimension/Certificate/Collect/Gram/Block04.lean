/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Gram
public import OnePhaseDimension.Certificate.Collect.Gram.Block04GramRef04Part0
public import OnePhaseDimension.Certificate.Collect.Gram.Block04GramRef04Part1

/-!
# Block 4 of the second table, `@ 2 sym I` (62 rows)

The block is expanded in 1 chunk(s) of first rows and merged;
the result agrees with an independently computed reference.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data Expand

/-- The chunks of block 4 (first row, number of first rows). -/
def gramCuts04 : List (ℕ × ℕ) := [(0, 62)]

theorem cutsCover_04 : cutsCover gramCuts04 0 (blockRows block04).length = true := by
  decide +kernel

/-- Block 4 (reference). -/
def gramRef04 : List (ℕ × ℤ) := gramRef04Part0 ++ gramRef04Part1

set_option maxRecDepth 100000 in
/-- The chunk `[0, 62)` of block 4 equals `gramRef04`. -/
theorem gramChunk_04_0 :
    gramChunk block04.proj block04.rank.toNat 0 62 (blockRows block04) = gramRef04 := by
  rw [← gramChunk_k_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The collected block 4 before the multiplier. -/
theorem gramPre_04 : gramPre block04 gramCuts04 = gramRef04 := by
  simp only [gramPre, gramCuts04, List.map_cons, List.map_nil]
  rw [gramChunk_04_0, ← Poly.mergeAll_k_eq]
  decide +kernel

/-- The Gram contribution of block 4. -/
theorem gramBlock_04 : gramBlock block04 gramCuts04 = gramRef04 :=
  gramPre_04

end OnePhaseDimension.Certificate.Collect
