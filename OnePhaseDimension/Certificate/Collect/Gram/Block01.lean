/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Gram

/-!
# Block 1 of the second table, `@ 0 none I` (1 rows)

The block is expanded in 1 chunk(s) of first rows and merged;
the result agrees with an independently computed reference.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data Expand

/-- The chunks of block 1 (first row, number of first rows). -/
def gramCuts01 : List (ℕ × ℕ) := [(0, 1)]

theorem cutsCover_01 : cutsCover gramCuts01 0 (blockRows block01).length = true := by
  decide +kernel

/-- Block 1 (reference). -/
def gramRef01 : List (ℕ × ℤ) := [
  (281474976841728, .ofNat 33856)]

set_option maxRecDepth 100000 in
/-- The chunk `[0, 1)` of block 1 equals `gramRef01`. -/
theorem gramChunk_01_0 :
    gramChunk block01.proj block01.rank.toNat 0 1 (blockRows block01) = gramRef01 := by
  rw [← gramChunk_k_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The collected block 1 before the multiplier. -/
theorem gramPre_01 : gramPre block01 gramCuts01 = gramRef01 := by
  simp only [gramPre, gramCuts01, List.map_cons, List.map_nil]
  rw [gramChunk_01_0, ← Poly.mergeAll_k_eq]
  decide +kernel

/-- The Gram contribution of block 1. -/
theorem gramBlock_01 : gramBlock block01 gramCuts01 = gramRef01 :=
  gramPre_01

end OnePhaseDimension.Certificate.Collect
