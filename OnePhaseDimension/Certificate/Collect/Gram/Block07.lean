/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Gram

/-!
# Block 7 of the second table, `@ 2 anti I` (2 rows)

The block is expanded in 1 chunk(s) of first rows and merged;
the result agrees with an independently computed reference.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data Expand

/-- The chunks of block 7 (first row, number of first rows). -/
def gramCuts07 : List (ℕ × ℕ) := [(0, 2)]

theorem cutsCover_07 : cutsCover gramCuts07 0 (blockRows block07).length = true := by
  decide +kernel

/-- Block 7 (reference). -/
def gramRef07 : List (ℕ × ℤ) := [
  (22302786892732465684971278016184893797761792, .ofNat 22099739473296),
  (22302786892732465684971278160300081873486592, .negSucc 22099739473295),
  (374167255119801088578580815723187773768716513379072, .ofNat 18097174000104),
  (374167255119801088619066406767976850560492448580352, .negSucc 18097174000103),
  (6277293297329422804757216284084650152020258932273170285312, .ofNat 19475891227778),
  (6277293297329422805435122561934957251923567015885791101697, .negSucc 19475891227777)]

set_option maxRecDepth 100000 in
/-- The chunk `[0, 2)` of block 7 equals `gramRef07`. -/
theorem gramChunk_07_0 :
    gramChunk block07.proj block07.rank.toNat 0 2 (blockRows block07) = gramRef07 := by
  rw [← gramChunk_k_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The collected block 7 before the multiplier. -/
theorem gramPre_07 : gramPre block07 gramCuts07 = gramRef07 := by
  simp only [gramPre, gramCuts07, List.map_cons, List.map_nil]
  rw [gramChunk_07_0, ← Poly.mergeAll_k_eq]
  decide +kernel

/-- The Gram contribution of block 7. -/
theorem gramBlock_07 : gramBlock block07 gramCuts07 = gramRef07 :=
  gramPre_07

end OnePhaseDimension.Certificate.Collect
