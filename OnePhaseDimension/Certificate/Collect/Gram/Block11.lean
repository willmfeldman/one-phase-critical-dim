/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Gram
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C0
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C6
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C13
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C21
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C30
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C41
public import OnePhaseDimension.Certificate.Collect.Gram.Block11C58
public import OnePhaseDimension.Certificate.Collect.Gram.Block11GramRef11Part0
public import OnePhaseDimension.Certificate.Collect.Gram.Block11GramRef11Part1

/-!
# Block 11 of the second table, `@ 3 sym I` (78 rows)

The block is expanded in 7 chunk(s) of first rows and merged;
the result agrees with an independently computed reference.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data Expand

/-- The chunks of block 11 (first row, number of first rows). -/
def gramCuts11 : List (ℕ × ℕ) := [(0, 6), (6, 7), (13, 8), (21, 9), (30, 11),
    (41, 17), (58, 20)]

theorem cutsCover_11 : cutsCover gramCuts11 0 (blockRows block11).length = true := by
  decide +kernel

/-- Block 11 (reference). -/
def gramRef11 : List (ℕ × ℤ) := gramRef11Part0 ++ gramRef11Part1

set_option maxRecDepth 100000 in
/-- The collected block 11 before the multiplier. -/
theorem gramPre_11 : gramPre block11 gramCuts11 = gramRef11 := by
  simp only [gramPre, gramCuts11, List.map_cons, List.map_nil]
  rw [gramChunk_11_0, gramChunk_11_6, gramChunk_11_13, gramChunk_11_21,
    gramChunk_11_30, gramChunk_11_41, gramChunk_11_58, ← Poly.mergeAll_k_eq]
  decide +kernel

/-- The Gram contribution of block 11. -/
theorem gramBlock_11 : gramBlock block11 gramCuts11 = gramRef11 :=
  gramPre_11

end OnePhaseDimension.Certificate.Collect
