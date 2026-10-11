/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Gram
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C0
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C7
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C15
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C24
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C35
public import OnePhaseDimension.Certificate.Collect.Gram.Block12C51
public import OnePhaseDimension.Certificate.Collect.Gram.Block12GramRef12Part0
public import OnePhaseDimension.Certificate.Collect.Gram.Block12GramRef12Part1

/-!
# Block 12 of the second table, `@ 3 hook I` (73 rows)

The block is expanded in 6 chunk(s) of first rows and merged;
the result agrees with an independently computed reference.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data Expand

/-- The chunks of block 12 (first row, number of first rows). -/
def gramCuts12 : List (ℕ × ℕ) := [(0, 7), (7, 8), (15, 9), (24, 11), (35, 16),
    (51, 22)]

theorem cutsCover_12 : cutsCover gramCuts12 0 (blockRows block12).length = true := by
  decide +kernel

/-- Block 12 (reference). -/
def gramRef12 : List (ℕ × ℤ) := gramRef12Part0 ++ gramRef12Part1

set_option maxRecDepth 100000 in
/-- The collected block 12 before the multiplier. -/
theorem gramPre_12 : gramPre block12 gramCuts12 = gramRef12 := by
  simp only [gramPre, gramCuts12, List.map_cons, List.map_nil]
  rw [gramChunk_12_0, gramChunk_12_7, gramChunk_12_15, gramChunk_12_24,
    gramChunk_12_35, gramChunk_12_51, ← Poly.mergeAll_k_eq]
  decide +kernel

/-- The Gram contribution of block 12. -/
theorem gramBlock_12 : gramBlock block12 gramCuts12 = gramRef12 :=
  gramPre_12

end OnePhaseDimension.Certificate.Collect
