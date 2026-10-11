/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Gram.Block00
public import OnePhaseDimension.Certificate.Collect.Gram.Block01
public import OnePhaseDimension.Certificate.Collect.Gram.Block02
public import OnePhaseDimension.Certificate.Collect.Gram.Block03
public import OnePhaseDimension.Certificate.Collect.Gram.Block04
public import OnePhaseDimension.Certificate.Collect.Gram.Block05
public import OnePhaseDimension.Certificate.Collect.Gram.Block06
public import OnePhaseDimension.Certificate.Collect.Gram.Block07
public import OnePhaseDimension.Certificate.Collect.Gram.Block08
public import OnePhaseDimension.Certificate.Collect.Gram.Block09
public import OnePhaseDimension.Certificate.Collect.Gram.Block10
public import OnePhaseDimension.Certificate.Collect.Gram.Block11
public import OnePhaseDimension.Certificate.Collect.Gram.Block12
public import OnePhaseDimension.Certificate.Collect.Gram.Block13
public import OnePhaseDimension.Certificate.Collect.Gram.Block14
public import OnePhaseDimension.Certificate.Collect.Gram.Block15
public import OnePhaseDimension.Certificate.Collect.Gram.Block16
public import OnePhaseDimension.Certificate.Collect.Gram.Block17
public import OnePhaseDimension.Certificate.Collect.Gram.Block18
public import OnePhaseDimension.Certificate.Collect.InteriorTotal
public import OnePhaseDimension.Certificate.Collect.KeyTypes

/-!
# The interior remainder `E = Γ + ∑ d_i y_i² − 𝓘`

With `y = (w, z, ℓ, X)` and `d = (2/25, 2/25, 1/4, 1)`, the remainder is collected from the
19 Gram blocks, the four squares `d_i y_i²` and the interior expression, all scaled by `Q²`.
The kernel checks that it has exactly the 1714 keys and coefficients of the reference (whose
key types are counted in `OnePhaseDimension.Certificate.Collect.KeyTypes`).
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data

/-- The collected Gram part `Q² Γ`: the merge of the 19 interior blocks. -/
def gammaPoly : Poly :=
  Poly.mergeAll [gramBlock block00 gramCuts00, gramBlock block01 gramCuts01,
    gramBlock block02 gramCuts02, gramBlock block03 gramCuts03, gramBlock block04 gramCuts04,
    gramBlock block05 gramCuts05, gramBlock block06 gramCuts06, gramBlock block07 gramCuts07,
    gramBlock block08 gramCuts08, gramBlock block09 gramCuts09, gramBlock block10 gramCuts10,
    gramBlock block11 gramCuts11, gramBlock block12 gramCuts12, gramBlock block13 gramCuts13,
    gramBlock block14 gramCuts14, gramBlock block15 gramCuts15, gramBlock block16 gramCuts16,
    gramBlock block17 gramCuts17, gramBlock block18 gramCuts18]

/-- The key `w²`. -/
def wSqKey : Key := ⟨0, 0, 2, 0, [], []⟩

/-- The key `|X|² = X_{abc} Y_{abc}`. -/
def xSqKey : Key := ⟨0, 0, 0, 0, [], [⟨.x 0, .x 1, 0⟩, ⟨.x 0, .x 1, 0⟩, ⟨.x 0, .x 1, 0⟩]⟩

/-- The squares `Q² ∑ d_i y_i²`, `d = (2/25, 2/25, 1/4, 1)`, `Q² = 62500000000`. -/
def ySqPoly : Poly :=
  Poly.mergeAll [Key.term 5000000000 wSqKey, Key.term 5000000000 (zKey 2),
    Key.term 15625000000 ellSqKey, Key.term 62500000000 xSqKey]

/-- The collected remainder `Q² E = Q² (Γ + ∑ d_i y_i² − 𝓘)`. -/
def remainderPoly : Poly := Poly.mergeAll [gammaPoly, ySqPoly, Poly.smul (-1) interiorPoly]

set_option maxRecDepth 100000 in
/-- The collected remainder is the reference list of 1714 keys. -/
theorem collect_E : remainderPoly = remainderRef := by
  rw [remainderPoly, gammaPoly, gramBlock_00, gramBlock_01, gramBlock_02, gramBlock_03,
    gramBlock_04, gramBlock_05, gramBlock_06, gramBlock_07, gramBlock_08, gramBlock_09,
    gramBlock_10, gramBlock_11, gramBlock_12, gramBlock_13, gramBlock_14, gramBlock_15,
    gramBlock_16, gramBlock_17, gramBlock_18, interiorPoly_eq]
  simp only [← Poly.mergeAll_k_eq]
  decide +kernel

end OnePhaseDimension.Certificate.Collect
