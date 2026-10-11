/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Gram

/-!
# Block 3 of the second table, `@ 1 none B` (3 rows)

The block is expanded in 1 chunk(s) of first rows and merged, then multiplied by `χ`;
the result agrees with an independently computed reference (before and after `χ`).
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data Expand

/-- The chunks of block 3 (first row, number of first rows). -/
def gramCuts03 : List (ℕ × ℕ) := [(0, 3)]

theorem cutsCover_03 : cutsCover gramCuts03 0 (blockRows block03).length = true := by
  decide +kernel

/-- Block 3 before the multiplier `χ` (reference). -/
def gramPreRef03 : List (ℕ × ℤ) := [
  (4722366482869662122500, .ofNat 3077449198756),
  (79228162514264902751161090817, .negSucc 5343336352059),
  (79228162514264902751177868032, .negSucc 8849387819935),
  (1329227995784930077041425266101125889, .ofNat 2319391932025),
  (1329227995784930077041706741061059329, .ofNat 7682540405680),
  (1329227995784930077041988216037769984, .ofNat 6361734973504)]

set_option maxRecDepth 100000 in
/-- The chunk `[0, 3)` of block 3 equals `gramPreRef03`. -/
theorem gramChunk_03_0 :
    gramChunk block03.proj block03.rank.toNat 0 3 (blockRows block03) = gramPreRef03 := by
  rw [← gramChunk_k_eq]
  decide +kernel

set_option maxRecDepth 100000 in
/-- The collected block 3 before the multiplier. -/
theorem gramPre_03 : gramPre block03 gramCuts03 = gramPreRef03 := by
  simp only [gramPre, gramCuts03, List.map_cons, List.map_nil]
  rw [gramChunk_03_0, ← Poly.mergeAll_k_eq]
  decide +kernel

/-- Block 3 (reference). -/
def gramRef03 : List (ℕ × ℤ) := [
  (4722366482869662122500, .ofNat 3077449198756),
  (4722510598057737978372, .negSucc 3077449198755),
  (79228162514264902751161090817, .negSucc 5343336352059),
  (79228162514264902751177868032, .negSucc 11926837018691),
  (79230580365904132009510503169, .ofNat 5343336352060),
  (79230580365904132009527280384, .ofNat 8849387819936),
  (1329227995784930077041425266101125889, .ofNat 2319391932025),
  (1329227995784930077041706741061059329, .ofNat 13025876757740),
  (1329227995784930077041988216037769984, .ofNat 15211122793440),
  (1329268560604137380382273160603697921, .negSucc 2319391932024),
  (1329268560604137380382554635563631361, .negSucc 7682540405679),
  (1329268560604137380382836110540342016, .negSucc 6361734973503),
  (22300745198530940675583146901292185450382081, .negSucc 2319391932024),
  (22300745198530940675587869267775055078818561, .negSucc 7682540405679),
  (22300745198530940675592591634257924724032256, .negSucc 6361734973503)]

set_option maxRecDepth 100000 in
/-- The Gram contribution of block 3. -/
theorem gramBlock_03 : gramBlock block03 gramCuts03 = gramRef03 := by
  rw [show gramBlock block03 gramCuts03 = mulChi (gramPre block03 gramCuts03) from rfl,
    gramPre_03, ← mulChi_k_eq]
  decide +kernel

end OnePhaseDimension.Certificate.Collect
