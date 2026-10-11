/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Spike.Expand
public import OnePhaseDimension.Certificate.Data.TableII.Spike

/-!
# Kernel expansion of the block `@ 1 none B`

The block has three rank-one rows and one coefficient column. Its Gram contribution
`Q² ∑_c ⟨J_c, J_c⟩` is collected, and then multiplied by `χ = 1 - |p|² - g²`. Both results are
checked by kernel reduction against independently computed reference lists (packed canonical
keys with `Q²`-scaled integer coefficients).
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Spike

open Expand Data

/-- The collected block before multiplication by `χ` (reference). -/
def expectedNoneB1Pre : List (ℕ × ℤ) := [
  (4722366482869662122500, .ofNat 3077449198756),
  (79228162514264902751161090817, .negSucc 5343336352059),
  (79228162514264902751177868032, .negSucc 8849387819935),
  (1329227995784930077041425266101125889, .ofNat 2319391932025),
  (1329227995784930077041706741061059329, .ofNat 7682540405680),
  (1329227995784930077041988216037769984, .ofNat 6361734973504)]

/-- The collected block multiplied by `χ` (reference). -/
def expectedNoneB1 : List (ℕ × ℤ) := [
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

theorem block_1_none_B_pre :
    block 0 1 (rowsNoneB1.map (decodeRow 1)) = expectedNoneB1Pre := by
  rw [block, ← blockChunk_k_eq]
  decide +kernel

theorem block_1_none_B :
    mulChi (block 0 1 (rowsNoneB1.map (decodeRow 1))) = expectedNoneB1 := by
  rw [block_1_none_B_pre, ← mulChi_k_eq]
  decide +kernel

end OnePhaseDimension.Certificate.Spike
