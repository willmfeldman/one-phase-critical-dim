/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Remainder
public import OnePhaseDimension.Certificate.Collect.GramSound

/-!
# The collected Gram part is nonnegative

For each of the 19 interior blocks the kernel checks that its chunks partition the rows, that
its rows are linear keys of the block's rank, that the collected block (before and after the
multiplier) has no overflow marker, and, for blocks with multiplier `χ`, that the collected
block before `χ` consists of linear scalar keys. Hence, on admissible data with
`g² + |p|² ≤ 1`, every collected block, and their merge `gammaPoly`, is nonnegative.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data

theorem blockOK_00 : blockOK block00 gramCuts00 gramRef00 gramRef00 = true := by
  decide +kernel

theorem blockOK_01 : blockOK block01 gramCuts01 gramRef01 gramRef01 = true := by
  decide +kernel

theorem blockOK_02 : blockOK block02 gramCuts02 gramRef02 gramRef02 = true := by
  decide +kernel

theorem blockOK_03 : blockOK block03 gramCuts03 gramPreRef03 gramRef03 = true := by
  decide +kernel

theorem blockOK_04 : blockOK block04 gramCuts04 gramRef04 gramRef04 = true := by
  decide +kernel

theorem blockOK_05 : blockOK block05 gramCuts05 gramRef05 gramRef05 = true := by
  decide +kernel

theorem blockOK_06 : blockOK block06 gramCuts06 gramRef06 gramRef06 = true := by
  decide +kernel

theorem blockOK_07 : blockOK block07 gramCuts07 gramRef07 gramRef07 = true := by
  decide +kernel

theorem blockOK_08 : blockOK block08 gramCuts08 gramPreRef08 gramRef08 = true := by
  decide +kernel

theorem blockOK_09 : blockOK block09 gramCuts09 gramPreRef09 gramRef09 = true := by
  decide +kernel

theorem blockOK_10 : blockOK block10 gramCuts10 gramPreRef10 gramRef10 = true := by
  decide +kernel

theorem blockOK_11 : blockOK block11 gramCuts11 gramRef11 gramRef11 = true := by
  decide +kernel

theorem blockOK_12 : blockOK block12 gramCuts12 gramRef12 gramRef12 = true := by
  decide +kernel

theorem blockOK_13 : blockOK block13 gramCuts13 gramRef13 gramRef13 = true := by
  decide +kernel

theorem blockOK_14 : blockOK block14 gramCuts14 gramRef14 gramRef14 = true := by
  decide +kernel

theorem blockOK_15 : blockOK block15 gramCuts15 gramPreRef15 gramRef15 = true := by
  decide +kernel

theorem blockOK_16 : blockOK block16 gramCuts16 gramPreRef16 gramRef16 = true := by
  decide +kernel

theorem blockOK_17 : blockOK block17 gramCuts17 gramPreRef17 gramRef17 = true := by
  decide +kernel

theorem blockOK_18 : blockOK block18 gramCuts18 gramPreRef18 gramRef18 = true := by
  decide +kernel

/-- The collected Gram part is nonnegative on admissible data with `g² + |p|² ≤ 1`. -/
theorem gammaPoly_eval_nonneg_of {d : CertData} (hd : d.Admissible)
    (hχ : ∑ a, d.p a ^ 2 + d.g ^ 2 ≤ 1) (ι : ℕ → Fin 5) : 0 ≤ gammaPoly.eval d ι := by
  have h00 := gramBlock_eval_nonneg ι hd hχ gramPre_00 gramBlock_00 blockOK_00
  have h01 := gramBlock_eval_nonneg ι hd hχ gramPre_01 gramBlock_01 blockOK_01
  have h02 := gramBlock_eval_nonneg ι hd hχ gramPre_02 gramBlock_02 blockOK_02
  have h03 := gramBlock_eval_nonneg ι hd hχ gramPre_03 gramBlock_03 blockOK_03
  have h04 := gramBlock_eval_nonneg ι hd hχ gramPre_04 gramBlock_04 blockOK_04
  have h05 := gramBlock_eval_nonneg ι hd hχ gramPre_05 gramBlock_05 blockOK_05
  have h06 := gramBlock_eval_nonneg ι hd hχ gramPre_06 gramBlock_06 blockOK_06
  have h07 := gramBlock_eval_nonneg ι hd hχ gramPre_07 gramBlock_07 blockOK_07
  have h08 := gramBlock_eval_nonneg ι hd hχ gramPre_08 gramBlock_08 blockOK_08
  have h09 := gramBlock_eval_nonneg ι hd hχ gramPre_09 gramBlock_09 blockOK_09
  have h10 := gramBlock_eval_nonneg ι hd hχ gramPre_10 gramBlock_10 blockOK_10
  have h11 := gramBlock_eval_nonneg ι hd hχ gramPre_11 gramBlock_11 blockOK_11
  have h12 := gramBlock_eval_nonneg ι hd hχ gramPre_12 gramBlock_12 blockOK_12
  have h13 := gramBlock_eval_nonneg ι hd hχ gramPre_13 gramBlock_13 blockOK_13
  have h14 := gramBlock_eval_nonneg ι hd hχ gramPre_14 gramBlock_14 blockOK_14
  have h15 := gramBlock_eval_nonneg ι hd hχ gramPre_15 gramBlock_15 blockOK_15
  have h16 := gramBlock_eval_nonneg ι hd hχ gramPre_16 gramBlock_16 blockOK_16
  have h17 := gramBlock_eval_nonneg ι hd hχ gramPre_17 gramBlock_17 blockOK_17
  have h18 := gramBlock_eval_nonneg ι hd hχ gramPre_18 gramBlock_18 blockOK_18
  simp only [gammaPoly, Poly.eval_mergeAll, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil]
  linarith

end OnePhaseDimension.Certificate.Collect
