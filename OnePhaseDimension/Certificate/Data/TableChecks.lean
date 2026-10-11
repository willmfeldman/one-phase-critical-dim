/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Polynomials
public import OnePhaseDimension.Certificate.Data.TableI
public import OnePhaseDimension.Certificate.Data.TableII
public import OnePhaseDimension.Certificate.Data.TableII.Spike

/-!
# Structural checks of the coefficient tables

Checked by `decide` on the transcribed data:

* the row counts of the first table (`34, 57, 34, 74, 32` rows for `f, U, K, M, P`, 231 in all)
  and of the second table (21 blocks; 19 interior blocks with 529 rows; two boundary blocks with
  14 rows each; 557 rows in all), and that every block has a constant number of columns;
* the shape assertions of the source about the first table: every row is free of `X, ℓ, w, z`,
  every free slot occurs exactly once and the rank is that of the family; the `U` and `K` rows
  have an even number of `p` endpoints; every `P` row has a positive power of `g`;
* the decoding examples `𝓜₀(200550) = g²|p|²`, `𝓜₄(000500520131)_{lijk} = p_l p_j A_{ik}` and
  `𝓜₁(000771700)_l = q_l` at the level of keys (their values are computed in
  `OnePhaseDimension.Certificate.Eval`);
* that the two blocks used by the engine's regression checks agree with the full table.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Data

/-- The rows of the family `F` of the first table as (coefficient, key) pairs. -/
def famEntries (F : Fam) : List (ℤ × Key) :=
  (tableI.filter fun r => r.fam == F).map fun r => (r.coef, r.key)

/-! ### Row counts -/

theorem tableI_length : tableI.length = 231 := by decide +kernel

theorem famEntries_lengths :
    [(famEntries .f).length, (famEntries .U).length, (famEntries .K).length,
      (famEntries .M).length, (famEntries .P).length] = [34, 57, 34, 74, 32] := by
  decide +kernel

theorem tableII_length : tableII.length = 21 := by decide +kernel

theorem tableII_rows : tableII.map (fun b => b.rows.length) =
    [1, 1, 12, 3, 62, 20, 50, 2, 44, 11, 15, 78, 73, 32, 31, 27, 29, 20, 18, 14, 14] := by
  decide +kernel

theorem tableII_cols : tableII.map (fun b => b.rows.map fun r => r.2.2.length) =
    tableII.map (fun b => b.rows.map fun _ => (b.rows.headD (0, 0, [])).2.2.length) := by
  decide +kernel

theorem tableII_headers : tableII.map (fun b => (b.rank, b.proj, b.mode)) =
    [(0, .none, .I), (0, .none, .I), (1, .none, .I), (1, .none, .B), (2, .sym, .I),
      (2, .anti, .I), (2, .sym, .I), (2, .anti, .I), (2, .sym, .B), (2, .anti, .B),
      (2, .sym, .B), (3, .sym, .I), (3, .hook, .I), (3, .sym, .I), (3, .hook, .I), (3, .sym, .B),
      (3, .hook, .B), (3, .sym, .B), (3, .hook, .B), (-1, .none, .I), (-1, .none, .H)] := by
  decide +kernel

theorem tableIIInterior_rows : (tableIIInterior.map fun b => b.rows.length).sum = 529 := by
  decide +kernel

/-! ### Shape of the rows of the first table -/

theorem rowsOfRank_famEntries_f : RowsOfRank (famEntries .f) 0 :=
  rowsOfRank_of_check (by decide +kernel)

theorem rowsOfRank_famEntries_U : RowsOfRank (famEntries .U) 2 :=
  rowsOfRank_of_check (by decide +kernel)

theorem rowsOfRank_famEntries_K : RowsOfRank (famEntries .K) 4 :=
  rowsOfRank_of_check (by decide +kernel)

theorem rowsOfRank_famEntries_M : RowsOfRank (famEntries .M) 1 :=
  rowsOfRank_of_check (by decide +kernel)

theorem rowsOfRank_famEntries_P : RowsOfRank (famEntries .P) 1 :=
  rowsOfRank_of_check (by decide +kernel)

theorem even_pCount_famEntries_U : ∀ t ∈ famEntries .U, Even t.2.pCount :=
  even_pCount_of_check (by decide +kernel)

theorem even_pCount_famEntries_K : ∀ t ∈ famEntries .K, Even t.2.pCount :=
  even_pCount_of_check (by decide +kernel)

theorem gPow_ne_zero_famEntries_P : ∀ t ∈ famEntries .P, t.2.gPow ≠ 0 :=
  gPow_ne_zero_of_check (by decide +kernel)

/-! ### Decoding examples -/

/-- `𝓜₀(200550) = g²|p|²`, which is the seventh row of the first table. -/
theorem decode_example_gp : decodeWord 0 (wordDigits 6 200550) = ⟨0, 2, 0, 0, [], [⟨.p, .p, 0⟩]⟩ ∧
    (tableI[6]?.map TableIRow.key) = some ⟨0, 2, 0, 0, [], [⟨.p, .p, 0⟩]⟩ := by
  decide +kernel

/-- `𝓜₄(000500520131)_{lijk} = p_l p_j A_{ik}`. -/
theorem decode_example_ppA : decodeWord 4 (wordDigits 12 500520131) =
    ⟨4, 0, 0, 0, [], [⟨.p, .slot 0, 0⟩, ⟨.p, .slot 2, 0⟩, ⟨.slot 1, .slot 3, 1⟩]⟩ := by
  decide +kernel

/-- `𝓜₁(000771700)_l = q_l = X_{lij} A_{ij}`. -/
theorem decode_example_q : decodeWord 1 (wordDigits 9 771700) =
    ⟨1, 0, 0, 0, [], [⟨.x 0, .x 0, 1⟩, ⟨.x 0, .slot 0, 0⟩]⟩ := by
  decide +kernel

/-! ### Agreement with the regression-check data -/

theorem rowsNoneB1_eq : rowsNoneB1 = block03.rows := by decide +kernel

theorem rowsSymI3_eq : rowsSymI3 = block11.rows := by decide +kernel

end OnePhaseDimension.Certificate.Data
