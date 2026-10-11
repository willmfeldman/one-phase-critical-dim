/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Matching
public import OnePhaseDimension.Certificate.Data.TableII

/-!
# Expansion of the Gram blocks

A block of the second table with rank `r`, projection `Π` and rows `s_1, …, s_N` with
coefficient columns `(c_{tc})` contributes `ρ ∑_c ⟨J_c, Π J_c⟩`, `J_c = Q⁻¹ ∑_t c_{tc} 𝓜(s_t)`.
Scaled by `Q²`, it is the sum over unordered pairs `s ≤ t` of the weight `∑_c c_{sc} c_{tc}`
(doubled when `s ≠ t`) times `⟨𝓜(s_t), Π 𝓜(s_s)⟩`, multiplied by `ρ = 1` (mode `I`) or
`χ = 1 - |p|² - g²` (mode `B`, applied once to the collected block).

The pair terms are the matching forms of the four projections:
* `none`: `⟨T, S⟩`;
* `anti` (rank `2`): `⟨T, S⟩ - ⟨T, S^{(12)}⟩`;
* `sym` (ranks `2, 3`) and `hook` (rank `3`): `Expand.pairTerms` and `Expand.hookTerms`.

A block is expanded in chunks of consecutive first rows `[a, a + n)`; the chunks of a block
are merged. `cutsCover` checks that the chunks partition the rows.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data Expand

/-- The pair terms of `⟨T, Π S⟩` for the `anti` projection of rank `2`. -/
def antiTerms (S T : Key) : List (ℤ × Key) :=
  [(1, (S.mul T).contractPairs 2), (-1, ((S.permSlots [1, 0]).mul T).contractPairs 2)]

/-- The pair terms of `⟨T, Π S⟩` for a projection label and a rank. -/
def gramPairTerms : Proj → ℕ → Key → Key → List (ℤ × Key)
  | .none, r => pairTerms 0 r
  | .sym, r => pairTerms 1 r
  | .anti, _ => antiTerms
  | .hook, _ => hookTerms

/-- The decoded rows of a block (rank `-1` blocks are not expanded here). -/
def blockRows (b : Block) : List Row := b.rows.map (decodeRow b.rank.toNat)

/-- The chunk of a Gram block with first rows `a ≤ s < a + n`, scaled by `Q²`, before `ρ`. -/
def gramChunk (pj : Proj) (r a n : ℕ) (rows : List Row) : Poly :=
  Poly.mergeAll (blockTermsWith (gramPairTerms pj r) n (rows.drop a))

/-- The chunks `(a, n)` partition `[0, N)`: they are consecutive and start at `0`. -/
def cutsCover : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], a, N => a == N
  | c :: cs, a, N => c.1 == a && 0 < c.2 && cutsCover cs (a + c.2) N

/-- The collected block before the multiplier, as the merge of its chunks. -/
def gramPre (b : Block) (cuts : List (ℕ × ℕ)) : Poly :=
  Poly.mergeAll (cuts.map fun c => gramChunk b.proj b.rank.toNat c.1 c.2 (blockRows b))

/-- The Gram contribution of a block, scaled by `Q²`. -/
def gramBlock (b : Block) (cuts : List (ℕ × ℕ)) : Poly :=
  match b.mode with
  | .B => mulChi (gramPre b cuts)
  | _ => gramPre b cuts

/-! ### Kernel versions -/

/-- `antiTerms` by recursors. -/
noncomputable def antiTerms_k (S T : Key) : List (ℤ × Key) :=
  [(1, (S.mul_k T).contractPairs_k 2), (-1, ((S.permSlots_k [1, 0]).mul_k T).contractPairs_k 2)]

/-- `gramPairTerms` by recursors. -/
noncomputable def gramPairTerms_k (pj : Proj) (r : ℕ) : Key → Key → List (ℤ × Key) :=
  Proj.rec (motive := fun _ => Key → Key → List (ℤ × Key)) (pairTerms_k 0 r) antiTerms_k
    (pairTerms_k 1 r) hookTerms_k pj

/-- `gramChunk` by recursors. -/
noncomputable def gramChunk_k (pj : Proj) (r a n : ℕ) (rows : List Row) : Poly :=
  Poly.mergeAll_k (blockTermsWith_k (gramPairTerms_k pj r) n (ldrop_k a rows))

theorem antiTerms_k_eq : antiTerms_k = antiTerms := by
  funext S T
  simp only [antiTerms_k, antiTerms, Key.mul_k_eq, Key.contractPairs_k_eq, Key.permSlots_k_eq]

theorem gramPairTerms_k_eq (pj : Proj) (r : ℕ) : gramPairTerms_k pj r = gramPairTerms pj r := by
  funext S T
  cases pj <;>
    simp only [gramPairTerms_k, gramPairTerms, pairTerms_k_eq, antiTerms_k_eq, hookTerms_k_eq]

theorem gramChunk_k_eq (pj : Proj) (r a n : ℕ) (rows : List Row) :
    gramChunk_k pj r a n rows = gramChunk pj r a n rows := by
  rw [gramChunk_k, gramChunk, Poly.mergeAll_k_eq, gramPairTerms_k_eq, blockTermsWith_k_eq,
    ldrop_k_eq]

/-! ### The `anti` pair terms evaluate to `⟨T, Π S⟩` -/

section Anti

variable {d : CertData} (hd : d.Admissible) {S T : Key} (hS : S.Linear) (hT : T.Linear)
include hd hS hT

/-- `anti`, rank two: the pair terms evaluate to `⟨T, Π S⟩`. -/
theorem antiTerms_eq (hS2 : S.rank = 2) (hT2 : T.rank = 2) (ι : ℕ → Fin 5) :
    ((antiTerms S T).map fun e => (e.1 : ℝ) * e.2.eval d ι).sum =
      Proj.inner2 (T.ten2 d) (Proj.projAnti2 (S.ten2 d)) := by
  simp only [antiTerms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [eval_mulTerm2 hd hS hT hS2 hT2, Key.eval_permTerm2 hd hS hT hS2 hT2 permOK_10,
    Proj.inner_projAnti2]
  simp only [Proj.inner2, Proj.swap2, idx2, List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [mul_comm]
  ring

end Anti

end OnePhaseDimension.Certificate.Collect
