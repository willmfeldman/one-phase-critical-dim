/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Kernel

/-!
# Expansion of a Gram block (readable version)

A Gram block of rank `r` has rows `s_1, …, s_N` (tensor monomials) and an integer coefficient
matrix `(c_{tc})`. Its contribution is `ρ ∑_c ⟨J_c, Π J_c⟩` with `J_c = Q⁻¹ ∑_t c_{tc} 𝓜(s_t)`.
We expand it over unordered pairs of rows `s ≤ t` with weight `∑_c c_{sc} c_{tc}`, doubled when
`s ≠ t`, times `⟨𝓜(s_t), Π 𝓜(s_s)⟩`; the coefficients are integers scaled by `Q²`.

The projections are used in matching form:
* `none`: `⟨T, Π S⟩ = ⟨T, S⟩`;
* `sym`, rank 2: `⟨T, Π S⟩ = 5 ∑_{π ∈ S₂} ⟨T, S^π⟩ - 2 tr T · tr S`;
* `sym`, rank 3: `⟨T, Π S⟩ = 7 ∑_{π ∈ S₃} ⟨T, S^π⟩ - 2 ⟨τ T, τ S⟩`, where
  `τ S = Tr₁₂ S + Tr₁₃ S + Tr₂₃ S` (each a vector in the remaining slot).

For mode `B` the collected block is multiplied once by `χ = 1 - |p|² - g²`.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

namespace Expand

/-- The permutations of three slots, as lists of images. -/
def perms3 : List (List ℕ) := [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

/-- The three partial traces of a rank-3 key. -/
def traces3 (k : Key) : List Key := [k.contract 0 1, k.contract 0 2, k.contract 1 2]

/-- The terms of `⟨T, Π S⟩` for the projection `kind` (`0 = none`, `1 = sym`) at rank `r`,
as a list of (weight, key) pairs before canonicalization. -/
def pairTerms (kind r : ℕ) (S T : Key) : List (ℤ × Key) :=
  if kind = 0 then [(1, (S.mul T).contractPairs r)]
  else if r = 2 then
    [(5, (S.mul T).contractPairs 2), (5, ((S.permSlots [1, 0]).mul T).contractPairs 2),
     (-2, (S.contract 0 1).mul (T.contract 0 1))]
  else
    perms3.map (fun σ => (7, ((S.permSlots σ).mul T).contractPairs 3)) ++
      (traces3 S).flatMap fun a => (traces3 T).map fun b => (-2, (a.mul b).contractPairs 1)

/-- A row: the key and its coefficient column. -/
abbrev Row := Key × List ℤ

/-- The weight `∑_c c_{sc} c_{tc}` of a pair of rows. -/
def dot : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- The terms contributed by the pairs `(s, t)` with `t` ranging over `ts` (all after `s`). -/
def pairsFrom (kind r : ℕ) (s : Row) (ts : List Row) : List Poly :=
  ts.flatMap fun t =>
    let w := 2 * dot s.2 t.2
    if w = 0 then [] else (pairTerms kind r s.1 t.1).map fun e => Key.term (w * e.1) e.2

/-- The terms of the pairs `(s, t)` with `s` among the first `n` rows of `rows` (and `t ≥ s`). -/
def blockTermsN (kind r : ℕ) : ℕ → List Row → List Poly
  | 0, _ => []
  | _, [] => []
  | n + 1, s :: ts =>
    let w := dot s.2 s.2
    ((if w = 0 then [] else (pairTerms kind r s.1 s.1).map fun e => Key.term (w * e.1) e.2) ++
      pairsFrom kind r s ts) ++ blockTermsN kind r n ts

/-- A chunk of a block: the pairs `(s, t)`, `t ≥ s`, with `a ≤ s < a + n`. -/
def blockChunk (kind r a n : ℕ) (rows : List Row) : Poly :=
  Poly.mergeAll (blockTermsN kind r n (rows.drop a))

/-- The collected Gram block before the multiplier `ρ`, scaled by `Q²`. -/
def block (kind r : ℕ) (rows : List Row) : Poly := blockChunk kind r 0 rows.length rows

/-- The multiplier `χ = 1 - |p|² - g²`. -/
def chi : List (ℤ × Key) :=
  [(1, ⟨0, 0, 0, 0, [], []⟩), (-1, ⟨0, 0, 0, 0, [], [⟨.p, .p, 0⟩]⟩), (-1, ⟨0, 2, 0, 0, [], []⟩)]

/-- Multiply a polynomial by `χ`. -/
def mulChi (P : Poly) : Poly :=
  Poly.mergeAll (P.flatMap fun t =>
    chi.map fun e => Key.term (e.1 * t.2) ((Key.unpack t.1).mul e.2))

/-- Decode a row given as `(number of digits, word, coefficients)`. -/
def decodeRow (r : ℕ) (row : ℕ × ℕ × List ℤ) : Row :=
  (decodeWord r (wordDigits row.1 row.2.1), row.2.2)

/-! ### Kernel-reducible versions -/

/-- `Expand.pairTerms` by recursors. -/
noncomputable def pairTerms_k (kind r : ℕ) (S T : Key) : List (ℤ × Key) :=
  Bool.rec
    (Bool.rec
      (lappend_k (lmap_k (fun σ => ((7 : ℤ), ((S.permSlots_k σ).mul_k T).contractPairs_k 3)) perms3)
        (lflatMap_k (fun a => lmap_k (fun b => ((-2 : ℤ), (a.mul_k b).contractPairs_k 1))
          [T.contract_k 0 1, T.contract_k 0 2, T.contract_k 1 2])
          [S.contract_k 0 1, S.contract_k 0 2, S.contract_k 1 2]))
      [(5, (S.mul_k T).contractPairs_k 2), (5, ((S.permSlots_k [1, 0]).mul_k T).contractPairs_k 2),
        (-2, (S.contract_k 0 1).mul_k (T.contract_k 0 1))]
      (Nat.beq r 2))
    [(1, (S.mul_k T).contractPairs_k r)]
    (Nat.beq kind 0)

/-- `Expand.dot` by recursors. -/
noncomputable def dot_k (l : List ℤ) : List ℤ → ℤ :=
  List.rec (motive := fun _ => List ℤ → ℤ) (fun _ => 0)
    (fun a _ ih m => List.rec (motive := fun _ => ℤ) 0 (fun b bs _ => Int.add (Int.mul a b) (ih bs))
      m) l

/-- The terms of one pair with weight `w`. -/
noncomputable def weighted_k (kind r : ℕ) (w : ℤ) (S T : Key) : List Poly :=
  Bool.rec (lmap_k (fun e => Key.term_k (Int.mul w e.1) e.2) (pairTerms_k kind r S T)) []
    (Int.beq' w 0)

/-- `Expand.pairsFrom` by recursors. -/
noncomputable def pairsFrom_k (kind r : ℕ) (s : Row) (ts : List Row) : List Poly :=
  lflatMap_k (fun t => weighted_k kind r (Int.mul 2 (dot_k s.2 t.2)) s.1 t.1) ts

/-- `Expand.blockTermsN` by recursors. -/
noncomputable def blockTermsN_k (kind r n : ℕ) (rows : List Row) : List Poly :=
  Nat.rec (motive := fun _ => List Row → List Poly) (fun _ => [])
    (fun _ ih rows => List.rec (motive := fun _ => List Poly) []
      (fun s ts _ => lappend_k (lappend_k (weighted_k kind r (dot_k s.2 s.2) s.1 s.1)
        (pairsFrom_k kind r s ts)) (ih ts)) rows) n rows

/-- `List.drop` by recursors. -/
noncomputable def ldrop_k {α : Type} (n : ℕ) (l : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun l => l)
    (fun _ ih l => ih (List.rec (motive := fun _ => List α) [] (fun _ t _ => t) l)) n l

/-- `Expand.blockChunk` by recursors. -/
noncomputable def blockChunk_k (kind r a n : ℕ) (rows : List Row) : Poly :=
  Poly.mergeAll_k (blockTermsN_k kind r n (ldrop_k a rows))

/-- `Expand.mulChi` by recursors (keys are unpacked with `Key.unpack`). -/
noncomputable def mulChi_k (P : Poly) : Poly :=
  Poly.mergeAll_k (lflatMap_k (fun t =>
    lmap_k (fun e => Key.term_k (Int.mul e.1 t.2) ((Key.unpack t.1).mul_k e.2)) chi) P)

/-! ### Agreement of the kernel versions with the readable ones -/

theorem pairTerms_k_eq (kind r : ℕ) (S T : Key) :
    pairTerms_k kind r S T = pairTerms kind r S T := by
  simp only [pairTerms_k, pairTerms, brec_eq_ite, Nat.beq_eq, lappend_k_eq, lmap_k_eq,
    lflatMap_k_eq, Key.mul_k_eq, Key.contractPairs_k_eq, Key.permSlots_k_eq, Key.contract_k_eq,
    traces3]

theorem dot_k_eq (l m : List ℤ) : dot_k l m = dot l m := by
  induction l generalizing m with
  | nil => rfl
  | cons a l ih =>
    cases m with
    | nil => rfl
    | cons b m =>
      change Int.add (Int.mul a b) (dot_k l m) = _
      rw [ih, dot, Int.add_def, Int.mul_def]

theorem weighted_k_eq (kind r : ℕ) (w : ℤ) (S T : Key) :
    weighted_k kind r w S T =
      if w = 0 then [] else (pairTerms kind r S T).map fun e => Key.term (w * e.1) e.2 := by
  simp only [weighted_k, brec_eq_ite, Int.beq'_eq, lmap_k_eq, pairTerms_k_eq, Key.term_k_eq,
    Int.mul_def]

theorem pairsFrom_k_eq (kind r : ℕ) (s : Row) (ts : List Row) :
    pairsFrom_k kind r s ts = pairsFrom kind r s ts := by
  simp only [pairsFrom_k, pairsFrom, lflatMap_k_eq, weighted_k_eq, dot_k_eq, Int.mul_def]

theorem blockTermsN_k_eq (kind r n : ℕ) (rows : List Row) :
    blockTermsN_k kind r n rows = blockTermsN kind r n rows := by
  induction n generalizing rows with
  | zero => cases rows <;> rfl
  | succ n ih =>
    cases rows with
    | nil => rfl
    | cons s ts =>
      change lappend_k (lappend_k (weighted_k kind r (dot_k s.2 s.2) s.1 s.1)
        (pairsFrom_k kind r s ts)) (blockTermsN_k kind r n ts) = _
      rw [ih, lappend_k_eq, lappend_k_eq, weighted_k_eq, pairsFrom_k_eq, dot_k_eq, blockTermsN]

theorem ldrop_k_eq {α : Type} (n : ℕ) (l : List α) : ldrop_k n l = l.drop n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    change ldrop_k n (List.rec (motive := fun _ => List α) [] (fun _ t _ => t) l) = _
    rw [ih]
    cases l <;> simp

theorem blockChunk_k_eq (kind r a n : ℕ) (rows : List Row) :
    blockChunk_k kind r a n rows = blockChunk kind r a n rows := by
  rw [blockChunk_k, blockChunk, Poly.mergeAll_k_eq, blockTermsN_k_eq, ldrop_k_eq]

theorem mulChi_k_eq (P : Poly) : mulChi_k P = mulChi P := by
  simp only [mulChi_k, mulChi, Poly.mergeAll_k_eq, lflatMap_k_eq, lmap_k_eq, Key.term_k_eq,
    Key.mul_k_eq, Int.mul_def]

end Expand

end OnePhaseDimension.Certificate
