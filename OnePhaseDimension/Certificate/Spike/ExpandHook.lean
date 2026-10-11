/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Spike.Expand

/-!
# Expansion of a Gram block with the `hook` projection

The `hook` projection of rank three is used in matching form (see
`OnePhaseDimension.Certificate.Proj.inner_projHook`):

  `⟨T, Π S⟩ = 16 (⟨T, S⟩ + ⟨T, S^{(12)}⟩) - 8 ∑_{π ∉ {1, (12)}} ⟨T, S^π⟩ - 2 ⟨w T, w S⟩`,

with `w = 2 Tr₁₂ - Tr₁₃ - Tr₂₃`. The block expansion is that of `Expand.block`, with the pair
terms supplied as a parameter.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

namespace Expand

/-- The six permutations of three slots with their `hook` weights. -/
def hookPerms : List (ℤ × List ℕ) :=
  [(16, [0, 1, 2]), (-8, [0, 2, 1]), (16, [1, 0, 2]), (-8, [1, 2, 0]), (-8, [2, 0, 1]),
    (-8, [2, 1, 0])]

/-- The three partial traces of a rank-3 key with the weights `2, -1, -1` of `w`. -/
def hookTraces (k : Key) : List (ℤ × Key) :=
  [(2, k.contract 0 1), (-1, k.contract 0 2), (-1, k.contract 1 2)]

/-- The terms of `⟨T, Π S⟩` for the `hook` projection, before canonicalization. -/
def hookTerms (S T : Key) : List (ℤ × Key) :=
  hookPerms.map (fun σ => (σ.1, ((S.permSlots σ.2).mul T).contractPairs 3)) ++
    (hookTraces S).flatMap fun a =>
      (hookTraces T).map fun b => (-2 * a.1 * b.1, (a.2.mul b.2).contractPairs 1)

/-- The terms of one pair with weight `w`, for pair terms `pt`. -/
def weightedWith (pt : Key → Key → List (ℤ × Key)) (w : ℤ) (S T : Key) : List Poly :=
  if w = 0 then [] else (pt S T).map fun e => Key.term (w * e.1) e.2

/-- The terms of the pairs `(s, t)`, `t ∈ ts`. -/
def pairsFromWith (pt : Key → Key → List (ℤ × Key)) (s : Row) (ts : List Row) : List Poly :=
  ts.flatMap fun t => weightedWith pt (2 * dot s.2 t.2) s.1 t.1

/-- The terms of the pairs `(s, t)` with `s` among the first `n` rows (and `t ≥ s`). -/
def blockTermsWith (pt : Key → Key → List (ℤ × Key)) : ℕ → List Row → List Poly
  | 0, _ => []
  | _, [] => []
  | n + 1, s :: ts =>
    (weightedWith pt (dot s.2 s.2) s.1 s.1 ++ pairsFromWith pt s ts) ++ blockTermsWith pt n ts

/-- The collected block for pair terms `pt`, scaled by `Q²`. -/
def blockWith (pt : Key → Key → List (ℤ × Key)) (rows : List Row) : Poly :=
  Poly.mergeAll (blockTermsWith pt rows.length rows)

/-! ### Kernel-reducible versions -/

/-- `Expand.hookTerms` by recursors. -/
noncomputable def hookTerms_k (S T : Key) : List (ℤ × Key) :=
  lappend_k
    (lmap_k (fun σ : ℤ × List ℕ => (σ.1, ((S.permSlots_k σ.2).mul_k T).contractPairs_k 3))
      hookPerms)
    (lflatMap_k (fun a : ℤ × Key => lmap_k (fun b : ℤ × Key =>
        (Int.mul (Int.mul (-2) a.1) b.1, (a.2.mul_k b.2).contractPairs_k 1))
      [(2, T.contract_k 0 1), (-1, T.contract_k 0 2), (-1, T.contract_k 1 2)])
      [(2, S.contract_k 0 1), (-1, S.contract_k 0 2), (-1, S.contract_k 1 2)])

/-- `Expand.weightedWith` by recursors. -/
noncomputable def weightedWith_k (pt : Key → Key → List (ℤ × Key)) (w : ℤ) (S T : Key) :
    List Poly :=
  Bool.rec (lmap_k (fun e => Key.term_k (Int.mul w e.1) e.2) (pt S T)) [] (Int.beq' w 0)

/-- `Expand.blockTermsWith` by recursors. -/
noncomputable def blockTermsWith_k (pt : Key → Key → List (ℤ × Key)) (n : ℕ)
    (rows : List Row) : List Poly :=
  Nat.rec (motive := fun _ => List Row → List Poly) (fun _ => [])
    (fun _ ih rows => List.rec (motive := fun _ => List Poly) []
      (fun s ts _ => lappend_k (lappend_k (weightedWith_k pt (dot_k s.2 s.2) s.1 s.1)
        (lflatMap_k (fun t => weightedWith_k pt (Int.mul 2 (dot_k s.2 t.2)) s.1 t.1) ts))
        (ih ts)) rows) n rows

/-- `Expand.blockWith` by recursors. -/
noncomputable def blockWith_k (pt : Key → Key → List (ℤ × Key)) (rows : List Row) : Poly :=
  Poly.mergeAll_k (blockTermsWith_k pt (length_k rows) rows)

theorem hookTerms_k_eq (S T : Key) : hookTerms_k S T = hookTerms S T := by
  simp only [hookTerms_k, hookTerms, hookTraces, lappend_k_eq, lmap_k_eq, lflatMap_k_eq,
    Key.mul_k_eq, Key.contractPairs_k_eq, Key.permSlots_k_eq, Key.contract_k_eq, Int.mul_def]

theorem weightedWith_k_eq (pt : Key → Key → List (ℤ × Key)) (w : ℤ) (S T : Key) :
    weightedWith_k pt w S T = weightedWith pt w S T := by
  simp only [weightedWith_k, weightedWith, brec_eq_ite, Int.beq'_eq, lmap_k_eq, Key.term_k_eq,
    Int.mul_def]

theorem blockTermsWith_k_eq (pt : Key → Key → List (ℤ × Key)) (n : ℕ) (rows : List Row) :
    blockTermsWith_k pt n rows = blockTermsWith pt n rows := by
  induction n generalizing rows with
  | zero => cases rows <;> rfl
  | succ n ih =>
    cases rows with
    | nil => rfl
    | cons s ts =>
      change lappend_k (lappend_k (weightedWith_k pt (dot_k s.2 s.2) s.1 s.1)
        (lflatMap_k (fun t => weightedWith_k pt (Int.mul 2 (dot_k s.2 t.2)) s.1 t.1) ts))
        (blockTermsWith_k pt n ts) = _
      simp only [ih, lappend_k_eq, lflatMap_k_eq, weightedWith_k_eq, dot_k_eq, Int.mul_def,
        blockTermsWith, pairsFromWith]

theorem blockWith_k_eq (pt : Key → Key → List (ℤ × Key)) (rows : List Row) :
    blockWith_k pt rows = blockWith pt rows := by
  rw [blockWith_k, blockWith, Poly.mergeAll_k_eq, blockTermsWith_k_eq, length_k_eq]

end Expand

end OnePhaseDimension.Certificate
