/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Kernel
public import OnePhaseDimension.Certificate.Derivation
public import OnePhaseDimension.Certificate.Data.TableI

/-!
# The interior expression as a graph polynomial

Each row `(F, s, c)` of the first table contributes `(c/Q) 𝓜(s)` to the coefficient `F`, and
hence a polynomial in graph keys to the interior expression

  `𝓘 = z²[5 U_{jk}A_{jk} + C_{lijk}(δ_{lj}A_{ik} + δ_{lk}A_{ij}) − 4f]`
    `+ [D_l G_{lijk} + (2a−1) q_l G_{lijk}] X_{ijk} + w [D_l M_l + (2a+1) q_l M_l]`
    `+ z [D_l P_l + 2a q_l P_l] + f|ℓ|² − (D_l f + 2a q_l f) ℓ_l`,

with `C_{lijk} = K_{lijk} − K_{iljk}`, `G_{lijk} = δ_{li}U_{jk} + C_{lijk}`, `a = 29/50`,
`Q = 250000`. All coefficients are scaled by `Q²`, so that they are integers: the row
coefficient `c` becomes `Q c = 250000 c`, and the three constants `2a − 1 = 4/25`,
`2a + 1 = 54/25` and `2a = 29/25` give `Q c (2a − 1) = 40000 c`, etc.

For one row with key `m` of rank `r`:

* `D_l` is the graph derivative `Key.derivTerms`, whose derivative index is the new last slot
  `r`; a divergence `D_l F_{l…}` contracts slot `0` with slot `r`;
* `q_l F_{l…}` is the product `q ⊗ m` contracted in slots `0, 1`;
* `X_{ijk}` is contracted by a full contraction of rank `3`, and `ℓ_l` by one of rank `1`;
* for a `K` row, `C = K − K^{(01)}` is formed by exchanging slots `0` and `1`; for a `U` row,
  `G = δ ⊗ U` (slots `l, i` carry `δ`).

Every term is a pair (integer weight, key); `Key.term` canonicalizes it. The kernel versions
(suffix `_k`) use the twins of `OnePhaseDimension.Certificate.Kernel` and agree with the readable
definitions (`*_k_eq`).

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data

/-! ### Fixed keys -/

/-- The scalar `z^n`. -/
def zKey (n : ℕ) : Key := ⟨0, 0, 0, n, [], []⟩

/-- The scalar `w`. -/
def wKey : Key := ⟨0, 0, 1, 0, [], []⟩

/-- The scalar `|ℓ|²`. -/
def ellSqKey : Key := ⟨0, 0, 0, 0, [], [⟨.ell, .ell, 0⟩]⟩

/-- The vector `ℓ_l`. -/
def ellKey : Key := ⟨1, 0, 0, 0, [], [⟨.ell, .slot 0, 0⟩]⟩

/-- The vector `q_l = X_{lij} A_{ij}`. -/
def qKey : Key := ⟨1, 0, 0, 0, [], [⟨.x 0, .x 0, 1⟩, ⟨.x 0, .slot 0, 0⟩]⟩

/-- The matrix `A_{jk}`. -/
def aKey : Key := ⟨2, 0, 0, 0, [], [⟨.slot 0, .slot 1, 1⟩]⟩

/-- The matrix `δ_{li}`. -/
def deltaKey : Key := ⟨2, 0, 0, 0, [], [⟨.slot 0, .slot 1, 0⟩]⟩

/-- The three-tensor `X_{ijk}`. -/
def xKey : Key := ⟨3, 0, 0, 0, [], [⟨.x 0, .slot 0, 0⟩, ⟨.x 0, .slot 1, 0⟩, ⟨.x 0, .slot 2, 0⟩]⟩

/-- The four-tensor `δ_{lj}A_{ik} + δ_{lk}A_{ij}` (slots `l, i, j, k = 0, 1, 2, 3`). -/
def zTestKeys : List (ℤ × Key) :=
  [(1, ⟨4, 0, 0, 0, [], [⟨.slot 0, .slot 2, 0⟩, ⟨.slot 1, .slot 3, 1⟩]⟩),
   (1, ⟨4, 0, 0, 0, [], [⟨.slot 0, .slot 3, 0⟩, ⟨.slot 1, .slot 2, 1⟩]⟩)]

/-! ### The contribution of one row -/

/-- The terms of `s · D_l F_{l…} + κ · q_l F_{l…}` for `F = ∑ a_g g` of rank `r` (`r ≥ 1`), where
the scaled weights are `s` and `κ`. -/
def divTerms (r : ℕ) (s κ : ℤ) (F : List (ℤ × Key)) : List (ℤ × Key) :=
  F.flatMap fun g =>
    (g.2.derivTerms.map fun u => (s * g.1 * u.1, u.2.contract 0 r)) ++
      [(κ * g.1, (qKey.mul g.2).contract 0 1)]

/-- Contract a rank-`3` term with `X_{ijk}`. -/
def withX (e : ℤ × Key) : ℤ × Key := (e.1, (e.2.mul xKey).contractPairs 3)

/-- The terms of the contribution of a row of the first table to `Q² 𝓘`, before
canonicalization. -/
def rowTerms (row : TableIRow) : List (ℤ × Key) :=
  let m := row.key
  let s := 250000 * row.coef
  let c := 10000 * row.coef
  match row.fam with
  | .f =>
    [(-1000000 * row.coef, m.mul (zKey 2)), (s, m.mul ellSqKey)] ++
      (m.derivTerms.map fun u => (-250000 * row.coef * u.1, (u.2.mul ellKey).contractPairs 1)) ++
      [(-290000 * row.coef, ((qKey.mul m).mul ellKey).contractPairs 1)]
  | .U =>
    (5 * s, ((m.mul aKey).contractPairs 2).mul (zKey 2)) ::
      (divTerms 4 s (4 * c) [(1, deltaKey.mul m)]).map withX
  | .K =>
    let C : List (ℤ × Key) := [(1, m), (-1, m.permSlots [1, 0])]
    (C.flatMap fun a => zTestKeys.map fun b =>
        (s * a.1 * b.1, ((a.2.mul b.2).contractPairs 4).mul (zKey 2))) ++
      (divTerms 4 s (4 * c) C).map withX
  | .M => (divTerms 1 s (54 * c) [(1, m)]).map fun e => (e.1, e.2.mul wKey)
  | .P => (divTerms 1 s (29 * c) [(1, m)]).map fun e => (e.1, e.2.mul (zKey 1))

/-- The canonicalized single-term polynomials of a row. -/
def rowPolys (row : TableIRow) : List Poly := (rowTerms row).map fun e => Key.term e.1 e.2

/-- The collected contribution of a list of rows to `Q² 𝓘`. -/
def rowsPoly (rows : List TableIRow) : Poly := Poly.mergeAll (rows.flatMap rowPolys)

/-- The rows of the first table belonging to the family `F`. -/
def famRows (F : Fam) : List TableIRow := tableI.filter fun r => r.fam == F

/-! ### Kernel versions -/

/-- `divTerms` by recursors. -/
noncomputable def divTerms_k (r : ℕ) (s κ : ℤ) (F : List (ℤ × Key)) : List (ℤ × Key) :=
  lflatMap_k (fun g : ℤ × Key =>
    lappend_k (lmap_k (fun u : ℤ × Key => (Int.mul (Int.mul s g.1) u.1, u.2.contract_k 0 r))
        g.2.derivTerms)
      [(Int.mul κ g.1, (qKey.mul_k g.2).contract_k 0 1)]) F

/-- `withX` by recursors. -/
noncomputable def withX_k (e : ℤ × Key) : ℤ × Key := (e.1, (e.2.mul_k xKey).contractPairs_k 3)

/-- `rowTerms` by recursors. -/
noncomputable def rowTerms_k (row : TableIRow) : List (ℤ × Key) :=
  Fam.rec (motive := fun _ => List (ℤ × Key))
    (lappend_k (lappend_k
      [(Int.mul (-1000000) row.coef, row.key.mul_k (zKey 2)),
        (Int.mul 250000 row.coef, row.key.mul_k ellSqKey)]
      (lmap_k (fun u : ℤ × Key => (Int.mul (Int.mul (-250000) row.coef) u.1,
        (u.2.mul_k ellKey).contractPairs_k 1)) row.key.derivTerms))
      [(Int.mul (-290000) row.coef,
        ((qKey.mul_k row.key).mul_k ellKey).contractPairs_k 1)])
    ((Int.mul 5 (Int.mul 250000 row.coef),
        ((row.key.mul_k aKey).contractPairs_k 2).mul_k (zKey 2)) ::
      lmap_k withX_k (divTerms_k 4 (Int.mul 250000 row.coef)
        (Int.mul 4 (Int.mul 10000 row.coef)) [(1, deltaKey.mul_k row.key)]))
    (lappend_k
      (lflatMap_k (fun a : ℤ × Key => lmap_k (fun b : ℤ × Key =>
          (Int.mul (Int.mul (Int.mul 250000 row.coef) a.1) b.1,
            ((a.2.mul_k b.2).contractPairs_k 4).mul_k (zKey 2))) zTestKeys)
        [(1, row.key), (-1, row.key.permSlots_k [1, 0])])
      (lmap_k withX_k (divTerms_k 4 (Int.mul 250000 row.coef)
        (Int.mul 4 (Int.mul 10000 row.coef)) [(1, row.key), (-1, row.key.permSlots_k [1, 0])])))
    (lmap_k (fun e : ℤ × Key => (e.1, e.2.mul_k wKey))
      (divTerms_k 1 (Int.mul 250000 row.coef) (Int.mul 54 (Int.mul 10000 row.coef))
        [(1, row.key)]))
    (lmap_k (fun e : ℤ × Key => (e.1, e.2.mul_k (zKey 1)))
      (divTerms_k 1 (Int.mul 250000 row.coef) (Int.mul 29 (Int.mul 10000 row.coef))
        [(1, row.key)]))
    row.fam

/-- `rowsPoly` by recursors. -/
noncomputable def rowsPoly_k (rows : List TableIRow) : Poly :=
  Poly.mergeAll_k (lflatMap_k (fun row => lmap_k (fun e : ℤ × Key => Key.term_k e.1 e.2)
    (rowTerms_k row)) rows)

/-! ### Agreement -/

theorem divTerms_k_eq (r : ℕ) (s κ : ℤ) (F : List (ℤ × Key)) :
    divTerms_k r s κ F = divTerms r s κ F := by
  simp only [divTerms_k, divTerms, lflatMap_k_eq, lappend_k_eq, lmap_k_eq, Key.contract_k_eq,
    Key.mul_k_eq, Int.mul_def]

theorem withX_k_eq : withX_k = withX := by
  funext e
  simp only [withX_k, withX, Key.mul_k_eq, Key.contractPairs_k_eq]

theorem rowTerms_k_eq (row : TableIRow) : rowTerms_k row = rowTerms row := by
  obtain ⟨F, len, word, c⟩ := row
  cases F <;>
    simp only [rowTerms_k, rowTerms, divTerms_k_eq, withX_k_eq, lflatMap_k_eq, lappend_k_eq,
      lmap_k_eq, Key.mul_k_eq, Key.contractPairs_k_eq, Key.permSlots_k_eq, Int.mul_def,
      List.cons_append, List.nil_append]

theorem rowsPoly_k_eq (rows : List TableIRow) : rowsPoly_k rows = rowsPoly rows := by
  simp only [rowsPoly_k, rowsPoly, Poly.mergeAll_k_eq, lflatMap_k_eq, lmap_k_eq,
    rowTerms_k_eq, Key.term_k_eq]
  rfl

/-! ### The single row `U = A`

The row `U_{jk} = A_{jk}` with coefficient one contributes `5z² + |X|² + (2a − 2)|q|²` to `𝓘`
(the 2026-09-24 version, Section "Exact contraction and differentiation rules"). Scaled by
`Q²`, with coefficient `1` (that is, `U = A/Q`), the coefficients are `5Q`, `Q` and
`(2a − 2)Q = −210000`; the keys are `z²`, `|X|²` and `|q|²`. -/

theorem rowsPoly_U_eq_A :
    rowsPoly [⟨.U, 6, 11, 1⟩] =
      [(281474976841728, 1250000), (1329227995784930040003537148487729409, -210000),
        (1329227995784930040075313267548881152, 250000)] := by
  rw [← rowsPoly_k_eq]
  decide +kernel

end OnePhaseDimension.Certificate.Collect
