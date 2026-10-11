/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Graph

/-!
# Formats of the two coefficient tables

The certificate is specified by two tables of integer numerators over `Q = 250000`.

* The first table lists the coefficient polynomials `f, U, K, M, P`: each row is a family, a
  decimal monomial word and a coefficient. The ranks are `0, 2, 4, 1, 1` and the slot orders are
  empty, `(j, k)`, `(l, i, j, k)`, `(l)`, `(l)`.
* The second table lists the comparison blocks: each block has a rank, a projection label
  (`none`, `anti`, `sym`, `hook`), a multiplier mode, and rows made of a monomial word and a
  column of coefficients. For nonnegative rank the modes `I` and `B` mean the multiplier `1` and
  `χ = 1 - |p|² - g²`. The two boundary blocks have rank `-1`; their four-digit words are
  exponent vectors of four scalar variables, and their modes are `I` (multiplier `1`) and `H`
  (multiplier `-λ`).

Words are stored as a number of digits and a natural number, so that leading zeros are kept
without any `String` processing in the kernel (`wordDigits` restores the digit list).

The functions `TableIRow.dumpLine` and `Block.dumpLines` print the tables in a normalized
text format (one line per row) so that the Lean data can be compared line by line with an
independent parse of the source tables.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Data

/-- The five coefficient families of the first table. -/
inductive Fam where
  | f | U | K | M | P
  deriving DecidableEq, Repr, Inhabited

namespace Fam

/-- The rank of the family: `f ↦ 0`, `U ↦ 2`, `K ↦ 4`, `M ↦ 1`, `P ↦ 1`. -/
def rank : Fam → ℕ
  | f => 0
  | U => 2
  | K => 4
  | M => 1
  | P => 1

/-- The one-letter name of the family. -/
def name : Fam → String
  | f => "f"
  | U => "U"
  | K => "K"
  | M => "M"
  | P => "P"

end Fam

/-- A row of the first table: family, number of decimal digits of the word, the word read as a
natural number, and the coefficient numerator (over `Q = 250000`). -/
structure TableIRow where
  /-- The family. -/
  fam : Fam
  /-- The number of decimal digits of the word (leading zeros are significant). -/
  len : ℕ
  /-- The word, read as a natural number. -/
  word : ℕ
  /-- The coefficient numerator. -/
  coef : ℤ
  deriving DecidableEq, Repr

namespace TableIRow

/-- The graph key of the monomial of a row, of the rank of its family. -/
def key (r : TableIRow) : Key := decodeWord r.fam.rank (wordDigits r.len r.word)

end TableIRow

/-- The projection label of a block of the second table. -/
inductive Proj where
  | none | anti | sym | hook
  deriving DecidableEq, Repr, Inhabited

/-- The label as printed in the table. -/
def Proj.name : Proj → String
  | none => "none"
  | anti => "anti"
  | sym => "sym"
  | hook => "hook"

/-- The multiplier mode of a block: `I` (multiplier `1`), `B` (multiplier `χ`), and `H`
(multiplier `-λ`, boundary blocks only). -/
inductive Mode where
  | I | B | H
  deriving DecidableEq, Repr, Inhabited

/-- The mode as printed in the table. -/
def Mode.name : Mode → String
  | I => "I"
  | B => "B"
  | H => "H"

/-- A block of the second table. A row is `(number of digits, word, coefficient column)`. -/
structure Block where
  /-- The rank (`-1` for the two boundary blocks). -/
  rank : ℤ
  /-- The projection label. -/
  proj : Proj
  /-- The multiplier mode. -/
  mode : Mode
  /-- The rows: number of digits, word, coefficient column. -/
  rows : List (ℕ × ℕ × List ℤ)
  deriving DecidableEq, Repr

/-! ### Normalized text dump -/

/-- The word with `len` digits, with leading zeros. -/
def wordString (len word : ℕ) : String :=
  String.join ((wordDigits len word).map toString)

/-- The normalized line `TABLE_I <F> <word> <coef>` of a row of the first table. -/
def TableIRow.dumpLine (r : TableIRow) : String :=
  s!"TABLE_I {r.fam.name} {wordString r.len r.word} {r.coef}"

/-- The normalized lines `BLOCK <idx> <rank> <kind> <mode> ROW <word> <c1> …` of the block with
index `idx`. -/
def Block.dumpLines (idx : ℕ) (b : Block) : List String :=
  b.rows.map fun row =>
    s!"BLOCK {idx} {b.rank} {b.proj.name} {b.mode.name} ROW {wordString row.1 row.2.1} " ++
      " ".intercalate (row.2.2.map toString)

/-- The normalized dump of both tables, one line per row. -/
def dumpTables (t1 : List TableIRow) (t2 : List Block) : List String :=
  t1.map TableIRow.dumpLine ++
    ((List.range t2.length).zip t2).flatMap fun ib => ib.2.dumpLines ib.1

end OnePhaseDimension.Certificate.Data
