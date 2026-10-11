/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Bounds.GraphBound
public import OnePhaseDimension.Certificate.Data.Remainder

/-!
# Types of the keys of the interior remainder

Every key of the remainder has exactly two factors among `y = (w, z, ℓ, X)`; its type is the pair
`(i, j)`, `i ≤ j`, of their indices. The numbers of keys of the ten types are
`89, 53, 123, 170, 64, 85, 106, 238, 414, 372` (1714 in all), as printed in the 2026-09-24
version.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data

theorem remainderRef_length : remainderRef.length = 1714 := by decide +kernel

/-! ### Types of the keys -/

/-- The ten types `(i, j)`, `i ≤ j`. -/
def yPairs : List (List ℕ) :=
  [[1, 1], [1, 2], [1, 3], [1, 4], [2, 2], [2, 3], [2, 4], [3, 3], [3, 4], [4, 4]]

/-- Add one at position `i`. -/
def incAt : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, a :: l => (a + 1) :: l
  | i + 1, a :: l => a :: incAt i l

/-- The numbers of keys of each of the ten types, followed by the number of keys of no type. -/
def typeCounts (P : Poly) : List ℕ :=
  P.foldr (fun t acc => incAt (yPairs.findIdx (· == (Key.unpack t.1).types)) acc)
    (List.replicate 11 0)

/-- The numbers of keys of each type (the counts printed in the 2026-09-24 version); every
key has exactly two factors among `w, z, ℓ, X`. -/
theorem typeCounts_remainderRef :
    typeCounts remainderRef = [89, 53, 123, 170, 64, 85, 106, 238, 414, 372, 0] := by
  decide +kernel

end OnePhaseDimension.Certificate.Collect
