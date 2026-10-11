/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.KeyTypes

/-!
# Rational bounds of the remainder keys and the matrix `D₀`

For a scalar key `t` of degree two in `y = (|w|, |z|, |ℓ|, |X|)`, the rational factor `L_t²` of
the bound `|𝓜(t)| ≤ L_t y_i y_j` is `Lsq t` (the 2026-09-24 version, Section "Bounds for scalar
graphs"). The rounded numerators `n_t` are supplied as data; the kernel checks, for every
remainder key, that it is accepted by the graph-bound classification and that
`n_t² ≥ 10¹⁰ L_t²` (minimality of `n_t` is not needed). It also checks the ten
sums `2·10⁵ Q² (D₀)_{ij} = ∑_t |Q² e_t| n_t (2 if i = j, 1 otherwise)` against the printed
integers, and `D₀ ≤ D̄` entrywise.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data

/-- The checks on every entry `(key, e, n)`: the key is accepted by the graph-bound
classification, and `n² ≥ 10¹⁰ L_t²`. -/
def roundingOK (data : List (ℕ × ℤ × ℕ)) : Bool :=
  data.all fun t =>
    (classify (Key.unpack t.1)).isSome &&
      decide (10 ^ 10 * Lsq (Key.unpack t.1) ≤ (t.2.2 : ℚ) ^ 2)

/-- The type index `0, …, 9` of a key (`10` if it has no type). -/
def typeIdx (k : Key) : ℕ := yPairs.findIdx (· == k.types)

/-- Whether a type index is diagonal (`(1,1), (2,2), (3,3), (4,4)`). -/
def isDiagIdx (i : ℕ) : Bool := i == 0 || i == 4 || i == 7 || i == 9

/-- Add `a` at position `i`. -/
def addAt (a : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | 0, x :: l => (x + a) :: l
  | i + 1, x :: l => x :: addAt a i l

/-- The ten sums `2·10⁵ Q² (D₀)_{ij} = ∑_t |Q² e_t| n_t (2 if i = j, 1 otherwise)` (and an
eleventh entry for keys of no type). -/
def d0Sums (data : List (ℕ × ℤ × ℕ)) : List ℕ :=
  data.foldr (fun t acc =>
      let i := typeIdx (Key.unpack t.1)
      addAt (t.2.1.natAbs * t.2.2 * (if isDiagIdx i then 2 else 1)) i acc)
    (List.replicate 11 0)

/-- The printed integers `2·10⁵ Q² (D₀)_{ij}`. -/
def d0Printed : List ℕ :=
  [321268243322644, 96616799870252, 294707669526536, 385792585960684, 269583307398596,
    115717471031956, 125155603107368, 605509501361296, 618424270356936, 1004504025266456]

/-- The upper entries `10⁵ D̄_{ij}` in the same order. -/
def dBarScaled : List ℕ := [2571, 773, 2358, 3087, 2157, 926, 1002, 4845, 4948, 8037]

/-- The ten sums of `D₀` are the printed integers. -/
theorem d0Sums_remainderData : d0Sums remainderData = d0Printed ++ [0] := by
  decide +kernel

/-- `D₀ ≤ D̄` entrywise: `2·10⁵ Q² (D₀)_{ij} ≤ 2 Q² · 10⁵ D̄_{ij}`. -/
theorem d0Printed_le_dBar :
    (d0Printed.zip dBarScaled).all (fun x => Nat.ble x.1 (2 * 62500000000 * x.2)) = true := by
  decide +kernel

/-- The types of every remainder key are the pair of its type index (in particular every key has
one of the ten types). -/
theorem yTypes_remainderData : (remainderData.all fun t =>
    (Key.unpack t.1).types == yPairs.getD (typeIdx (Key.unpack t.1)) []) = true := by
  decide +kernel

end OnePhaseDimension.Certificate.Collect
