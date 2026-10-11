/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Data.RemainderA
public import OnePhaseDimension.Certificate.Data.RemainderB

/-!
# The interior remainder (reference data)

The 1714 nonzero keys of the collected interior remainder `E = Γ + ∑ d_i y_i² − 𝓘`, with
coefficients scaled by `Q²` and the rounded bound numerators `n_t`, sorted by packed key.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Data

/-- The remainder data `(packed key, Q² e_t, n_t)`. -/
def remainderData : List (ℕ × ℤ × ℕ) := remainderDataA ++ remainderDataB

/-- The reference remainder polynomial `Q² E`. -/
def remainderRef : List (ℕ × ℤ) := remainderData.map fun t => (t.1, t.2.1)

/-- The rounded bound numerators `n_t`, by packed key. -/
def nRound : List (ℕ × ℕ) := remainderData.map fun t => (t.1, t.2.2)

end OnePhaseDimension.Certificate.Data
