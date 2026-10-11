/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Bounds.GraphBound

/-!
# Kernel checks of the graph-bound classification

Two keys of each of the eleven topology classes `(#X, #self-edges, #cross-edges)`, taken from
an independent reference computation of the remainder keys: `classify` accepts each, `Lsq`
equals the reference value of `L_t²`, and the degree types agree with the reference. The
check for the full list of remainder keys is made where that list is defined.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

/-- Sample keys with their reference values `(key, L_t², i, j)`. -/
def graphBoundSamples : List (Key × ℚ × ℕ × ℕ) := [
  ((⟨0, 0, 0, 2, [],
    [⟨.p, .p, 2⟩]⟩ : Key),
    16/25, 2, 2),
  ((⟨0, 4, 2, 0, [3],
    []⟩ : Key),
    9/20, 1, 1),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 0, .ell, 1⟩, ⟨.x 0, .p, 0⟩, ⟨.x 0, .p, 0⟩, ⟨.p, .p, 0⟩, ⟨.p, .p, 2⟩]⟩ : Key),
    64/125, 3, 4),
  ((⟨0, 0, 1, 0, [3],
    [⟨.x 0, .p, 0⟩, ⟨.x 0, .p, 0⟩, ⟨.x 0, .p, 0⟩, ⟨.p, .p, 0⟩]⟩ : Key),
    9/20, 1, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 0, .x 0, 1⟩, ⟨.x 0, .p, 0⟩, ⟨.ell, .p, 2⟩, ⟨.p, .p, 0⟩, ⟨.p, .p, 0⟩]⟩ : Key),
    16/35, 3, 4),
  ((⟨0, 3, 0, 1, [],
    [⟨.x 0, .x 0, 1⟩, ⟨.x 0, .p, 0⟩, ⟨.p, .p, 3⟩]⟩ : Key),
    1/175, 2, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .p, 0⟩, ⟨.x 1, .p, 1⟩, ⟨.x 1, .p, 1⟩, ⟨.x 0, .p, 0⟩, ⟨.x 0, .p, 0⟩,
     ⟨.x 0, .p, 0⟩, ⟨.p, .p, 0⟩]⟩ : Key),
    16/25, 4, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .p, 0⟩, ⟨.x 1, .p, 1⟩, ⟨.x 1, .p, 1⟩, ⟨.x 0, .p, 0⟩, ⟨.x 0, .p, 0⟩,
     ⟨.x 0, .p, 1⟩]⟩ : Key),
    64/125, 4, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .x 0, 4⟩, ⟨.x 1, .p, 0⟩, ⟨.x 1, .p, 0⟩, ⟨.x 0, .p, 0⟩, ⟨.x 0, .p, 0⟩]⟩ : Key),
    256/625, 4, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .x 0, 1⟩, ⟨.x 1, .p, 0⟩, ⟨.x 1, .p, 0⟩, ⟨.x 0, .p, 0⟩, ⟨.x 0, .p, 0⟩,
     ⟨.p, .p, 1⟩]⟩ : Key),
    16/25, 4, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .x 0, 0⟩, ⟨.x 1, .x 0, 0⟩, ⟨.x 1, .p, 0⟩, ⟨.x 0, .p, 0⟩, ⟨.p, .p, 0⟩,
     ⟨.p, .p, 0⟩, ⟨.p, .p, 0⟩]⟩ : Key),
    1, 4, 4),
  ((⟨0, 2, 0, 0, [],
    [⟨.x 1, .x 0, 0⟩, ⟨.x 1, .x 0, 0⟩, ⟨.x 1, .p, 0⟩, ⟨.x 0, .p, 0⟩, ⟨.p, .p, 1⟩]⟩ : Key),
    64/3645, 4, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .x 0, 0⟩, ⟨.x 1, .x 0, 0⟩, ⟨.x 1, .x 0, 0⟩]⟩ : Key),
    1, 4, 4),
  ((⟨0, 2, 0, 0, [],
    [⟨.x 1, .x 0, 0⟩, ⟨.x 1, .x 0, 0⟩, ⟨.x 1, .x 0, 0⟩, ⟨.p, .p, 0⟩, ⟨.p, .p, 0⟩,
     ⟨.p, .p, 0⟩]⟩ : Key),
    729/65536, 4, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .p, 0⟩, ⟨.x 1, .p, 1⟩, ⟨.x 1, .p, 1⟩, ⟨.x 0, .x 0, 1⟩, ⟨.x 0, .p, 0⟩,
     ⟨.p, .p, 0⟩]⟩ : Key),
    16/35, 4, 4),
  ((⟨0, 2, 0, 0, [],
    [⟨.x 1, .p, 0⟩, ⟨.x 1, .p, 0⟩, ⟨.x 1, .p, 1⟩, ⟨.x 0, .x 0, 1⟩, ⟨.x 0, .p, 0⟩]⟩ : Key),
    64/5103, 4, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .x 0, 0⟩, ⟨.x 1, .p, 0⟩, ⟨.x 1, .p, 0⟩, ⟨.x 0, .x 0, 1⟩]⟩ : Key),
    5/7, 4, 4),
  ((⟨0, 2, 0, 0, [],
    [⟨.x 1, .x 0, 0⟩, ⟨.x 1, .p, 0⟩, ⟨.x 1, .p, 2⟩, ⟨.x 0, .x 0, 1⟩, ⟨.p, .p, 0⟩]⟩ : Key),
    256/25515, 4, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .x 1, 1⟩, ⟨.x 1, .p, 2⟩, ⟨.x 0, .x 0, 1⟩, ⟨.x 0, .p, 0⟩]⟩ : Key),
    16/49, 4, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .x 1, 1⟩, ⟨.x 1, .p, 1⟩, ⟨.x 0, .x 0, 1⟩, ⟨.x 0, .p, 1⟩]⟩ : Key),
    16/49, 4, 4),
  ((⟨0, 2, 0, 0, [],
    [⟨.x 1, .x 1, 1⟩, ⟨.x 1, .x 0, 2⟩, ⟨.x 0, .x 0, 1⟩, ⟨.p, .p, 0⟩]⟩ : Key),
    1/49, 4, 4),
  ((⟨0, 0, 0, 0, [],
    [⟨.x 1, .x 1, 1⟩, ⟨.x 1, .x 0, 0⟩, ⟨.x 0, .x 0, 1⟩, ⟨.p, .p, 0⟩, ⟨.p, .p, 0⟩,
     ⟨.p, .p, 2⟩]⟩ : Key),
    16/49, 4, 4)
]

/-- Every sample key is accepted by `classify`, with the reference `L_t²` and degree types. -/
theorem graphBoundSamples_ok :
    graphBoundSamples.all (fun x => (classify x.1).isSome && Lsq x.1 == x.2.1 &&
      x.1.typeI == x.2.2.1 && x.1.typeJ == x.2.2.2) = true := by
  decide +kernel

end OnePhaseDimension.Certificate
