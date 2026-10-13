/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Main
public import OnePhaseDimension.Sanity.Textbook.Equivalence

/-!
# Solution: flatness of one-homogeneous one-phase minimizers in dimensions at most six

Proves the statement of `Challenge.lean` from the library's main theorem
`OnePhaseDimension.flat_of_oneHomogeneous_of_le_six`. Its minimality hypothesis
`IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u` is obtained from `TextbookMin u` by
`OnePhaseDimension.Textbook.isLocalEnergyMinimizer_of_textbookMin`.

The vocabulary comes from the library module `OnePhaseDimension.Sanity.Textbook.Defs`, of which
`Vocabulary.lean` is a verbatim copy and the generated block of `Challenge.lean` a restatement;
the statement check compares them. This file imports the library only, not `Vocabulary`, since
both declare the same names.
-/

open MeasureTheory

@[expose] public section

namespace OnePhaseDimension.Headline

open OnePhaseDimension.Textbook

theorem challenge_flat_of_textbookMin {d : ℕ} (hd₁ : 1 ≤ d) (hd₆ : d ≤ 6)
    (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (hnn : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), 0 ≤ u x)
    (hmin : TextbookMin u)
    (hhom : ∀ r : ℝ, 0 < r →
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), u (r • x) = r * u x)
    (hne : ¬ u =ᵐ[volume] 0) :
    ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), u x = max (inner ℝ x e) 0 :=
  flat_of_oneHomogeneous_of_le_six hd₁ hd₆ u hnn (isLocalEnergyMinimizer_of_textbookMin hmin)
    hhom hne

end OnePhaseDimension.Headline
