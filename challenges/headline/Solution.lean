/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Main
public import OnePhaseDimension.Sanity.Textbook.Equivalence
public import OnePhaseDimension.Sanity.Harmonic

/-!
# Solution: flatness of one-homogeneous one-phase minimizers in dimensions at most six

Proves the statement of `Challenge.lean` from the library's main theorem
`OnePhaseDimension.flat_of_oneHomogeneous_of_le_six`. Its minimality hypothesis
`IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u` is obtained from `TextbookMin u` by
`OnePhaseDimension.Textbook.isLocalEnergyMinimizer_of_textbookMin`.

The six checks of the definitions in `OnePhaseDimension.Sanity` (not headline results) come from
facts about the library's minimizer class `IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1)` in
`OnePhaseDimension/Sanity/Minimizer.lean` and `OnePhaseDimension/Sanity/Harmonic.lean`; the
passage to `TextbookMin` uses the equivalence of the two classes,
`isLocalEnergyMinimizer_of_textbookMin` and `textbookMin_of_isLocalEnergyMinimizer`.

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

namespace OnePhaseDimension.Sanity

open OnePhaseDimension.Textbook

theorem challenge_textbookMin_halfSpace {d : ℕ} {e : EuclideanSpace ℝ (Fin d)} (he : ‖e‖ = 1) :
    TextbookMin (fun x ↦ max (inner ℝ x e) 0) :=
  textbookMin_of_isLocalEnergyMinimizer (isLocalEnergyMinimizer_max_inner he)

theorem challenge_not_textbookMin_slope {e : EuclideanSpace ℝ (Fin 1)} (he : ‖e‖ = 1) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≠ 1) : ¬ TextbookMin (fun x ↦ s * max (inner ℝ x e) 0) :=
  fun h ↦ not_isLocalEnergyMinimizer_smul_max_inner he hs hs1
    (isLocalEnergyMinimizer_of_textbookMin h)

theorem challenge_not_textbookMin_two_sided {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬ TextbookMin (fun x : EuclideanSpace ℝ (Fin 1) ↦ a * max (x 0) 0 + b * max (-x 0) 0) :=
  fun h ↦ not_isLocalEnergyMinimizer_two_sided ha hb (isLocalEnergyMinimizer_of_textbookMin h)

theorem challenge_not_textbookMin_one_add_norm_sq {d : ℕ} (hd : 1 ≤ d) :
    ¬ TextbookMin (fun x : EuclideanSpace ℝ (Fin d) ↦ 1 + ‖x‖ ^ 2) :=
  fun h ↦ not_isLocalEnergyMinimizer_one_add_norm_sq hd (isLocalEnergyMinimizer_of_textbookMin h)

theorem challenge_textbookMin_zero {d : ℕ} :
    TextbookMin (fun _ : EuclideanSpace ℝ (Fin d) ↦ (0 : ℝ)) ∧
      ¬ ∃ e : EuclideanSpace ℝ (Fin d), ‖e‖ = 1 ∧
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), (0 : ℝ) = max (inner ℝ x e) 0 := by
  refine ⟨?_, not_flatAE_zero⟩
  exact textbookMin_of_isLocalEnergyMinimizer isLocalEnergyMinimizer_zero

theorem challenge_textbookMin_shifted_halfSpace {d : ℕ} {e : EuclideanSpace ℝ (Fin d)}
    (he : ‖e‖ = 1) :
    TextbookMin (fun x ↦ max (inner ℝ x e - 1) 0) ∧
      (∀ x, 0 ≤ max (inner ℝ x e - 1) 0) ∧
      ¬ (fun x ↦ max (inner ℝ x e - 1) 0) =ᵐ[volume] 0 ∧
      ¬ ∃ e' : EuclideanSpace ℝ (Fin d), ‖e'‖ = 1 ∧
        ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
          max (inner ℝ x e - 1) 0 = max (inner ℝ x e') 0 := by
  refine ⟨?_, fun _ ↦ le_max_right _ _, not_ae_eq_zero_and_not_flatAE_max_inner_sub_one he⟩
  exact textbookMin_of_isLocalEnergyMinimizer (isLocalEnergyMinimizer_max_inner_sub_one he)

end OnePhaseDimension.Sanity
