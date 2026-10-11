/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Statements.Headline
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# From almost-everywhere to pointwise statements

The headline hypotheses are almost-everywhere statements about a Sobolev class: one-homogeneity
for each dilation factor, flatness, and "nonzero". For a continuous representative they become
pointwise statements, and they are insensitive to the choice of representative.

## Main results

* `oneHomogeneousAE_congr`: a.e. one-homogeneity passes to a.e.-equal functions (dilations are
  quasi-measure-preserving).
* `oneHomogeneous_of_ae_of_continuous`: for a continuous function, a.e. one-homogeneity is
  one-homogeneity everywhere.
* `flatAE_congr`, `flatAE_of_flat`: flatness everywhere of a representative gives `FlatAE`.
* `flat_of_flatAE_of_continuous`: for a continuous function, `FlatAE` is flatness everywhere.
* `exists_pos_of_not_ae_eq_zero`: a nonnegative representative of a function that is not a.e.
  zero is positive somewhere.

## Differences from the source

The 2026-09-24 version passes from the a.e. identity to the pointwise one in one sentence, by
continuity of the representative; we prove it with the fact that Lebesgue measure charges every
nonempty open set.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open MeasureTheory
open scoped RealInnerProductSpace

@[expose] public section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ} {u v : E d → ℝ}

/-- A.e. one-homogeneity only depends on the a.e. class: dilations `x ↦ r • x`, `r ≠ 0`, are
quasi-measure-preserving. -/
theorem oneHomogeneousAE_congr (huv : u =ᵐ[volume] v) (hu : OneHomogeneousAE u) :
    OneHomogeneousAE v := by
  intro r hr
  have hcomp : (fun x : E d ↦ u (r • x)) =ᵐ[volume] fun x ↦ v (r • x) :=
    (Measure.quasiMeasurePreserving_smul volume hr.ne').ae_eq_comp huv
  filter_upwards [hu r hr, hcomp, huv] with x h₁ h₂ h₃
  rw [← h₂, h₁, h₃]

/-- One-homogeneity everywhere implies a.e. one-homogeneity. -/
theorem oneHomogeneousAE_of_forall (h : ∀ r : ℝ, 0 < r → ∀ x, v (r • x) = r * v x) :
    OneHomogeneousAE v :=
  fun r hr ↦ Filter.Eventually.of_forall (h r hr)

/-- For a continuous function, a.e. one-homogeneity (for each dilation factor) is
one-homogeneity everywhere. -/
theorem oneHomogeneous_of_ae_of_continuous (hv : Continuous v) (h : OneHomogeneousAE v) :
    ∀ r : ℝ, 0 < r → ∀ x, v (r • x) = r * v x := by
  intro r hr
  have := (Continuous.ae_eq_iff_eq volume (hv.comp (continuous_const_smul r))
    (continuous_const.mul hv)).1 (h r hr)
  exact congrFun this

/-- `FlatAE` only depends on the a.e. class. -/
theorem flatAE_congr (huv : u =ᵐ[volume] v) (hu : FlatAE u) : FlatAE v := by
  obtain ⟨e, he, hflat⟩ := hu
  refine ⟨e, he, ?_⟩
  filter_upwards [hflat, huv] with x h₁ h₂
  rw [← h₂, h₁]

/-- If a representative `v` of `u` is flat everywhere, then `u` is flat almost everywhere. -/
theorem flatAE_of_flat (hvu : v =ᵐ[volume] u) {e : E d} (he : ‖e‖ = 1)
    (hflat : ∀ x, v x = max ⟪x, e⟫ 0) : FlatAE u :=
  flatAE_congr hvu ⟨e, he, Filter.Eventually.of_forall hflat⟩

/-- For a continuous function, flatness almost everywhere is flatness everywhere. -/
theorem flat_of_flatAE_of_continuous (hv : Continuous v) (h : FlatAE v) :
    ∃ e : E d, ‖e‖ = 1 ∧ ∀ x, v x = max ⟪x, e⟫ 0 := by
  obtain ⟨e, he, hflat⟩ := h
  have hc : Continuous fun x : E d ↦ max ⟪x, e⟫ 0 :=
    (continuous_id.inner continuous_const).max continuous_const
  exact ⟨e, he, congrFun ((Continuous.ae_eq_iff_eq volume hv hc).1 hflat)⟩

/-- A nonnegative representative `v` of a function `u` that is not a.e. zero is positive at some
point. -/
theorem exists_pos_of_not_ae_eq_zero (hvu : v =ᵐ[volume] u) (hv : ∀ x, 0 ≤ v x)
    (hu : ¬ u =ᵐ[volume] 0) : ∃ x, 0 < v x := by
  by_contra h
  push Not at h
  refine hu ?_
  filter_upwards [hvu] with x hx
  rw [← hx, Pi.zero_apply]
  exact le_antisymm (h x) (hv x)

end OnePhaseDimension
