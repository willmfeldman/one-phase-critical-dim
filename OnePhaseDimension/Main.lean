/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Main
public import OnePhaseDimension.Cutoff.Exclusion
public import OnePhaseDimension.Reduction.Interface
public import OnePhaseDimension.Reduction.OneDim
public import OnePhaseDimension.LowDim.DimFour

/-!
# Flatness of one-homogeneous minimizers in dimensions at most six

Every nonzero, nonnegative, one-homogeneous global minimizer of the one-phase Bernoulli energy
`J(v; B) = ∫_B |∇v|² + 1_{v > 0}` in `ℝᵈ`, `1 ≤ d ≤ 6`, is flat: `u(x) = (x · e)₊` for a unit
vector `e`, almost everywhere.

## Main statements

* `exclusion`: there is no working cone, from the certificate.
* `flatInDim_of_flatInDim_sub_one`: for `d ∈ {5, 6}`, flatness in dimension `d - 1` gives
  flatness in dimension `d`.
* `headline_of_dim_one`: the headline statement, given the one-dimensional classification.
* `flat_of_oneHomogeneous_of_le_six_of_dim_one`: the same with explicit hypotheses.

## Differences from the source

* The 2026-09-24 version argues with a least dimension `d_* ∈ {5, 6}` carrying a nonflat
  one-homogeneous minimizer. We use an induction on the dimension: dimensions two, three and
  four are proved by the exclusion of cones with an isolated singularity, and for `d ∈ {5, 6}`
  flatness in dimension `d - 1` together with the exclusion of working cones gives flatness in
  dimension `d`.
* The 2026-09-24 version cites the classification for `d ≤ 4`. Dimensions two, three and
  four are proved here (`flatInDim_two`, `flatInDim_three`, `flatInDim_four`) by the reduction to
  a cone with an isolated singularity; dimensions three and four use new universal certificates on
  `ℝ²` and `ℝ³`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open MeasureTheory

@[expose] public section

namespace OnePhaseDimension

open EllipticBernoulli

/-- **Exclusion.** There is no working cone. -/
theorem exclusion : ExclusionStatement :=
  exclusion_of_certificate Certificate.certificateStatement_holds

/-- **Inductive step.** For `d ∈ {5, 6}`, if every nonzero, nonnegative, one-homogeneous global
minimizer in `ℝ^{d-1}` is flat, then so is every such minimizer in `ℝᵈ`. -/
theorem flatInDim_of_flatInDim_sub_one {d : ℕ} (hd : d = 5 ∨ d = 6)
    (hlow : FlatInDim (d - 1)) : FlatInDim d := by
  intro u hnn hmin hhom hne
  have hd₂ : 2 ≤ d := by omega
  obtain ⟨v, hvu, -, hc, hnn', hhom', hmin', -, -, hpos⟩ :=
    exists_headline_representative hd₂ hnn hmin hhom hne
  by_cases hflat : FlatAE v
  · exact flatAE_congr hvu hflat
  · exact (exclusion.false
      (exists_workingCone d hd hlow v hc hnn' hmin' hhom' hpos hflat).some).elim

/-- **The headline statement, given the one-dimensional classification.** Every nonzero,
nonnegative, one-homogeneous global minimizer of the one-phase energy in `ℝᵈ`, `1 ≤ d ≤ 6`, is
flat, provided this holds for `d = 1`. -/
theorem headline_of_dim_one (h1 : FlatInDim 1) : HeadlineStatement := by
  have h3 : FlatInDim 3 := flatInDim_three
  have h4 : FlatInDim 4 := flatInDim_four
  have h5 : FlatInDim 5 := flatInDim_of_flatInDim_sub_one (d := 5) (by norm_num) h4
  have h6 : FlatInDim 6 := flatInDim_of_flatInDim_sub_one (d := 6) (by norm_num) h5
  intro d hd₁ hd₆
  interval_cases d
  · exact h1
  · exact flatInDim_two
  · exact h3
  · exact h4
  · exact h5
  · exact h6

/-- **Flatness in dimensions at most six, given the one-dimensional classification.** A nonzero,
nonnegative, one-homogeneous global minimizer `u` of the one-phase energy in `ℝᵈ`, `1 ≤ d ≤ 6`,
satisfies `u x = max ⟪x, e⟫ 0` for almost every `x`, for some unit vector `e`. -/
theorem flat_of_oneHomogeneous_of_le_six_of_dim_one (h1 : FlatInDim 1) {d : ℕ} (hd₁ : 1 ≤ d)
    (hd₆ : d ≤ 6) (u : E d → ℝ) (hnn : ∀ᵐ x ∂(volume : Measure (E d)), 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u) (hhom : OneHomogeneousAE u)
    (hne : ¬ u =ᵐ[volume] 0) :
    ∃ e : E d, ‖e‖ = 1 ∧ ∀ᵐ x ∂(volume : Measure (E d)), u x = max (inner ℝ x e) 0 :=
  headline_of_dim_one h1 d hd₁ hd₆ u hnn hmin hhom hne

/-- **Main theorem.** For `1 ≤ d ≤ 6`, every nonnegative, nonzero, one-homogeneous global minimizer
of the one-phase Bernoulli energy in `ℝᵈ` is flat. -/
theorem headline : HeadlineStatement :=
  headline_of_dim_one flatInDim_one

/-- **Main theorem**, with explicit hypotheses: if `1 ≤ d ≤ 6` and `u` is a nonnegative (a.e.),
one-homogeneous (a.e.), not a.e. vanishing local energy minimizer of `∫ |∇v|² + 1_{v > 0}` on all
of `ℝᵈ`, then `u = (x · e)⁺` almost everywhere for some unit vector `e`. -/
theorem flat_of_oneHomogeneous_of_le_six {d : ℕ} (hd₁ : 1 ≤ d) (hd₆ : d ≤ 6) (u : E d → ℝ)
    (hnn : ∀ᵐ x ∂volume, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u)
    (hhom : OneHomogeneousAE u) (hne : ¬ u =ᵐ[volume] 0) :
    ∃ e : E d, ‖e‖ = 1 ∧ ∀ᵐ x ∂volume, u x = max (inner ℝ x e) 0 :=
  flat_of_oneHomogeneous_of_le_six_of_dim_one flatInDim_one hd₁ hd₆ u hnn hmin hhom hne

end OnePhaseDimension
