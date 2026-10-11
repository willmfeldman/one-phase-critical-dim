/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Homogeneity
public import OnePhaseDimension.Registry.Regularity
public import EllipticBernoulli.Sobolev.Energy
public import EllipticBernoulli.Variational.EnergyMinimizer

/-!
# Minimizer bridges and continuous representatives

## Main results

* `isLocalEnergyMinimizer_congr_ae`: local energy minimality
  only depends on the a.e. class of the function (the energy and the competitor class are
  defined through a.e. conditions).
* `IsNonnegCompetitorMinimizer`: minimality against nonnegative competitors only, the competitor
  class of the source.
* `isLocalEnergyMinimizer_iff_nonnegCompetitorMinimizer`: for `u ≥ 0` a.e. the two notions agree,
  since `v ↦ v₊` keeps the boundary values and does not increase the energy.
* `exists_continuous_minimizer_representative`: a nonnegative global minimizer has a locally
  Lipschitz, everywhere nonnegative representative which is smooth and harmonic in its positivity
  set and is itself a global minimizer.
* `exists_headline_representative`: the same under the hypotheses of the headline statement,
  with one-homogeneity everywhere and a point of positivity.

## Differences from the source

The 2026-09-24 version compares a minimizer with nonnegative competitors `v ∈ H¹(B)`,
`v - u ∈ H¹₀(B)`, and replaces a general competitor by its positive part in a remark. We use
competitors in `H¹_loc(ℝᵈ)` agreeing with `u` a.e. off the ball, real-valued for local energy
minimality and nonnegative for `IsNonnegCompetitorMinimizer`, and prove the equivalence of the
two notions for `u ≥ 0` with the same positive-part argument.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set MeasureTheory Metric
open scoped ContDiff Laplacian

@[expose] public section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ} {U : Set (E d)} {Q u v : E d → ℝ}

/-! ### Invariance under a.e. modification -/

/-- `H¹_loc` membership with a given weak gradient only depends on the a.e. class of the
function on `U`. -/
theorem memH1Loc_congr_fun_ae {G : E d → E d} (hu : MemH1Loc U u G)
    (huv : ∀ᵐ x ∂(volume.restrict U), u x = v x) : MemH1Loc U v G := by
  refine ⟨hu.1.congr_fun_ae huv, fun K hK hKc ↦ ⟨?_, (hu.2 K hK hKc).2⟩⟩
  exact (hu.2 K hK hKc).1.ae_eq (ae_restrict_of_ae_restrict_of_subset hK huv)

/-- Local energy minimality only depends on the a.e. class of the function. -/
theorem isLocalEnergyMinimizer_congr_ae (huv : u =ᵐ[volume] v) :
    IsLocalEnergyMinimizer U Q u ↔ IsLocalEnergyMinimizer U Q v :=
  ⟨fun h ↦ h.congr_ae (ae_restrict_of_ae huv.symm),
    fun h ↦ h.congr_ae (ae_restrict_of_ae huv)⟩

/-! ### Nonnegative competitors -/

/-- `u` is a local minimizer of `J_Q` in `U` against nonnegative competitors: for some weak
gradient `Gu`, `u ∈ H¹_loc(U)` and, on every ball `B = ball x r` with `closedBall x r ⊆ U`,
`J_Q(u; B) ≤ J_Q(v; B)` for every `v ∈ H¹_loc(U)` with `v ≥ 0` a.e. on `U` and `v = u` a.e. on
`U \ B`. -/
def IsNonnegCompetitorMinimizer (U : Set (E d)) (Q u : E d → ℝ) : Prop :=
  ∃ Gu, MemH1Loc U u Gu ∧ ∀ (x : E d) (r : ℝ), 0 < r → closedBall x r ⊆ U →
    ∀ (v : E d → ℝ) (Gv : E d → E d), MemH1Loc U v Gv →
      (∀ᵐ y ∂(volume.restrict (U \ ball x r)), v y = u y) →
      (∀ᵐ y ∂(volume.restrict U), 0 ≤ v y) →
      energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv

/-- A local energy minimizer is a minimizer against nonnegative competitors. -/
theorem isNonnegCompetitorMinimizer_of_isLocalEnergyMinimizer
    (h : IsLocalEnergyMinimizer U Q u) :
    IsNonnegCompetitorMinimizer U Q u := by
  obtain ⟨Gu, hGu, hmin⟩ := h
  exact ⟨Gu, hGu, fun x r hr hxr v Gv hv hvB _ ↦
    (hmin x r hr hxr).2.2.2 v Gv hv hvB (Filter.Eventually.of_forall fun _ ↦ mem_univ _)⟩

/-- For `u ≥ 0` a.e. on the open set `U`, a minimizer against nonnegative competitors is a local
energy minimizer: a real competitor `v` may be replaced by `v₊`, which has the same values off
the ball (since `u ≥ 0`) and no larger energy. -/
theorem IsNonnegCompetitorMinimizer.isLocalEnergyMinimizer (hU : IsOpen U)
    (hnn : ∀ᵐ y ∂(volume.restrict U), 0 ≤ u y) (h : IsNonnegCompetitorMinimizer U Q u) :
    IsLocalEnergyMinimizer U Q u := by
  obtain ⟨Gu, hGu, hmin⟩ := h
  refine ⟨Gu, hGu, fun x r hr hxr ↦ ⟨hGu, fun _ _ ↦ rfl, fun _ _ ↦ mem_univ _,
    fun v Gv hv hvB _ ↦ ?_⟩⟩
  refine (hmin x r hr hxr _ _ (memH1Loc_posPart hU hv) ?_
    (Filter.Eventually.of_forall fun _ ↦ le_max_right _ _)).trans (energyJ_posPart_le _ _ _ _)
  filter_upwards [hvB, ae_restrict_of_ae_restrict_of_subset sdiff_subset hnn] with y h₁ h₂
  rw [h₁, max_eq_left h₂]

/-- For `u ≥ 0` a.e. on the open set `U`, local energy minimality against real competitors is
equivalent to minimality against nonnegative competitors. -/
theorem isLocalEnergyMinimizer_iff_nonnegCompetitorMinimizer (hU : IsOpen U)
    (hnn : ∀ᵐ y ∂(volume.restrict U), 0 ≤ u y) :
    IsLocalEnergyMinimizer U Q u ↔ IsNonnegCompetitorMinimizer U Q u :=
  ⟨fun h ↦ isNonnegCompetitorMinimizer_of_isLocalEnergyMinimizer h,
    fun h ↦ h.isLocalEnergyMinimizer hU hnn⟩

/-! ### Continuous representatives -/

/-- A nonnegative global minimizer in `ℝᵈ`, `d ≥ 2`, has a locally Lipschitz, everywhere
nonnegative representative which is smooth and harmonic in its positivity set and is itself a
global minimizer. -/
theorem exists_continuous_minimizer_representative (hd : 2 ≤ d)
    (hnn : ∀ᵐ x ∂(volume : Measure (E d)), 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) :
    ∃ v : E d → ℝ, v =ᵐ[volume] u ∧ LocallyLipschitz v ∧ Continuous v ∧ (∀ x, 0 ≤ v x) ∧
      ContDiffOn ℝ ∞ v {x | 0 < v x} ∧ (∀ x, 0 < v x → Δ v x = 0) ∧
      IsLocalEnergyMinimizer univ (fun _ ↦ 1) v := by
  obtain ⟨v, hvu, hlip, hnn', hsmooth, hharm⟩ :=
    Registry.exists_continuous_representative hd hnn hmin
  exact ⟨v, hvu, hlip, hlip.continuous, hnn', hsmooth, hharm,
    (isLocalEnergyMinimizer_congr_ae hvu.symm).1 hmin⟩

/-- Under the hypotheses of the headline statement (`d ≥ 2`), `u` has a representative `v` that
is locally Lipschitz, nonnegative, one-homogeneous everywhere, a global minimizer, smooth and
harmonic in its positivity set, and positive somewhere. Flatness of `v` everywhere gives
`FlatAE u` by `flatAE_of_flat`. -/
theorem exists_headline_representative (hd : 2 ≤ d)
    (hnn : ∀ᵐ x ∂(volume : Measure (E d)), 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hhom : OneHomogeneousAE u)
    (hne : ¬ u =ᵐ[volume] 0) :
    ∃ v : E d → ℝ, v =ᵐ[volume] u ∧ LocallyLipschitz v ∧ Continuous v ∧ (∀ x, 0 ≤ v x) ∧
      (∀ r : ℝ, 0 < r → ∀ x, v (r • x) = r * v x) ∧
      IsLocalEnergyMinimizer univ (fun _ ↦ 1) v ∧
      ContDiffOn ℝ ∞ v {x | 0 < v x} ∧ (∀ x, 0 < v x → Δ v x = 0) ∧ ∃ x, 0 < v x := by
  obtain ⟨v, hvu, hlip, hcont, hnn', hsmooth, hharm, hmin'⟩ :=
    exists_continuous_minimizer_representative hd hnn hmin
  exact ⟨v, hvu, hlip, hcont, hnn',
    oneHomogeneous_of_ae_of_continuous hcont (oneHomogeneousAE_congr hvu.symm hhom),
    hmin', hsmooth, hharm, exists_pos_of_not_ae_eq_zero hvu hnn' hne⟩

end OnePhaseDimension
