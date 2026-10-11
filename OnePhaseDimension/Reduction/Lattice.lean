/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational
public import EllipticBernoulli.Sobolev.Energy
public import EllipticBernoulli.Sobolev.Uniqueness
public import PerronVariational.Stationary.DirectionalStable.Basic

/-!
# Two-sided minimality is one-sided minimality in both directions

## Main results

* `energyJ_le_of_isLocalEnergyMinimizer`: a local energy minimizer has no larger energy than any
  competitor on a ball, whatever weak gradient is used for it (weak gradients are unique a.e.).
* `isDownwardMinimizer_of_contDiffOn`, `isUpwardMinimizer_of_contDiffOn`: a
  local energy minimizer which is harmonic in its (open) positivity set is a downward and an
  upward minimizer.
* `isLocalEnergyMinimizer_of_isDownwardMinimizer_of_isUpwardMinimizer`: conversely, a function
  which is both a downward and an upward minimizer is a local energy minimizer.
* `isLocalEnergyMinimizer_iff`: the two notions agree.

## Proof of the converse

For a competitor `w` on the ball `B`, both `max u w` and `min u w` are admissible one-sided
competitors (`u ≤ max u w`, `min u w ≤ u`, and both agree with `u` off `B`). At every point the
pair `(max u w, min u w)`, with gradients, is a permutation of `(u, w)`, so
`J(max u w; B) + J(min u w; B) ≤ J(u; B) + J(w; B)`. Hence
`2 J(u; B) ≤ J(u; B) + J(w; B)`, and `J(u; B) < ∞` gives `J(u; B) ≤ J(w; B)`. The weak gradient
of `min u w` is taken as `G_u + G_w - G_{max u w}`, so no Stampacchia-type statement on
`{u = w}` is needed.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Laplacian

@[expose] public section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ} {U : Set (E d)} {Q u : E d → ℝ}

/-- A local energy minimizer has no larger energy on a ball than any competitor agreeing with it
off the ball, for any choice of its weak gradient. -/
theorem energyJ_le_of_isLocalEnergyMinimizer (hU : IsOpen U)
    (h : IsLocalEnergyMinimizer U Q u) {x : E d} {r : ℝ} (hr : 0 < r)
    (hB : closedBall x r ⊆ U) {Gu : E d → E d} (hGu : MemH1Loc U u Gu) {v : E d → ℝ}
    {Gv : E d → E d} (hv : MemH1Loc U v Gv)
    (hvB : ∀ᵐ y ∂(volume.restrict (U \ ball x r)), v y = u y) :
    energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv := by
  obtain ⟨Gu₀, hGu₀, hmin⟩ := h
  have hae : ∀ᵐ y ∂(volume.restrict U), Gu y = Gu₀ y :=
    HasWeakGradient.ae_eq_of_eqOn hU hU subset_rfl hGu.1 hGu₀.1 fun _ _ ↦ rfl
  have hBU : ball x r ⊆ U := ball_subset_closedBall.trans hB
  rw [energyJ_congr_ae measurableSet_ball (Eventually.of_forall fun _ ↦ rfl)
    (ae_restrict_of_ae_restrict_of_subset hBU hae)]
  exact (hmin x r hr hB).2.2.2 v Gv hv hvB (Eventually.of_forall fun _ ↦ mem_univ _)

/-- A local energy minimizer, harmonic in its open positivity set, is a downward minimizer. -/
theorem isDownwardMinimizer_of_contDiffOn (hU : IsOpen U)
    (h : IsLocalEnergyMinimizer U Q u) (hopen : IsOpen (posSet u U))
    (hc2 : ContDiffOn ℝ 2 u (posSet u U)) (hΔ : ∀ x ∈ posSet u U, Δ u x = 0) :
    IsDownwardMinimizer U Q u :=
  ⟨⟨_, h.choose_spec.1⟩, hopen, hc2, hΔ, fun _ _ hr hB _ _ _ hGu hv _ hvB ↦
    energyJ_le_of_isLocalEnergyMinimizer hU h hr hB hGu hv hvB⟩

/-- A local energy minimizer, harmonic in its open positivity set, is an upward minimizer. -/
theorem isUpwardMinimizer_of_contDiffOn (hU : IsOpen U)
    (h : IsLocalEnergyMinimizer U Q u) (hopen : IsOpen (posSet u U))
    (hc2 : ContDiffOn ℝ 2 u (posSet u U)) (hΔ : ∀ x ∈ posSet u U, Δ u x = 0) :
    IsUpwardMinimizer U Q u :=
  ⟨⟨_, h.choose_spec.1⟩, hopen, hc2, hΔ, fun _ _ hr hB _ _ _ hGu hv _ hvB ↦
    energyJ_le_of_isLocalEnergyMinimizer hU h hr hB hGu hv hvB⟩

/-- `min u w` has weak gradient `G_u` where `u < w` and `G_w` elsewhere (the complementary
choice to the one of `MemH1Loc.max`). -/
theorem memH1Loc_min' (hU : IsOpen U) {w : E d → ℝ} {Gu Gw : E d → E d}
    (hu : MemH1Loc U u Gu) (hw : MemH1Loc U w Gw) :
    MemH1Loc U (fun y ↦ min (u y) (w y)) (fun y ↦ if u y < w y then Gu y else Gw y) := by
  have h := (hu.add hw).sub (hu.max hU hw)
  have hf : (fun y ↦ u y + w y - max (u y) (w y)) = fun y ↦ min (u y) (w y) := by
    funext y
    linarith [min_add_max (u y) (w y)]
  have hG : (fun y ↦ Gu y + Gw y - if u y < w y then Gw y else Gu y) =
      fun y ↦ if u y < w y then Gu y else Gw y := by
    funext y
    split_ifs <;> abel
  rwa [hf, hG] at h

/-- **Two-sided minimality from one-sided minimality.** On an open set `U`, with `Q` measurable
and bounded, a function which is both a downward and an upward minimizer of `J_Q` is a local
energy minimizer. -/
theorem isLocalEnergyMinimizer_of_isDownwardMinimizer_of_isUpwardMinimizer (hU : IsOpen U)
    (hQm : Measurable Q) (hQb : ∃ C, ∀ x ∈ U, |Q x| ≤ C) (hdown : IsDownwardMinimizer U Q u)
    (hup : IsUpwardMinimizer U Q u) : IsLocalEnergyMinimizer U Q u := by
  obtain ⟨⟨Gu, hGu⟩, hopen, -, -, hdmin⟩ := hdown
  obtain ⟨C, hC⟩ := hQb
  refine ⟨Gu, hGu, fun x r hr hB ↦ ⟨hGu, fun _ _ ↦ rfl, fun _ _ ↦ mem_univ _,
    fun w Gw hw hwB _ ↦ ?_⟩⟩
  have hBU : ball x r ⊆ U := ball_subset_closedBall.trans hB
  have hmax := hGu.max hU hw
  have hmin := memH1Loc_min' hU hGu hw
  -- the two one-sided comparisons
  have h1 : energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q (fun y ↦ max (u y) (w y))
      (fun y ↦ if u y < w y then Gw y else Gu y) :=
    hup.2.2.2.2 x r hr hB Gu _ _ hGu hmax (Eventually.of_forall fun y ↦ le_max_left _ _)
      (hwB.mono fun y hy ↦ by simp only [hy, max_self])
  have h2 : energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q (fun y ↦ min (u y) (w y))
      (fun y ↦ if u y < w y then Gu y else Gw y) :=
    hdmin x r hr hB Gu _ _ hGu hmin (Eventually.of_forall fun y ↦ min_le_left _ _)
      (hwB.mono fun y hy ↦ by simp only [hy, min_self])
  -- the lattice inequality
  have hS : MeasurableSet (posSet u (ball x r)) := by
    have : posSet u (ball x r) = posSet u U ∩ ball x r := by
      ext y
      simp only [posSet, mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨fun h ↦ ⟨⟨hBU h.1, h.2⟩, h.1⟩, fun h ↦ ⟨h.2, h.1.2⟩⟩
    rw [this]
    exact hopen.measurableSet.inter measurableSet_ball
  have hGm : AEStronglyMeasurable Gu (volume.restrict (ball x r)) :=
    (hGu.1.2.1.aestronglyMeasurable).mono_measure (Measure.restrict_mono hBU le_rfl)
  have hm : AEMeasurable (fun y ↦ ENNReal.ofReal (‖Gu y‖ ^ 2 + Q y ^ 2 *
      (posSet u (ball x r)).indicator 1 y)) (volume.restrict (ball x r)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable ((hGm.norm.aemeasurable.pow_const 2).add
      ((hQm.pow_const 2).mul (measurable_const.indicator hS)).aemeasurable)
  have h3 : energyJ (ball x r) Q (fun y ↦ max (u y) (w y))
      (fun y ↦ if u y < w y then Gw y else Gu y) +
      energyJ (ball x r) Q (fun y ↦ min (u y) (w y)) (fun y ↦ if u y < w y then Gu y else Gw y) ≤
      energyJ (ball x r) Q u Gu + energyJ (ball x r) Q w Gw := by
    refine PerronVariational.DirectionalStable.energyJ_add_le_of_swap measurableSet_ball
      (fun y _ ↦ ?_) hm
    by_cases huw : u y < w y
    · right
      simp only [huw, ite_true, max_eq_right huw.le, min_eq_left huw.le, and_self]
    · left
      push Not at huw
      simp only [not_lt.2 huw, ite_false, max_eq_left huw, min_eq_right huw, and_self]
  have hfin : energyJ (ball x r) Q u Gu ≠ ⊤ := by
    refine (energyJ_lt_top hGu ((isCompact_closedBall x r).of_isClosed_subset isClosed_closure
      closure_ball_subset_closedBall) (closure_ball_subset_closedBall.trans hB)
      (CQ := C) fun y hy ↦ hC y (hBU hy)).ne
  exact ENNReal.le_of_add_le_add_left hfin ((add_le_add h1 h2).trans h3)

/-- For a function harmonic in its open positivity set, local energy minimality is equivalent
to being both a downward and an upward minimizer. -/
theorem isLocalEnergyMinimizer_iff (hU : IsOpen U) (hQm : Measurable Q)
    (hQb : ∃ C, ∀ x ∈ U, |Q x| ≤ C) (hopen : IsOpen (posSet u U))
    (hc2 : ContDiffOn ℝ 2 u (posSet u U)) (hΔ : ∀ x ∈ posSet u U, Δ u x = 0) :
    IsLocalEnergyMinimizer U Q u ↔ IsDownwardMinimizer U Q u ∧ IsUpwardMinimizer U Q u :=
  ⟨fun h ↦ ⟨isDownwardMinimizer_of_contDiffOn hU h hopen hc2 hΔ,
      isUpwardMinimizer_of_contDiffOn hU h hopen hc2 hΔ⟩,
    fun h ↦ isLocalEnergyMinimizer_of_isDownwardMinimizer_of_isUpwardMinimizer hU hQm hQb h.1 h.2⟩

end OnePhaseDimension
