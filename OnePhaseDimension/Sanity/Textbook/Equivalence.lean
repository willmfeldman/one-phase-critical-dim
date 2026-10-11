/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Sanity.Textbook.H10Ball
public import OnePhaseDimension.Sanity.Textbook.ZeroExtension
public import EllipticBernoulli.Sobolev.Lattice

/-!
# The minimizer class is the textbook class

`IsLocalEnergyMinimizer univ (fun _ ↦ 1) u`, the minimizer class of the headline statement, is the
textbook class `TextbookMin u` of Alt and Caffarelli
(`isLocalEnergyMinimizer_univ_one_iff_textbookMin`).

The two definitions differ in one genuine point, the boundary condition on a ball `B`: our
competitors are `H¹_loc(ℝᵈ)` functions agreeing with `u` almost everywhere off `B`, while textbook
competitors `v ∈ H¹(B)` satisfy `v - u ∈ H¹₀(B)`.

* Textbook minimizers are minimizers in our sense (`isLocalEnergyMinimizer_of_textbookMin`). An
  `H¹_loc(ℝᵈ)` function vanishing off a ball lies in `H¹₀` of the ball (`h10_ball_of_memH1Loc`),
  so each of our competitors restricts to a textbook competitor with the same energy.
* Our minimizers are textbook minimizers (`textbookMin_of_isLocalEnergyMinimizer`). The zero
  extension of an `H¹₀(B)` function lies in `H¹_loc(ℝᵈ)` (`hasWeakGradient_univ_indicator_of_h10`),
  so each textbook competitor `v` extends to `u + 1_B (v - u)`, one of our competitors with the
  same energy on `B`.

No sign condition on `u` is needed: both classes allow competitors of any sign.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension.Textbook

open EllipticBernoulli

variable {d : ℕ}

/-- **Textbook minimizers are minimizers.** Every textbook global minimizer of the one-phase
energy is a local energy minimizer in `ℝᵈ` with volume coefficient `1`. -/
theorem isLocalEnergyMinimizer_of_textbookMin {u : E d → ℝ} (h : TextbookMin u) :
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) u := by
  obtain ⟨G, hG⟩ := h
  have hu : MemH1Loc univ u G := memH1Loc_univ_of_h1_ball fun c r hr ↦ (hG c r hr).1
  refine ⟨G, hu, fun x r hr _ ↦ ⟨hu, fun _ _ ↦ rfl, fun _ _ ↦ mem_univ _,
    fun v Gv hv hvu _ ↦ ?_⟩⟩
  have hH1v := h1_ball_of_memH1Loc hv x r
  have h0 : ∀ᵐ y ∂(volume.restrict (ball x r)ᶜ), v y - u y = 0 := by
    rw [compl_eq_univ_sdiff]
    filter_upwards [hvu] with y hy
    rw [hy, sub_self]
  have h10 := h10_ball_of_memH1Loc hr (hv.sub hu) h0
  have hle := (hG x r hr).2 v Gv hH1v h10
  rw [energyJ_ball_eq_ofReal_J (hG x r hr).1.1.aestronglyMeasurable (hG x r hr).1.2.1,
    energyJ_ball_eq_ofReal_J hH1v.1.aestronglyMeasurable hH1v.2.1]
  exact ENNReal.ofReal_le_ofReal hle

/-- **Minimizers are textbook minimizers.** Every local energy minimizer in `ℝᵈ` with volume
coefficient `1` is a textbook global minimizer of the one-phase energy. -/
theorem textbookMin_of_isLocalEnergyMinimizer {u : E d → ℝ}
    (h : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) : TextbookMin u := by
  obtain ⟨G, hu, hmin⟩ := h
  refine ⟨G, fun c r hr ↦ ⟨h1_ball_of_memH1Loc hu c r, fun v V hv h10 ↦ ?_⟩⟩
  set B := ball c r
  set z := B.indicator fun y ↦ v y - u y
  set Z := B.indicator fun y ↦ V y - G y
  have hz : MemH1Loc univ z Z := by
    refine ⟨hasWeakGradient_univ_indicator_of_h10 h10, fun K _ _ ↦ ⟨?_, ?_⟩⟩
    · exact ((memLp_indicator_iff_restrict measurableSet_ball).2 h10.1.1).restrict K
    · exact ((memLp_indicator_iff_restrict measurableSet_ball).2 h10.1.2.1).restrict K
  have hw := hu.add hz
  have hoff : ∀ᵐ y ∂(volume.restrict (univ \ B)), u y + z y = u y := by
    rw [ae_restrict_iff' (MeasurableSet.univ.diff measurableSet_ball)]
    exact Eventually.of_forall fun y hy ↦ by
      rw [show z y = 0 from indicator_of_notMem hy.2 _, add_zero]
  have hle := (hmin c r hr (subset_univ _)).2.2.2 _ _ hw hoff
    (Eventually.of_forall fun _ ↦ mem_univ _)
  have hH1u := h1_ball_of_memH1Loc hu c r
  have hH1w := h1_ball_of_memH1Loc hw c r
  rw [energyJ_ball_eq_ofReal_J hH1u.1.aestronglyMeasurable hH1u.2.1,
    energyJ_ball_eq_ofReal_J hH1w.1.aestronglyMeasurable hH1w.2.1] at hle
  have hJ : J B (fun y ↦ u y + z y) (fun y ↦ G y + Z y) = J B v V :=
    setIntegral_congr_fun measurableSet_ball fun y hy ↦ by simp [z, Z, indicator_of_mem hy]
  rwa [hJ, ENNReal.ofReal_le_ofReal_iff (J_nonneg _ _ _)] at hle

/-- **The minimizer class is the textbook class.** A function is a local energy minimizer in `ℝᵈ`
with volume coefficient `1` if and only if it is a textbook global minimizer of the one-phase
energy. -/
theorem isLocalEnergyMinimizer_univ_one_iff_textbookMin {u : E d → ℝ} :
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) u ↔ TextbookMin u :=
  ⟨textbookMin_of_isLocalEnergyMinimizer, isLocalEnergyMinimizer_of_textbookMin⟩

end OnePhaseDimension.Textbook
