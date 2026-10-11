/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Slice
public import EllipticBernoulli.Sobolev.Energy

/-!
# Suspension preserves global minimality

If `u` is a global minimizer of the one-phase energy in `ℝᵏ`, then `ũ(y, s) = u(y)` is a global
minimizer in `ℝ^{k+1}`.

## Proof

Let `W` be a competitor for `ũ` on a ball `𝓑 = B_R(c)`, i.e. `W ∈ H¹_loc(ℝ^{k+1})` with `W = ũ`
a.e. off `𝓑`. The horizontal slices of `𝓑` are the balls `B_s = B_{ρ(s)}(π c)`,
`ρ(s) = (R² - (s - c_{k+1})²)^{1/2}`. For almost every `s`, the slice `W(·, s)` lies in
`H¹_loc(ℝᵏ)` with weak gradient `π ∇W(·, s)` and agrees with `u` a.e. off `B_s`; so it is a
competitor for `u` on `B_s`. By Tonelli, and dropping `|∂_s W|²`,
`J(ũ; 𝓑) ≤ ∫ J(u; B_s) ds ≤ ∫ J(W(·, s); B_s) ds ≤ J(W; 𝓑)`.

## Main results

* `ae_memH1Loc_slice`: slices of `H¹_loc` functions.
* `isLocalEnergyMinimizer_suspension`: the suspension of a global minimizer is a global
  minimizer.
* `suspensionMinimality_holds`: the same in the form used by the regularity argument.

## Differences from the source

The 2026-09-24 version compares with nonnegative competitors `V ∈ H¹(𝓑)`, `V - ũ ∈ H¹₀(𝓑)`, and
shows that almost every slice of the difference lies in `H¹₀(B_s)` by approximation with smooth
compactly supported functions. We use competitors in `H¹_loc` agreeing with `ũ` a.e. off the
ball, as in the definition of local energy minimality; the boundary condition on the slices is
then an a.e. statement given by Fubini. The weak gradient of almost every slice is identified
directly (`ae_hasWeakGradient_slice`). No sign condition on `u` is needed.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff RealInnerProductSpace ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {k : ℕ}

/-! ### Slices of `H¹_loc` functions -/

theorem memLp_prod_of_memLp_sliceBox {F : Type*} [NormedAddCommGroup F] {f : E (k + 1) → F}
    {R : ℝ} (hf : MemLp f 2 (volume.restrict (sliceBox k R))) :
    MemLp (fun p : ℝ × E k ↦ f (joinLast p.2 p.1)) 2
      (((volume : Measure ℝ).restrict (Icc (-R) R)).prod
        ((volume : Measure (E k)).restrict (closedBall 0 R))) := by
  rw [Measure.prod_restrict]
  have hmp := measurePreserving_sliceEquiv_symm.restrict_preimage_emb
    (MeasurableEquiv.measurableEmbedding _) (sliceBox k R)
  have hpre : (sliceEquiv (k := k)).symm ⁻¹' sliceBox k R = Icc (-R) R ×ˢ closedBall 0 R := by
    ext p
    simp only [mem_preimage, sliceBox, sliceEquiv_symm_apply, joinLast,
      ContinuousLinearEquiv.apply_symm_apply, mem_prod]
    tauto
  rw [hpre] at hmp
  exact hf.comp_measurePreserving hmp

/-- Slices of a function that is `L²` on compact sets are `L²` on compact sets, for almost every
`s`. -/
theorem ae_memLp_slice {F : Type*} [NormedAddCommGroup F] {f : E (k + 1) → F}
    (hf : ∀ K, IsCompact K → MemLp f 2 (volume.restrict K)) :
    ∀ᵐ s : ℝ, ∀ K, IsCompact K → MemLp (fun y ↦ f (joinLast y s)) 2 (volume.restrict K) := by
  have hn : ∀ n : ℕ, ∀ᵐ s : ℝ, s ∈ Icc (-(n : ℝ)) n →
      MemLp (fun y ↦ f (joinLast y s)) 2 (volume.restrict (closedBall 0 n)) := fun n ↦ by
    have hm := memLp_prod_of_memLp_sliceBox (hf _ (isCompact_sliceBox (n : ℝ)))
    have hi := ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).1 hm).prod_right_ae
    have ha := hm.aestronglyMeasurable.prodMk_left
    have := hi.and ha
    rw [ae_restrict_iff' measurableSet_Icc] at this
    filter_upwards [this] with s hs hsI
    exact (memLp_two_iff_integrable_sq_norm (hs hsI).2).2 (hs hsI).1
  filter_upwards [ae_all_iff.2 hn] with s hs K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨n, hn'⟩ := exists_nat_ge (max R |s|)
  exact (hs n (abs_le.1 ((le_max_right _ _).trans hn'))).mono_measure
    (Measure.restrict_mono (hR.trans (closedBall_subset_closedBall ((le_max_left _ _).trans hn')))
      le_rfl)

/-- **Slices of `H¹_loc` functions.** For almost every `s`, the slice `V(·, s)` lies in
`H¹_loc(ℝᵏ)` with weak gradient `π G(·, s)`. -/
theorem ae_memH1Loc_slice {V : E (k + 1) → ℝ} {G : E (k + 1) → E (k + 1)}
    (h : MemH1Loc univ V G) :
    ∀ᵐ s : ℝ, MemH1Loc univ (fun y ↦ V (joinLast y s)) (fun y ↦ projInit k (G (joinLast y s))) := by
  have h1 := ae_memLp_slice fun K hK ↦ (h.2 K (subset_univ _) hK).1
  have h2 := ae_memLp_slice (f := fun x ↦ projInit k (G x)) fun K hK ↦
    (h.2 K (subset_univ _) hK).2.continuousLinearMap_comp (projInit k)
  filter_upwards [ae_hasWeakGradient_slice h.1, h1, h2] with s hs hs1 hs2
  exact ⟨hs, fun K _ hK ↦ ⟨hs1 K hK, hs2 K hK⟩⟩

/-! ### Slices of balls -/

theorem norm_sq_joinLast (y : E k) (s : ℝ) : ‖joinLast y s‖ ^ 2 = ‖y‖ ^ 2 + s ^ 2 := by
  rw [norm_sq_eq_splitLast]
  simp [joinLast]

theorem joinLast_sub (y y' : E k) (s s' : ℝ) :
    joinLast y s - joinLast y' s' = joinLast (y - y') (s - s') := by
  simp only [joinLast, ← map_sub, Prod.mk_sub_mk]

/-- The horizontal slices of a ball are balls. -/
theorem joinLast_mem_ball_iff {c : E (k + 1)} {R : ℝ} (hR : 0 < R) (y : E k) (s : ℝ) :
    joinLast y s ∈ ball c R ↔
      y ∈ ball (projInit k c) (√(R ^ 2 - (s - c (Fin.last k)) ^ 2)) := by
  rw [mem_ball, mem_ball, dist_eq_norm, dist_eq_norm, Real.lt_sqrt (norm_nonneg _)]
  conv_lhs => rw [← joinLast_projInit c, joinLast_sub]
  rw [← sq_lt_sq₀ (norm_nonneg _) hR.le, norm_sq_joinLast]
  constructor <;> intro h <;> linarith

/-- The energy with unit coefficient, with the positivity indicator written through `w`. -/
theorem energyJ_one_eq {d : ℕ} {V : Set (E d)} (hV : MeasurableSet V) (w : E d → ℝ)
    (G : E d → E d) :
    energyJ V (fun _ ↦ 1) w G =
      ∫⁻ x in V, ENNReal.ofReal (‖G x‖ ^ 2 + (Ioi (0 : ℝ)).indicator 1 (w x)) := by
  rw [energyJ_eq_lintegral_indicator_Ioi hV]
  simp only [one_pow, one_mul]

/-! ### Suspension -/

/-- **Suspension preserves global minimality.** If `u` is a global minimizer of the one-phase
energy in `ℝᵏ`, then `x ↦ u(π x)` is a global minimizer in `ℝ^{k+1}`. -/
theorem isLocalEnergyMinimizer_suspension {u : E k → ℝ}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) :
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) (fun x ↦ u (projInit k x)) := by
  obtain ⟨Gu, hGu, hm⟩ := hmin
  have hGt := memH1Loc_comp_projInit hGu
  refine ⟨_, hGt, fun c R hR _ ↦ ⟨hGt, fun _ _ ↦ rfl, fun _ _ ↦ mem_univ _,
    fun W GW hW hWoff _ ↦ ?_⟩⟩
  set yc := projInit k c
  set FW : E (k + 1) → ℝ≥0∞ :=
    fun x ↦ ENNReal.ofReal (‖GW x‖ ^ 2 + (Ioi (0 : ℝ)).indicator 1 (W x)) with hFW_def
  have hmem := joinLast_mem_ball_iff (c := c) hR
  -- the suspension is bounded by the integral of the slice energies
  have h1 : energyJ (ball c R) (fun _ ↦ 1) (fun x ↦ u (projInit k x))
      (fun x ↦ (projInit k).adjoint (Gu (projInit k x))) ≤
      ∫⁻ s, energyJ (ball yc (√(R ^ 2 - (s - c (Fin.last k)) ^ 2))) (fun _ ↦ 1) u Gu := by
    rw [energyJ_one_eq measurableSet_ball, ← lintegral_indicator measurableSet_ball]
    refine (lintegral_le_lintegral_slices _).trans (lintegral_mono fun s ↦ ?_)
    rw [energyJ_one_eq measurableSet_ball, ← lintegral_indicator measurableSet_ball]
    refine le_of_eq (lintegral_congr fun y ↦ ?_)
    by_cases hy : y ∈ ball yc (√(R ^ 2 - (s - c (Fin.last k)) ^ 2))
    · rw [indicator_of_mem ((hmem y s).2 hy), indicator_of_mem hy]
      simp [norm_projInit_adjoint]
    · rw [indicator_of_notMem (mt (hmem y s).1 hy), indicator_of_notMem hy]
  -- the slice energies are bounded by the energy of `W`
  have hGWm : AEStronglyMeasurable GW volume :=
    (locallyIntegrableOn_univ.1 hW.1.2.1).aestronglyMeasurable
  have hWm : AEMeasurable W volume :=
    (locallyIntegrableOn_univ.1 hW.1.1).aestronglyMeasurable.aemeasurable
  have hFWm : AEMeasurable ((ball c R).indicator FW) := by
    refine AEMeasurable.indicator ?_ measurableSet_ball
    exact ((hGWm.norm.aemeasurable.pow_const 2).add
      ((measurable_const.indicator measurableSet_Ioi).comp_aemeasurable hWm)).ennreal_ofReal
  have h3 : ∀ s, energyJ (ball yc (√(R ^ 2 - (s - c (Fin.last k)) ^ 2))) (fun _ ↦ 1)
      (fun y ↦ W (joinLast y s)) (fun y ↦ projInit k (GW (joinLast y s))) ≤
      ∫⁻ y, (ball c R).indicator FW (joinLast y s) := by
    intro s
    rw [energyJ_one_eq measurableSet_ball, ← lintegral_indicator measurableSet_ball]
    refine lintegral_mono fun y ↦ ?_
    by_cases hy : y ∈ ball yc (√(R ^ 2 - (s - c (Fin.last k)) ^ 2))
    · rw [indicator_of_mem hy, indicator_of_mem ((hmem y s).2 hy)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := norm_projInit_le (GW (joinLast y s))
      gcongr
    · rw [indicator_of_notMem hy]
      exact bot_le
  have hJW : energyJ (ball c R) (fun _ ↦ 1) W GW =
      ∫⁻ s, ∫⁻ y, (ball c R).indicator FW (joinLast y s) := by
    rw [energyJ_one_eq measurableSet_ball, ← lintegral_indicator measurableSet_ball,
      lintegral_eq_lintegral_slices hFWm]
  -- almost every slice of `W` is a competitor
  have hoff : ∀ᵐ s : ℝ, ∀ᵐ y : E k, joinLast y s ∉ ball c R → W (joinLast y s) = u y := by
    have hx : ∀ᵐ x : E (k + 1), x ∉ ball c R → W x = u (projInit k x) := by
      have := hWoff
      rw [ae_restrict_iff' (MeasurableSet.univ.diff measurableSet_ball)] at this
      filter_upwards [this] with x hx hxB using hx ⟨mem_univ _, hxB⟩
    filter_upwards [ae_ae_slices hx] with s hs
    filter_upwards [hs] with y hy hyB
    simpa using hy hyB
  have h2 : ∀ᵐ s : ℝ, energyJ (ball yc (√(R ^ 2 - (s - c (Fin.last k)) ^ 2))) (fun _ ↦ 1) u Gu ≤
      energyJ (ball yc (√(R ^ 2 - (s - c (Fin.last k)) ^ 2))) (fun _ ↦ 1)
        (fun y ↦ W (joinLast y s)) (fun y ↦ projInit k (GW (joinLast y s))) := by
    filter_upwards [ae_memH1Loc_slice hW, hoff] with s hs hso
    rcases (Real.sqrt_nonneg (R ^ 2 - (s - c (Fin.last k)) ^ 2)).lt_or_eq with hρ | hρ
    · refine (hm yc _ hρ (subset_univ _)).2.2.2 _ _ hs ?_
        (Eventually.of_forall fun _ ↦ mem_univ _)
      rw [ae_restrict_iff' (MeasurableSet.univ.diff measurableSet_ball)]
      filter_upwards [hso] with y hy hyB
      exact hy fun h ↦ hyB.2 ((hmem y s).1 h)
    · rw [← hρ, ball_zero]
      simp [energyJ]
  calc _ ≤ _ := h1
    _ ≤ _ := lintegral_mono_ae h2
    _ ≤ _ := lintegral_mono h3
    _ = _ := hJW.symm

/-- Suspension minimality in the form used by the regularity argument. -/
theorem suspensionMinimality_holds : SuspensionMinimality :=
  fun _ _ _ hmin ↦ isLocalEnergyMinimizer_suspension hmin

end OnePhaseDimension
