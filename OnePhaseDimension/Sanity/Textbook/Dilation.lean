/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Basic
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Dilations in `L²(ℝᵈ)`

For a centre `c` and a factor `s ≥ 1` write `x ↦ c + s (x - c)` for the dilation about `c`.

* `eLpNorm_comp_dilation_le`: composing with the dilation does not increase the `L²` norm (it
  multiplies it by `s^{-d/2}`).
* `exists_eLpNorm_mul_comp_dilation_sub_le`: continuity of dilations in `L²`. For `h ∈ L²(ℝᵈ)`,
  `a h(c + s(x - c)) → h` in `L²` as `s ↓ 1` and `a → 1`.

The continuity is first proved for continuous compactly supported functions, where it is uniform
convergence on a fixed compact set, and then extended by density.
-/

open Set Filter Topology MeasureTheory Metric Module
open scoped ContDiff ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension.Textbook

open EllipticBernoulli

variable {d : ℕ}

theorem dilation_eq_comp (c : E d) (s : ℝ) :
    (fun x : E d ↦ c + s • (x - c)) = (fun y ↦ y + (c - s • c)) ∘ (fun x ↦ s • x) := by
  funext x
  simp only [Function.comp_apply, smul_sub]
  abel

theorem quasiMeasurePreserving_dilation (c : E d) {s : ℝ} (hs : s ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : E d ↦ c + s • (x - c)) volume volume := by
  rw [dilation_eq_comp]
  exact (measurePreserving_add_right volume _).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume hs)

theorem continuous_dilation (c : E d) (s : ℝ) : Continuous fun x : E d ↦ c + s • (x - c) := by
  fun_prop

theorem measurable_dilation (c : E d) (s : ℝ) : Measurable fun x : E d ↦ c + s • (x - c) :=
  (continuous_dilation c s).measurable

theorem map_dilation (c : E d) {s : ℝ} (hs : s ≠ 0) :
    Measure.map (fun x : E d ↦ c + s • (x - c)) volume =
      ENNReal.ofReal |(s ^ d)⁻¹| • volume := by
  rw [dilation_eq_comp, ← Measure.map_map (measurable_add_const _) (measurable_const_smul s),
    Measure.map_addHaar_smul volume hs, Measure.map_smul, map_add_right_eq_self,
    finrank_euclideanSpace_fin]
  exact (measurable_add_const _).aemeasurable

/-- Composing with a dilation of factor `s ≥ 1` does not increase the `L²` norm. -/
theorem eLpNorm_comp_dilation_le (c : E d) {s : ℝ} (hs : 1 ≤ s) {h : E d → ℝ}
    (hh : AEStronglyMeasurable h volume) :
    eLpNorm (fun x ↦ h (c + s • (x - c))) 2 volume ≤ eLpNorm h 2 volume := by
  have hs0 : s ≠ 0 := (zero_lt_one.trans_le hs).ne'
  have hk : ENNReal.ofReal |(s ^ d)⁻¹| ≤ 1 := by
    refine ENNReal.ofReal_le_one.2 ?_
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hs)
  have hmap := map_dilation c hs0
  have hm : AEStronglyMeasurable h (Measure.map (fun x : E d ↦ c + s • (x - c)) volume) := by
    rw [hmap]; exact hh.smul_measure _
  have e := eLpNorm_map_measure (p := 2) hm (measurable_dilation c s).aemeasurable
  rw [Function.comp_def] at e
  rw [← e, hmap]
  refine eLpNorm_mono_measure _ ?_
  intro S
  rw [Measure.smul_apply, smul_eq_mul]
  exact mul_le_of_le_one_left zero_le hk

theorem aestronglyMeasurable_comp_dilation {h : E d → ℝ} (hh : AEStronglyMeasurable h volume)
    (c : E d) {s : ℝ} (hs : s ≠ 0) :
    AEStronglyMeasurable (fun x ↦ h (c + s • (x - c))) volume :=
  hh.comp_quasiMeasurePreserving (quasiMeasurePreserving_dilation c hs)

/-- Dilations of a continuous compactly supported function converge uniformly on a fixed compact
set, hence in `L²`. -/
theorem exists_eLpNorm_mul_comp_dilation_sub_le_of_continuous {g : E d → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (c : E d) {η : ℝ} (hη : 0 < η) :
    ∃ σ > 0, ∀ s a : ℝ, 1 ≤ s → s ≤ 1 + σ → |a - 1| ≤ σ →
      eLpNorm (fun x ↦ a * g (c + s • (x - c)) - g x) 2 volume ≤ ENNReal.ofReal η := by
  obtain ⟨R, hR⟩ := hgc.isBounded.subset_closedBall c
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  set S := closedBall c (max R 0)
  have hgS : ∀ x, x ∉ S → g x = 0 := fun x hx ↦ image_eq_zero_of_notMem_tsupport fun h ↦
    hx (closedBall_subset_closedBall (le_max_left _ _) (hR h))
  set A := (volume S ^ (2 : ℝ≥0∞).toReal⁻¹).toReal
  have hA : volume S ^ (2 : ℝ≥0∞).toReal⁻¹ = ENNReal.ofReal A := by
    rw [ENNReal.ofReal_toReal]
    exact ENNReal.rpow_ne_top_of_nonneg (by positivity) measure_closedBall_lt_top.ne
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  set C := η / (A + 1)
  have hC : 0 < C := by positivity
  have hAC : A * C ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1
    (hgc.uniformContinuous_of_continuous hg) (C / 2) (by positivity)
  set M' := max M 0
  set R' := max R 0
  refine ⟨min (C / (2 * (M' + 1))) (δ / (2 * (R' + 1))), by positivity, ?_⟩
  intro s a hs1 hsσ haσ
  have hσ1 : s - 1 ≤ δ / (2 * (R' + 1)) := by
    have := min_le_right (C / (2 * (M' + 1))) (δ / (2 * (R' + 1)))
    linarith
  have hσ2 : |a - 1| ≤ C / (2 * (M' + 1)) := haσ.trans (min_le_left _ _)
  set F := fun x ↦ a * g (c + s • (x - c)) - g x
  have hFm : AEStronglyMeasurable F volume :=
    ((continuous_const.mul (hg.comp (continuous_dilation c s))).sub hg).aestronglyMeasurable
  have hsupp : Function.support F ⊆ S := by
    intro x hx
    by_contra hxS
    refine hx ?_
    have hxS' : R' < dist x c := lt_of_not_ge fun h ↦ hxS (mem_closedBall.2 h)
    have h2 : c + s • (x - c) ∉ S := by
      simp only [S, mem_closedBall, not_le, dist_eq_norm, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hs1)]
      rw [dist_eq_norm] at hxS'
      nlinarith [norm_nonneg (x - c)]
    simp only [F, hgS x hxS, hgS _ h2, mul_zero, sub_zero]
  rw [← eLpNorm_restrict_eq_of_support_subset hFm hsupp]
  refine (eLpNorm_le_of_ae_bound (C := C) hFm.restrict ?_).trans ?_
  · rw [ae_restrict_iff' measurableSet_closedBall]
    refine Eventually.of_forall fun x hx ↦ ?_
    have hxc : ‖x - c‖ ≤ R' := by rwa [← dist_eq_norm]
    have hdist : dist (c + s • (x - c)) x < δ := by
      have : c + s • (x - c) - x = (s - 1) • (x - c) := by rw [sub_smul, one_smul]; abel
      rw [dist_eq_norm, this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      calc (s - 1) * ‖x - c‖ ≤ δ / (2 * (R' + 1)) * R' :=
            mul_le_mul hσ1 hxc (norm_nonneg _) (by positivity)
        _ < δ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [le_max_right R 0]
    have h1 : |g (c + s • (x - c)) - g x| < C / 2 := by
      have := hδg hdist; rwa [Real.dist_eq] at this
    have h2 : |a - 1| * |g (c + s • (x - c))| ≤ C / 2 := by
      have hg' : |g (c + s • (x - c))| ≤ M' := (hM _).trans (le_max_left _ _)
      calc |a - 1| * |g (c + s • (x - c))| ≤ C / (2 * (M' + 1)) * M' :=
            mul_le_mul hσ2 hg' (abs_nonneg _) (by positivity)
        _ ≤ C / 2 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [le_max_right M 0]
    have e : F x = (a - 1) * g (c + s • (x - c)) + (g (c + s • (x - c)) - g x) := by
      simp only [F]; ring
    rw [Real.norm_eq_abs, e]
    calc |(a - 1) * g (c + s • (x - c)) + (g (c + s • (x - c)) - g x)|
        ≤ |(a - 1) * g (c + s • (x - c))| + |g (c + s • (x - c)) - g x| := abs_add_le _ _
      _ ≤ C / 2 + C / 2 := by rw [abs_mul]; exact add_le_add h2 h1.le
      _ = C := by ring
  · rw [Measure.restrict_apply_univ, hA, ← ENNReal.ofReal_mul hA0]
    exact ENNReal.ofReal_le_ofReal hAC

/-- **Continuity of dilations in `L²`.** For `h ∈ L²(ℝᵈ)`, `a h(c + s(x - c)) → h` in `L²` as
`s ↓ 1` and `a → 1` (with `|a| ≤ 2`). -/
theorem exists_eLpNorm_mul_comp_dilation_sub_le {h : E d → ℝ} (hh : MemLp h 2 volume)
    (c : E d) {η : ℝ} (hη : 0 < η) :
    ∃ σ > 0, ∀ s a : ℝ, 1 ≤ s → s ≤ 1 + σ → |a - 1| ≤ σ → |a| ≤ 2 →
      eLpNorm (fun x ↦ a * h (c + s • (x - c)) - h x) 2 volume ≤ ENNReal.ofReal η := by
  obtain ⟨g, hgc, hgs, hgh⟩ := hh.exist_eLpNorm_sub_le ENNReal.ofNat_ne_top one_le_two
    (show 0 < η / 4 by positivity)
  have hg : Continuous g := hgs.continuous
  obtain ⟨σ, hσ, hσg⟩ := exists_eLpNorm_mul_comp_dilation_sub_le_of_continuous hg hgc c
    (show 0 < η / 4 by positivity)
  refine ⟨σ, hσ, fun s a hs1 hsσ haσ ha2 ↦ ?_⟩
  have hs0 : s ≠ 0 := (zero_lt_one.trans_le hs1).ne'
  have hhg : AEStronglyMeasurable (h - g) volume :=
    hh.aestronglyMeasurable.sub hg.aestronglyMeasurable
  have e : (fun x ↦ a * h (c + s • (x - c)) - h x) =
      a • (fun x ↦ (h - g) (c + s • (x - c))) +
        ((fun x ↦ a * g (c + s • (x - c)) - g x) + (g - h)) := by
    funext x; simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have m1 : AEStronglyMeasurable (a • fun x ↦ (h - g) (c + s • (x - c))) volume :=
    (aestronglyMeasurable_comp_dilation hhg c hs0).const_smul a
  have m2 : AEStronglyMeasurable (fun x ↦ a * g (c + s • (x - c)) - g x) volume :=
    ((continuous_const.mul (hg.comp (continuous_dilation c s))).sub hg).aestronglyMeasurable
  have m3 : AEStronglyMeasurable (g - h) volume :=
    hg.aestronglyMeasurable.sub hh.aestronglyMeasurable
  have b1 : eLpNorm (a • fun x ↦ (h - g) (c + s • (x - c))) 2 volume ≤ ENNReal.ofReal (η / 2) := by
    rw [eLpNorm_const_smul]
    calc ‖a‖ₑ * eLpNorm (fun x ↦ (h - g) (c + s • (x - c))) 2 volume
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal (η / 4) := by
          gcongr
          · rw [← ofReal_norm, Real.norm_eq_abs]; exact ENNReal.ofReal_le_ofReal ha2
          · exact (eLpNorm_comp_dilation_le c hs1 hhg).trans hgh
      _ = ENNReal.ofReal (η / 2) := by
          rw [← ENNReal.ofReal_mul zero_le_two]; congr 1; ring
  have b3 : eLpNorm (g - h) 2 volume ≤ ENNReal.ofReal (η / 4) := by
    rw [eLpNorm_sub_comm]; exact hgh
  rw [e]
  calc eLpNorm (a • (fun x ↦ (h - g) (c + s • (x - c))) +
        ((fun x ↦ a * g (c + s • (x - c)) - g x) + (g - h))) 2 volume
      ≤ eLpNorm (a • fun x ↦ (h - g) (c + s • (x - c))) 2 volume +
        (eLpNorm (fun x ↦ a * g (c + s • (x - c)) - g x) 2 volume +
          eLpNorm (g - h) 2 volume) :=
        (eLpNorm_add_le one_le_two).trans (by gcongr; exact eLpNorm_add_le one_le_two)
    _ ≤ ENNReal.ofReal (η / 2) + (ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 4)) :=
        add_le_add b1 (add_le_add (hσg s a hs1 hsσ haσ) b3)
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

end OnePhaseDimension.Textbook
