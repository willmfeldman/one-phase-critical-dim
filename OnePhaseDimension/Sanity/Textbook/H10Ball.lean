/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Sanity.Textbook.Encoding
public import OnePhaseDimension.Sanity.Textbook.Dilation
public import EllipticBernoulli.Sobolev.Mollify
public import EllipticBernoulli.Sobolev.ZeroExtension

/-!
# `H¹₀` of a ball

If `w ∈ H¹_loc(ℝᵈ)` vanishes almost everywhere off the ball `B = ball c r`, then `w ∈ H¹₀(B)`:
it is an `H¹(B)` limit of functions in `C_c^∞(B)` (`h10_ball_of_memH1Loc`).

Proof: shrink, then mollify. For `s > 1` close to `1` the dilation `w(c + s(x - c))` is close to
`w` in `L²`, and its gradient `s Γ(c + s(x - c))` is close to `Γ`
(`exists_eLpNorm_mul_comp_dilation_sub_le`). It vanishes off `ball c (r / s)`. With `s` fixed,
mollify `w` at a scale `δ < (s - 1) r`: the mollification `f = w ⋆ ρ_δ` is smooth, vanishes off
`ball c (r + δ)`, and has gradient `Γ ⋆ ρ_δ`, and `f → w`, `Γ ⋆ ρ_δ → Γ` in `L²` as `δ → 0`.
The approximant is `φ(x) = f(c + s(x - c))`, which lies in `C_c^∞(B)`. Its distance to
`(w, Γ)` is at most the dilation error plus the mollification error, because composing with the
dilation does not increase `L²` norms (`eLpNorm_comp_dilation_le`).

Dilating the mollification of `w`, rather than mollifying the dilation of `w`, is the same up to
rescaling the mollifier and avoids a change of variables in the weak-gradient identity.
-/

open Set Filter Topology MeasureTheory Metric ContinuousLinearMap
open scoped ContDiff ENNReal Convolution

@[expose] public noncomputable section

namespace OnePhaseDimension.Textbook

open EllipticBernoulli

variable {d : ℕ}

/-- Mollifiers of radius `1 / (n + 1)`. -/
def stdBump (n : ℕ) : ContDiffBump (0 : E d) where
  rIn := 1 / (n + 2)
  rOut := 1 / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := one_div_lt_one_div_of_lt (by positivity) (by linarith)

theorem tendsto_stdBump_rOut : Tendsto (fun n ↦ (stdBump n : ContDiffBump (0 : E d)).rOut)
    atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Mollifications of an `L²` function converge in `L²`, eventually within any tolerance. -/
theorem eventually_eLpNorm_convolution_stdBump_sub_le {h : E d → ℝ} (hh : MemLp h 2 volume)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, eLpNorm (h ⋆[lsmul ℝ ℝ, volume] ((stdBump n).normed volume) - h) 2 volume ≤
      ENNReal.ofReal η := by
  have h2 : ENNReal.ofReal 2 = 2 := by simp
  have hh' : MemLp h (ENNReal.ofReal 2) volume := by rwa [h2]
  have := tendsto_eLpNorm_convolution_sub (p := 2) one_le_two hh' tendsto_stdBump_rOut
  rw [h2] at this
  exact ENNReal.tendsto_nhds_zero.1 this _ (ENNReal.ofReal_pos.2 hη)

theorem memLp_apply {μ : Measure (E d)} {Γ : E d → E d} (hΓ : MemLp Γ 2 μ) (i : Fin d) :
    MemLp (fun x ↦ Γ x i) 2 μ :=
  (EuclideanSpace.proj i : E d →L[ℝ] ℝ).comp_memLp' hΓ

theorem hasFDerivAt_dilation (c : E d) (s : ℝ) (x : E d) :
    HasFDerivAt (fun y : E d ↦ c + s • (y - c)) (s • ContinuousLinearMap.id ℝ (E d)) x := by
  simpa using (((hasFDerivAt_id x).sub_const c).const_smul s).const_add c

/-- **Smooth approximation in `H¹` of a function vanishing off a ball.** If `w ∈ L²(ℝᵈ)` has the
weak gradient `Γ ∈ L²(ℝᵈ)` on `ℝᵈ` and `w = 0` off `ball c r`, then for every `η > 0` some
`φ ∈ C_c^∞(ball c r)` is `η`-close to `w` in `L²` with each partial derivative `η`-close to the
corresponding component of `Γ`. -/
theorem exists_smooth_approx_of_eq_zero_off_ball {c : E d} {r : ℝ} (hr : 0 < r) {w : E d → ℝ}
    {Γ : E d → E d} (hw : MemLp w 2 volume) (hΓ : MemLp Γ 2 volume)
    (hwg : HasWeakGradient univ w Γ) (h0 : ∀ x, x ∉ ball c r → w x = 0) {η : ℝ} (hη : 0 < η) :
    ∃ φ : E d → ℝ, ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ ball c r ∧
      eLpNorm (fun x ↦ w x - φ x) 2 volume ≤ ENNReal.ofReal η ∧
      ∀ i : Fin d, eLpNorm (fun x ↦ Γ x i - partialDeriv i φ x) 2 volume ≤ ENNReal.ofReal η := by
  have hΓi : ∀ i, MemLp (fun x ↦ Γ x i) 2 volume := memLp_apply hΓ
  -- Step 1: the dilation factor `s`.
  have hev : ∀ (h : E d → ℝ), MemLp h 2 volume → ∀ᶠ s in 𝓝[>] (1 : ℝ),
      eLpNorm (fun x ↦ 1 * h (c + s • (x - c)) - h x) 2 volume ≤ ENNReal.ofReal (η / 2) ∧
      eLpNorm (fun x ↦ s * h (c + s • (x - c)) - h x) 2 volume ≤ ENNReal.ofReal (η / 2) ∧
      s ≤ 2 := by
    intro h hh
    obtain ⟨σ, hσ, hσh⟩ :=
      exists_eLpNorm_mul_comp_dilation_sub_le hh c (show 0 < η / 2 by positivity)
    filter_upwards [Ioc_mem_nhdsGT (show (1 : ℝ) < 1 + min σ 1 by
      linarith [lt_min hσ one_pos])] with s hs
    have hs1 : 1 ≤ s := hs.1.le
    have hsσ : s ≤ 1 + σ := hs.2.trans (by linarith [min_le_left σ 1])
    have hs2 : s ≤ 2 := hs.2.trans (by linarith [min_le_right σ 1])
    refine ⟨hσh s 1 hs1 hsσ (by simp [hσ.le]) (by norm_num), hσh s s hs1 hsσ ?_ ?_, hs2⟩
    · rw [abs_of_nonneg (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; exact hs2
  obtain ⟨s, ⟨⟨hsw, -, hs2⟩, hsΓ⟩, hs1⟩ :=
    ((hev w hw).and (eventually_all.2 fun i ↦ hev _ (hΓi i))).and self_mem_nhdsWithin
      |>.exists
  have hs1 : (1 : ℝ) < s := hs1
  have hs0 : s ≠ 0 := (zero_lt_one.trans hs1).ne'
  -- Step 2: the mollification scale.
  have hrδ : (0 : ℝ) < (s - 1) * r := mul_pos (by linarith) hr
  obtain ⟨n, ⟨hnw, hnΓ⟩, hnr⟩ := ((eventually_eLpNorm_convolution_stdBump_sub_le hw
    (show 0 < η / 2 by positivity)).and (eventually_all.2 fun i ↦
      eventually_eLpNorm_convolution_stdBump_sub_le (hΓi i) (show 0 < η / 4 by positivity))).and
    (tendsto_stdBump_rOut.eventually (gt_mem_nhds hrδ)) |>.exists
  set ρ : ContDiffBump (0 : E d) := stdBump n
  set k := ρ.normed volume
  set δ := ρ.rOut
  have hδ : 0 < δ := ρ.rOut_pos
  have hwsupp : Function.support w ⊆ ball c r := fun x hx ↦ by
    by_contra h; exact hx (h0 x h)
  have hwi : Integrable w := (integrableOn_iff_integrable_of_support_subset hwsupp).1
    (integrableOn_of_memLp_ball (hw.restrict _))
  set f := w ⋆[lsmul ℝ ℝ, volume] k
  have hf : ContDiff ℝ ∞ f :=
    ρ.hasCompactSupport_normed.contDiff_convolution_right (L := lsmul ℝ ℝ) hwi.locallyIntegrable
      ρ.contDiff_normed
  have hfsupp : ∀ y, y ∉ ball c (r + δ) → f y = 0 := by
    intro y hy
    by_contra hfy
    have h1 := support_convolution_subset (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) (μ := volume) hfy
    rw [ρ.support_normed_eq] at h1
    have h2 := add_subset_add hwsupp subset_rfl h1
    rw [ball_add_ball hr hδ, add_zero] at h2
    exact hy h2
  have hfd : ∀ i y, partialDeriv i f y = ((fun x ↦ Γ x i) ⋆[lsmul ℝ ℝ, volume] k) y := by
    intro i y
    have hid : ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ univ →
        ∀ v : E d, ∫ x, w x * fderiv ℝ φ x v = -∫ x, inner ℝ (Γ x) v * φ x := by
      intro φ hφ hφc _ v
      simpa only [Measure.restrict_univ] using hwg.2.2 φ hφ hφc (subset_univ _) v
    have := fderiv_convolution_indicator_eq MeasurableSet.univ hwi.integrableOn hid ρ
      (EuclideanSpace.single i 1) (subset_univ (closedBall y δ))
    simp only [indicator_univ, inner_single_one] at this
    exact this
  -- Step 3: the approximant.
  set φ : E d → ℝ := fun x ↦ f (c + s • (x - c))
  have hφ : ContDiff ℝ ∞ φ := hf.comp (by fun_prop)
  have hφsupp : ∀ x, x ∉ closedBall c ((r + δ) / s) → φ x = 0 := by
    intro x hx
    refine hfsupp _ fun hmem ↦ hx ?_
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (zero_lt_one.trans hs1)] at hmem
    rw [mem_closedBall, dist_eq_norm, le_div_iff₀ (zero_lt_one.trans hs1)]
    linarith
  have hball : closedBall c ((r + δ) / s) ⊆ ball c r := by
    refine closedBall_subset_ball ?_
    rw [div_lt_iff₀ (zero_lt_one.trans hs1)]
    nlinarith
  have hφc : HasCompactSupport φ := HasCompactSupport.intro (isCompact_closedBall _ _) hφsupp
  have hφB : tsupport φ ⊆ ball c r :=
    (closure_minimal (fun x hx ↦ by_contra fun h ↦ Function.mem_support.1 hx (hφsupp x h))
      isClosed_closedBall).trans
      hball
  have hφd : ∀ i x, partialDeriv i φ x =
      s * ((fun x ↦ Γ x i) ⋆[lsmul ℝ ℝ, volume] k) (c + s • (x - c)) := by
    intro i x
    have h := ((hf.differentiable (by simp) _).hasFDerivAt.comp x
      (hasFDerivAt_dilation c s x)).fderiv
    simp only [partialDeriv] at hfd ⊢
    change fderiv ℝ (f ∘ fun x ↦ c + s • (x - c)) x (EuclideanSpace.single i 1) = _
    rw [h,
      ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
      map_smul, smul_eq_mul, hfd]
  refine ⟨φ, hφ, hφc, hφB, ?_, fun i ↦ ?_⟩
  · -- the function
    have hfm : AEStronglyMeasurable (w - f) volume :=
      hw.aestronglyMeasurable.sub hf.continuous.aestronglyMeasurable
    have e : (fun x ↦ w x - φ x) = (fun x ↦ (w - f) (c + s • (x - c))) +
        -(fun x ↦ 1 * w (c + s • (x - c)) - w x) := by
      funext x; simp only [φ, Pi.add_apply, Pi.neg_apply, Pi.sub_apply]; ring
    rw [e]
    calc eLpNorm ((fun x ↦ (w - f) (c + s • (x - c))) +
          -(fun x ↦ 1 * w (c + s • (x - c)) - w x)) 2 volume
        ≤ eLpNorm (fun x ↦ (w - f) (c + s • (x - c))) 2 volume +
          eLpNorm (fun x ↦ 1 * w (c + s • (x - c)) - w x) 2 volume := by
          refine (eLpNorm_add_le one_le_two).trans_eq ?_
          rw [eLpNorm_neg]
      _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) := by
          gcongr
          refine (eLpNorm_comp_dilation_le c hs1.le hfm).trans ?_
          rw [eLpNorm_sub_comm]; exact hnw
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
  · -- the gradient
    set Γi := fun x ↦ Γ x i
    set g := Γi ⋆[lsmul ℝ ℝ, volume] k
    have hgc : Continuous g :=
      ρ.hasCompactSupport_normed.continuous_convolution_right (L := lsmul ℝ ℝ)
        ((hΓi i).locallyIntegrable one_le_two) ρ.continuous_normed
    have hgm : AEStronglyMeasurable (Γi - g) volume :=
      (hΓi i).aestronglyMeasurable.sub hgc.aestronglyMeasurable
    have e : (fun x ↦ Γ x i - partialDeriv i φ x) = s • (fun x ↦ (Γi - g) (c + s • (x - c))) +
        -(fun x ↦ s * Γi (c + s • (x - c)) - Γi x) := by
      funext x
      simp only [hφd, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Γi, g]
      ring
    rw [e]
    calc eLpNorm (s • (fun x ↦ (Γi - g) (c + s • (x - c))) +
          -(fun x ↦ s * Γi (c + s • (x - c)) - Γi x)) 2 volume
        ≤ ‖s‖ₑ * eLpNorm (fun x ↦ (Γi - g) (c + s • (x - c))) 2 volume +
          eLpNorm (fun x ↦ s * Γi (c + s • (x - c)) - Γi x) 2 volume := by
          refine (eLpNorm_add_le one_le_two).trans_eq ?_
          rw [eLpNorm_neg, eLpNorm_const_smul]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (η / 4) + ENNReal.ofReal (η / 2) := by
          gcongr
          · rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (zero_lt_one.trans hs1)]
            exact ENNReal.ofReal_le_ofReal hs2
          · refine (eLpNorm_comp_dilation_le c hs1.le hgm).trans ?_
            rw [eLpNorm_sub_comm]; exact hnΓ i
          · exact (hsΓ i).2.1
      _ = ENNReal.ofReal η := by
          rw [← ENNReal.ofReal_mul zero_le_two, ← ENNReal.ofReal_add (by positivity)
            (by positivity)]
          congr 1; ring

/-- **`H¹₀` of a ball.** If `w ∈ H¹_loc(ℝᵈ)` with weak gradient `Γ` vanishes almost everywhere
off the ball `B = ball c r`, then `w ∈ H¹₀(B)` with weak gradient `Γ`. -/
theorem h10_ball_of_memH1Loc {c : E d} {r : ℝ} (hr : 0 < r) {w : E d → ℝ} {Γ : E d → E d}
    (hw : MemH1Loc univ w Γ) (h0 : ∀ᵐ x ∂(volume.restrict (ball c r)ᶜ), w x = 0) :
    H10 (ball c r) w Γ := by
  have hH1 := h1_ball_of_memH1Loc hw c r
  refine ⟨hH1, fun ε hε ↦ ?_⟩
  set B := ball c r
  -- `w` and `Γ` are square integrable on `ℝᵈ`.
  have hwB : w =ᵐ[volume] B.indicator w := by
    rw [ae_restrict_iff' measurableSet_ball.compl] at h0
    filter_upwards [h0] with x hx
    by_cases hxB : x ∈ B
    · rw [indicator_of_mem hxB]
    · rw [indicator_of_notMem hxB, hx hxB]
  have hw2 : MemLp w 2 volume :=
    ((memLp_indicator_iff_restrict measurableSet_ball).2 hH1.1).ae_eq hwB.symm
  obtain ⟨hwc, hΓc⟩ := hw.2 (closedBall c r) (subset_univ _) (isCompact_closedBall c r)
  have hΓ0 : ∀ᵐ x ∂(volume.restrict (closedBall c r)ᶜ), Γ x = 0 :=
    hw.1.ae_eq_zero_of_ae_eq_zero_on isClosed_closedBall.isOpen_compl (subset_univ _)
      (ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 ball_subset_closedBall) h0)
  have hΓB : Γ =ᵐ[volume] (closedBall c r).indicator Γ := by
    rw [ae_restrict_iff' measurableSet_closedBall.compl] at hΓ0
    filter_upwards [hΓ0] with x hx
    by_cases hxB : x ∈ closedBall c r
    · rw [indicator_of_mem hxB]
    · rw [indicator_of_notMem hxB, hx hxB]
  have hΓ2 : MemLp Γ 2 volume :=
    ((memLp_indicator_iff_restrict measurableSet_closedBall).2 hΓc).ae_eq hΓB.symm
  -- Replace `w` by its zero extension off `B`.
  have hwg' : HasWeakGradient univ (B.indicator w) Γ := by
    obtain ⟨h1, h2, h3⟩ := hasWeakGradient_univ_iff.1 hw.1
    exact hasWeakGradient_univ_iff.2 ⟨h1.congr hwB, h2, h3.congr_ae hwB (ae_eq_refl _)⟩
  obtain ⟨φ, hφ, hφc, hφB, hφw, hφΓ⟩ := exists_smooth_approx_of_eq_zero_off_ball hr
    (hw2.ae_eq hwB) hΓ2 hwg' (fun x hx ↦ indicator_of_notMem hx w)
    (show 0 < ε / 2 by positivity)
  have hlt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  refine ⟨φ, hφ, hφc, hφB, ?_, fun i ↦ ?_⟩
  · have e : (fun x ↦ w x - φ x) =ᵐ[volume.restrict B] fun x ↦ B.indicator w x - φ x := by
      rw [EventuallyEq, ae_restrict_iff' measurableSet_ball]
      exact Eventually.of_forall fun x hx ↦ by rw [indicator_of_mem hx]
    rw [eLpNorm_congr_ae e]
    exact ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans hφw).trans_lt hlt
  · exact ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hφΓ i)).trans_lt hlt

end OnePhaseDimension.Textbook
