/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The radial Hardy identity and the logarithmic cutoff

For a radial profile `ζ` on `(0, ∞)` the separated stability inequality in `ℝ⁶` has the radial
factors `∫₀^∞ r³ ζ² dr` and `∫₀^∞ r⁵ ζ'² dr`. The sharp ratio between them is `β² = 4`,
`β = (m - 1)/2` with `m = 5`, approached by the logarithmic profiles
`ζ_k(r) = r⁻² ψ(log r / k)`.

* `logProfile g r = r⁻² g(log r)` for `r > 0` (and `0` for `r ≤ 0`). For `g` smooth with compact
  support it is smooth on `ℝ` with compact support in `(0, ∞)`.
* `integral_pow_three_mul_logProfile_sq`: `∫₀^∞ r³ ζ² dr = ∫_ℝ g²`.
* `integral_pow_five_mul_deriv_logProfile_sq`: `∫₀^∞ r⁵ ζ'² dr = ∫_ℝ (g' - 2g)² = ∫ g'² + 4 ∫ g²`
  (substitution `r = eᵗ`; the cross term `∫ g g'` vanishes by compact support).
* `radial_hardy_ratio`: for `ζ_k(r) = r⁻² ψ(log r / k)`, `∫ r³ ζ_k² = k ∫ ψ²` and
  `∫ r⁵ ζ_k'² = k (4 ∫ ψ² + k⁻² ∫ ψ'²)`, so the ratio is `4 + k⁻² ‖ψ'‖² / ‖ψ‖² → 4`.
* `exists_radial_profile_ratio_le`: for every `η > 0` there is a smooth profile with compact
  support in `(0, ∞)`, with `∫ r³ ζ² > 0` and `∫ r⁵ ζ'² ≤ (4 + η) ∫ r³ ζ²`.

## General dimension

In `ℝⁿ` (`n ≥ 3`, link `S^{n-1}`) the radial factors are `∫ r^{n-3} ζ²` and `∫ r^{n-1} ζ'²` and
the sharp constant is `β² = ((n - 2)/2)²`. With `p = n - 3` and `2β = p + 1`:

* `powLogProfile β g r = r^{-β} g(log r)` (written `exp(-β log r) g(log r)`), with
  `logProfile g = powLogProfile 2 g`;
* `integral_pow_mul_powLogProfile_sq`: `∫₀^∞ rᵖ ζ² = ∫ g²`;
* `integral_pow_add_two_mul_deriv_powLogProfile_sq`: `∫₀^∞ r^{p+2} ζ'² = ∫ (g' - βg)²`;
* `integral_deriv_sub_mul_sq`: `∫ (g' - βg)² = ∫ g'² + β² ∫ g²`;
* `exists_radial_profile_pow_ratio_le`: for every `p ∈ ℕ` and `η > 0` there is a profile with
  `∫ r^{p+2} ζ'² ≤ (((p + 1)/2)² + η) ∫ rᵖ ζ²`.

The statements for `ℝ⁶` above are the case `p = 3`, `β = 2`.

The inequality `∫ r⁵ ζ'² ≥ 4 ∫ r³ ζ²` itself (the Hardy identity's sign) is not needed: only the
existence of profiles approaching the constant `4` enters the spherical comparison.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff

@[expose] public noncomputable section

namespace OnePhaseDimension

/-- The logarithmic profile `r ↦ r⁻² g(log r)` on `(0, ∞)`, extended by `0` to `r ≤ 0`. -/
def logProfile (g : ℝ → ℝ) (r : ℝ) : ℝ := if 0 < r then (r ^ 2)⁻¹ * g (Real.log r) else 0

theorem logProfile_of_pos (g : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    logProfile g r = (r ^ 2)⁻¹ * g (Real.log r) := by simp [logProfile, hr]

theorem logProfile_of_nonpos (g : ℝ → ℝ) {r : ℝ} (hr : r ≤ 0) : logProfile g r = 0 := by
  simp [logProfile, not_lt.2 hr]

theorem logProfile_exp (g : ℝ → ℝ) (t : ℝ) :
    logProfile g (Real.exp t) = (Real.exp t ^ 2)⁻¹ * g t := by
  rw [logProfile_of_pos g (Real.exp_pos t), Real.log_exp]

/-- The derivative of the logarithmic profile: `ζ'(r) = r⁻³ (g'(log r) - 2 g(log r))`. -/
theorem hasDerivAt_logProfile {g : ℝ → ℝ} (hg : Differentiable ℝ g) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (logProfile g)
      ((r ^ 3)⁻¹ * (deriv g (Real.log r) - 2 * g (Real.log r))) r := by
  have h1 := (hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr.ne')
  have h2 : HasDerivAt (fun s ↦ g (Real.log s)) (deriv g (Real.log r) * r⁻¹) r :=
    (hg _).hasDerivAt.comp r (Real.hasDerivAt_log hr.ne')
  have h := h1.mul h2
  have heq : (fun s ↦ (s ^ 2)⁻¹ * g (Real.log s)) =ᶠ[𝓝 r] logProfile g := by
    filter_upwards [lt_mem_nhds hr] with s hs
    rw [logProfile_of_pos g hs]
  refine (h.congr_of_eventuallyEq heq.symm).congr_deriv ?_
  simp only [Pi.inv_apply]
  field_simp
  ring

/-- A compactly supported `g` vanishes outside some interval `[-L, L]`. -/
theorem exists_eq_zero_of_abs_gt {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t, L < |t| → g t = 0 := by
  obtain ⟨L, hL⟩ := hgc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max L 0, le_max_right _ _, fun t ht ↦ ?_⟩
  by_contra h
  have hmem := hL (subset_tsupport g h)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
  exact absurd (hmem.trans (le_max_left L 0)) (not_le.2 ht)

theorem logProfile_eq_zero_of_notMem {g : ℝ → ℝ} {L : ℝ} (hL : ∀ t, L < |t| → g t = 0) {r : ℝ}
    (hr : r ∉ Icc (Real.exp (-L)) (Real.exp L)) : logProfile g r = 0 := by
  rcases le_or_gt r 0 with h | h
  · exact logProfile_of_nonpos g h
  rw [logProfile_of_pos g h, hL, mul_zero]
  rw [mem_Icc, not_and_or, not_le, not_le] at hr
  rcases hr with hr | hr
  · have : Real.log r < -L := by rwa [Real.log_lt_iff_lt_exp h]
    linarith [neg_le_abs (Real.log r)]
  · have : L < Real.log r := by rwa [Real.lt_log_iff_exp_lt h]
    exact this.trans_le (le_abs_self _)

theorem hasCompactSupport_logProfile {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    HasCompactSupport (logProfile g) := by
  obtain ⟨L, -, hL⟩ := exists_eq_zero_of_abs_gt hgc
  exact HasCompactSupport.intro isCompact_Icc fun r hr ↦ logProfile_eq_zero_of_notMem hL hr

/-- The logarithmic profile is supported in `(0, ∞)`. -/
theorem tsupport_logProfile_subset {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    tsupport (logProfile g) ⊆ Ioi 0 := by
  obtain ⟨L, -, hL⟩ := exists_eq_zero_of_abs_gt hgc
  refine (closure_minimal (t := Icc (Real.exp (-L)) (Real.exp L)) (fun r hr ↦ ?_)
    isClosed_Icc).trans
    fun r (hr : r ∈ Icc _ _) ↦ (Real.exp_pos (-L)).trans_le hr.1
  by_contra h
  exact hr (logProfile_eq_zero_of_notMem hL h)

theorem contDiff_logProfile {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ContDiff ℝ ∞ (logProfile g) := by
  obtain ⟨L, -, hL⟩ := exists_eq_zero_of_abs_gt hgc
  refine contDiff_iff_contDiffAt.2 fun r ↦ ?_
  rcases lt_or_ge r (Real.exp (-L)) with h | h
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds h] with s hs
    exact logProfile_eq_zero_of_notMem hL fun hm ↦ absurd hm.1 (not_le.2 hs)
  · have hr : 0 < r := (Real.exp_pos _).trans_le h
    have hsm : ContDiffAt ℝ ∞ (fun s : ℝ ↦ (s ^ 2)⁻¹ * g (Real.log s)) r :=
      ((contDiffAt_id.pow 2).inv (pow_ne_zero 2 hr.ne')).mul
        (hg.contDiffAt.comp r (Real.contDiffAt_log.2 hr.ne'))
    refine hsm.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hr] with s hs
    rw [logProfile_of_pos g hs]

/-! ### The profiles `r ↦ r^{-β} g(log r)` -/

/-- The logarithmic profile with exponent `β`: `r ↦ r^{-β} g(log r)` on `(0, ∞)`, written as
`exp(-β log r) g(log r)`, and extended by `0` to `r ≤ 0`. -/
def powLogProfile (β : ℝ) (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  if 0 < r then Real.exp (-β * Real.log r) * g (Real.log r) else 0

theorem powLogProfile_of_pos (β : ℝ) (g : ℝ → ℝ) {r : ℝ} (hr : 0 < r) :
    powLogProfile β g r = Real.exp (-β * Real.log r) * g (Real.log r) := by
  simp [powLogProfile, hr]

theorem powLogProfile_of_nonpos (β : ℝ) (g : ℝ → ℝ) {r : ℝ} (hr : r ≤ 0) :
    powLogProfile β g r = 0 := by
  simp [powLogProfile, not_lt.2 hr]

theorem powLogProfile_exp (β : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    powLogProfile β g (Real.exp t) = Real.exp (-β * t) * g t := by
  rw [powLogProfile_of_pos β g (Real.exp_pos t), Real.log_exp]

/-- For `β = 2` the profile `r^{-β} g(log r)` is `logProfile g`. -/
theorem logProfile_eq_powLogProfile (g : ℝ → ℝ) : logProfile g = powLogProfile 2 g := by
  funext r
  rcases le_or_gt r 0 with hr | hr
  · rw [logProfile_of_nonpos g hr, powLogProfile_of_nonpos 2 g hr]
  · rw [logProfile_of_pos g hr, powLogProfile_of_pos 2 g hr, neg_mul, Real.exp_neg,
      mul_comm (2 : ℝ), ← Real.rpow_def_of_pos hr, Real.rpow_two]

/-- The derivative of `r^{-β} g(log r)`: `ζ'(r) = r⁻¹ r^{-β} (g'(log r) - β g(log r))`. -/
theorem hasDerivAt_powLogProfile (β : ℝ) {g : ℝ → ℝ} (hg : Differentiable ℝ g) {r : ℝ}
    (hr : 0 < r) :
    HasDerivAt (powLogProfile β g)
      (r⁻¹ * (Real.exp (-β * Real.log r) *
        (deriv g (Real.log r) - β * g (Real.log r)))) r := by
  have hlog := Real.hasDerivAt_log hr.ne'
  have h1 : HasDerivAt (fun s ↦ Real.exp (-β * Real.log s))
      (Real.exp (-β * Real.log r) * (-β * r⁻¹)) r :=
    (hlog.const_mul (-β)).exp
  have h2 : HasDerivAt (fun s ↦ g (Real.log s)) (deriv g (Real.log r) * r⁻¹) r :=
    (hg _).hasDerivAt.comp r hlog
  have heq : (fun s ↦ Real.exp (-β * Real.log s) * g (Real.log s)) =ᶠ[𝓝 r] powLogProfile β g := by
    filter_upwards [lt_mem_nhds hr] with s hs
    rw [powLogProfile_of_pos β g hs]
  refine ((h1.mul h2).congr_of_eventuallyEq heq.symm).congr_deriv ?_
  ring

theorem powLogProfile_eq_zero_of_notMem (β : ℝ) {g : ℝ → ℝ} {L : ℝ}
    (hL : ∀ t, L < |t| → g t = 0) {r : ℝ} (hr : r ∉ Icc (Real.exp (-L)) (Real.exp L)) :
    powLogProfile β g r = 0 := by
  rcases le_or_gt r 0 with h | h
  · exact powLogProfile_of_nonpos β g h
  rw [powLogProfile_of_pos β g h, hL, mul_zero]
  rw [mem_Icc, not_and_or, not_le, not_le] at hr
  rcases hr with hr | hr
  · have : Real.log r < -L := by rwa [Real.log_lt_iff_lt_exp h]
    linarith [neg_le_abs (Real.log r)]
  · have : L < Real.log r := by rwa [Real.lt_log_iff_exp_lt h]
    exact this.trans_le (le_abs_self _)

theorem hasCompactSupport_powLogProfile (β : ℝ) {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    HasCompactSupport (powLogProfile β g) := by
  obtain ⟨L, -, hL⟩ := exists_eq_zero_of_abs_gt hgc
  exact HasCompactSupport.intro isCompact_Icc fun r hr ↦ powLogProfile_eq_zero_of_notMem β hL hr

/-- The profile `r^{-β} g(log r)` is supported in `(0, ∞)`. -/
theorem tsupport_powLogProfile_subset (β : ℝ) {g : ℝ → ℝ} (hgc : HasCompactSupport g) :
    tsupport (powLogProfile β g) ⊆ Ioi 0 := by
  obtain ⟨L, -, hL⟩ := exists_eq_zero_of_abs_gt hgc
  refine (closure_minimal (t := Icc (Real.exp (-L)) (Real.exp L)) (fun r hr ↦ ?_)
    isClosed_Icc).trans
    fun r (hr : r ∈ Icc _ _) ↦ (Real.exp_pos (-L)).trans_le hr.1
  by_contra h
  exact hr (powLogProfile_eq_zero_of_notMem β hL h)

theorem contDiff_powLogProfile (β : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) : ContDiff ℝ ∞ (powLogProfile β g) := by
  obtain ⟨L, -, hL⟩ := exists_eq_zero_of_abs_gt hgc
  refine contDiff_iff_contDiffAt.2 fun r ↦ ?_
  rcases lt_or_ge r (Real.exp (-L)) with h | h
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [gt_mem_nhds h] with s hs
    exact powLogProfile_eq_zero_of_notMem β hL fun hm ↦ absurd hm.1 (not_le.2 hs)
  · have hr : 0 < r := (Real.exp_pos _).trans_le h
    have hlog : ContDiffAt ℝ ∞ Real.log r := Real.contDiffAt_log.2 hr.ne'
    have hsm : ContDiffAt ℝ ∞ (fun s : ℝ ↦ Real.exp (-β * Real.log s) * g (Real.log s)) r :=
      (Real.contDiff_exp.contDiffAt.comp r (contDiffAt_const.mul hlog)).mul
        (hg.contDiffAt.comp r hlog)
    refine hsm.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds hr] with s hs
    rw [powLogProfile_of_pos β g hs]

/-- `eᵗ (eᵗ)^p e^{-2βt} = 1` when `2β = p + 1`. -/
theorem exp_mul_exp_pow_mul_exp_sq {p : ℕ} {β : ℝ} (hβ : 2 * β = p + 1) (t : ℝ) :
    Real.exp t * Real.exp t ^ p * Real.exp (-β * t) ^ 2 = 1 := by
  rw [← Real.exp_nat_mul, pow_two, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    Real.exp_eq_one_iff]
  linear_combination (-t) * hβ

/-- **Substitution `r = eᵗ`, mass term, general weight**: if `2β = p + 1`, then
`∫₀^∞ rᵖ ζ² dr = ∫_ℝ g²` for `ζ(r) = r^{-β} g(log r)`. -/
theorem integral_pow_mul_powLogProfile_sq (p : ℕ) {β : ℝ} (hβ : 2 * β = p + 1) (g : ℝ → ℝ) :
    ∫ r in Ioi (0 : ℝ), r ^ p * powLogProfile β g r ^ 2 = ∫ t, g t ^ 2 := by
  rw [← integral_comp_exp]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp only [smul_eq_mul, powLogProfile_exp]
  calc Real.exp t * (Real.exp t ^ p * (Real.exp (-β * t) * g t) ^ 2)
      = (Real.exp t * Real.exp t ^ p * Real.exp (-β * t) ^ 2) * g t ^ 2 := by ring
    _ = g t ^ 2 := by rw [exp_mul_exp_pow_mul_exp_sq hβ, one_mul]

/-- **Substitution `r = eᵗ`, energy term, general weight**: if `2β = p + 1`, then
`∫₀^∞ r^{p+2} ζ'² dr = ∫_ℝ (g' - βg)²` for `ζ(r) = r^{-β} g(log r)`. -/
theorem integral_pow_add_two_mul_deriv_powLogProfile_sq (p : ℕ) {β : ℝ}
    (hβ : 2 * β = p + 1) {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    ∫ r in Ioi (0 : ℝ), r ^ (p + 2) * deriv (powLogProfile β g) r ^ 2 =
      ∫ t, (deriv g t - β * g t) ^ 2 := by
  rw [← integral_comp_exp]
  refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
  simp only [smul_eq_mul, (hasDerivAt_powLogProfile β hg (Real.exp_pos t)).deriv,
    Real.log_exp]
  have he : Real.exp t * (Real.exp t)⁻¹ = 1 := mul_inv_cancel₀ (Real.exp_pos t).ne'
  calc Real.exp t * (Real.exp t ^ (p + 2) *
        ((Real.exp t)⁻¹ * (Real.exp (-β * t) * (deriv g t - β * g t))) ^ 2)
      = (Real.exp t * Real.exp t ^ p * Real.exp (-β * t) ^ 2) * (Real.exp t * (Real.exp t)⁻¹) ^ 2 *
          (deriv g t - β * g t) ^ 2 := by ring
    _ = (deriv g t - β * g t) ^ 2 := by rw [exp_mul_exp_pow_mul_exp_sq hβ, he]; ring

/-- **Substitution `r = eᵗ`, mass term**: `∫₀^∞ r³ ζ² dr = ∫_ℝ g²` for `ζ = logProfile g`. -/
theorem integral_pow_three_mul_logProfile_sq (g : ℝ → ℝ) :
    ∫ r in Ioi (0 : ℝ), r ^ 3 * logProfile g r ^ 2 = ∫ t, g t ^ 2 := by
  rw [logProfile_eq_powLogProfile]
  exact integral_pow_mul_powLogProfile_sq 3 (by norm_num) g

/-- **Substitution `r = eᵗ`, energy term**: `∫₀^∞ r⁵ ζ'² dr = ∫_ℝ (g' - 2g)²`. -/
theorem integral_pow_five_mul_deriv_logProfile_sq {g : ℝ → ℝ} (hg : Differentiable ℝ g) :
    ∫ r in Ioi (0 : ℝ), r ^ 5 * deriv (logProfile g) r ^ 2 =
      ∫ t, (deriv g t - 2 * g t) ^ 2 := by
  rw [logProfile_eq_powLogProfile]
  exact integral_pow_add_two_mul_deriv_powLogProfile_sq 3 (by norm_num) hg

theorem hasCompactSupport_sq {f : ℝ → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport fun t ↦ f t ^ 2 :=
  hf.mono fun t ht h ↦ ht (by simpa using h)

theorem integrable_sq_of_continuous {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable fun t ↦ f t ^ 2 :=
  (hf.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hfc)

/-- `∫ g g' = 0` for `g` of class `C¹` with compact support. -/
theorem integral_mul_deriv_eq_zero {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) : ∫ t, g t * deriv g t = 0 := by
  have hd : ∀ t, HasDerivAt (fun s ↦ g s ^ 2 / 2) (g t * deriv g t) t := fun t ↦ by
    have := ((hg.differentiable one_ne_zero t).hasDerivAt.pow 2).div_const 2
    convert this using 1
    push_cast
    ring
  have hint : Integrable fun t ↦ g t * deriv g t :=
    (hg.continuous.mul (hg.continuous_deriv le_rfl)).integrable_of_hasCompactSupport
      (hgc.mul_right)
  have hc : HasCompactSupport fun s ↦ g s ^ 2 / 2 :=
    hgc.mono fun t ht h ↦ ht (by simpa using h)
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at hc
  have h := integral_of_hasDerivAt_of_tendsto hd hint
    ((hc.filter_mono atBot_le_cocompact).tendsto) ((hc.filter_mono atTop_le_cocompact).tendsto)
  simpa using h

/-- `∫ (g' - βg)² = ∫ g'² + β² ∫ g²` for `g` of class `C¹` with compact support. -/
theorem integral_deriv_sub_mul_sq (β : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    ∫ t, (deriv g t - β * g t) ^ 2 = (∫ t, deriv g t ^ 2) + β ^ 2 * ∫ t, g t ^ 2 := by
  have hc : Continuous g := hg.continuous
  have hc' : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hdc : HasCompactSupport (deriv g) := hgc.deriv
  have i1 : Integrable fun t ↦ deriv g t ^ 2 :=
    integrable_sq_of_continuous hc' hdc
  have i2 : Integrable fun t ↦ (2 * β) * (g t * deriv g t) :=
    ((hc.mul hc').integrable_of_hasCompactSupport hgc.mul_right).const_mul (2 * β)
  have i3 : Integrable fun t ↦ β ^ 2 * g t ^ 2 :=
    (integrable_sq_of_continuous hc hgc).const_mul (β ^ 2)
  have hexp : (fun t ↦ (deriv g t - β * g t) ^ 2) =
      fun t ↦ deriv g t ^ 2 - (2 * β) * (g t * deriv g t) + β ^ 2 * g t ^ 2 := by
    funext t; ring
  have i12 : Integrable fun t ↦ deriv g t ^ 2 - (2 * β) * (g t * deriv g t) := i1.sub i2
  have h1 := integral_add i12 i3
  have h2 := integral_sub i1 i2
  have h3 := integral_const_mul (μ := volume) (2 * β) fun t ↦ g t * deriv g t
  have h4 := integral_const_mul (μ := volume) (β ^ 2) fun t ↦ g t ^ 2
  rw [hexp, h1, h2, h3, h4, integral_mul_deriv_eq_zero hg hgc]
  ring

/-- `∫ (g' - 2g)² = ∫ g'² + 4 ∫ g²` for `g` of class `C¹` with compact support. -/
theorem integral_deriv_sub_two_mul_sq {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) :
    ∫ t, (deriv g t - 2 * g t) ^ 2 = (∫ t, deriv g t ^ 2) + 4 * ∫ t, g t ^ 2 := by
  rw [integral_deriv_sub_mul_sq 2 hg hgc]
  norm_num

/-! ### The logarithmic cutoffs `ζ_k(r) = r⁻² ψ(log r / k)` -/

theorem hasDerivAt_comp_div {ψ : ℝ → ℝ} (hψ : Differentiable ℝ ψ) (k t : ℝ) :
    HasDerivAt (fun s ↦ ψ (s / k)) (k⁻¹ * deriv ψ (t / k)) t := by
  have := (hψ (t / k)).hasDerivAt.comp t ((hasDerivAt_id t).div_const k)
  exact this.congr_deriv (by ring)

theorem hasCompactSupport_comp_div {ψ : ℝ → ℝ} (hψc : HasCompactSupport ψ) {k : ℝ} (hk : 0 < k) :
    HasCompactSupport fun t ↦ ψ (t / k) := by
  have h := hψc.comp_smul (inv_ne_zero hk.ne')
  simp only [smul_eq_mul] at h
  convert h using 2 with t
  rw [div_eq_mul_inv, mul_comm]

/-- **The radial Hardy ratio for the logarithmic cutoffs, general weight.** Let `2β = p + 1`.
With `ζ_k(r) = r^{-β} ψ(log r / k)`, `∫₀^∞ rᵖ ζ_k² = k ∫ ψ²` and
`∫₀^∞ r^{p+2} ζ_k'² = k (β² ∫ ψ² + k⁻² ∫ ψ'²)`. -/
theorem radial_hardy_ratio_pow (p : ℕ) {β : ℝ} (hβ : 2 * β = p + 1) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {k : ℝ} (hk : 0 < k) :
    (∫ r in Ioi (0 : ℝ), r ^ p * powLogProfile β (fun t ↦ ψ (t / k)) r ^ 2) =
      k * ∫ t, ψ t ^ 2 ∧
    (∫ r in Ioi (0 : ℝ), r ^ (p + 2) * deriv (powLogProfile β (fun t ↦ ψ (t / k))) r ^ 2) =
      k * (β ^ 2 * (∫ t, ψ t ^ 2) + (k ^ 2)⁻¹ * ∫ t, deriv ψ t ^ 2) := by
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hg : ContDiff ℝ ∞ fun t ↦ ψ (t / k) := hψ.comp (contDiff_id.div_const k)
  have hgc : HasCompactSupport fun t ↦ ψ (t / k) := hasCompactSupport_comp_div hψc hk
  have hmass : ∫ t, ψ (t / k) ^ 2 = k * ∫ t, ψ t ^ 2 := by
    have := Measure.integral_comp_div (fun s ↦ ψ s ^ 2) k
    rw [abs_of_pos hk, smul_eq_mul] at this
    exact this
  have hdg : deriv (fun t ↦ ψ (t / k)) = fun t ↦ k⁻¹ * deriv ψ (t / k) :=
    funext fun t ↦ (hasDerivAt_comp_div hψd k t).deriv
  have hgrad : ∫ t, deriv (fun t ↦ ψ (t / k)) t ^ 2 = k * ((k ^ 2)⁻¹ * ∫ t, deriv ψ t ^ 2) := by
    have := Measure.integral_comp_div (fun s ↦ deriv ψ s ^ 2) k
    rw [abs_of_pos hk, smul_eq_mul] at this
    simp_rw [hdg, mul_pow]
    rw [integral_const_mul, this, inv_pow]
    ring
  refine ⟨by rw [integral_pow_mul_powLogProfile_sq p hβ, hmass], ?_⟩
  rw [integral_pow_add_two_mul_deriv_powLogProfile_sq p hβ (hg.differentiable (by simp)),
    integral_deriv_sub_mul_sq β (hg.of_le (by simp)) hgc]
  linear_combination hgrad + β ^ 2 * hmass

/-- **The radial Hardy ratio for the logarithmic cutoffs.** With `ζ_k(r) = r⁻² ψ(log r / k)`,
`∫₀^∞ r³ ζ_k² = k ∫ ψ²` and `∫₀^∞ r⁵ ζ_k'² = k (4 ∫ ψ² + k⁻² ∫ ψ'²)`. -/
theorem radial_hardy_ratio {ψ : ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    {k : ℝ} (hk : 0 < k) :
    (∫ r in Ioi (0 : ℝ), r ^ 3 * logProfile (fun t ↦ ψ (t / k)) r ^ 2) = k * ∫ t, ψ t ^ 2 ∧
    (∫ r in Ioi (0 : ℝ), r ^ 5 * deriv (logProfile (fun t ↦ ψ (t / k))) r ^ 2) =
      k * (4 * (∫ t, ψ t ^ 2) + (k ^ 2)⁻¹ * ∫ t, deriv ψ t ^ 2) := by
  rw [logProfile_eq_powLogProfile]
  obtain ⟨h1, h2⟩ := radial_hardy_ratio_pow 3 (β := 2) (by norm_num) hψ hψc hk
  refine ⟨h1, ?_⟩
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num]
  exact h2

/-- A fixed nonzero smooth compactly supported function on `ℝ`. -/
theorem exists_contDiff_hasCompactSupport_integral_sq_pos :
    ∃ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ 0 < ∫ t, ψ t ^ 2 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨⇑b, b.contDiff, b.hasCompactSupport, ?_⟩
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
    (b.continuous.pow 2) (hasCompactSupport_sq b.hasCompactSupport) (fun t ↦ sq_nonneg _) ?_
  simp [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]

/-- **The Hardy limit, general weight.** Let `p ∈ ℕ` and `β = (p + 1)/2`. For every `η > 0`
there is a smooth radial profile `ζ`, with compact support in `(0, ∞)`, such that
`∫₀^∞ rᵖ ζ² > 0` and `∫₀^∞ r^{p+2} ζ'² ≤ (β² + η) ∫₀^∞ rᵖ ζ²`.

In `ℝⁿ` (`n ≥ 3`) the separated stability inequality has `p = n - 3` and `β = (n - 2)/2`. -/
theorem exists_radial_profile_pow_ratio_le (p : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ Ioi 0 ∧
      0 < ∫ r in Ioi (0 : ℝ), r ^ p * ζ r ^ 2 ∧
      ∫ r in Ioi (0 : ℝ), r ^ (p + 2) * deriv ζ r ^ 2 ≤
        ((((p : ℝ) + 1) / 2) ^ 2 + η) * ∫ r in Ioi (0 : ℝ), r ^ p * ζ r ^ 2 := by
  set β : ℝ := ((p : ℝ) + 1) / 2 with hβ_def
  have hβ : 2 * β = p + 1 := by rw [hβ_def]; ring
  obtain ⟨ψ, hψ, hψc, hpos⟩ := exists_contDiff_hasCompactSupport_integral_sq_pos
  set A := ∫ t, ψ t ^ 2
  set B := ∫ t, deriv ψ t ^ 2
  have hB : 0 ≤ B := integral_nonneg fun t ↦ sq_nonneg _
  -- choose `k` with `k⁻² B ≤ η A`
  obtain ⟨k, hk1, hk⟩ : ∃ k : ℝ, 1 ≤ k ∧ B ≤ η * A * k ^ 2 := by
    refine ⟨max 1 (B / (η * A)), le_max_left _ _, ?_⟩
    have hηA : 0 < η * A := mul_pos hη hpos
    have h1 : B / (η * A) ≤ max 1 (B / (η * A)) := le_max_right _ _
    have h2 : 1 ≤ max 1 (B / (η * A)) := le_max_left _ _
    have h3 : B ≤ η * A * max 1 (B / (η * A)) := by
      rw [div_le_iff₀ hηA] at h1; linarith
    nlinarith
  have hk0 : 0 < k := one_pos.trans_le hk1
  obtain ⟨h3, h5⟩ := radial_hardy_ratio_pow p hβ hψ hψc hk0
  have hgc := hasCompactSupport_comp_div hψc hk0
  refine ⟨powLogProfile β fun t ↦ ψ (t / k),
    contDiff_powLogProfile β (hψ.comp (contDiff_id.div_const k)) hgc,
    hasCompactSupport_powLogProfile β hgc, tsupport_powLogProfile_subset β hgc, ?_, ?_⟩
  · rw [h3]; exact mul_pos hk0 hpos
  · rw [h3, h5]
    have : (k ^ 2)⁻¹ * B ≤ η * A := by
      rw [inv_mul_le_iff₀ (by positivity)]; linarith
    nlinarith

/-- **The Hardy limit.** For every `η > 0` there is a smooth radial profile `ζ`, with compact
support in `(0, ∞)`, such that `∫₀^∞ r³ ζ² > 0` and `∫₀^∞ r⁵ ζ'² ≤ (4 + η) ∫₀^∞ r³ ζ²`. -/
theorem exists_radial_profile_ratio_le {η : ℝ} (hη : 0 < η) :
    ∃ ζ : ℝ → ℝ, ContDiff ℝ ∞ ζ ∧ HasCompactSupport ζ ∧ tsupport ζ ⊆ Ioi 0 ∧
      0 < ∫ r in Ioi (0 : ℝ), r ^ 3 * ζ r ^ 2 ∧
      ∫ r in Ioi (0 : ℝ), r ^ 5 * deriv ζ r ^ 2 ≤
        (4 + η) * ∫ r in Ioi (0 : ℝ), r ^ 3 * ζ r ^ 2 := by
  have h := exists_radial_profile_pow_ratio_le 3 hη
  norm_num at h
  exact h

end OnePhaseDimension
