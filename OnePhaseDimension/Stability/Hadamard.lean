/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Stability.FluxFunctional
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The Hadamard formula for superlevel sets, in volume form

For `F_s = F + s φ` and densities `K_s`, all compactly supported,

  `∫_{F_{s₁} > 0} K_{s₁} - ∫_{F_{s₀} > 0} K_{s₀}
    = ∫_{s₀}^{s₁} (∫_{F_s > 0} ∂_s K_s + Flux_{F_s > 0}(V_s)) ds`,

where `V_s` is any `C¹` field with `⟨∇F_s, V_s⟩ = φ K_s` on a strip `{0 < F_s < δ}`
(for instance `V_s = K_s φ ∇F_s / |∇F_s|²` near the zero set of `F_s`, cut off away from it).

The proof replaces the indicator of `{F_s > 0}` by the smoothed Heaviside function
`H_ε(F_s) = η(F_s/ε)`, differentiates under the integral sign in `s`, integrates by parts in `x`
using `H_ε'(F_s) φ K_s = ⟨∇(H_ε ∘ F_s), V_s⟩`, and lets `ε → 0` by dominated convergence.

## Main results

* `heaviside`: the smoothed Heaviside function `H_ε(r) = η(r/ε)`.
* `integral_heavisideDeriv_mul_eq`: the integration by parts at fixed `s`.
* `hasDerivAt_integral_heaviside`: the derivative in `s` at fixed `ε`.
* `HadamardHyp`: the hypotheses on `[a, b]`; `superlevelIntegral` (`Λ`) and `hadamardRate`.
* `HadamardHyp.integrated`: `Λ(b) - Λ(a) = ∫_a^b rate`.
* `HadamardHyp.hasDerivAt`: `Λ' = rate` at interior points where the rate is continuous.
* `HadamardHyp.continuousOn`, `HadamardHyp.exists_bound_hadamardRate`,
  `HadamardHyp.intervalIntegrable_hadamardRate`.

## Differences from the source

The 2026-09-24 version computes the change of the energy across the moving boundary in flow
coordinates (a boundary layer with a Jacobian expansion). We use the Hadamard formula above,
proved with a smoothed Heaviside function; boundary terms appear only through the flux
functional `Flux_D(V) = -∫_D div V`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace Function
open scoped ContDiff Gradient NNReal RealInnerProductSpace Interval

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

/-! ### The smoothed Heaviside function -/

/-- The smoothed Heaviside function `H_ε(r) = η(r/ε)`: `0` for `r ≤ ε/2`, `1` for `r ≥ ε`. -/
def heaviside (ε r : ℝ) : ℝ := cutη (r / ε)

/-- The derivative `H_ε'(r) = η'(r/ε)/ε`. -/
def heavisideDeriv (ε r : ℝ) : ℝ := deriv cutη (r / ε) / ε

section Heaviside

variable {ε r : ℝ}

theorem heaviside_of_nonpos (hε : 0 < ε) (hr : r ≤ 0) : heaviside ε r = 0 :=
  cutη_eq_zero ((div_nonpos_of_nonpos_of_nonneg hr hε.le).trans (by norm_num))

theorem heaviside_of_le (hε : 0 < ε) (hr : ε ≤ r) : heaviside ε r = 1 :=
  cutη_eq_one ((one_le_div hε).2 hr)

theorem heaviside_nonneg : 0 ≤ heaviside ε r := cutη_nonneg _

theorem heaviside_le_one : heaviside ε r ≤ 1 := cutη_le_one _

theorem abs_heaviside_le_one : |heaviside ε r| ≤ 1 := by
  rw [abs_of_nonneg heaviside_nonneg]; exact heaviside_le_one

theorem contDiff_heaviside (ε : ℝ) : ContDiff ℝ ∞ (heaviside ε) :=
  contDiff_cutη.comp (contDiff_id.div_const ε)

theorem continuous_heaviside (ε : ℝ) : Continuous (heaviside ε) :=
  (contDiff_heaviside ε).continuous

theorem hasDerivAt_heaviside (ε r : ℝ) : HasDerivAt (heaviside ε) (heavisideDeriv ε r) r := by
  have h1 : HasDerivAt (fun r : ℝ ↦ r / ε) (1 / ε) r := (hasDerivAt_id r).div_const ε
  have h2 : HasDerivAt cutη (deriv cutη (r / ε)) (r / ε) :=
    (contDiff_cutη.differentiable (by simp) _).hasDerivAt
  have h3 : HasDerivAt (cutη ∘ fun r : ℝ ↦ r / ε) (deriv cutη (r / ε) * (1 / ε)) r := h2.comp r h1
  have h4 : deriv cutη (r / ε) * (1 / ε) = heavisideDeriv ε r := by
    simp [heavisideDeriv, div_eq_mul_inv]
  rw [h4] at h3
  exact h3

theorem continuous_heavisideDeriv (ε : ℝ) : Continuous (heavisideDeriv ε) :=
  (continuous_deriv_cutη.comp (continuous_id.div_const ε)).div_const ε

theorem heavisideDeriv_eq_zero (hε : 0 < ε) (hr : r ≤ 0 ∨ ε < r) : heavisideDeriv ε r = 0 := by
  unfold heavisideDeriv
  rw [deriv_cutη_eq_zero, zero_div]
  rcases hr with hr | hr
  · exact Or.inl ((div_nonpos_of_nonpos_of_nonneg hr hε.le).trans_lt (by norm_num))
  · exact Or.inr ((one_lt_div hε).2 hr)

/-- `H_ε(r) → 1_{r > 0}` as `ε ↓ 0`. -/
theorem tendsto_heaviside (r : ℝ) :
    Tendsto (fun ε ↦ heaviside ε r) (𝓝[>] 0) (𝓝 (if 0 < r then 1 else 0)) := by
  split_ifs with hr
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hr] with ε hε
    exact (heaviside_of_le hε.1 hε.2.le).symm
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (heaviside_of_nonpos hε (not_lt.1 hr)).symm

end Heaviside

/-! ### Integration by parts at a fixed parameter -/

/-- A `C¹` compactly supported field has zero total divergence. -/
theorem integral_divergence_eq_zero_of_contDiff {W : E n → E n} (hW : ContDiff ℝ 1 W)
    (hWc : HasCompactSupport W) : ∫ x, divergence W x = 0 := by
  obtain ⟨K, hK⟩ := lipschitzWith_of_locallyLipschitz_of_hasCompactSupport
    (fun x ↦ hW.locallyLipschitz x) hWc
  exact integral_divergence_eq_zero hK hWc

/-- **Integration by parts against `H_ε'(G)`.** If `⟨∇G, V⟩ = φ K` on `{0 < G ≤ ε}`, then
`∫ H_ε'(G) φ K = -∫ H_ε(G) div V`. -/
theorem integral_heavisideDeriv_mul_eq {G φ K : E n → ℝ} {V : E n → E n} {ε : ℝ}
    (hε : 0 < ε) (hG : ContDiff ℝ 1 G) (hV : ContDiff ℝ 1 V) (hVc : HasCompactSupport V)
    (hstrip : ∀ x, 0 < G x → G x ≤ ε → fderiv ℝ G x (V x) = φ x * K x) :
    ∫ x, heavisideDeriv ε (G x) * (φ x * K x) = -∫ x, heaviside ε (G x) * divergence V x := by
  have ha : ContDiff ℝ 1 fun y ↦ heaviside ε (G y) :=
    ((contDiff_heaviside ε).of_le (by exact_mod_cast le_top)).comp hG
  have hW : ContDiff ℝ 1 fun y ↦ heaviside ε (G y) • V y := ha.smul hV
  have hWc : HasCompactSupport fun y ↦ heaviside ε (G y) • V y :=
    hasCompactSupport_smul_right hVc
  have h0 := integral_divergence_eq_zero_of_contDiff hW hWc
  have hderiv : ∀ x, fderiv ℝ (fun y ↦ heaviside ε (G y)) x (V x) =
      heavisideDeriv ε (G x) * (φ x * K x) := by
    intro x
    have hGd := (hG.differentiable one_ne_zero x).hasFDerivAt
    have h := ((hasDerivAt_heaviside ε (G x)).comp_hasFDerivAt x hGd).fderiv
    rw [show (fun y ↦ heaviside ε (G y)) = heaviside ε ∘ G from rfl, h]
    simp only [smul_apply, smul_eq_mul]
    by_cases h : heavisideDeriv ε (G x) = 0
    · rw [h, zero_mul, zero_mul]
    · have hpos : 0 < G x := by
        by_contra hle
        exact h (heavisideDeriv_eq_zero hε (Or.inl (not_lt.1 hle)))
      have hle : G x ≤ ε := by
        by_contra hlt
        exact h (heavisideDeriv_eq_zero hε (Or.inr (not_le.1 hlt)))
      rw [hstrip x hpos hle]
  have hdiv : ∀ x, divergence (fun y ↦ heaviside ε (G y) • V y) x =
      heaviside ε (G x) * divergence V x + heavisideDeriv ε (G x) * (φ x * K x) := by
    intro x
    rw [divergence_smul (ha.differentiable one_ne_zero x) (hV.differentiable one_ne_zero x),
      hderiv]
  have hi1 : Integrable fun x ↦ heaviside ε (G x) * divergence V x :=
    (((continuous_heaviside ε).comp hG.continuous).mul
      (continuous_divergence hV)).integrable_of_hasCompactSupport
      (hasCompactSupport_divergence hVc).mul_left
  have hi2 : Integrable fun x ↦ heavisideDeriv ε (G x) * (φ x * K x) :=
    ((integrable_divergence hW hWc).sub hi1).congr
      (Eventually.of_forall fun x ↦ by rw [Pi.sub_apply, hdiv]; ring)
  have hsum : ∫ x, divergence (fun y ↦ heaviside ε (G y) • V y) x =
      (∫ x, heaviside ε (G x) * divergence V x) +
        ∫ x, heavisideDeriv ε (G x) * (φ x * K x) := by
    simp_rw [hdiv]
    exact integral_add hi1 hi2
  linarith

/-! ### Differentiation in the parameter -/

section Parameter

variable {F φ : E n → ℝ} {K K' : ℝ → E n → ℝ} {M : Set (E n)}

theorem continuous_param (hF : Continuous F) (hφ : Continuous φ) :
    Continuous fun p : ℝ × E n ↦ F p.2 + p.1 * φ p.2 :=
  (hF.comp continuous_snd).add (continuous_fst.mul (hφ.comp continuous_snd))

/-- The `s`-derivative of a density vanishing off `M` vanishes off `M`. -/
theorem deriv_eq_zero_of_notMem (hKd : ∀ s x, HasDerivAt (fun s ↦ K s x) (K' s x) s)
    (hKM : ∀ s, ∀ x ∉ M, K s x = 0) (s : ℝ) {x : E n} (hx : x ∉ M) : K' s x = 0 := by
  refine (hKd s x).unique ?_
  have : (fun s ↦ K s x) = fun _ ↦ (0 : ℝ) := funext fun s ↦ hKM s x hx
  rw [this]
  exact hasDerivAt_const s 0

/-- **Differentiation under the integral sign at fixed `ε`.** -/
theorem hasDerivAt_integral_heaviside (hF : Continuous F) (hφ : Continuous φ) (hM : IsCompact M)
    (hK : Continuous (uncurry K)) (hK' : Continuous (uncurry K'))
    (hKd : ∀ s x, HasDerivAt (fun s ↦ K s x) (K' s x) s) (hKM : ∀ s, ∀ x ∉ M, K s x = 0)
    (ε s : ℝ) :
    HasDerivAt (fun s ↦ ∫ x, heaviside ε (F x + s * φ x) * K s x)
      (∫ x, (heavisideDeriv ε (F x + s * φ x) * (φ x * K s x) +
        heaviside ε (F x + s * φ x) * K' s x)) s := by
  set f : ℝ → E n → ℝ := fun s x ↦ heaviside ε (F x + s * φ x) * K s x with hf_def
  set f' : ℝ → E n → ℝ := fun s x ↦ heavisideDeriv ε (F x + s * φ x) * (φ x * K s x) +
    heaviside ε (F x + s * φ x) * K' s x with hf'_def
  have hG := continuous_param hF hφ
  have hfc : Continuous (uncurry f) := ((continuous_heaviside ε).comp hG).mul hK
  have hf'c : Continuous (uncurry f') :=
    (((continuous_heavisideDeriv ε).comp hG).mul ((hφ.comp continuous_snd).mul hK)).add
      (((continuous_heaviside ε).comp hG).mul hK')
  have hfM : ∀ s, ∀ x ∉ M, f s x = 0 := fun s x hx ↦ by simp [hf_def, hKM s x hx]
  have hf'M : ∀ s, ∀ x ∉ M, f' s x = 0 := fun s x hx ↦ by
    simp [hf'_def, hKM s x hx, deriv_eq_zero_of_notMem hKd hKM s hx]
  have e1 : (fun s ↦ ∫ x, f s x) = fun s ↦ ∫ x in M, f s x :=
    funext fun s ↦ (setIntegral_eq_integral_of_forall_compl_eq_zero (hfM s)).symm
  have e2 : ∫ x, f' s x = ∫ x in M, f' s x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hf'M s)).symm
  change HasDerivAt (fun s ↦ ∫ x, f s x) (∫ x, f' s x) s
  rw [e1, e2]
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s 1).prod hM).exists_bound_of_continuousOn
    hf'c.continuousOn
  have hcx : ∀ s, Continuous (f s) := fun s ↦ hfc.comp (continuous_const.prodMk continuous_id)
  have hcx' : ∀ s, Continuous (f' s) := fun s ↦ hf'c.comp (continuous_const.prodMk continuous_id)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict M)
    (F := f) (F' := f') (bound := fun _ ↦ C) (ball_mem_nhds s one_pos)
    (Eventually.of_forall fun s ↦ (hcx s).aestronglyMeasurable)
    ((hcx s).continuousOn.integrableOn_compact hM) (hcx' s).aestronglyMeasurable ?_
    (integrableOn_const hM.measure_lt_top.ne) ?_).2
  · refine (ae_restrict_iff' hM.measurableSet).2 (Eventually.of_forall fun x hx s' hs' ↦ ?_)
    exact hC (s', x) ⟨ball_subset_closedBall hs', hx⟩
  · refine Eventually.of_forall fun x s' _ ↦ ?_
    have hG' : HasDerivAt (fun s ↦ F x + s * φ x) (φ x) s' := by
      simpa using ((hasDerivAt_id s').mul_const (φ x)).const_add (F x)
    have := ((hasDerivAt_heaviside ε _).comp s' hG').mul (hKd s' x)
    exact this.congr_deriv (by simp only [hf'_def, Function.comp_apply]; ring)

end Parameter

/-! ### The integrated Hadamard formula -/

section Integrated

variable {F φ : E n → ℝ} {K K' : ℝ → E n → ℝ} {M : Set (E n)}

theorem integrable_of_eq_zero_off {f : E n → ℝ} (hf : Continuous f) (hM : IsCompact M)
    (h : ∀ x ∉ M, f x = 0) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hM h)

theorem continuous_integral_of_eq_zero_off {f : ℝ → E n → ℝ} (hf : Continuous (uncurry f))
    (hM : IsCompact M) (h : ∀ s, ∀ x ∉ M, f s x = 0) : Continuous fun s ↦ ∫ x, f s x := by
  have e : (fun s ↦ ∫ x, f s x) = fun s ↦ ∫ x in M, f s x :=
    funext fun s ↦ (setIntegral_eq_integral_of_forall_compl_eq_zero (h s)).symm
  rw [e]
  exact continuous_parametric_integral_of_continuous hf hM

/-- `∫ H_ε(G) f → ∫_{G > 0} f` as `ε ↓ 0`. -/
theorem tendsto_integral_heaviside_mul {G f : E n → ℝ} (hG : Continuous G) (hf : Integrable f) :
    Tendsto (fun ε ↦ ∫ x, heaviside ε (G x) * f x) (𝓝[>] 0)
      (𝓝 (∫ x in {x | 0 < G x}, f x)) := by
  have hmeas : MeasurableSet {x | 0 < G x} := (isOpen_lt continuous_const hG).measurableSet
  rw [← integral_indicator hmeas]
  refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖) ?_ ?_ hf.norm ?_
  · exact Eventually.of_forall fun ε ↦
      (((continuous_heaviside ε).comp hG).aestronglyMeasurable).mul hf.aestronglyMeasurable
  · refine Eventually.of_forall fun ε ↦ Eventually.of_forall fun x ↦ ?_
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (by
      rw [Real.norm_eq_abs]; exact abs_heaviside_le_one)
  · refine Eventually.of_forall fun x ↦ ?_
    have h := (tendsto_heaviside (G x)).mul_const (f x)
    by_cases hx : 0 < G x
    · simpa [hx, indicator_of_mem (show x ∈ {x | 0 < G x} from hx)] using h
    · simpa [hx, indicator_of_notMem (show x ∉ {x | 0 < G x} from hx)] using h

/-- The superlevel integral `Λ(s) = ∫_{F + s φ > 0} K_s`. -/
def superlevelIntegral (F φ : E n → ℝ) (K : ℝ → E n → ℝ) (s : ℝ) : ℝ :=
  ∫ x in {x | 0 < F x + s * φ x}, K s x

/-- The Hadamard rate `∫_{F + s φ > 0} K'_s + Flux_{F + s φ > 0}(V_s)`. -/
def hadamardRate (F φ : E n → ℝ) (K' : ℝ → E n → ℝ) (V : ℝ → E n → E n) (s : ℝ) : ℝ :=
  (∫ x in {x | 0 < F x + s * φ x}, K' s x) + fluxFunctional {x | 0 < F x + s * φ x} (V s)

/-- The hypotheses of the Hadamard formula on `[a, b]`: `F_s = F + s φ` with `F, φ` of class
`C¹`; densities `K_s` vanishing off the compact set `M`, jointly continuous with jointly
continuous `s`-derivative `K'_s`; and, for `s ∈ [a, b]`, `C¹` fields `V_s` supported in `M`
with uniformly bounded divergence and `⟨∇F_s, V_s⟩ = φ K_s` on the strip `{0 < F_s < δ}`. -/
structure HadamardHyp (F φ : E n → ℝ) (K K' : ℝ → E n → ℝ) (V : ℝ → E n → E n)
    (M : Set (E n)) (a b δ : ℝ) : Prop where
  contDiff_F : ContDiff ℝ 1 F
  contDiff_φ : ContDiff ℝ 1 φ
  isCompact : IsCompact M
  continuous_K : Continuous (uncurry K)
  continuous_K' : Continuous (uncurry K')
  hasDerivAt_K : ∀ s x, HasDerivAt (fun s ↦ K s x) (K' s x) s
  K_eq_zero : ∀ s, ∀ x ∉ M, K s x = 0
  le : a ≤ b
  pos : 0 < δ
  contDiff_V : ∀ s ∈ Icc a b, ContDiff ℝ 1 (V s)
  tsupport_V : ∀ s ∈ Icc a b, tsupport (V s) ⊆ M
  bdd_divergence : ∃ B, ∀ s ∈ Icc a b, ∀ x, |divergence (V s) x| ≤ B
  strip : ∀ s ∈ Icc a b, ∀ x, 0 < F x + s * φ x → F x + s * φ x < δ →
    fderiv ℝ (fun y ↦ F y + s * φ y) x (V s x) = φ x * K s x

namespace HadamardHyp

variable {V : ℝ → E n → E n} {a b δ : ℝ}

/-- The hypotheses restrict to subintervals. -/
theorem mono (h : HadamardHyp F φ K K' V M a b δ) {a' b' : ℝ} (hab : a' ≤ b') (ha : a ≤ a')
    (hb : b' ≤ b) : HadamardHyp F φ K K' V M a' b' δ := by
  have hsub : Icc a' b' ⊆ Icc a b := Icc_subset_Icc ha hb
  obtain ⟨B, hB⟩ := h.bdd_divergence
  exact ⟨h.contDiff_F, h.contDiff_φ, h.isCompact, h.continuous_K, h.continuous_K',
    h.hasDerivAt_K, h.K_eq_zero, hab, h.pos, fun s hs ↦ h.contDiff_V s (hsub hs),
    fun s hs ↦ h.tsupport_V s (hsub hs), ⟨B, fun s hs ↦ hB s (hsub hs)⟩,
    fun s hs ↦ h.strip s (hsub hs)⟩

/-- The regularized rate `∫ (H_ε'(F_s) φ K_s + H_ε(F_s) K'_s)`. -/
def regRate (F φ : E n → ℝ) (K K' : ℝ → E n → ℝ) (ε s : ℝ) : ℝ :=
  ∫ x, (heavisideDeriv ε (F x + s * φ x) * (φ x * K s x) +
    heaviside ε (F x + s * φ x) * K' s x)

/-- The key facts at fixed `ε`: the regularized rate is continuous in `s`, it is the derivative
of `∫ H_ε(F_s) K_s`, it converges to the Hadamard rate on `[a, b]`, and it is bounded there. -/
theorem regRate_facts (h : HadamardHyp F φ K K' V M a b δ) :
    (∀ ε, Continuous (regRate F φ K K' ε)) ∧
    (∀ ε s, HasDerivAt (fun s ↦ ∫ x, heaviside ε (F x + s * φ x) * K s x)
      (regRate F φ K K' ε s) s) ∧
    (∀ s ∈ Icc a b, Tendsto (fun ε ↦ regRate F φ K K' ε s) (𝓝[>] 0)
      (𝓝 (hadamardRate F φ K' V s))) ∧
    ∃ C, ∀ᶠ ε in 𝓝[>] 0, ∀ s ∈ Icc a b, ‖regRate F φ K K' ε s‖ ≤ C := by
  obtain ⟨B, hB⟩ := h.bdd_divergence
  have hM := h.isCompact
  have hFc := h.contDiff_F.continuous
  have hφc := h.contDiff_φ.continuous
  have hG : Continuous fun p : ℝ × E n ↦ F p.2 + p.1 * φ p.2 := continuous_param hFc hφc
  have hGs : ∀ s, ContDiff ℝ 1 fun y ↦ F y + s * φ y := fun s ↦
    h.contDiff_F.add (contDiff_const.mul h.contDiff_φ)
  have hK'M := deriv_eq_zero_of_notMem h.hasDerivAt_K h.K_eq_zero
  have hKs : ∀ s, Continuous (K s) := fun s ↦
    h.continuous_K.comp (continuous_const.prodMk continuous_id)
  have hK's : ∀ s, Continuous (K' s) := fun s ↦
    h.continuous_K'.comp (continuous_const.prodMk continuous_id)
  have hVc : ∀ s ∈ Icc a b, HasCompactSupport (V s) := fun s hs ↦
    hM.of_isClosed_subset (isClosed_tsupport _) (h.tsupport_V s hs)
  have hdivM : ∀ s ∈ Icc a b, ∀ x ∉ M, divergence (V s) x = 0 := fun s hs x hx ↦
    divergence_of_notMem_tsupport fun h' ↦ hx (h.tsupport_V s hs h')
  set Bε : ℝ → ℝ → ℝ := fun ε s ↦
    ∫ x, heaviside ε (F x + s * φ x) * (K' s x - divergence (V s) x) with hB_def
  -- integration by parts: `regRate ε = Bε ε` on `[a, b]` for small `ε`
  have hAB : ∀ ε, 0 < ε → ε < δ → ∀ s ∈ Icc a b, regRate F φ K K' ε s = Bε ε s := by
    intro ε hε hεδ s hs
    have hibp := integral_heavisideDeriv_mul_eq (G := fun y ↦ F y + s * φ y) (φ := φ)
      (K := K s) hε (hGs s) (h.contDiff_V s hs) (hVc s hs)
      (fun x h0 h1 ↦ h.strip s hs x h0 (h1.trans_lt hεδ))
    have hc1 : Continuous fun x ↦ heavisideDeriv ε (F x + s * φ x) * (φ x * K s x) :=
      ((continuous_heavisideDeriv ε).comp ((hGs s).continuous)).mul (hφc.mul (hKs s))
    have hc2 : Continuous fun x ↦ heaviside ε (F x + s * φ x) * K' s x :=
      ((continuous_heaviside ε).comp ((hGs s).continuous)).mul (hK's s)
    have hc3 : Continuous fun x ↦ heaviside ε (F x + s * φ x) * divergence (V s) x :=
      ((continuous_heaviside ε).comp ((hGs s).continuous)).mul
        (continuous_divergence (h.contDiff_V s hs))
    have hi1 := integrable_of_eq_zero_off hc1 hM fun x hx ↦ by simp [h.K_eq_zero s x hx]
    have hi2 := integrable_of_eq_zero_off hc2 hM fun x hx ↦ by simp [hK'M s hx]
    have hi3 := integrable_of_eq_zero_off hc3 hM fun x hx ↦ by simp [hdivM s hs x hx]
    simp only [regRate, hB_def, mul_sub]
    rw [integral_add hi1 hi2, integral_sub hi2 hi3, hibp]
    ring
  refine ⟨fun ε ↦ ?_, fun ε s ↦ hasDerivAt_integral_heaviside hFc hφc hM h.continuous_K
    h.continuous_K' h.hasDerivAt_K h.K_eq_zero ε s, fun s hs ↦ ?_, ?_⟩
  · refine continuous_integral_of_eq_zero_off (M := M) ?_ hM fun s x hx ↦ ?_
    · exact (((continuous_heavisideDeriv ε).comp hG).mul
        ((hφc.comp continuous_snd).mul h.continuous_K)).add
        (((continuous_heaviside ε).comp hG).mul h.continuous_K')
    · simp [h.K_eq_zero s x hx, hK'M s hx]
  · have hlim := tendsto_integral_heaviside_mul ((hGs s).continuous)
      ((integrable_of_eq_zero_off (hK's s) hM fun x hx ↦ hK'M s hx).sub
        (integrable_divergence (h.contDiff_V s hs) (hVc s hs)))
    have hval : (∫ x in {x | 0 < F x + s * φ x}, (K' s x - divergence (V s) x)) =
        hadamardRate F φ K' V s := by
      simp only [hadamardRate, fluxFunctional]
      rw [integral_sub (integrable_of_eq_zero_off (hK's s) hM fun x hx ↦ hK'M s hx).integrableOn
        (integrable_divergence (h.contDiff_V s hs) (hVc s hs)).integrableOn]
      ring
    rw [← hval]
    refine hlim.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT h.pos] with ε hε
    exact (hAB ε hε.1 hε.2 s hs).symm
  · obtain ⟨CK, hCK⟩ := (isCompact_Icc.prod hM).exists_bound_of_continuousOn
      (s := Icc a b ×ˢ M) h.continuous_K'.continuousOn
    refine ⟨(CK + B) * (volume M).toReal, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT h.pos] with ε hε
    intro s hs
    rw [hAB ε hε.1 hε.2 s hs]
    have hg : Integrable (M.indicator fun _ ↦ CK + B) :=
      (integrableOn_const hM.measure_lt_top.ne).integrable_indicator hM.measurableSet
    calc ‖Bε ε s‖ ≤ ∫ x, M.indicator (fun _ ↦ CK + B) x := by
          refine norm_integral_le_of_norm_le hg (Eventually.of_forall fun x ↦ ?_)
          by_cases hx : x ∈ M
          · rw [indicator_of_mem hx, norm_mul]
            have h1 : ‖heaviside ε (F x + s * φ x)‖ ≤ 1 := by
              rw [Real.norm_eq_abs]; exact abs_heaviside_le_one
            have h2 : ‖K' s x - divergence (V s) x‖ ≤ CK + B := by
              refine (norm_sub_le _ _).trans (add_le_add (hCK (s, x) ⟨hs, hx⟩) ?_)
              rw [Real.norm_eq_abs]; exact hB s hs x
            calc ‖heaviside ε (F x + s * φ x)‖ * ‖K' s x - divergence (V s) x‖
                ≤ 1 * (CK + B) := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
              _ = CK + B := one_mul _
          · rw [indicator_of_notMem hx, hK'M s hx, hdivM s hs x hx]
            simp
      _ = (CK + B) * (volume M).toReal := by
          rw [integral_indicator_const _ hM.measurableSet, smul_eq_mul, Measure.real, mul_comm]

/-- The Hadamard rate is bounded on `[a, b]`. -/
theorem exists_bound_hadamardRate (h : HadamardHyp F φ K K' V M a b δ) :
    ∃ C, ∀ s ∈ Icc a b, ‖hadamardRate F φ K' V s‖ ≤ C := by
  obtain ⟨-, -, hlim, C, hC⟩ := h.regRate_facts
  exact ⟨C, fun s hs ↦ le_of_tendsto (hlim s hs).norm (hC.mono fun ε hε ↦ hε s hs)⟩

/-- The Hadamard rate is a.e.-strongly measurable on `[a, b]`. -/
theorem aestronglyMeasurable_hadamardRate (h : HadamardHyp F φ K K' V M a b δ) :
    AEStronglyMeasurable (hadamardRate F φ K' V) (volume.restrict (Icc a b)) := by
  obtain ⟨hcont, -, hlim, -⟩ := h.regRate_facts
  exact aestronglyMeasurable_of_tendsto_ae (𝓝[>] (0 : ℝ))
    (fun ε ↦ (hcont ε).aestronglyMeasurable)
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hlim))

theorem intervalIntegrable_hadamardRate (h : HadamardHyp F φ K K' V M a b δ) :
    IntervalIntegrable (hadamardRate F φ K' V) volume a b := by
  obtain ⟨C, hC⟩ := h.exists_bound_hadamardRate
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le h.le]
  exact IntegrableOn.of_bound measure_Icc_lt_top h.aestronglyMeasurable_hadamardRate C
    ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hC))

/-- **The integrated Hadamard formula.**
`Λ(b) - Λ(a) = ∫_a^b (∫_{F_s > 0} K'_s + Flux_{F_s > 0}(V_s)) ds`, with
`Λ(s) = ∫_{F_s > 0} K_s` and `F_s = F + s φ`. -/
theorem integrated (h : HadamardHyp F φ K K' V M a b δ) :
    superlevelIntegral F φ K b - superlevelIntegral F φ K a =
      ∫ s in a..b, hadamardRate F φ K' V s := by
  obtain ⟨hcont, hderiv, hlim, C, hC⟩ := h.regRate_facts
  have hM := h.isCompact
  have hGs : ∀ s, Continuous fun y ↦ F y + s * φ y := fun s ↦
    (h.contDiff_F.add (contDiff_const.mul h.contDiff_φ)).continuous
  have hKs : ∀ s, Continuous (K s) := fun s ↦
    h.continuous_K.comp (continuous_const.prodMk continuous_id)
  set I : ℝ → ℝ → ℝ := fun ε s ↦ ∫ x, heaviside ε (F x + s * φ x) * K s x with hI_def
  have hFTC : ∀ ε, ∫ s in a..b, regRate F φ K K' ε s = I ε b - I ε a := fun ε ↦
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hderiv ε s)
      ((hcont ε).intervalIntegrable _ _)
  have hIlim : ∀ s, Tendsto (fun ε ↦ I ε s) (𝓝[>] 0) (𝓝 (superlevelIntegral F φ K s)) :=
    fun s ↦ tendsto_integral_heaviside_mul (hGs s)
      (integrable_of_eq_zero_off (hKs s) hM (h.K_eq_zero s))
  have hIoc : ∀ s ∈ Ι a b, s ∈ Icc a b := fun s hs ↦ by
    rw [uIoc_of_le h.le] at hs
    exact Ioc_subset_Icc_self hs
  have hRlim : Tendsto (fun ε ↦ ∫ s in a..b, regRate F φ K K' ε s) (𝓝[>] 0)
      (𝓝 (∫ s in a..b, hadamardRate F φ K' V s)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ C)
      (Eventually.of_forall fun ε ↦ (hcont ε).aestronglyMeasurable) ?_ intervalIntegrable_const
      (Eventually.of_forall fun s hs ↦ hlim s (hIoc s hs))
    exact hC.mono fun ε hε ↦ Eventually.of_forall fun s hs ↦ hε s (hIoc s hs)
  have hlim2 : Tendsto (fun ε ↦ I ε b - I ε a) (𝓝[>] 0)
      (𝓝 (∫ s in a..b, hadamardRate F φ K' V s)) := by
    refine hRlim.congr fun ε ↦ ?_
    exact hFTC ε
  exact tendsto_nhds_unique ((hIlim b).sub (hIlim a)) hlim2

/-- **The Hadamard derivative.** If the Hadamard rate is continuous at an interior point `s` of
`[a, b]`, then `Λ'(s)` is the Hadamard rate at `s`. -/
theorem hasDerivAt (h : HadamardHyp F φ K K' V M a b δ) {s : ℝ} (hs : s ∈ Ioo a b)
    (hcont : ContinuousAt (hadamardRate F φ K' V) s) :
    HasDerivAt (superlevelIntegral F φ K) (hadamardRate F φ K' V s) s := by
  have hint := (h.mono hs.1.le le_rfl hs.2.le).intervalIntegrable_hadamardRate
  have hmeas : StronglyMeasurableAtFilter (hadamardRate F φ K' V) (𝓝 s) :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem h.aestronglyMeasurable_hadamardRate
      (Icc_mem_nhds hs.1 hs.2)
  have hd := (intervalIntegral.integral_hasDerivAt_right hint hmeas hcont).const_add
    (superlevelIntegral F φ K a)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
  have := (h.mono ht.1.le le_rfl ht.2.le).integrated
  linarith

/-- `Λ(s) = ∫_{F_s > 0} K_s` is continuous on `[a, b]`. -/
theorem continuousOn (h : HadamardHyp F φ K K' V M a b δ) :
    ContinuousOn (superlevelIntegral F φ K) (Icc a b) := by
  have heq : EqOn (fun t ↦ superlevelIntegral F φ K a + ∫ s in a..t, hadamardRate F φ K' V s)
      (superlevelIntegral F φ K) (Icc a b) := fun t ht ↦ by
    have := (h.mono ht.1 le_rfl ht.2).integrated
    simp only
    linarith
  have hprim := intervalIntegral.continuousOn_primitive_interval'
    h.intervalIntegrable_hadamardRate (left_mem_uIcc (a := a) (b := b))
  rw [uIcc_of_le h.le] at hprim
  exact (continuousOn_const.add hprim).congr fun t ht ↦ (heq ht).symm

end HadamardHyp

end Integrated

end OnePhaseDimension
