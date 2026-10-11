/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Statements.Stability
public import EllipticBernoulli.Classical.InnerVariationCalculus
public import EllipticBernoulli.Sobolev.Cutoff
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The flux functional

For an open set `D` with a `C¹` defining function near the support of a `C¹` compactly supported
vector field `Q`, the flux functional `Flux_D(Q) = -∫_D div Q` replaces the boundary integral
`∫_{∂D} ⟨Q, N⟩ dσ` (with `N` the inward unit normal). No surface measure is used.

## Main results

* `HasBoundaryCharts k D u S`: near each point of `closure D ∩ S`, `u = max F 0` with `F` of class
  `C^k`, `D = {F > 0}`, and `∇F ≠ 0` on `{F = 0}`.
* `integral_strip_eq`: for `t > 0`,
  `t⁻¹ ∫_{D ∩ {u < t}} ⟨Q, ∇u⟩ = -∫ min(u/t, 1) 1_D div Q`. This is `∫ div (ψ_t Q) = 0` for the
  Lipschitz compactly supported field `ψ_t Q`, `ψ_t = 1_D min(u/t, 1)`.
* `tendsto_integral_strip`: `t⁻¹ ∫_{D ∩ {u < t}} ⟨Q, ∇u⟩ → Flux_D(Q)` as `t ↓ 0`.
* `fluxFunctional_add`, `fluxFunctional_smul`, `fluxFunctional_neg`, `fluxFunctional_sub`:
  linearity.
* `exists_measure_strip_le`: `|D ∩ {u < t} ∩ K| ≤ C t` for compact `K` (charts of class `C²`).
* `fluxFunctional_nonneg`: if `⟨Q, ∇F⟩ ≥ 0` on the boundary of `D` in every defining chart, then
  `Flux_D(Q) ≥ 0`.
* `fluxFunctional_congr_boundary`: the flux depends only on the normal component of `Q` on the
  boundary.
* `ConeData.tendsto_integral_strip`, `ConeData.fluxFunctional_nonneg`,
  `ConeData.fluxFunctional_congr_boundary`: the same for a cone component, for fields supported
  away from the singular set.

## Differences from the source

The 2026-09-24 version integrates by parts over the boundary of the link with the surface
measure. We use the volume-only functional `Flux_D(Q) = -∫_D div Q` and its strip
representation; boundary values enter only through limits of volume integrals over the strips
`D ∩ {u < t}`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Gradient NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

/-! ### Defining charts -/

/-- `(U, F)` is a defining chart of class `C^k` for `D` and `u`: `U` is open, `F` is `C^k` on
`U`, `u = max F 0` and `D = {F > 0}` on `U`, and `∇F ≠ 0` on `{F = 0} ∩ U`. -/
structure IsBoundaryChart (k : WithTop ℕ∞) (D : Set (E n)) (u : E n → ℝ) (U : Set (E n))
    (F : E n → ℝ) : Prop where
  isOpen : IsOpen U
  contDiffOn : ContDiffOn ℝ k F U
  eq_max : ∀ x ∈ U, u x = max (F x) 0
  mem_iff : ∀ x ∈ U, x ∈ D ↔ 0 < F x
  gradient_ne_zero : ∀ x ∈ U, F x = 0 → ∇ F x ≠ 0

/-- `D` has defining charts of class `C^k` at every point of `closure D ∩ S`. -/
def HasBoundaryCharts (k : WithTop ℕ∞) (D : Set (E n)) (u : E n → ℝ) (S : Set (E n)) : Prop :=
  ∀ x₀ ∈ closure D ∩ S, ∃ U F, x₀ ∈ U ∧ IsBoundaryChart k D u U F

namespace IsBoundaryChart

variable {k : WithTop ℕ∞} {D : Set (E n)} {u : E n → ℝ} {U : Set (E n)} {F : E n → ℝ}

theorem of_le {k' : WithTop ℕ∞} (h : IsBoundaryChart k D u U F) (hk : k' ≤ k) :
    IsBoundaryChart k' D u U F :=
  ⟨h.isOpen, h.contDiffOn.of_le hk, h.eq_max, h.mem_iff, h.gradient_ne_zero⟩

/-- A chart at one point is a chart at every point of its domain. -/
theorem hasBoundaryCharts (h : IsBoundaryChart k D u U F) : HasBoundaryCharts k D u U :=
  fun _ hx ↦ ⟨U, F, hx.2, h⟩

theorem continuousAt (h : IsBoundaryChart k D u U F) {x : E n} (hx : x ∈ U) :
    ContinuousAt F x :=
  h.contDiffOn.continuousOn.continuousAt (h.isOpen.mem_nhds hx)

theorem nonneg_of_mem_closure (h : IsBoundaryChart k D u U F) {x : E n} (hxU : x ∈ U)
    (hxD : x ∈ closure D) : 0 ≤ F x := by
  by_contra hneg
  push Not at hneg
  have hopen : IsOpen (U ∩ F ⁻¹' Iio 0) :=
    h.contDiffOn.continuousOn.isOpen_inter_preimage h.isOpen isOpen_Iio
  obtain ⟨y, ⟨hyU, hy⟩, hyD⟩ := mem_closure_iff.1 hxD _ hopen ⟨hxU, hneg⟩
  exact absurd ((h.mem_iff y hyU).1 hyD) (not_lt.2 (le_of_lt hy))

/-- `u = F` near a point of `D ∩ U`. -/
theorem eventuallyEq_of_mem (h : IsBoundaryChart k D u U F) {x : E n} (hxU : x ∈ U)
    (hxD : x ∈ D) : u =ᶠ[𝓝 x] F := by
  have hopen : IsOpen (U ∩ F ⁻¹' Ioi 0) :=
    h.contDiffOn.continuousOn.isOpen_inter_preimage h.isOpen isOpen_Ioi
  filter_upwards [hopen.mem_nhds ⟨hxU, (h.mem_iff x hxU).1 hxD⟩] with y hy
  rw [h.eq_max y hy.1, max_eq_left (le_of_lt hy.2)]

end IsBoundaryChart

theorem HasBoundaryCharts.mono {k k' : WithTop ℕ∞} {D : Set (E n)} {u : E n → ℝ}
    {S S' : Set (E n)} (h : HasBoundaryCharts k D u S) (hk : k' ≤ k) (hS : S' ⊆ S) :
    HasBoundaryCharts k' D u S' := fun x hx ↦ by
  obtain ⟨U, F, hxU, hF⟩ := h x ⟨hx.1, hS hx.2⟩
  exact ⟨U, F, hxU, hF.of_le hk⟩

/-- The cones of `ConeData` have smooth defining charts away from the singular set. -/
theorem ConeData.hasBoundaryCharts (C : ConeData n) :
    HasBoundaryCharts ∞ C.D C.u C.Singᶜ := by
  intro x₀ hx₀
  obtain ⟨U, hU, hx₀U, F, hF, hu, hD, hgrad, -⟩ := C.chart x₀ ⟨hx₀.1, hx₀.2⟩
  refine ⟨U, F, hx₀U, hU, hF, hu, fun x hx ↦ ⟨fun hxD ↦ ?_, hD x hx⟩,
    fun x hx hF0 h0 ↦ by simpa [h0] using hgrad x hx hF0⟩
  have hpos : 0 < C.u x := by
    have hsub : C.D ⊆ {x | 0 < C.u x} := by rw [C.D_eq]; exact connectedComponentIn_subset _ _
    exact hsub hxD
  rw [hu x hx] at hpos
  by_contra hle
  exact (lt_irrefl _) (hpos.trans_le (max_le (not_lt.1 hle) le_rfl))

theorem ConeData.isOpen_D (C : ConeData n) : IsOpen C.D := by
  rw [C.D_eq]
  exact (isOpen_lt continuous_const C.continuous).connectedComponentIn

/-! ### The divergence -/

/-- The trace on `E n →L[ℝ] E n`, as a continuous linear functional. -/
def traceCLM : (E n →L[ℝ] E n) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℝ (E n)).comp (ContinuousLinearMap.coeLM ℝ))

theorem divergence_eq_traceCLM (Q : E n → E n) (x : E n) :
    divergence Q x = traceCLM (fderiv ℝ Q x) := rfl

theorem continuous_divergence {Q : E n → E n} (hQ : ContDiff ℝ 1 Q) :
    Continuous (divergence Q) :=
  traceCLM.continuous.comp (hQ.continuous_fderiv one_ne_zero)

theorem divergence_of_notMem_tsupport {Q : E n → E n} {x : E n} (hx : x ∉ tsupport Q) :
    divergence Q x = 0 := by
  rw [divergence_eq_traceCLM, fderiv_of_notMem_tsupport ℝ hx, map_zero]

theorem hasCompactSupport_divergence {Q : E n → E n} (hQ : HasCompactSupport Q) :
    HasCompactSupport (divergence Q) :=
  hQ.fderiv (𝕜 := ℝ) |>.comp_left (g := traceCLM) (map_zero _)

theorem integrable_divergence {Q : E n → E n} (hQ : ContDiff ℝ 1 Q) (hQc : HasCompactSupport Q) :
    Integrable (divergence Q) :=
  (continuous_divergence hQ).integrable_of_hasCompactSupport (hasCompactSupport_divergence hQc)

/-- The divergence of a Lipschitz compactly supported field is integrable. -/
theorem integrable_divergence_of_lipschitzWith {W : E n → E n} {K : ℝ≥0}
    (hW : LipschitzWith K W) (hWc : HasCompactSupport W) : Integrable (divergence W) := by
  have hmeas : Measurable (divergence W) :=
    traceCLM.continuous.measurable.comp (measurable_fderiv ℝ W)
  have hon : IntegrableOn (divergence W) (tsupport W) :=
    Measure.integrableOn_of_bounded (M := ‖(traceCLM : (E n →L[ℝ] E n) →L[ℝ] ℝ)‖ * K)
      hWc.isCompact.measure_lt_top.ne hmeas.aestronglyMeasurable
      (Eventually.of_forall fun x ↦ by
        rw [divergence_eq_traceCLM]
        exact (traceCLM.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hW) (norm_nonneg _)))
  exact integrableOn_univ.1 (hon.of_forall_sdiff_eq_zero MeasurableSet.univ fun x hx ↦
    divergence_of_notMem_tsupport hx.2)

/-! ### Linearity -/

theorem divergence_add {Q₁ Q₂ : E n → E n} {x : E n} (h₁ : DifferentiableAt ℝ Q₁ x)
    (h₂ : DifferentiableAt ℝ Q₂ x) :
    divergence (Q₁ + Q₂) x = divergence Q₁ x + divergence Q₂ x := by
  rw [divergence_eq_traceCLM, fderiv_add h₁ h₂, map_add]; rfl

theorem divergence_const_smul {Q : E n → E n} {x : E n} (h : DifferentiableAt ℝ Q x) (c : ℝ) :
    divergence (c • Q) x = c * divergence Q x := by
  rw [divergence_eq_traceCLM, fderiv_const_smul h, map_smul, smul_eq_mul]; rfl

/-! ### The strip cut-off `ψ_t = 1_D min(u/t, 1)` -/

/-- The cut-off `ψ_t = 1_D · min(u/t, 1)`: it vanishes off `D`, equals `u/t` on the strip
`D ∩ {u < t}` and `1` on `D ∩ {u ≥ t}`. -/
def stripCut (D : Set (E n)) (u : E n → ℝ) (t : ℝ) : E n → ℝ :=
  D.indicator fun x ↦ min (u x / t) 1

section StripCut

variable {D : Set (E n)} {u : E n → ℝ} {t : ℝ}

theorem stripCut_le_one (x : E n) : stripCut D u t x ≤ 1 := by
  unfold stripCut
  by_cases hx : x ∈ D
  · rw [indicator_of_mem hx]; exact min_le_right _ _
  · rw [indicator_of_notMem hx]; exact zero_le_one

theorem stripCut_of_notMem {x : E n} (hx : x ∉ D) : stripCut D u t x = 0 :=
  indicator_of_notMem hx _

theorem stripCut_of_mem {x : E n} (hx : x ∈ D) : stripCut D u t x = min (u x / t) 1 :=
  indicator_of_mem hx _

/-- `r ↦ min(max r 0 / t, 1)` is Lipschitz. -/
theorem lipschitzWith_clamp (t : ℝ) :
    ∃ K, LipschitzWith K fun r : ℝ ↦ min (max r 0 / t) 1 := by
  have h := ((lipschitzWith_smul (t⁻¹ : ℝ)).comp (LipschitzWith.id.max_const (0 : ℝ))).min_const
    (1 : ℝ)
  refine ⟨‖t⁻¹‖₊ * 1, ?_⟩
  convert h using 1
  funext r
  simp [div_eq_inv_mul, smul_eq_mul]

theorem lipschitzOnWith_of_eqOn {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {K : ℝ≥0} {f g : α → β} {s : Set α} (hf : LipschitzOnWith K f s) (h : EqOn f g s) :
    LipschitzOnWith K g s := fun x hx y hy ↦ by
  rw [← h hx, ← h hy]; exact hf hx hy

theorem IsBoundaryChart.stripCut_eq {k : WithTop ℕ∞} {U : Set (E n)} {F : E n → ℝ}
    (h : IsBoundaryChart k D u U F) {x : E n} (hx : x ∈ U) :
    stripCut D u t x = min (max (F x) 0 / t) 1 := by
  by_cases hxD : x ∈ D
  · rw [stripCut_of_mem hxD, h.eq_max x hx]
  · rw [stripCut_of_notMem hxD, max_eq_right (not_lt.1 fun hF ↦ hxD ((h.mem_iff x hx).2 hF)),
      zero_div, min_eq_left zero_le_one]

/-- Near every point of `S`, `ψ_t` is Lipschitz and nonnegative. -/
theorem exists_lipschitzOnWith_stripCut {S : Set (E n)} (hC : HasBoundaryCharts 1 D u S)
    (ht : 0 < t) {x : E n} (hx : x ∈ S) :
    ∃ K, ∃ V ∈ 𝓝 x, LipschitzOnWith K (stripCut D u t) V ∧ ∀ y ∈ V, 0 ≤ stripCut D u t y := by
  by_cases hxD : x ∈ closure D
  · obtain ⟨U, F, hxU, hF⟩ := hC x ⟨hxD, hx⟩
    obtain ⟨K, V, hV, hlip⟩ :=
      (hF.contDiffOn.contDiffAt (hF.isOpen.mem_nhds hxU)).exists_lipschitzOnWith
    obtain ⟨Kc, hc⟩ := lipschitzWith_clamp t
    refine ⟨Kc * K, V ∩ U, inter_mem hV (hF.isOpen.mem_nhds hxU), ?_, fun y hy ↦ ?_⟩
    · exact lipschitzOnWith_of_eqOn (hc.comp_lipschitzOnWith (hlip.mono inter_subset_left))
        fun y hy ↦ (hF.stripCut_eq hy.2).symm
    · rw [hF.stripCut_eq hy.2]
      exact le_min (div_nonneg (le_max_right _ _) ht.le) zero_le_one
  · have hV : (closure D)ᶜ ∈ 𝓝 x := isClosed_closure.isOpen_compl.mem_nhds hxD
    have h0 : ∀ y ∈ (closure D)ᶜ, stripCut D u t y = 0 := fun y hy ↦
      stripCut_of_notMem fun h ↦ hy (subset_closure h)
    refine ⟨0, _, hV, lipschitzOnWith_of_eqOn (LipschitzWith.const (0 : ℝ)).lipschitzOnWith
      fun y hy ↦ (h0 y hy).symm, fun y hy ↦ (h0 y hy).ge⟩

theorem continuousAt_stripCut {S : Set (E n)} (hC : HasBoundaryCharts 1 D u S) (ht : 0 < t)
    {x : E n} (hx : x ∈ S) : ContinuousAt (stripCut D u t) x := by
  obtain ⟨K, V, hV, hlip, -⟩ := exists_lipschitzOnWith_stripCut hC ht hx
  exact hlip.continuousOn.continuousAt hV

theorem stripCut_nonneg {S : Set (E n)} (hC : HasBoundaryCharts 1 D u S) (ht : 0 < t)
    {x : E n} (hx : x ∈ S) : 0 ≤ stripCut D u t x := by
  obtain ⟨K, V, hV, -, hnn⟩ := exists_lipschitzOnWith_stripCut hC ht hx
  exact hnn x (mem_of_mem_nhds hV)

end StripCut

/-! ### Derivative of a product with a vanishing factor -/

/-- If `Q x = 0` and `ψ` is continuous at `x`, then `ψ Q` is differentiable at `x` with
derivative `ψ(x) DQ(x)`. -/
theorem hasFDerivAt_smul_of_eq_zero {ψ : E n → ℝ} {Q : E n → E n} {Q' : E n →L[ℝ] E n}
    {x : E n} (hQ : HasFDerivAt Q Q' x) (hQx : Q x = 0) (hψ : ContinuousAt ψ x) :
    HasFDerivAt (fun y ↦ ψ y • Q y) (ψ x • Q') x := by
  rw [hasFDerivAt_iff_isLittleO]
  have h1 : (fun y ↦ ψ y - ψ x) =o[𝓝 x] (fun _ ↦ (1 : ℝ)) :=
    (Asymptotics.isLittleO_one_iff ℝ).2 (by
      have := (hψ.tendsto.sub (tendsto_const_nhds (x := ψ x)))
      rwa [sub_self] at this)
  have h2 : (fun y ↦ (ψ y - ψ x) • (Q y - Q x)) =o[𝓝 x] (fun y ↦ y - x) := by
    simpa only [one_smul] using h1.smul_isBigO hQ.isBigO_sub
  have h3 : (fun y ↦ ψ x • (Q y - Q x - Q' (y - x))) =o[𝓝 x] (fun y ↦ y - x) :=
    (hasFDerivAt_iff_isLittleO.1 hQ).const_smul_left (ψ x)
  refine (h2.add h3).congr_left fun y ↦ ?_
  simp only [hQx, smul_zero, sub_zero, smul_apply, smul_sub, sub_smul]
  abel

/-! ### The strip identity -/

section Strip

variable {D : Set (E n)} {u : E n → ℝ} {S : Set (E n)} {Q : E n → E n} {t : ℝ}

/-- Lipschitz near `x` is preserved by products `ψ Q`. -/
theorem lipAt_smul {ψ : E n → ℝ} {x : E n} (hψ : ∃ K, ∃ V ∈ 𝓝 x, LipschitzOnWith K ψ V)
    (hQ : ∃ K, ∃ V ∈ 𝓝 x, LipschitzOnWith K Q V) :
    ∃ K, ∃ V ∈ 𝓝 x, LipschitzOnWith K (fun y ↦ ψ y • Q y) V := by
  have h1 := lipAt_prodMk hψ hQ
  have h2 := lipAt_comp_contDiff (g := fun p : ℝ × E n ↦ p.1 • p.2)
    (contDiff_fst.smul contDiff_snd) h1
  exact h2

theorem hasCompactSupport_smul_right {ψ : E n → ℝ} (hQc : HasCompactSupport Q) :
    HasCompactSupport fun y ↦ ψ y • Q y :=
  hQc.mono fun _ hx ↦ right_ne_zero_of_smul hx

/-- The field `ψ_t Q` is locally Lipschitz. -/
theorem locallyLipschitz_stripCut_smul (hC : HasBoundaryCharts 1 D u S) (hQ : ContDiff ℝ 1 Q)
    (hQS : tsupport Q ⊆ S) (ht : 0 < t) :
    LocallyLipschitz fun y ↦ stripCut D u t y • Q y := by
  intro x
  by_cases hx : x ∈ tsupport Q
  · obtain ⟨K, V, hV, hlip, -⟩ := exists_lipschitzOnWith_stripCut hC ht (hQS hx)
    exact lipAt_smul ⟨K, V, hV, hlip⟩ (hQ.locallyLipschitz x)
  · refine lipAt_congr ?_ ⟨0, univ, univ_mem, (LipschitzWith.const (0 : E n)).lipschitzOnWith⟩
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
    simp [hy]

/-- `ψ_t div Q` is continuous. -/
theorem continuous_stripCut_mul_divergence (hC : HasBoundaryCharts 1 D u S) (hQ : ContDiff ℝ 1 Q)
    (hQS : tsupport Q ⊆ S) (ht : 0 < t) :
    Continuous fun x ↦ stripCut D u t x * divergence Q x := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : x ∈ tsupport Q
  · exact (continuousAt_stripCut hC ht (hQS hx)).mul (continuous_divergence hQ).continuousAt
  · have h : (fun x ↦ stripCut D u t x * divergence Q x) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [(isClosed_tsupport Q).isOpen_compl.mem_nhds hx] with y hy
      rw [divergence_of_notMem_tsupport hy, mul_zero]
    exact continuousAt_const.congr h.symm

theorem inner_gradient_eq_fderiv (f : E n → ℝ) (x v : E n) : ⟪v, ∇ f x⟫ = fderiv ℝ f x v := by
  rw [real_inner_comm, gradient, toDual_symm_apply]

/-- Almost everywhere, `div(ψ_t Q) = ψ_t div Q + t⁻¹ 1_{D ∩ {u < t}} ⟨Q, ∇u⟩`. -/
theorem ae_divergence_stripCut_smul (hC : HasBoundaryCharts 1 D u S) (hQ : ContDiff ℝ 1 Q)
    (hQc : HasCompactSupport Q) (hQS : tsupport Q ⊆ S) (ht : 0 < t) :
    ∀ᵐ x, divergence (fun y ↦ stripCut D u t y • Q y) x = stripCut D u t x * divergence Q x +
      t⁻¹ * (D ∩ {x | u x < t}).indicator (fun y ↦ ⟪Q y, ∇ u y⟫) x := by
  obtain ⟨K, hK⟩ := lipschitzWith_of_locallyLipschitz_of_hasCompactSupport
    (locallyLipschitz_stripCut_smul hC hQ hQS ht) (hasCompactSupport_smul_right hQc)
  filter_upwards [hK.ae_differentiableAt] with x hWx
  set ψ := stripCut D u t with hψ_def
  have hQd : ∀ y, DifferentiableAt ℝ Q y := fun y ↦ hQ.differentiable one_ne_zero y
  by_cases hxQ : x ∈ tsupport Q
  swap
  · have hW0 : (fun y ↦ ψ y • Q y) =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hxQ] with y hy
      simp [hy]
    rw [divergence_eq_traceCLM, hW0.fderiv_eq, divergence_of_notMem_tsupport hxQ]
    simp [image_eq_zero_of_notMem_tsupport hxQ]
  have hψc := continuousAt_stripCut hC ht (hQS hxQ)
  by_cases hQx : Q x = 0
  · rw [divergence_eq_traceCLM, (hasFDerivAt_smul_of_eq_zero (hQd x).hasFDerivAt hQx hψc).fderiv,
      map_smul, smul_eq_mul, ← divergence_eq_traceCLM]
    have h0 : (D ∩ {x | u x < t}).indicator (fun y ↦ ⟪Q y, ∇ u y⟫) x = 0 := by
      simp [hQx]
    rw [h0, mul_zero, add_zero]
  have hψeq : ψ =ᶠ[𝓝 x] fun y ↦ ⟪Q y, ψ y • Q y⟫ * (‖Q y‖ ^ 2)⁻¹ := by
    filter_upwards [(hQd x).continuousAt.eventually_ne hQx] with y hy
    rw [inner_smul_right, real_inner_self_eq_norm_sq, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.2 hy)), mul_one]
  have hψd : DifferentiableAt ℝ ψ x := by
    refine DifferentiableAt.congr_of_eventuallyEq ?_ hψeq
    exact ((hQd x).inner ℝ hWx).mul
      (((hQd x).norm_sq ℝ).fun_inv (pow_ne_zero 2 (norm_ne_zero_iff.2 hQx)))
  rw [divergence_smul hψd (hQd x)]
  congr 1
  by_cases hxD : x ∈ D
  · by_cases hut : u x < t
    · obtain ⟨U, F, hxU, hF⟩ := hC x ⟨subset_closure hxD, hQS hxQ⟩
      have huF := hF.eventuallyEq_of_mem hxU hxD
      have hFx : F x = u x := huF.eq_of_nhds.symm
      have hFpos : 0 < F x := (hF.mem_iff x hxU).1 hxD
      have hψF : ψ =ᶠ[𝓝 x] fun y ↦ t⁻¹ • F y := by
        filter_upwards [hF.isOpen.mem_nhds hxU,
          (hF.continuousAt hxU).eventually (lt_mem_nhds hFpos),
          (hF.continuousAt hxU).eventually (gt_mem_nhds (hFx ▸ hut))] with y hyU hy0 hyt
        rw [hψ_def, hF.stripCut_eq hyU, max_eq_left hy0.le, min_eq_left ((div_le_one ht).2 hyt.le),
          smul_eq_mul, div_eq_inv_mul]
      have hFd : DifferentiableAt ℝ F x :=
        (hF.contDiffOn.contDiffAt (hF.isOpen.mem_nhds hxU)).differentiableAt one_ne_zero
      rw [hψF.fderiv_eq, indicator_of_mem (show x ∈ D ∩ {x | u x < t} from ⟨hxD, hut⟩),
        inner_gradient_eq_fderiv, huF.fderiv_eq, fderiv_fun_const_smul hFd]
      rfl
    · have h1 : ψ x = 1 := by
        rw [hψ_def, stripCut_of_mem hxD, min_eq_right ((one_le_div ht).2 (not_lt.1 hut))]
      have hmax : IsLocalMax ψ x :=
        Eventually.of_forall fun y ↦ (stripCut_le_one y).trans_eq h1.symm
      rw [hmax.fderiv_eq_zero, indicator_of_notMem (fun h ↦ hut h.2)]
      simp
  · obtain ⟨K', V, hV, -, hnn⟩ := exists_lipschitzOnWith_stripCut hC ht (hQS hxQ)
    have hmin : IsLocalMin ψ x := by
      filter_upwards [hV] with y hy
      rw [hψ_def, stripCut_of_notMem hxD]
      exact hnn y hy
    rw [hmin.fderiv_eq_zero, indicator_of_notMem (fun h ↦ hxD h.1)]
    simp

/-- **The strip identity.** For `t > 0`,
`t⁻¹ ∫_{D ∩ {u < t}} ⟨Q, ∇u⟩ = -∫ ψ_t div Q`, with `ψ_t = 1_D min(u/t, 1)`; in particular the
left integrand is integrable on the strip. -/
theorem integral_strip_eq (hD : MeasurableSet D) (hu : Measurable u)
    (hC : HasBoundaryCharts 1 D u S) (hQ : ContDiff ℝ 1 Q) (hQc : HasCompactSupport Q)
    (hQS : tsupport Q ⊆ S) (ht : 0 < t) :
    IntegrableOn (fun x ↦ ⟪Q x, ∇ u x⟫) (D ∩ {x | u x < t}) ∧
      t⁻¹ * ∫ x in D ∩ {x | u x < t}, ⟪Q x, ∇ u x⟫ = -∫ x, stripCut D u t x * divergence Q x := by
  obtain ⟨K, hK⟩ := lipschitzWith_of_locallyLipschitz_of_hasCompactSupport
    (locallyLipschitz_stripCut_smul hC hQ hQS ht) (hasCompactSupport_smul_right hQc)
  have hWc : HasCompactSupport fun y ↦ stripCut D u t y • Q y := hasCompactSupport_smul_right hQc
  have hint0 := integral_divergence_eq_zero hK hWc
  have hdivW := integrable_divergence_of_lipschitzWith hK hWc
  have ha : Integrable fun x ↦ stripCut D u t x * divergence Q x :=
    (continuous_stripCut_mul_divergence hC hQ hQS ht).integrable_of_hasCompactSupport
      (hasCompactSupport_divergence hQc).mul_left
  have hae := ae_divergence_stripCut_smul hC hQ hQc hQS ht
  set s := D ∩ {x | u x < t} with hs_def
  have hs : MeasurableSet s := hD.inter (measurableSet_lt hu measurable_const)
  have hb : Integrable fun x ↦ t⁻¹ * s.indicator (fun y ↦ ⟪Q y, ∇ u y⟫) x :=
    (hdivW.sub ha).congr (by filter_upwards [hae] with x hx; rw [Pi.sub_apply, hx]; ring)
  have hind : Integrable (s.indicator fun y ↦ ⟪Q y, ∇ u y⟫) := by
    have := hb.const_mul t
    simpa [← mul_assoc, mul_inv_cancel₀ ht.ne'] using this
  refine ⟨(integrable_indicator_iff hs).1 hind, ?_⟩
  have hsum : ∫ x, divergence (fun y ↦ stripCut D u t y • Q y) x =
      (∫ x, stripCut D u t x * divergence Q x) +
        ∫ x, t⁻¹ * s.indicator (fun y ↦ ⟪Q y, ∇ u y⟫) x := by
    rw [integral_congr_ae hae, integral_add ha hb]
  rw [integral_const_mul, integral_indicator hs, hint0] at hsum
  linarith

/-- **The strip representation of the flux.**
`t⁻¹ ∫_{D ∩ {u < t}} ⟨Q, ∇u⟩ → Flux_D(Q) = -∫_D div Q` as `t ↓ 0`. -/
theorem tendsto_integral_strip (hD : MeasurableSet D) (hu : Measurable u)
    (hC : HasBoundaryCharts 1 D u S) (hQ : ContDiff ℝ 1 Q) (hQc : HasCompactSupport Q)
    (hQS : tsupport Q ⊆ S) :
    Tendsto (fun t ↦ t⁻¹ * ∫ x in D ∩ {x | u x < t}, ⟪Q x, ∇ u x⟫) (𝓝[>] 0)
      (𝓝 (fluxFunctional D Q)) := by
  have hlim : Tendsto (fun t ↦ ∫ x, stripCut D u t x * divergence Q x) (𝓝[>] 0)
      (𝓝 (∫ x, D.indicator (divergence Q) x)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖divergence Q x‖) ?_ ?_
      (integrable_divergence hQ hQc).norm ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (continuous_stripCut_mul_divergence hC hQ hQS ht).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with t ht
      refine Eventually.of_forall fun x ↦ ?_
      by_cases hx : x ∈ tsupport Q
      · rw [norm_mul]
        refine mul_le_of_le_one_left (norm_nonneg _) ?_
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [stripCut_nonneg hC ht (hQS hx)], stripCut_le_one x⟩
      · simp [divergence_of_notMem_tsupport hx]
    · refine Eventually.of_forall fun x ↦ ?_
      by_cases hxD : x ∈ D
      swap
      · simp only [stripCut_of_notMem hxD, indicator_of_notMem hxD, zero_mul]
        exact tendsto_const_nhds
      by_cases hx : x ∈ tsupport Q
      swap
      · simp only [divergence_of_notMem_tsupport hx, mul_zero, indicator_of_mem hxD]
        exact tendsto_const_nhds
      obtain ⟨U, F, hxU, hF⟩ := hC x ⟨subset_closure hxD, hQS hx⟩
      have hux : 0 < u x := by
        rw [hF.eq_max x hxU]; exact lt_max_of_lt_left ((hF.mem_iff x hxU).1 hxD)
      rw [indicator_of_mem hxD]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT hux] with t ht
      rw [stripCut_of_mem hxD, min_eq_right ((one_le_div ht.1).2 ht.2.le), one_mul]
  rw [integral_indicator hD] at hlim
  unfold fluxFunctional
  refine hlim.neg.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ((integral_strip_eq hD hu hC hQ hQc hQS ht).2).symm

end Strip

/-! ### Linearity of the flux -/

section Linearity

variable {D : Set (E n)} {Q Q₁ Q₂ : E n → E n}

theorem fluxFunctional_add (h₁ : ContDiff ℝ 1 Q₁) (h₂ : ContDiff ℝ 1 Q₂)
    (hc₁ : HasCompactSupport Q₁) (hc₂ : HasCompactSupport Q₂) :
    fluxFunctional D (Q₁ + Q₂) = fluxFunctional D Q₁ + fluxFunctional D Q₂ := by
  unfold fluxFunctional
  have : divergence (Q₁ + Q₂) = fun x ↦ divergence Q₁ x + divergence Q₂ x := funext fun x ↦
    divergence_add (h₁.differentiable one_ne_zero x) (h₂.differentiable one_ne_zero x)
  rw [this, integral_add (integrable_divergence h₁ hc₁).integrableOn
    (integrable_divergence h₂ hc₂).integrableOn]
  ring

theorem fluxFunctional_smul (h : ContDiff ℝ 1 Q) (c : ℝ) :
    fluxFunctional D (c • Q) = c * fluxFunctional D Q := by
  unfold fluxFunctional
  have : divergence (c • Q) = fun x ↦ c * divergence Q x := funext fun x ↦
    divergence_const_smul (h.differentiable one_ne_zero x) c
  rw [this, integral_const_mul]
  ring

theorem fluxFunctional_neg (h : ContDiff ℝ 1 Q) : fluxFunctional D (-Q) = -fluxFunctional D Q := by
  rw [← neg_one_smul ℝ Q, fluxFunctional_smul h]
  ring

theorem fluxFunctional_sub (h₁ : ContDiff ℝ 1 Q₁) (h₂ : ContDiff ℝ 1 Q₂)
    (hc₁ : HasCompactSupport Q₁) (hc₂ : HasCompactSupport Q₂) :
    fluxFunctional D (Q₁ - Q₂) = fluxFunctional D Q₁ - fluxFunctional D Q₂ := by
  have h := fluxFunctional_add (D := D) (Q₁ := Q₁) (Q₂ := -Q₂) h₁ h₂.neg hc₁ hc₂.neg
  rw [sub_eq_add_neg, h, fluxFunctional_neg h₂]
  ring

end Linearity

/-! ### Gradients of chart functions -/

section Gradient

theorem contDiffOn_gradient {F : E n → ℝ} {U : Set (E n)} {k : WithTop ℕ∞} (hU : IsOpen U)
    (hF : ContDiffOn ℝ (k + 1) F U) : ContDiffOn ℝ k (∇ F) U := by
  have h := hF.fderiv_of_isOpen hU le_rfl
  exact (toDual ℝ (E n)).symm.contDiff.comp_contDiffOn h

theorem continuousOn_gradient {F : E n → ℝ} {U : Set (E n)} {k : WithTop ℕ∞} (hU : IsOpen U)
    (hF : ContDiffOn ℝ k F U) (hk : 1 ≤ k) : ContinuousOn (∇ F) U :=
  (toDual ℝ (E n)).symm.continuous.comp_continuousOn (hF.continuousOn_fderiv_of_isOpen hU hk)

/-- A smooth function supported in `U` times a field of class `C^k` on `U` is `C^k`. -/
theorem contDiff_smul_of_tsupport_subset {χ : E n → ℝ} {G : E n → E n} {U : Set (E n)}
    {k : WithTop ℕ∞} (hU : IsOpen U) (hχ : ContDiff ℝ k χ) (hG : ContDiffOn ℝ k G U)
    (hχU : tsupport χ ⊆ U) : ContDiff ℝ k fun y ↦ χ y • G y := by
  refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.smul (hG.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h ↦ hx (hχU h)
    refine (contDiffAt_const (c := (0 : E n))).congr_of_eventuallyEq ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
    simp [hy]

end Gradient

/-! ### The measure of the strips -/

section MeasureBound

variable {D : Set (E n)} {u : E n → ℝ} {k : WithTop ℕ∞}

theorem one_le_of_two_le (hk : 2 ≤ k) : 1 ≤ k := le_trans (by norm_num) hk

/-- Near a regular boundary point, `|D ∩ {u < t} ∩ V| ≤ C t`: apply the strip identity to
`Q₀ = χ ∇F`, for which `⟨Q₀, ∇u⟩ = χ |∇F|²` on `D`. -/
theorem IsBoundaryChart.exists_measure_strip_le (hD : MeasurableSet D) (hu : Measurable u)
    {U : Set (E n)} {F : E n → ℝ} (hF : IsBoundaryChart k D u U F) (hk : 2 ≤ k) {x₀ : E n}
    (hx₀ : x₀ ∈ U) (hF0 : F x₀ = 0) :
    ∃ V ∈ 𝓝 x₀, ∃ C, 0 ≤ C ∧ ∀ t, 0 < t →
      volume (D ∩ {x | u x < t} ∩ V) ≤ ENNReal.ofReal (C * t) := by
  have hk1 := one_le_of_two_le hk
  set c := ‖∇ F x₀‖ / 2 with hc_def
  have hc : 0 < c := half_pos (norm_pos_iff.2 (hF.gradient_ne_zero x₀ hx₀ hF0))
  have hev : ∀ᶠ y in 𝓝 x₀, y ∈ U ∧ c < ‖∇ F y‖ :=
    (hF.isOpen.eventually_mem hx₀).and
      (((continuousOn_gradient hF.isOpen hF.contDiffOn hk1).continuousAt
        (hF.isOpen.mem_nhds hx₀)).norm.eventually (lt_mem_nhds (half_lt_self (by
          rw [norm_pos_iff]; exact hF.gradient_ne_zero x₀ hx₀ hF0))))
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hballU : ball x₀ ρ ⊆ U := fun y hy ↦ (hball y hy).1
  obtain ⟨χ, hχ, hχc, hχU, hχ01, hχ1⟩ := exists_smooth_cutoff (isCompact_closedBall x₀ (ρ / 2))
    isOpen_ball (closedBall_subset_ball (half_lt_self hρ))
  set Q₀ : E n → E n := fun y ↦ χ y • ∇ F y with hQ₀_def
  have hk2 : (1 : WithTop ℕ∞) + 1 ≤ k := by
    have : (1 : WithTop ℕ∞) + 1 = 2 := by norm_num
    rw [this]; exact hk
  have hQ₀ : ContDiff ℝ 1 Q₀ :=
    contDiff_smul_of_tsupport_subset isOpen_ball (hχ.of_le (by exact_mod_cast le_top))
      ((contDiffOn_gradient hF.isOpen (hF.contDiffOn.of_le hk2)).mono hballU) hχU
  have hQ₀c : HasCompactSupport Q₀ := hχc.mono fun _ hx ↦ left_ne_zero_of_smul hx
  have hQ₀S : tsupport Q₀ ⊆ ball x₀ ρ := (tsupport_smul_subset_left _ _).trans hχU
  have hC' : HasBoundaryCharts 1 D u (ball x₀ ρ) :=
    ((hF.of_le hk1).hasBoundaryCharts).mono le_rfl hballU
  set C₀ := ∫ x, |divergence Q₀ x| with hC₀_def
  refine ⟨ball x₀ (ρ / 2), ball_mem_nhds x₀ (half_pos hρ), C₀ / c ^ 2,
    div_nonneg (integral_nonneg fun _ ↦ abs_nonneg _) (by positivity), fun t ht ↦ ?_⟩
  obtain ⟨hint, heq⟩ := integral_strip_eq hD hu hC' hQ₀ hQ₀c hQ₀S ht
  set s := D ∩ {x | u x < t} with hs_def
  have hs : MeasurableSet s := hD.inter (measurableSet_lt hu measurable_const)
  -- upper bound by `∫ |div Q₀|`
  have hup : t⁻¹ * ∫ x in s, ⟪Q₀ x, ∇ u x⟫ ≤ C₀ := by
    rw [heq, ← integral_neg]
    refine integral_mono
      ((continuous_stripCut_mul_divergence hC' hQ₀ hQ₀S ht).integrable_of_hasCompactSupport
        (hasCompactSupport_divergence hQ₀c).mul_left).neg
      (integrable_divergence hQ₀ hQ₀c).abs fun x ↦ ?_
    by_cases hx : x ∈ tsupport Q₀
    · have h0 := stripCut_nonneg hC' ht (hQ₀S hx)
      have h1 := stripCut_le_one (D := D) (u := u) (t := t) x
      calc -(stripCut D u t x * divergence Q₀ x) ≤ |stripCut D u t x * divergence Q₀ x| :=
            neg_le_abs _
        _ = stripCut D u t x * |divergence Q₀ x| := by rw [abs_mul, abs_of_nonneg h0]
        _ ≤ 1 * |divergence Q₀ x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = |divergence Q₀ x| := one_mul _
    · simp [divergence_of_notMem_tsupport hx]
  -- lower bound by `c² |s ∩ B|`
  have hfin : volume (ball x₀ (ρ / 2)) ≠ ⊤ := measure_ball_lt_top.ne
  have hg : Integrable fun x ↦ c ^ 2 * (ball x₀ (ρ / 2)).indicator (1 : E n → ℝ) x :=
    ((integrableOn_const hfin).integrable_indicator measurableSet_ball).const_mul _
  have hlow : c ^ 2 * (volume (s ∩ ball x₀ (ρ / 2))).toReal ≤ ∫ x in s, ⟪Q₀ x, ∇ u x⟫ := by
    have h1 : ∫ x in s, c ^ 2 * (ball x₀ (ρ / 2)).indicator (1 : E n → ℝ) x =
        c ^ 2 * (volume (s ∩ ball x₀ (ρ / 2))).toReal := by
      rw [integral_const_mul, integral_indicator_one measurableSet_ball, Measure.real,
        Measure.restrict_apply measurableSet_ball, inter_comm]
    rw [← h1]
    refine setIntegral_mono_on hg.integrableOn hint hs fun x hx ↦ ?_
    by_cases hxρ : x ∈ ball x₀ ρ
    · have hgrad : ∇ u x = ∇ F x := (hF.eventuallyEq_of_mem (hballU hxρ) hx.1).gradient_eq
      have hinner : ⟪Q₀ x, ∇ u x⟫ = χ x * ‖∇ F x‖ ^ 2 := by
        rw [hgrad, hQ₀_def, inner_smul_left, real_inner_self_eq_norm_sq]; rfl
      rw [hinner]
      by_cases hxr : x ∈ ball x₀ (ρ / 2)
      · rw [indicator_of_mem hxr, Pi.one_apply, mul_one, hχ1 x (ball_subset_closedBall hxr),
          one_mul]
        exact pow_le_pow_left₀ hc.le (hball x hxρ).2.le 2
      · rw [indicator_of_notMem hxr, mul_zero]
        exact mul_nonneg (hχ01 x).1 (by positivity)
    · have hxr : x ∉ ball x₀ (ρ / 2) := fun h ↦ hxρ (ball_subset_ball (half_le_self hρ.le) h)
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hxρ (hχU h)
      rw [indicator_of_notMem hxr, mul_zero, hQ₀_def]
      simp [hχx]
  have hint_le : ∫ x in s, ⟪Q₀ x, ∇ u x⟫ ≤ C₀ * t := by
    have := (inv_mul_le_iff₀ ht).1 hup
    linarith
  have hvol : (volume (s ∩ ball x₀ (ρ / 2))).toReal ≤ C₀ / c ^ 2 * t := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  rw [ENNReal.le_ofReal_iff_toReal_le
    (ne_top_of_le_ne_top hfin (measure_mono inter_subset_right))
    (mul_nonneg (div_nonneg (integral_nonneg fun _ ↦ abs_nonneg _) (by positivity)) ht.le)]
  exact hvol

/-- **Measure bound for the strips.** For a compact `K ⊆ S`, `|D ∩ {u < t} ∩ K| ≤ C t` for all
`t > 0`. -/
theorem exists_measure_strip_le {S : Set (E n)} (hD : MeasurableSet D) (hu : Measurable u)
    (hC : HasBoundaryCharts k D u S) (hk : 2 ≤ k) {K : Set (E n)} (hK : IsCompact K)
    (hKS : K ⊆ S) :
    ∃ C, 0 ≤ C ∧ ∀ t, 0 < t → volume (D ∩ {x | u x < t} ∩ K) ≤ ENNReal.ofReal (C * t) := by
  have hloc : ∀ x ∈ K, ∃ V ∈ 𝓝 x, ∃ C, 0 ≤ C ∧ ∀ t, 0 < t →
      volume (D ∩ {x | u x < t} ∩ V) ≤ ENNReal.ofReal (C * t) := by
    intro x hx
    by_cases hxD : x ∈ closure D
    swap
    · refine ⟨(closure D)ᶜ, isClosed_closure.isOpen_compl.mem_nhds hxD, 0, le_rfl,
        fun t _ ↦ ?_⟩
      have : D ∩ {x | u x < t} ∩ (closure D)ᶜ = ∅ :=
        eq_empty_iff_forall_notMem.2 fun y hy ↦ hy.2 (subset_closure hy.1.1)
      rw [this, measure_empty]
      exact bot_le
    obtain ⟨U, F, hxU, hF⟩ := hC x ⟨hxD, hKS hx⟩
    rcases (hF.nonneg_of_mem_closure hxU hxD).lt_or_eq with hpos | hzero
    · set M := (volume (ball x 1)).toReal with hM_def
      have hfin : volume (ball x 1) ≠ ⊤ := measure_ball_lt_top.ne
      refine ⟨U ∩ F ⁻¹' Ioi (F x / 2) ∩ ball x 1,
        inter_mem (inter_mem (hF.isOpen.mem_nhds hxU)
          ((hF.continuousAt hxU).preimage_mem_nhds (Ioi_mem_nhds (half_lt_self hpos))))
          (ball_mem_nhds x one_pos),
        M * 2 / F x, div_nonneg (mul_nonneg ENNReal.toReal_nonneg zero_le_two) hpos.le,
        fun t ht ↦ ?_⟩
      by_cases hts : t ≤ F x / 2
      · have : D ∩ {x | u x < t} ∩ (U ∩ F ⁻¹' Ioi (F x / 2) ∩ ball x 1) = ∅ := by
          refine eq_empty_iff_forall_notMem.2 fun y hy ↦ ?_
          have h1 : u y = max (F y) 0 := hF.eq_max y hy.2.1.1
          have h2 : F x / 2 < F y := hy.2.1.2
          have h3 : u y < t := hy.1.2
          have h4 : F y ≤ max (F y) 0 := le_max_left _ _
          linarith
        rw [this, measure_empty]
        exact bot_le
      · calc volume (D ∩ {x | u x < t} ∩ (U ∩ F ⁻¹' Ioi (F x / 2) ∩ ball x 1))
            ≤ volume (ball x 1) := measure_mono (inter_subset_right.trans inter_subset_right)
          _ = ENNReal.ofReal M := (ENNReal.ofReal_toReal hfin).symm
          _ ≤ ENNReal.ofReal (M * 2 / F x * t) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have h1 : 1 ≤ 2 * t / F x := (one_le_div hpos).2 (by linarith)
            have h2 : M * 2 / F x * t = M * (2 * t / F x) := by ring
            rw [h2]
            exact le_mul_of_one_le_right ENNReal.toReal_nonneg h1
    · exact hF.exists_measure_strip_le hD hu hk hxU hzero.symm
  choose! V hV C hC0 hCb using hloc
  obtain ⟨T, hTK, hcover⟩ := hK.elim_nhds_subcover V hV
  refine ⟨∑ x ∈ T, C x, Finset.sum_nonneg fun x hx ↦ hC0 x (hTK x hx), fun t ht ↦ ?_⟩
  calc volume (D ∩ {x | u x < t} ∩ K)
      ≤ volume (⋃ x ∈ T, D ∩ {x | u x < t} ∩ V x) := by
        refine measure_mono fun y hy ↦ ?_
        obtain ⟨x, hxT, hyV⟩ := mem_iUnion₂.1 (hcover hy.2)
        exact mem_iUnion₂.2 ⟨x, hxT, hy.1, hyV⟩
    _ ≤ ∑ x ∈ T, volume (D ∩ {x | u x < t} ∩ V x) := measure_biUnion_finset_le T _
    _ ≤ ∑ x ∈ T, ENNReal.ofReal (C x * t) :=
        Finset.sum_le_sum fun x hx ↦ hCb x (hTK x hx) t ht
    _ = ENNReal.ofReal ((∑ x ∈ T, C x) * t) := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun x hx ↦
          mul_nonneg (hC0 x (hTK x hx)) ht.le]

end MeasureBound

/-! ### Sign and boundary-trace dependence -/

section Sign

variable {D : Set (E n)} {u : E n → ℝ} {k : WithTop ℕ∞} {S : Set (E n)} {Q : E n → E n}

/-- If `⟨Q, ∇F⟩ ≥ 0` at the boundary points of `D` in `K`, read in every chart, then
`⟨Q, ∇u⟩ ≥ -η` on `D ∩ K ∩ {u < r}` for some `r > 0`. -/
theorem exists_inner_gradient_ge (hC : HasBoundaryCharts k D u S) (hk : 1 ≤ k)
    (hQ : Continuous Q) {K : Set (E n)} (hK : IsCompact K) (hKS : K ⊆ S)
    (hsign : ∀ x₀ ∈ frontier D ∩ K, ∀ U F, x₀ ∈ U → IsBoundaryChart k D u U F →
      0 ≤ ⟪Q x₀, ∇ F x₀⟫) {η : ℝ} (hη : 0 < η) :
    ∃ r, 0 < r ∧ ∀ x ∈ D ∩ K, u x < r → -η ≤ ⟪Q x, ∇ u x⟫ := by
  have hloc : ∀ y ∈ K, ∀ᶠ z : ℝ × E n in 𝓝 ((0 : ℝ), y),
      (z.2 ∈ D → u z.2 < z.1 → -η ≤ ⟪Q z.2, ∇ u z.2⟫) := by
    intro y hy
    rw [nhds_prod_eq]
    by_cases hyD : y ∈ closure D
    swap
    · refine Filter.eventually_of_mem (prod_mem_prod univ_mem
        (isClosed_closure.isOpen_compl.mem_nhds hyD)) fun z hz hzD _ ↦ ?_
      exact absurd (subset_closure hzD) hz.2
    obtain ⟨U, F, hyU, hF⟩ := hC y ⟨hyD, hKS hy⟩
    rcases (hF.nonneg_of_mem_closure hyU hyD).lt_or_eq with hpos | hzero
    · refine Filter.eventually_of_mem (prod_mem_prod (Iio_mem_nhds (half_pos hpos))
        (inter_mem (hF.isOpen.mem_nhds hyU)
          ((hF.continuousAt hyU).preimage_mem_nhds (Ioi_mem_nhds (half_lt_self hpos)))))
        fun z hz hzD hzu ↦ ?_
      have h1 : u z.2 = max (F z.2) 0 := hF.eq_max z.2 hz.2.1
      have h2 : F y / 2 < F z.2 := hz.2.2
      have h3 : z.1 < F y / 2 := hz.1
      have h4 : F z.2 ≤ max (F z.2) 0 := le_max_left _ _
      linarith
    · have hyD' : y ∉ D := fun h ↦ (lt_irrefl _) (hzero ▸ (hF.mem_iff y hyU).1 h)
      have hfr : y ∈ frontier D := ⟨hyD, fun h ↦ hyD' (interior_subset h)⟩
      have hs := hsign y ⟨hfr, hy⟩ U F hyU hF
      have hcont : ContinuousAt (fun z ↦ ⟪Q z, ∇ F z⟫) y :=
        hQ.continuousAt.inner ((continuousOn_gradient hF.isOpen hF.contDiffOn hk).continuousAt
          (hF.isOpen.mem_nhds hyU))
      refine Filter.eventually_of_mem (prod_mem_prod univ_mem
        (inter_mem (hF.isOpen.mem_nhds hyU)
          (hcont.eventually (lt_mem_nhds (show -η < ⟪Q y, ∇ F y⟫ by linarith)))))
        fun z hz hzD _ ↦ ?_
      rw [(hF.eventuallyEq_of_mem hz.2.1 hzD).gradient_eq]
      exact hz.2.2.le
  have hev := hK.eventually_forall_of_forall_eventually
    (P := fun r x ↦ x ∈ D → u x < r → -η ≤ ⟪Q x, ∇ u x⟫) hloc
  obtain ⟨r, hr, hr0⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ)))).exists
  exact ⟨r, hr0, fun x hx hux ↦ hr x hx.2 hx.1 hux⟩

/-- **Sign of the flux.** If `⟨Q, ∇F⟩ ≥ 0` at every boundary point of `D` in the support of
`Q`, read in every defining chart (`∇F` is the inward normal there), then `Flux_D(Q) ≥ 0`. -/
theorem fluxFunctional_nonneg (hD : MeasurableSet D) (hu : Measurable u) (hk : 2 ≤ k)
    (hC : HasBoundaryCharts k D u S) (hQ : ContDiff ℝ 1 Q) (hQc : HasCompactSupport Q)
    (hQS : tsupport Q ⊆ S)
    (hsign : ∀ x₀ ∈ frontier D ∩ tsupport Q, ∀ U F, x₀ ∈ U → IsBoundaryChart k D u U F →
      0 ≤ ⟪Q x₀, ∇ F x₀⟫) :
    0 ≤ fluxFunctional D Q := by
  obtain ⟨C, hC0, hCb⟩ := exists_measure_strip_le hD hu hC hk hQc.isCompact hQS
  have hk1 := one_le_of_two_le hk
  have hlim := tendsto_integral_strip hD hu (hC.mono hk1 le_rfl) hQ hQc hQS
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  set η := ε / (C + 1) with hη_def
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨r, hr, hsg⟩ := exists_inner_gradient_ge hC hk1 hQ.continuous hQc.isCompact hQS
    hsign hη
  have hev : ∀ᶠ t in 𝓝[>] 0, -η * C ≤ t⁻¹ * ∫ x in D ∩ {x | u x < t}, ⟪Q x, ∇ u x⟫ := by
    filter_upwards [Ioo_mem_nhdsGT hr] with t ht
    obtain ⟨hint, -⟩ := integral_strip_eq hD hu (hC.mono hk1 le_rfl) hQ hQc hQS ht.1
    set s := D ∩ {x | u x < t} with hs_def
    have hs : MeasurableSet s := hD.inter (measurableSet_lt hu measurable_const)
    have hKm : MeasurableSet (tsupport Q) := (isClosed_tsupport Q).measurableSet
    have hg : Integrable fun x ↦ -η * (tsupport Q).indicator (1 : E n → ℝ) x :=
      ((integrableOn_const hQc.isCompact.measure_lt_top.ne).integrable_indicator hKm).const_mul _
    have h1 : ∫ x in s, -η * (tsupport Q).indicator (1 : E n → ℝ) x =
        -η * (volume (s ∩ tsupport Q)).toReal := by
      rw [integral_const_mul, integral_indicator_one hKm, Measure.real,
        Measure.restrict_apply hKm, inter_comm]
    have h2 : -η * (volume (s ∩ tsupport Q)).toReal ≤ ∫ x in s, ⟪Q x, ∇ u x⟫ := by
      rw [← h1]
      refine setIntegral_mono_on hg.integrableOn hint hs fun x hx ↦ ?_
      by_cases hxK : x ∈ tsupport Q
      · rw [indicator_of_mem hxK, Pi.one_apply, mul_one]
        exact hsg x ⟨hx.1, hxK⟩ (hx.2.trans ht.2)
      · rw [indicator_of_notMem hxK, mul_zero, image_eq_zero_of_notMem_tsupport hxK,
          inner_zero_left]
    have h3 : (volume (s ∩ tsupport Q)).toReal ≤ C * t :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC0 ht.1.le) (hCb t ht.1)
    have hti : 0 ≤ t⁻¹ := inv_nonneg.2 ht.1.le
    calc -η * C = t⁻¹ * (-η * (C * t)) := by field_simp [ht.1.ne']
      _ ≤ t⁻¹ * (-η * (volume (s ∩ tsupport Q)).toReal) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonpos_left h3 (by linarith)) hti
      _ ≤ t⁻¹ * ∫ x in s, ⟪Q x, ∇ u x⟫ := mul_le_mul_of_nonneg_left h2 hti
  have hge : -η * C ≤ fluxFunctional D Q := ge_of_tendsto hlim hev
  have hηC : η * C < ε := by
    rw [hη_def, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  linarith

theorem tsupport_sub_subset (Q₁ Q₂ : E n → E n) :
    tsupport (Q₁ - Q₂) ⊆ tsupport Q₁ ∪ tsupport Q₂ :=
  (closure_mono (Function.support_sub _ _)).trans closure_union.subset

/-- **Boundary-trace dependence.** If `⟨Q₁, ∇F⟩ = ⟨Q₂, ∇F⟩` at every boundary point of `D` in
the supports, read in every defining chart, then `Flux_D(Q₁) = Flux_D(Q₂)`. -/
theorem fluxFunctional_congr_boundary {Q₁ Q₂ : E n → E n} (hD : MeasurableSet D)
    (hu : Measurable u) (hk : 2 ≤ k) (hC : HasBoundaryCharts k D u S) (hQ₁ : ContDiff ℝ 1 Q₁)
    (hQ₂ : ContDiff ℝ 1 Q₂) (hc₁ : HasCompactSupport Q₁) (hc₂ : HasCompactSupport Q₂)
    (hS₁ : tsupport Q₁ ⊆ S) (hS₂ : tsupport Q₂ ⊆ S)
    (hbd : ∀ x₀ ∈ frontier D ∩ (tsupport Q₁ ∪ tsupport Q₂), ∀ U F, x₀ ∈ U →
      IsBoundaryChart k D u U F → ⟪Q₁ x₀, ∇ F x₀⟫ = ⟪Q₂ x₀, ∇ F x₀⟫) :
    fluxFunctional D Q₁ = fluxFunctional D Q₂ := by
  have h12 : ContDiff ℝ 1 (Q₁ - Q₂) := hQ₁.sub hQ₂
  have h21 : ContDiff ℝ 1 (Q₂ - Q₁) := hQ₂.sub hQ₁
  have hle₁ := fluxFunctional_nonneg hD hu hk hC h12 (hc₁.sub hc₂)
    ((tsupport_sub_subset Q₁ Q₂).trans (union_subset hS₁ hS₂)) fun x₀ hx U F hxU hF ↦ by
      rw [Pi.sub_apply, inner_sub_left,
        hbd x₀ ⟨hx.1, tsupport_sub_subset Q₁ Q₂ hx.2⟩ U F hxU hF, sub_self]
  have hle₂ := fluxFunctional_nonneg hD hu hk hC h21 (hc₂.sub hc₁)
    ((tsupport_sub_subset Q₂ Q₁).trans (union_subset hS₂ hS₁)) fun x₀ hx U F hxU hF ↦ by
      rw [Pi.sub_apply, inner_sub_left,
        hbd x₀ ⟨hx.1, (tsupport_sub_subset Q₂ Q₁ hx.2).symm⟩ U F hxU hF, sub_self]
  rw [fluxFunctional_sub hQ₁ hQ₂ hc₁ hc₂] at hle₁
  rw [fluxFunctional_sub hQ₂ hQ₁ hc₂ hc₁] at hle₂
  linarith

end Sign

/-! ### Specialization to cones -/

namespace ConeData

variable (C : ConeData n) {Q Q₁ Q₂ : E n → E n}

theorem two_le_infty : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

/-- The strip representation of the flux for a cone component, for fields supported away from
the singular set. -/
theorem tendsto_integral_strip (hQ : ContDiff ℝ 1 Q) (hQc : HasCompactSupport Q)
    (hQS : Disjoint (tsupport Q) C.Sing) :
    Tendsto (fun t ↦ t⁻¹ * ∫ x in C.D ∩ {x | C.u x < t}, ⟪Q x, ∇ C.u x⟫) (𝓝[>] 0)
      (𝓝 (fluxFunctional C.D Q)) :=
  OnePhaseDimension.tendsto_integral_strip C.isOpen_D.measurableSet C.continuous.measurable
    (C.hasBoundaryCharts.mono (le_trans (by norm_num) two_le_infty) le_rfl) hQ hQc
    hQS.subset_compl_right

/-- Sign of the flux for a cone component. -/
theorem fluxFunctional_nonneg (hQ : ContDiff ℝ 1 Q) (hQc : HasCompactSupport Q)
    (hQS : Disjoint (tsupport Q) C.Sing)
    (hsign : ∀ x₀ ∈ frontier C.D ∩ tsupport Q, ∀ U F, x₀ ∈ U → IsBoundaryChart ∞ C.D C.u U F →
      0 ≤ ⟪Q x₀, ∇ F x₀⟫) :
    0 ≤ fluxFunctional C.D Q :=
  OnePhaseDimension.fluxFunctional_nonneg C.isOpen_D.measurableSet C.continuous.measurable
    two_le_infty C.hasBoundaryCharts hQ hQc hQS.subset_compl_right hsign

/-- Boundary-trace dependence of the flux for a cone component. -/
theorem fluxFunctional_congr_boundary (hQ₁ : ContDiff ℝ 1 Q₁) (hQ₂ : ContDiff ℝ 1 Q₂)
    (hc₁ : HasCompactSupport Q₁) (hc₂ : HasCompactSupport Q₂)
    (hS₁ : Disjoint (tsupport Q₁) C.Sing) (hS₂ : Disjoint (tsupport Q₂) C.Sing)
    (hbd : ∀ x₀ ∈ frontier C.D ∩ (tsupport Q₁ ∪ tsupport Q₂), ∀ U F, x₀ ∈ U →
      IsBoundaryChart ∞ C.D C.u U F → ⟪Q₁ x₀, ∇ F x₀⟫ = ⟪Q₂ x₀, ∇ F x₀⟫) :
    fluxFunctional C.D Q₁ = fluxFunctional C.D Q₂ :=
  OnePhaseDimension.fluxFunctional_congr_boundary C.isOpen_D.measurableSet
    C.continuous.measurable two_le_infty C.hasBoundaryCharts hQ₁ hQ₂ hc₁ hc₂
    hS₁.subset_compl_right hS₂.subset_compl_right hbd

end ConeData

end OnePhaseDimension
