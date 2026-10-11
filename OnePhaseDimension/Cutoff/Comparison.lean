/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Cutoff.Cutoffs

/-!
# The integrated comparison for a fixed cut-off

Let `C` be a cone in `ℝⁿ`, `n ≥ 3`, `c` certificate data on `ℝ^{n-1}` with constant `ε > 0`,
`(W, F)` a collar of `C`, and `ξ` a `0`-homogeneous cut-off which is smooth near a compact set
`K ⊆ closure D ∩ S^{n-1} ∩ W` on which `w > 0`, and which vanishes near every other point of
`closure D ∩ S^{n-1}` (`Gen.IsCutoffData`). With the tests `v = ξ h` and `Z_ξ = ξ² Z`, built from
the fields of `F`, the spherical comparison `∫ div Z_ξ ≤ ∫ (|∇v|² + β² v²)` holds, with the Hardy
constant `β² = ((n - 2)/2)²` of `S^{n-1}`. Combined with the interior comparison
`div Z ≥ β² h² + |∇h|² + ε w^{2a}` on `D`, the energy terms cancel pointwise and
(`Gen.IsCutoffData.integrated_comparison`)

  `ε ∫_{D ∩ S^{n-1}} ξ² w^{2a} dσ ≤ ∫_{D ∩ S^{n-1}} (h²|∇ξ|² + 2ξh⟪∇h, ∇ξ⟫ - 2ξ⟪Z, ∇ξ⟫) dσ`,

with the fields of `u` on the right. The boundary sign `⟪Z, N⟫ + H h² ≥ 0` and the gradient bound
`|∇u|² ≤ 1` are hypotheses (`Gen.BoundarySign`); they hold on original cones and on suspensions.
The five-dimensional statements (`n = 6`, `β² = 4`, `ε = ε*`) are the instances at `n = 6`.

## Differences from the source

The 2026-09-24 version applies the divergence theorem on the link to `ξ² Z`, uses the boundary
comparison and then the spherical stability inequality with its boundary integral. We use the
volume-only spherical comparison, in which the boundary sign enters as a hypothesis, so no
boundary integral appears. The cut-off `ξ` is an abstract `0`-homogeneous function with the
properties listed in `IsCutoffData`; both cut-offs of the source are instances.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric Function
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### Calculus helpers -/

theorem gradient_fun_mul {n : ℕ} {f g : E n → ℝ} {x : E n} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    ∇ (fun y ↦ f y * g y) x = f x • ∇ g x + g x • ∇ f x := by
  simp only [gradient, fderiv_fun_mul hf hg, map_add, map_smul]

theorem fderiv_sq_apply {n : ℕ} {f : E n → ℝ} {x : E n} (hf : DifferentiableAt ℝ f x)
    (v : E n) : fderiv ℝ (fun y ↦ f y ^ 2) x v = 2 * f x * fderiv ℝ f x v := by
  have h : (fun y ↦ f y ^ 2) = fun y ↦ f y * f y := funext fun y ↦ sq _
  rw [h, fderiv_fun_mul hf hf]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem continuousAt_divergence {n : ℕ} {Q : E n → E n} {x : E n} (hQ : ContDiffAt ℝ 2 Q x) :
    ContinuousAt (divergence Q) x := by
  have h := (hQ.fderiv_right (m := 0) (by norm_num)).continuousAt
  exact traceCLM.continuous.continuousAt.comp h

/-- A function vanishing near `x` vanishes, with its gradient, near `x`. -/
theorem eventually_eq_zero_and_gradient {n : ℕ} {ξ : E n → ℝ} {x : E n} (h : ξ =ᶠ[𝓝 x] 0) :
    ∀ᶠ y in 𝓝 x, ξ y = 0 ∧ ∇ ξ y = 0 := by
  filter_upwards [h.eventuallyEq_nhds] with y hy
  refine ⟨hy.self_of_nhds, ?_⟩
  rw [hy.gradient_eq]
  simp [gradient]

/-! ### Integrability on the link -/

/-- A function continuous at every point of `closure D ∩ S^{n-1}` is integrable on the link. -/
theorem ConeData.integrable_sphere_indicator {n : ℕ} (C : ConeData n) {g : E n → ℝ}
    (hg : ∀ x ∈ closure C.D ∩ sphere 0 1, ContinuousAt g x) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ C.D.indicator g u)
      (volume : Measure (E n)).toSphere := by
  set L := closure C.D ∩ sphere (0 : E n) 1
  have hL : IsCompact L := (isCompact_sphere 0 1).inter_left isClosed_closure
  obtain ⟨M, hM⟩ := hL.exists_bound_of_continuousOn fun x hx ↦ (hg x hx).continuousWithinAt
  have heq : (fun u : sphere (0 : E n) 1 ↦ C.D.indicator g u) =
      fun u : sphere (0 : E n) 1 ↦ C.D.indicator (fun y ↦ g (radialProj y)) u :=
    funext fun u ↦ (indicator_radialProj_of_mem_sphere C g (norm_eq_of_mem_sphere u)).symm
  have hmeas : Measurable fun u : sphere (0 : E n) 1 ↦
      C.D.indicator (fun y ↦ g (radialProj y)) u := by
    refine measurable_sphere_indicator C.isOpen_D fun y hy ↦ ?_
    have hy0 := C.ne_zero_of_mem_D hy
    have hθ : radialProj y ∈ L :=
      ⟨subset_closure (C.radialProj_mem_D hy), mem_sphere_zero_iff_norm.2 (norm_radialProj hy0)⟩
    exact ((hg _ hθ).comp (contDiffAt_radialProj_of_ne_zero hy0 (k := 0)).continuousAt)
      |>.continuousWithinAt
  rw [heq]
  refine Integrable.mono' (integrable_const (max M 0)) hmeas.aestronglyMeasurable
    (ae_of_all _ fun u ↦ ?_)
  have hu1 := norm_eq_of_mem_sphere u
  by_cases hD : (u : E n) ∈ C.D
  · rw [indicator_of_mem hD, radialProj_of_norm_eq_one hu1]
    exact (hM _ ⟨subset_closure hD, mem_sphere_zero_iff_norm.2 hu1⟩).trans (le_max_left _ _)
  · rw [indicator_of_notMem hD, norm_zero]
    exact le_max_right _ _

/-- A function agreeing on `D ∩ S^{n-1}` with a function continuous on `closure D ∩ S^{n-1}` is
integrable on the link. -/
theorem ConeData.integrable_sphere_indicator_of_eq {n : ℕ} (C : ConeData n) {f g : E n → ℝ}
    (hg : ∀ x ∈ closure C.D ∩ sphere 0 1, ContinuousAt g x)
    (heq : ∀ x ∈ C.D ∩ sphere 0 1, f x = g x) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ C.D.indicator f u)
      (volume : Measure (E n)).toSphere := by
  refine (C.integrable_sphere_indicator hg).congr (ae_of_all _ fun u ↦ ?_)
  by_cases hD : (u : E n) ∈ C.D
  · simp only [indicator_of_mem hD]
    exact (heq u ⟨hD, u.2⟩).symm
  · simp only [indicator_of_notMem hD]

theorem continuousAt_of_eventuallyEq_zero {n : ℕ} {g : E n → ℝ} {x : E n}
    (h : g =ᶠ[𝓝 x] 0) : ContinuousAt g x :=
  continuousAt_const.congr h.symm

namespace Gen

variable {n : ℕ}

/-- The Hardy constant of `S^{n-1}` is `((n - 2)/2)²`. -/
theorem hardyConst_sub_one (hn : 1 ≤ n) : hardyConst (n - 1) = (((n : ℝ) - 2) / 2) ^ 2 := by
  rw [hardyConst, Nat.cast_sub hn]
  push_cast
  ring

/-! ### The tests and the cut-off data -/

/-- The angular test `v = ξ h`, with `h` built from `F`. -/
def cutoffTestV (c : Coeffs (n - 1)) (F ξ : E n → ℝ) (x : E n) : ℝ := ξ x * fluxH c F x

/-- The angular field `ξ² Z`, with `Z` built from `F`. -/
def cutoffTestZ (c : Coeffs (n - 1)) (F ξ : E n → ℝ) (x : E n) : E n := ξ x ^ 2 • fluxZ c F x

/-- The cut-off mass `ξ² w^{2a}`. -/
def cutoffMass (u ξ : E n → ℝ) (x : E n) : ℝ := ξ x ^ 2 * fluxW u x ^ (2 * aExp)

/-- The three cut-off errors `h²|∇ξ|² + 2ξh⟪∇h, ∇ξ⟫ - 2ξ⟪Z, ∇ξ⟫`. -/
def cutoffError (c : Coeffs (n - 1)) (u ξ : E n → ℝ) (x : E n) : ℝ :=
  fluxH c u x ^ 2 * ‖∇ ξ x‖ ^ 2 + 2 * ξ x * fluxH c u x * ⟪∇ (fluxH c u) x, ∇ ξ x⟫
    - 2 * ξ x * ⟪fluxZ c u x, ∇ ξ x⟫

/-- The boundary sign `⟪Z, N⟫ + H h² ≥ 0` at the unit points of `closure D \ D`, read through any
defining chart, for the fields of the chart. -/
def BoundarySign (c : Coeffs (n - 1)) (C : OnePhaseDimension.ConeData n) : Prop :=
  ∀ (U : Set (E n)) (G : E n → ℝ) (x₀ : E n), IsOpen U → x₀ ∈ U → ContDiffOn ℝ ∞ G U →
    (∀ y ∈ U, C.u y = max (G y) 0) → (∀ y ∈ U, 0 < G y → y ∈ C.D) →
    (∀ y ∈ U, G y = 0 → ‖∇ G y‖ = 1) → (∀ y ∈ U, 0 < G y → Δ G y = 0) →
    x₀ ∈ closure C.D → x₀ ∉ C.D → ‖x₀‖ = 1 →
    0 ≤ ⟪fluxZ c G x₀, ∇ G x₀⟫ - iteratedFDeriv ℝ 2 G x₀ ![∇ G x₀, ∇ G x₀] * fluxH c G x₀ ^ 2

/-- Cut-off data for a collar `(W, F)`: `ξ` is `0`-homogeneous, smooth near a compact set
`K ⊆ closure D ∩ S^{n-1} ∩ W` on which `w > 0`, and vanishes near every other point of
`closure D ∩ S^{n-1}`. -/
structure IsCutoffData (C : OnePhaseDimension.ConeData n) (W : Set (E n)) (F : E n → ℝ)
    (K : Set (E n)) (ξ : E n → ℝ) : Prop where
  homog : IsZeroHomogeneous ξ
  isCompact : IsCompact K
  subset_sphere : K ⊆ sphere 0 1
  subset_closure : K ⊆ closure C.D
  subset_W : K ⊆ W
  fluxW_pos : ∀ x ∈ K, 0 < fluxW F x
  smooth : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ ξ y
  eventually_zero : ∀ x ∈ closure C.D ∩ sphere 0 1, x ∉ K → ξ =ᶠ[𝓝 x] 0

namespace IsCutoffData

variable {c : Coeffs (n - 1)} {ε δ : ℝ} {C : OnePhaseDimension.ConeData n} {W : Set (E n)}
  {F : E n → ℝ} {K : Set (E n)}
  {ξ : E n → ℝ}

/-- The open set on which the tests are smooth. -/
def goodSet (c : Coeffs (n - 1)) (F ξ : E n → ℝ) : Set (E n) :=
  {y | y ≠ 0 ∧ 0 < fluxW F y ∧ 0 < fluxF c F y ∧ ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ ξ z}

theorem isOpen_goodSet (hc : CertificateHolds (n - 1) ε δ c) (hF : ContDiff ℝ ∞ F) :
    IsOpen (goodSet c F ξ) := by
  refine isOpen_iff_mem_nhds.2 fun y hy ↦ ?_
  obtain ⟨hy0, hw, hf, hξ⟩ := hy
  have hcw := continuousAt_fluxW hy0 hF.contDiffAt
  have hcf := (contDiffAt_fluxF hc hy0 hF.contDiffAt hw).continuousAt
  filter_upwards [isOpen_ne.mem_nhds hy0, hcw.eventually (lt_mem_nhds hw),
    hcf.eventually (lt_mem_nhds hf), hξ.eventually_nhds] with z hz0 hzw hzf hzξ
  exact ⟨hz0, hzw, hzf, hzξ⟩

theorem contDiffAt_testV (hc : CertificateHolds (n - 1) ε δ c) (hF : ContDiff ℝ ∞ F) {y : E n}
    (hy : y ∈ goodSet c F ξ) : ContDiffAt ℝ ∞ (cutoffTestV c F ξ) y :=
  hy.2.2.2.self_of_nhds.mul
    (contDiffAt_fluxH hc hy.1 hF.contDiffAt hy.2.1 hy.2.2.1.ne')

theorem contDiffAt_testZ (hc : CertificateHolds (n - 1) ε δ c) (hF : ContDiff ℝ ∞ F) {y : E n}
    (hy : y ∈ goodSet c F ξ) : ContDiffAt ℝ ∞ (cutoffTestZ c F ξ) y :=
  (hy.2.2.2.self_of_nhds.pow 2).smul (contDiffAt_fluxZ hc hy.1 hF.contDiffAt hy.2.1)

variable (hξ : IsCutoffData C W F K ξ)
include hξ

theorem norm_eq_one {x : E n} (hx : x ∈ K) : ‖x‖ = 1 :=
  mem_sphere_zero_iff_norm.1 (hξ.subset_sphere hx)

theorem ne_zero {x : E n} (hx : x ∈ K) : x ≠ 0 := by
  intro h0; have := hξ.norm_eq_one hx; rw [h0, norm_zero] at this; exact zero_ne_one this

theorem radialProj_eq {x : E n} (hx : x ∈ K) : radialProj x = x :=
  radialProj_of_norm_eq_one (hξ.norm_eq_one hx)

theorem subset_goodSet (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) : K ⊆ goodSet c F ξ := fun x hx ↦
  ⟨hξ.ne_zero hx, hξ.fluxW_pos x hx, hε.trans_le (ConeData.IsCollar.fluxF_ge hcol hc hs
    (hξ.subset_W hx) (hξ.subset_closure hx) (hξ.norm_eq_one hx) (hξ.fluxW_pos x hx)),
    hξ.smooth x hx⟩

theorem disjoint_sing (hcol : C.IsCollar W F) : Disjoint K C.Sing :=
  hcol.disjoint_sing.mono_left hξ.subset_W

/-- Off `K`, the cut-off and the tests vanish near the point. -/
theorem eventually_off {x : E n} (hx : x ∈ closure C.D ∩ sphere 0 1) (hxK : x ∉ K) :
    ∀ᶠ y in 𝓝 x, ξ y = 0 ∧ ∇ ξ y = 0 ∧ cutoffTestV c F ξ y = 0 ∧ cutoffTestZ c F ξ y = 0 := by
  filter_upwards [eventually_eq_zero_and_gradient (hξ.eventually_zero x hx hxK)] with y hy
  exact ⟨hy.1, hy.2, by simp [cutoffTestV, hy.1], by simp [cutoffTestZ, hy.1]⟩

theorem testV_eventuallyEq_zero {x : E n} (hx : x ∈ closure C.D ∩ sphere 0 1) (hxK : x ∉ K) :
    cutoffTestV c F ξ =ᶠ[𝓝 x] 0 := by
  filter_upwards [hξ.eventually_off (c := c) hx hxK] with y hy using hy.2.2.1

theorem testZ_eventuallyEq_zero {x : E n} (hx : x ∈ closure C.D ∩ sphere 0 1) (hxK : x ∉ K) :
    cutoffTestZ c F ξ =ᶠ[𝓝 x] 0 := by
  filter_upwards [hξ.eventually_off (c := c) hx hxK] with y hy using hy.2.2.2

/-- The tests form an admissible angular test. -/
theorem isSphericalTest (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) :
    IsSphericalTest C (cutoffTestV c F ξ) (cutoffTestZ c F ξ) K (goodSet c F ξ) where
  isOpen := isOpen_goodSet hc hcol.contDiff
  contDiffOn_v := fun y hy ↦ (contDiffAt_testV hc hcol.contDiff hy).contDiffWithinAt
  contDiffOn_Z := fun y hy ↦
    ((contDiffAt_testZ hc hcol.contDiff hy).of_le (by simp)).contDiffWithinAt
  homog_v := fun r hr x _ ↦ by
    simp only [cutoffTestV, hξ.homog r hr x, isZeroHomogeneous_fluxH c F r hr x]
  homog_Z := fun r hr x _ ↦ by
    simp only [cutoffTestZ, hξ.homog r hr x, isZeroHomogeneous_fluxZ c F r hr x]
  tangential := fun x _ ↦ by
    simp only [cutoffTestZ, inner_smul_right, isTangentialField_fluxZ c F x, mul_zero]
  isCompact := hξ.isCompact
  subset_sphere := hξ.subset_sphere
  subset_open := hξ.subset_goodSet hc hε hcol hs
  disjoint_sing := hξ.disjoint_sing hcol
  eq_zero := fun x hx hxK ↦ by
    have h := (hξ.eventually_off (c := c) hx hxK).self_of_nhds
    exact ⟨h.2.2.1, h.2.2.2⟩

/-- The boundary condition for the tests. -/
theorem sphericalBoundaryCondition (hcol : C.IsCollar W F) (hsign : BoundarySign c C) :
    SphericalBoundaryCondition C (cutoffTestV c F ξ) (cutoffTestZ c F ξ) K := by
  intro x₀ hx₀ U G hU hx₀U hG hu _
  have hx₀W : x₀ ∈ W := hξ.subset_W hx₀.2
  have hx₀cl : x₀ ∈ closure C.D := frontier_subset_closure hx₀.1
  have hgr := hcol.gradient_eq ⟨hx₀W, hx₀cl⟩ hU hx₀U hG hu
  have hhess := hcol.hessNormal_eq ⟨hx₀W, hx₀cl⟩ hU hx₀U hG hu
  rw [← hhess, ← hgr]
  have hsg := hsign W F x₀ hcol.isOpen hx₀W hcol.contDiff.contDiffOn hcol.chart.eq_max
    (fun y hy hpos ↦ (hcol.chart.mem_iff y hy).2 hpos) hcol.norm_gradient
    (fun y hy hpos ↦ hcol.laplacian_eq_zero ⟨hy, (hcol.chart.mem_iff y hy).2 hpos⟩) hx₀cl
    (C.notMem_of_mem_frontier hx₀.1) (hξ.norm_eq_one hx₀.2)
  have h2 : iteratedFDeriv ℝ 2 F x₀ ![∇ F x₀, ∇ F x₀] = hessNormal F x₀ := by
    simp [hessNormal, iteratedFDeriv_two_apply]
  rw [h2] at hsg
  have key : ⟪cutoffTestZ c F ξ x₀, ∇ F x₀⟫ - hessNormal F x₀ * cutoffTestV c F ξ x₀ ^ 2 =
      ξ x₀ ^ 2 * (⟪fluxZ c F x₀, ∇ F x₀⟫ - hessNormal F x₀ * fluxH c F x₀ ^ 2) := by
    simp only [cutoffTestZ, cutoffTestV, inner_smul_left, RCLike.conj_to_real]
    ring
  rw [key]
  exact mul_nonneg (sq_nonneg _) hsg

/-! ### Continuity and integrability of the integrands -/

theorem continuousAt_divergence_testZ (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε)
    (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) {x : E n} (hx : x ∈ closure C.D ∩ sphere 0 1) :
    ContinuousAt (divergence (cutoffTestZ c F ξ)) x := by
  by_cases hxK : x ∈ K
  · exact continuousAt_divergence ((contDiffAt_testZ hc hcol.contDiff
      (hξ.subset_goodSet hc hε hcol hs hxK)).of_le (by simp))
  · refine continuousAt_of_eventuallyEq_zero ?_
    filter_upwards [(hξ.testZ_eventuallyEq_zero (c := c) hx hxK).eventuallyEq_nhds] with y hy
    rw [divergence_congr hy]
    simp [divergence]

/-- The integrand `|∇v|² + β² v²`, with the Hardy constant `β²` of `S^{n-1}`. -/
def energyDensity (c : Coeffs (n - 1)) (F ξ : E n → ℝ) (x : E n) : ℝ :=
  ‖∇ (cutoffTestV c F ξ) x‖ ^ 2 + hardyConst (n - 1) * cutoffTestV c F ξ x ^ 2

theorem continuousAt_energyDensity (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε)
    (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) {x : E n} (hx : x ∈ closure C.D ∩ sphere 0 1) :
    ContinuousAt (energyDensity c F ξ) x := by
  by_cases hxK : x ∈ K
  · have hv := contDiffAt_testV hc hcol.contDiff (hξ.subset_goodSet hc hε hcol hs hxK)
    exact ((continuousAt_gradient_of_contDiffAt (hv.of_le (by simp))).norm.pow 2).add
      (continuousAt_const.mul (hv.continuousAt.pow 2))
  · refine continuousAt_of_eventuallyEq_zero ?_
    filter_upwards [eventually_eq_zero_and_gradient
      (hξ.testV_eventuallyEq_zero (c := c) hx hxK)] with y hy
    simp [energyDensity, hy.1, hy.2]

theorem continuousAt_mass {x : E n} (hF : ContDiff ℝ ∞ F) (hx : x ∈ closure C.D ∩ sphere 0 1) :
    ContinuousAt (cutoffMass F ξ) x := by
  by_cases hxK : x ∈ K
  · have hξc := ((hξ.smooth x hxK).self_of_nhds).continuousAt
    exact (hξc.pow 2).mul ((continuousAt_fluxW (hξ.ne_zero hxK) hF.contDiffAt).rpow_const
      (Or.inr (by norm_num [aExp])))
  · refine continuousAt_of_eventuallyEq_zero ?_
    filter_upwards [hξ.eventually_zero x hx hxK] with y hy
    simp [cutoffMass, hy]

theorem continuousAt_error (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε)
    (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) {x : E n} (hx : x ∈ closure C.D ∩ sphere 0 1) :
    ContinuousAt (cutoffError c F ξ) x := by
  by_cases hxK : x ∈ K
  · have hg := hξ.subset_goodSet hc hε hcol hs hxK
    have hξs := (hξ.smooth x hxK).self_of_nhds
    have hh := contDiffAt_fluxH hc hg.1 hcol.contDiff.contDiffAt hg.2.1 hg.2.2.1.ne'
    have hZ := contDiffAt_fluxZ hc hg.1 hcol.contDiff.contDiffAt hg.2.1
    have hgξ := continuousAt_gradient_of_contDiffAt (hξs.of_le (by simp))
    have hgh := continuousAt_gradient_of_contDiffAt (hh.of_le (by simp))
    unfold cutoffError
    exact (((hh.continuousAt.pow 2).mul (hgξ.norm.pow 2)).add
      (((continuousAt_const.mul hξs.continuousAt).mul hh.continuousAt).mul (hgh.inner hgξ))).sub
      ((continuousAt_const.mul hξs.continuousAt).mul (hZ.continuousAt.inner hgξ))
  · refine continuousAt_of_eventuallyEq_zero ?_
    filter_upwards [eventually_eq_zero_and_gradient (hξ.eventually_zero x hx hxK)] with y hy
    simp [cutoffError, hy.1, hy.2]

/-- On `D ∩ S^{n-1}`, the mass of `u` is that of the collar function. -/
theorem mass_eq (hcol : C.IsCollar W F) {x : E n} (hx : x ∈ C.D ∩ sphere 0 1) :
    cutoffMass C.u ξ x = cutoffMass F ξ x := by
  by_cases hxK : x ∈ K
  · have hx0 := hξ.ne_zero hxK
    have hxW : radialProj x ∈ W := by rw [hξ.radialProj_eq hxK]; exact hξ.subset_W hxK
    have hxD : radialProj x ∈ C.D := by rw [hξ.radialProj_eq hxK]; exact hx.1
    simp only [cutoffMass, (ConeData.IsCollar.fluxW_eventuallyEq hcol hx0 hxW hxD).self_of_nhds]
  · have h := (eventually_eq_zero_and_gradient
      (hξ.eventually_zero x ⟨_root_.subset_closure hx.1, hx.2⟩ hxK)).self_of_nhds
    simp [cutoffMass, h.1]

/-- On `D ∩ S^{n-1}`, the errors of `u` are those of the collar function. -/
theorem error_eq (hcol : C.IsCollar W F) {x : E n} (hx : x ∈ C.D ∩ sphere 0 1) :
    cutoffError c C.u ξ x = cutoffError c F ξ x := by
  by_cases hxK : x ∈ K
  · have hx0 := hξ.ne_zero hxK
    have hxW : radialProj x ∈ W := by rw [hξ.radialProj_eq hxK]; exact hξ.subset_W hxK
    have hxD : radialProj x ∈ C.D := by rw [hξ.radialProj_eq hxK]; exact hx.1
    have hH := ConeData.IsCollar.fluxH_eventuallyEq (c := c) hcol hx0 hxW hxD
    have hZ := (ConeData.IsCollar.fluxZ_eventuallyEq (c := c) hcol hx0 hxW hxD).self_of_nhds
    simp only [cutoffError, hH.self_of_nhds, hH.gradient_eq, hZ]
  · have h := (eventually_eq_zero_and_gradient
      (hξ.eventually_zero x ⟨_root_.subset_closure hx.1, hx.2⟩ hxK)).self_of_nhds
    simp [cutoffError, h.1, h.2]

theorem integrable_mass (hcol : C.IsCollar W F) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ C.D.indicator (cutoffMass C.u ξ) u)
      (volume : Measure (E n)).toSphere :=
  C.integrable_sphere_indicator_of_eq (fun _ hx ↦ hξ.continuousAt_mass hcol.contDiff hx)
    fun _ hx ↦ hξ.mass_eq hcol hx

theorem integrable_error (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ C.D.indicator (cutoffError c C.u ξ) u)
      (volume : Measure (E n)).toSphere :=
  C.integrable_sphere_indicator_of_eq (fun _ hx ↦ hξ.continuousAt_error hc hε hcol hs hx)
    fun _ hx ↦ hξ.error_eq hcol hx

/-! ### The pointwise comparison -/

/-- **Pointwise comparison** at a unit point of `D ∩ K`: with `v = ξh` and `Z_ξ = ξ² Z`,
`ε ξ² w^{2a} ≤ div Z_ξ - (|∇v|² + β² v²) + (h²|∇ξ|² + 2ξh⟪∇h, ∇ξ⟫ - 2ξ⟪Z, ∇ξ⟫)`. -/
theorem pointwise_of_mem (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) {x : E n} (hxK : x ∈ K) (hxD : x ∈ C.D) :
    ε * cutoffMass C.u ξ x ≤
      divergence (cutoffTestZ c F ξ) x - energyDensity c F ξ x + cutoffError c C.u ξ x := by
  have hx0 := hξ.ne_zero hxK
  have hx1 := hξ.norm_eq_one hxK
  have hxW' : radialProj x ∈ W := by rw [hξ.radialProj_eq hxK]; exact hξ.subset_W hxK
  have hxD' : radialProj x ∈ C.D := by rw [hξ.radialProj_eq hxK]; exact hxD
  have hg := hξ.subset_goodSet hc hε hcol hs hxK
  have hH := ConeData.IsCollar.fluxH_eventuallyEq (c := c) hcol hx0 hxW' hxD'
  have hZ := ConeData.IsCollar.fluxZ_eventuallyEq (c := c) hcol hx0 hxW' hxD'
  have hWe := (ConeData.IsCollar.fluxW_eventuallyEq hcol hx0 hxW' hxD').self_of_nhds
  have hξd : DifferentiableAt ℝ ξ x :=
    (hξ.smooth x hxK).self_of_nhds.differentiableAt (by simp)
  have hZu : DifferentiableAt ℝ (fluxZ c C.u) x :=
    ((contDiffAt_fluxZ hc hx0 hcol.contDiff.contDiffAt hg.2.1).differentiableAt
      (by simp)).congr_of_eventuallyEq hZ.symm
  have hHu : DifferentiableAt ℝ (fluxH c C.u) x :=
    ((contDiffAt_fluxH hc hx0 hcol.contDiff.contDiffAt hg.2.1 hg.2.2.1.ne').differentiableAt
      (by simp)).congr_of_eventuallyEq hH.symm
  -- the divergence of `ξ² Z`
  have hdiv : divergence (cutoffTestZ c F ξ) x =
      ξ x ^ 2 * divergence (fluxZ c C.u) x + 2 * ξ x * ⟪fluxZ c C.u x, ∇ ξ x⟫ := by
    have hev : cutoffTestZ c F ξ =ᶠ[𝓝 x] fun y ↦ ξ y ^ 2 • fluxZ c C.u y := by
      filter_upwards [hZ] with y hy
      simp only [cutoffTestZ, hy]
    rw [divergence_congr hev,
      EllipticBernoulli.divergence_smul (a := fun y ↦ ξ y ^ 2) (hξd.pow 2) hZu,
      fderiv_sq_apply hξd, inner_gradient_eq_fderiv]
  -- the gradient of `ξ h`
  have hgrad : ∇ (cutoffTestV c F ξ) x = ξ x • ∇ (fluxH c C.u) x + fluxH c C.u x • ∇ ξ x := by
    have hev : cutoffTestV c F ξ =ᶠ[𝓝 x] fun y ↦ ξ y * fluxH c C.u y := by
      filter_upwards [hH] with y hy
      simp only [cutoffTestV, hy]
    rw [hev.gradient_eq, gradient_fun_mul hξd hHu]
  have hv : cutoffTestV c F ξ x = ξ x * fluxH c C.u x := by
    simp only [cutoffTestV, hH.self_of_nhds]
  -- the interior comparison
  obtain ⟨hu, hΔ⟩ := ConeData.contDiffAt_u_and_eventually_laplacian hxD
    (hcol.notMem_sing (hξ.subset_W hxK))
  have hwu : 0 < fluxW C.u x := by rw [← hWe]; exact hg.2.1
  have hint := div_fluxZ_ge hc hε C.isOneHomogeneous_u hx1 hu hΔ hwu (hs x hxD)
  have hnorm : ‖ξ x • ∇ (fluxH c C.u) x + fluxH c C.u x • ∇ ξ x‖ ^ 2 =
      ξ x ^ 2 * ‖∇ (fluxH c C.u) x‖ ^ 2 +
        2 * ξ x * fluxH c C.u x * ⟪∇ (fluxH c C.u) x, ∇ ξ x⟫ +
        fluxH c C.u x ^ 2 * ‖∇ ξ x‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    simp only [RCLike.conj_to_real]
    ring
  unfold energyDensity cutoffError cutoffMass
  rw [hdiv, hgrad, hv, hnorm]
  nlinarith [mul_le_mul_of_nonneg_left hint (sq_nonneg (ξ x))]

/-- **Pointwise comparison on the link**: at every unit vector, for the indicators of `D`. -/
theorem pointwise (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) (u : sphere (0 : E n) 1) :
    ε * C.D.indicator (cutoffMass C.u ξ) u ≤
      C.D.indicator (divergence (cutoffTestZ c F ξ)) u - C.D.indicator (energyDensity c F ξ) u +
        C.D.indicator (cutoffError c C.u ξ) u := by
  by_cases hD : (u : E n) ∈ C.D
  · simp only [indicator_of_mem hD]
    by_cases hK : (u : E n) ∈ K
    · exact hξ.pointwise_of_mem hc hε hcol hs hK hD
    · have hx : (u : E n) ∈ closure C.D ∩ sphere 0 1 := ⟨_root_.subset_closure hD, u.2⟩
      have h1 := (hξ.eventually_off (c := c) hx hK).self_of_nhds
      have h2 : divergence (cutoffTestZ c F ξ) u = 0 := by
        rw [divergence_congr (hξ.testZ_eventuallyEq_zero (c := c) hx hK)]
        simp [divergence]
      have h3 : ∇ (cutoffTestV c F ξ) u = 0 := by
        rw [(hξ.testV_eventuallyEq_zero (c := c) hx hK).gradient_eq]
        simp [gradient]
      simp [cutoffMass, cutoffError, energyDensity, h1.1, h1.2.1, h1.2.2.1, h2, h3]
  · simp only [indicator_of_notMem hD]
    simp

/-- **The integrated comparison** for a fixed cut-off:

  `ε ∫_{D ∩ S^{n-1}} ξ² w^{2a} dσ ≤ ∫_{D ∩ S^{n-1}} (h²|∇ξ|² + 2ξh⟪∇h, ∇ξ⟫ - 2ξ⟪Z, ∇ξ⟫) dσ`. -/
theorem integrated_comparison (hn : 3 ≤ n) (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε)
    (hcol : C.IsCollar W F) (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) (hsign : BoundarySign c C) :
    ε * ∫ u : sphere (0 : E n) 1, C.D.indicator (cutoffMass C.u ξ) u
        ∂(volume : Measure (E n)).toSphere ≤
      ∫ u : sphere (0 : E n) 1, C.D.indicator (cutoffError c C.u ξ) u
        ∂(volume : Measure (E n)).toSphere := by
  set σ := (volume : Measure (E n)).toSphere
  have hcomp := spherical_comparison_of_three_le hn (hξ.isSphericalTest hc hε hcol hs)
    (hξ.sphericalBoundaryCondition hcol hsign)
  rw [← hardyConst_sub_one (by omega : 1 ≤ n)] at hcomp
  have iD : Integrable (fun u : sphere (0 : E n) 1 ↦
      C.D.indicator (divergence (cutoffTestZ c F ξ)) u) σ :=
    C.integrable_sphere_indicator fun _ hx ↦ hξ.continuousAt_divergence_testZ hc hε hcol hs hx
  have iG : Integrable (fun u : sphere (0 : E n) 1 ↦ C.D.indicator (energyDensity c F ξ) u) σ :=
    C.integrable_sphere_indicator fun _ hx ↦ hξ.continuousAt_energyDensity hc hε hcol hs hx
  have iM := hξ.integrable_mass hcol
  have iE := hξ.integrable_error hc hε hcol hs
  have hmono : ∫ u : sphere (0 : E n) 1, ε * C.D.indicator (cutoffMass C.u ξ) u ∂σ ≤
      ∫ u : sphere (0 : E n) 1, (C.D.indicator (divergence (cutoffTestZ c F ξ)) u -
        C.D.indicator (energyDensity c F ξ) u + C.D.indicator (cutoffError c C.u ξ) u) ∂σ :=
    integral_mono (iM.const_mul ε) ((iD.sub iG).add iE) (hξ.pointwise hc hε hcol hs)
  have iDG : Integrable (fun u : sphere (0 : E n) 1 ↦
      C.D.indicator (divergence (cutoffTestZ c F ξ)) u -
        C.D.indicator (energyDensity c F ξ) u) σ := iD.sub iG
  rw [integral_const_mul, integral_add iDG iE, integral_sub iD iG] at hmono
  have hG : ∫ u : sphere (0 : E n) 1, C.D.indicator (energyDensity c F ξ) u ∂σ =
      ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ ‖∇ (cutoffTestV c F ξ) x‖ ^ 2 +
        hardyConst (n - 1) * cutoffTestV c F ξ x ^ 2) u ∂σ := rfl
  linarith

end IsCutoffData

end Gen
/-! ### The tests and the cut-off data in `ℝ⁶` -/

/-- The angular test `v = ξ h`, with `h` built from `F`. -/
def cutoffTestV (c : Coeffs) (F ξ : E 6 → ℝ) (x : E 6) : ℝ := ξ x * fluxH c F x

/-- The angular field `ξ² Z`, with `Z` built from `F`. -/
def cutoffTestZ (c : Coeffs) (F ξ : E 6 → ℝ) (x : E 6) : E 6 := ξ x ^ 2 • fluxZ c F x

/-- The cut-off mass `ξ² w^{2a}`. -/
def cutoffMass (u ξ : E 6 → ℝ) (x : E 6) : ℝ := ξ x ^ 2 * fluxW u x ^ (2 * aExp)

/-- The three cut-off errors `h²|∇ξ|² + 2ξh⟪∇h, ∇ξ⟫ - 2ξ⟪Z, ∇ξ⟫`. -/
def cutoffError (c : Coeffs) (u ξ : E 6 → ℝ) (x : E 6) : ℝ :=
  fluxH c u x ^ 2 * ‖∇ ξ x‖ ^ 2 + 2 * ξ x * fluxH c u x * ⟪∇ (fluxH c u) x, ∇ ξ x⟫
    - 2 * ξ x * ⟪fluxZ c u x, ∇ ξ x⟫

/-- The boundary sign `⟪Z, N⟫ + H h² ≥ 0` at the unit points of `closure D \ D`, read through any
defining chart, for the fields of the chart. -/
def BoundarySign (c : Coeffs) (C : ConeData 6) : Prop :=
  ∀ (U : Set (E 6)) (G : E 6 → ℝ) (x₀ : E 6), IsOpen U → x₀ ∈ U → ContDiffOn ℝ ∞ G U →
    (∀ y ∈ U, C.u y = max (G y) 0) → (∀ y ∈ U, 0 < G y → y ∈ C.D) →
    (∀ y ∈ U, G y = 0 → ‖∇ G y‖ = 1) → (∀ y ∈ U, 0 < G y → Δ G y = 0) →
    x₀ ∈ closure C.D → x₀ ∉ C.D → ‖x₀‖ = 1 →
    0 ≤ ⟪fluxZ c G x₀, ∇ G x₀⟫ - iteratedFDeriv ℝ 2 G x₀ ![∇ G x₀, ∇ G x₀] * fluxH c G x₀ ^ 2

/-- Cut-off data for a collar `(W, F)`: `ξ` is `0`-homogeneous, smooth near a compact set
`K ⊆ closure D ∩ S⁵ ∩ W` on which `w > 0`, and vanishes near every other point of
`closure D ∩ S⁵`. -/
structure IsCutoffData (C : ConeData 6) (W : Set (E 6)) (F : E 6 → ℝ) (K : Set (E 6))
    (ξ : E 6 → ℝ) : Prop where
  homog : IsZeroHomogeneous ξ
  isCompact : IsCompact K
  subset_sphere : K ⊆ sphere 0 1
  subset_closure : K ⊆ closure C.D
  subset_W : K ⊆ W
  fluxW_pos : ∀ x ∈ K, 0 < fluxW F x
  smooth : ∀ x ∈ K, ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ ξ y
  eventually_zero : ∀ x ∈ closure C.D ∩ sphere 0 1, x ∉ K → ξ =ᶠ[𝓝 x] 0

theorem cutoffTestV_eq_gen (c : Coeffs) (F ξ : E 6 → ℝ) :
    cutoffTestV c F ξ = Gen.cutoffTestV (n := 6) c.toGen F ξ :=
  rfl

theorem cutoffTestZ_eq_gen (c : Coeffs) (F ξ : E 6 → ℝ) :
    cutoffTestZ c F ξ = Gen.cutoffTestZ (n := 6) c.toGen F ξ :=
  rfl

theorem cutoffMass_eq_gen (u ξ : E 6 → ℝ) : cutoffMass u ξ = Gen.cutoffMass u ξ :=
  rfl

theorem cutoffError_eq_gen (c : Coeffs) (u ξ : E 6 → ℝ) :
    cutoffError c u ξ = Gen.cutoffError (n := 6) c.toGen u ξ :=
  rfl

/-- The boundary sign in `ℝ⁶` is the generic one at `n = 6`. -/
theorem BoundarySign.toGen {c : Coeffs} {C : ConeData 6} (h : BoundarySign c C) :
    Gen.BoundarySign (n := 6) c.toGen C :=
  h

namespace IsCutoffData

variable {c : Coeffs} {C : ConeData 6} {W : Set (E 6)} {F : E 6 → ℝ} {K : Set (E 6)}
  {ξ : E 6 → ℝ}

/-- Cut-off data in `ℝ⁶` are generic cut-off data at `n = 6`. -/
theorem toGen (h : IsCutoffData C W F K ξ) : Gen.IsCutoffData C W F K ξ :=
  ⟨h.homog, h.isCompact, h.subset_sphere, h.subset_closure, h.subset_W, h.fluxW_pos, h.smooth,
    h.eventually_zero⟩

/-- The open set on which the tests are smooth. -/
def goodSet (c : Coeffs) (F ξ : E 6 → ℝ) : Set (E 6) :=
  {y | y ≠ 0 ∧ 0 < fluxW F y ∧ 0 < fluxF c F y ∧ ∀ᶠ z in 𝓝 y, ContDiffAt ℝ ∞ ξ z}

theorem goodSet_eq_gen (c : Coeffs) (F ξ : E 6 → ℝ) :
    goodSet c F ξ = Gen.IsCutoffData.goodSet (n := 6) c.toGen F ξ :=
  rfl

/-- The integrand `|∇v|² + 4v²`. -/
def energyDensity (c : Coeffs) (F ξ : E 6 → ℝ) (x : E 6) : ℝ :=
  ‖∇ (cutoffTestV c F ξ) x‖ ^ 2 + 4 * cutoffTestV c F ξ x ^ 2

/-- The energy density in `ℝ⁶` is the generic one at `n = 6`. -/
theorem energyDensity_eq_gen (c : Coeffs) (F ξ : E 6 → ℝ) :
    energyDensity c F ξ = Gen.IsCutoffData.energyDensity (n := 6) c.toGen F ξ := by
  funext x
  have h : Gen.hardyConst (6 - 1) = 4 := Gen.hardyConst_five
  simp only [Gen.IsCutoffData.energyDensity, h]
  rfl

theorem isOpen_goodSet (hc : CertificateHolds c) (hF : ContDiff ℝ ∞ F) :
    IsOpen (goodSet c F ξ) := by
  simp only [goodSet_eq_gen]
  exact Gen.IsCutoffData.isOpen_goodSet (n := 6) hc.toGen hF

theorem contDiffAt_testV (hc : CertificateHolds c) (hF : ContDiff ℝ ∞ F) {y : E 6}
    (hy : y ∈ goodSet c F ξ) : ContDiffAt ℝ ∞ (cutoffTestV c F ξ) y := by
  simp only [cutoffTestV_eq_gen]
  exact Gen.IsCutoffData.contDiffAt_testV (n := 6) hc.toGen hF hy

theorem contDiffAt_testZ (hc : CertificateHolds c) (hF : ContDiff ℝ ∞ F) {y : E 6}
    (hy : y ∈ goodSet c F ξ) : ContDiffAt ℝ ∞ (cutoffTestZ c F ξ) y := by
  simp only [cutoffTestZ_eq_gen]
  exact Gen.IsCutoffData.contDiffAt_testZ (n := 6) hc.toGen hF hy

variable (hξ : IsCutoffData C W F K ξ)
include hξ

theorem norm_eq_one {x : E 6} (hx : x ∈ K) : ‖x‖ = 1 :=
  hξ.toGen.norm_eq_one hx

theorem ne_zero {x : E 6} (hx : x ∈ K) : x ≠ 0 :=
  hξ.toGen.ne_zero hx

theorem radialProj_eq {x : E 6} (hx : x ∈ K) : radialProj x = x :=
  hξ.toGen.radialProj_eq hx

theorem subset_goodSet (hc : CertificateHolds c) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) : K ⊆ goodSet c F ξ := by
  simp only [goodSet_eq_gen]
  exact hξ.toGen.subset_goodSet hc.toGen εStar_pos hcol hs

theorem disjoint_sing (hcol : C.IsCollar W F) : Disjoint K C.Sing :=
  hξ.toGen.disjoint_sing hcol

/-- Off `K`, the cut-off and the tests vanish near the point. -/
theorem eventually_off {x : E 6} (hx : x ∈ closure C.D ∩ sphere 0 1) (hxK : x ∉ K) :
    ∀ᶠ y in 𝓝 x, ξ y = 0 ∧ ∇ ξ y = 0 ∧ cutoffTestV c F ξ y = 0 ∧ cutoffTestZ c F ξ y = 0 := by
  simp only [cutoffTestV_eq_gen, cutoffTestZ_eq_gen]
  exact hξ.toGen.eventually_off (c := c.toGen) hx hxK

theorem testV_eventuallyEq_zero {x : E 6} (hx : x ∈ closure C.D ∩ sphere 0 1) (hxK : x ∉ K) :
    cutoffTestV c F ξ =ᶠ[𝓝 x] 0 := by
  filter_upwards [hξ.eventually_off (c := c) hx hxK] with y hy using hy.2.2.1

theorem testZ_eventuallyEq_zero {x : E 6} (hx : x ∈ closure C.D ∩ sphere 0 1) (hxK : x ∉ K) :
    cutoffTestZ c F ξ =ᶠ[𝓝 x] 0 := by
  filter_upwards [hξ.eventually_off (c := c) hx hxK] with y hy using hy.2.2.2

/-- The tests form an admissible angular test. -/
theorem isSphericalTest (hc : CertificateHolds c) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) :
    IsSphericalTest C (cutoffTestV c F ξ) (cutoffTestZ c F ξ) K (goodSet c F ξ) := by
  simp only [cutoffTestV_eq_gen, cutoffTestZ_eq_gen, goodSet_eq_gen]
  exact Gen.IsCutoffData.isSphericalTest (n := 6) (c := c.toGen) hξ.toGen hc.toGen εStar_pos hcol hs

/-- The boundary condition for the tests. -/
theorem sphericalBoundaryCondition (hcol : C.IsCollar W F) (hsign : BoundarySign c C) :
    SphericalBoundaryCondition C (cutoffTestV c F ξ) (cutoffTestZ c F ξ) K := by
  simp only [cutoffTestV_eq_gen, cutoffTestZ_eq_gen]
  exact hξ.toGen.sphericalBoundaryCondition hcol hsign.toGen

/-! ### Continuity and integrability of the integrands -/

theorem continuousAt_divergence_testZ (hc : CertificateHolds c) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) {x : E 6} (hx : x ∈ closure C.D ∩ sphere 0 1) :
    ContinuousAt (divergence (cutoffTestZ c F ξ)) x := by
  simp only [cutoffTestZ_eq_gen]
  exact hξ.toGen.continuousAt_divergence_testZ hc.toGen εStar_pos hcol hs hx

theorem continuousAt_energyDensity (hc : CertificateHolds c) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) {x : E 6} (hx : x ∈ closure C.D ∩ sphere 0 1) :
    ContinuousAt (energyDensity c F ξ) x := by
  simp only [energyDensity_eq_gen]
  exact hξ.toGen.continuousAt_energyDensity hc.toGen εStar_pos hcol hs hx

theorem continuousAt_mass {x : E 6} (hF : ContDiff ℝ ∞ F) (hx : x ∈ closure C.D ∩ sphere 0 1) :
    ContinuousAt (cutoffMass F ξ) x := by
  simp only [cutoffMass_eq_gen]
  exact hξ.toGen.continuousAt_mass hF hx

theorem continuousAt_error (hc : CertificateHolds c) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) {x : E 6} (hx : x ∈ closure C.D ∩ sphere 0 1) :
    ContinuousAt (cutoffError c F ξ) x := by
  simp only [cutoffError_eq_gen]
  exact hξ.toGen.continuousAt_error hc.toGen εStar_pos hcol hs hx

/-- On `D ∩ S⁵`, the mass of `u` is that of the collar function. -/
theorem mass_eq (hcol : C.IsCollar W F) {x : E 6} (hx : x ∈ C.D ∩ sphere 0 1) :
    cutoffMass C.u ξ x = cutoffMass F ξ x := by
  simp only [cutoffMass_eq_gen]
  exact hξ.toGen.mass_eq hcol hx

/-- On `D ∩ S⁵`, the errors of `u` are those of the collar function. -/
theorem error_eq (hcol : C.IsCollar W F) {x : E 6} (hx : x ∈ C.D ∩ sphere 0 1) :
    cutoffError c C.u ξ x = cutoffError c F ξ x := by
  simp only [cutoffError_eq_gen]
  exact hξ.toGen.error_eq (c := c.toGen) hcol hx

theorem integrable_mass (hcol : C.IsCollar W F) :
    Integrable (fun u : sphere (0 : E 6) 1 ↦ C.D.indicator (cutoffMass C.u ξ) u)
      (volume : Measure (E 6)).toSphere := by
  simp only [cutoffMass_eq_gen]
  exact hξ.toGen.integrable_mass hcol

theorem integrable_error (hc : CertificateHolds c) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) :
    Integrable (fun u : sphere (0 : E 6) 1 ↦ C.D.indicator (cutoffError c C.u ξ) u)
      (volume : Measure (E 6)).toSphere := by
  simp only [cutoffError_eq_gen]
  exact hξ.toGen.integrable_error hc.toGen εStar_pos hcol hs

/-! ### The pointwise comparison -/

/-- **Pointwise comparison** at a unit point of `D ∩ K`: with `v = ξh` and `Z_ξ = ξ² Z`,
`ε* ξ² w^{2a} ≤ div Z_ξ - (|∇v|² + 4v²) + (h²|∇ξ|² + 2ξh⟪∇h, ∇ξ⟫ - 2ξ⟪Z, ∇ξ⟫)`. -/
theorem pointwise_of_mem (hc : CertificateHolds c) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) {x : E 6} (hxK : x ∈ K) (hxD : x ∈ C.D) :
    εStar * cutoffMass C.u ξ x ≤
      divergence (cutoffTestZ c F ξ) x - energyDensity c F ξ x + cutoffError c C.u ξ x := by
  simp only [cutoffTestZ_eq_gen, cutoffMass_eq_gen, cutoffError_eq_gen, energyDensity_eq_gen]
  exact hξ.toGen.pointwise_of_mem hc.toGen εStar_pos hcol hs hxK hxD

/-- **Pointwise comparison on the link**: at every unit vector, for the indicators of `D`. -/
theorem pointwise (hc : CertificateHolds c) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) (u : sphere (0 : E 6) 1) :
    εStar * C.D.indicator (cutoffMass C.u ξ) u ≤
      C.D.indicator (divergence (cutoffTestZ c F ξ)) u - C.D.indicator (energyDensity c F ξ) u +
        C.D.indicator (cutoffError c C.u ξ) u := by
  simp only [cutoffTestZ_eq_gen, cutoffMass_eq_gen, cutoffError_eq_gen, energyDensity_eq_gen]
  exact hξ.toGen.pointwise hc.toGen εStar_pos hcol hs u

/-- **The integrated comparison** for a fixed cut-off:

  `ε* ∫_{D ∩ S⁵} ξ² w^{2a} dσ ≤ ∫_{D ∩ S⁵} (h²|∇ξ|² + 2ξh⟪∇h, ∇ξ⟫ - 2ξ⟪Z, ∇ξ⟫) dσ`. -/
theorem integrated_comparison (hc : CertificateHolds c) (hcol : C.IsCollar W F)
    (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1) (hsign : BoundarySign c C) :
    εStar * ∫ u : sphere (0 : E 6) 1, C.D.indicator (cutoffMass C.u ξ) u
        ∂(volume : Measure (E 6)).toSphere ≤
      ∫ u : sphere (0 : E 6) 1, C.D.indicator (cutoffError c C.u ξ) u
        ∂(volume : Measure (E 6)).toSphere := by
  simp only [cutoffMass_eq_gen, cutoffError_eq_gen]
  exact hξ.toGen.integrated_comparison (by norm_num) hc.toGen εStar_pos hcol hs hsign.toGen

end IsCutoffData

end OnePhaseDimension
