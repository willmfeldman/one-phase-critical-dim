/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Stability.SuperlevelCalculus
public import OnePhaseDimension.Stability.Competitor
public import OnePhaseDimension.Stability.Gluing
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# The second variation and the stability inequality

Let `D` be the selected component of a cone, `F` a smooth collar extension of `u` near the
support of a test `φ`, and `Λ(s) = ∫_{F + sφ > 0} (1 + |∇(F + sφ)|²)` (localized). Minimality of
`u` gives `Λ(0) ≤ Λ(s)`. Two applications of the Hadamard formula compute

  `Λ''(0) = 2 ∫_D |∇φ|² + 2 Flux_D(D²F(∇F, ∇F) φ² ∇F)`,

using `ΔF = 0` and `|∇F| = 1` on `∂D` and the boundary-trace dependence of the flux. Since
`Λ''(0) ≥ 0`, this is the stability inequality `Flux_D(H φ² ∇F) ≤ ∫_D |∇φ|²` with
`H = -D²F(∇F, ∇F)` the mean curvature of `∂D`. Combined with the sign of the flux, it proves the
volume-only stability statement.

## Main results

* `ConeData.IsCollar`: the collar data `(W, F)`.
* `ConeData.IsCollar.neg_integral_le_flux`: `-∫_D |∇φ|² ≤ Flux_D(D²F(∇F, ∇F) φ² ∇F)`.
* `stability_flux`: the volume-only stability statement.
* `stability_flux_of_boundaryTrace`: `Flux_D(Q) ≤ ∫_D |∇φ|²` for any `C¹` field `Q` with
  `⟨Q, N⟩ = H φ²` on the regular boundary.

## Differences from the source

The 2026-09-24 version computes the second variation in flow coordinates near the boundary (a
boundary layer with a Jacobian expansion and a moving edge). We differentiate
`Λ(s) = ∫_{F_s > 0} K_s` twice with the Hadamard formula; the first derivative vanishes by
minimality (it is not computed), and only the existence of `Λ''(0)` (not `C²` regularity of `Λ`)
is used. Boundary terms are expressed through the flux functional `Flux_D(Q) = -∫_D div Q` and
evaluated through boundary-trace dependence, with no surface measure.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace Function
open scoped ContDiff Gradient NNReal RealInnerProductSpace Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

/-! ### Calculus helpers -/

theorem inner_fderiv_gradient (G : E n → ℝ) (x v w : E n) :
    ⟪fderiv ℝ (∇ G) x v, w⟫ = fderiv ℝ (fderiv ℝ G) x v w := by
  have h : ∇ G = (toDual ℝ (E n)).symm ∘ fderiv ℝ G := rfl
  rw [h, LinearIsometryEquiv.comp_fderiv]
  exact toDual_symm_apply

/-- The divergence of the gradient is the Laplacian. -/
theorem divergence_gradient (G : E n → ℝ) (x : E n) : divergence (∇ G) x = Δ G x := by
  set b := stdOrthonormalBasis ℝ (E n)
  rw [divergence, LinearMap.trace_eq_sum_inner _ b,
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis G b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply, ContinuousLinearMap.coe_coe, real_inner_comm,
    inner_fderiv_gradient]
  rfl

theorem gradient_eq_zero_of_notMem {G : E n → ℝ} {x : E n} (hx : x ∉ tsupport G) :
    ∇ G x = 0 := by
  simp [gradient, fderiv_of_notMem_tsupport ℝ hx]

/-- `D²F(∇F, ∇F)`; on the boundary of `{F > 0}`, with `|∇F| = 1`, this is minus the mean
curvature. -/
def hessNormal (F : E n → ℝ) (x : E n) : ℝ := fderiv ℝ (fun y ↦ fderiv ℝ F y) x (∇ F x) (∇ F x)

theorem contDiff_hessNormal {F : E n → ℝ} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (hessNormal F) := by
  have h2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ F)) :=
    (hF.fderiv_right infty_add_one_le).fderiv_right infty_add_one_le
  have hg := contDiff_gradient_of_contDiff hF
  exact (h2.clm_apply hg).clm_apply hg

/-! ### Collar data -/

/-- Collar data for the component `D` of a cone: a smooth `F` on the whole space which is a
defining chart of `D` on the open set `W` (away from the singular set), with `|∇F| = 1` on
`{F = 0} ∩ W`, and whose jets agree with those of every chart `u = max G 0` at the points of
`W ∩ closure D`. -/
structure ConeData.IsCollar (C : ConeData n) (W : Set (E n)) (F : E n → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ F
  chart : IsBoundaryChart ∞ C.D C.u W F
  disjoint_sing : Disjoint W C.Sing
  norm_gradient : ∀ x ∈ W, F x = 0 → ‖∇ F x‖ = 1
  jet : ∀ x ∈ W ∩ closure C.D, ∀ (U : Set (E n)) (G : E n → ℝ), IsOpen U → x ∈ U →
    ContDiffOn ℝ ∞ G U → (∀ y ∈ U, C.u y = max (G y) 0) →
    ∀ k : ℕ, iteratedFDeriv ℝ k F x = iteratedFDeriv ℝ k G x

theorem ConeData.notMem_of_mem_frontier (C : ConeData n) {x : E n} (hx : x ∈ frontier C.D) :
    x ∉ C.D := fun hxD ↦ hx.2 (by rw [C.isOpen_D.interior_eq]; exact hxD)

namespace ConeData.IsCollar

variable {C : ConeData n} {W : Set (E n)} {F : E n → ℝ} (h : C.IsCollar W F)
include h

theorem isOpen : IsOpen W := h.chart.isOpen

theorem eq_zero_of_mem_frontier {x : E n} (hx : x ∈ frontier C.D) (hxW : x ∈ W) : F x = 0 :=
  le_antisymm (not_lt.1 fun hpos ↦ C.notMem_of_mem_frontier hx ((h.chart.mem_iff x hxW).2 hpos))
    (h.chart.nonneg_of_mem_closure hxW hx.1)

theorem fderiv_eq {x : E n} (hx : x ∈ W ∩ closure C.D) {U : Set (E n)} {G : E n → ℝ}
    (hU : IsOpen U) (hxU : x ∈ U) (hG : ContDiffOn ℝ ∞ G U) (hu : ∀ y ∈ U, C.u y = max (G y) 0) :
    fderiv ℝ F x = fderiv ℝ G x := by
  ext v
  have := congrArg (fun T ↦ T (fun _ ↦ v)) (h.jet x hx U G hU hxU hG hu 1)
  simpa [iteratedFDeriv_one_apply] using this

theorem gradient_eq {x : E n} (hx : x ∈ W ∩ closure C.D) {U : Set (E n)} {G : E n → ℝ}
    (hU : IsOpen U) (hxU : x ∈ U) (hG : ContDiffOn ℝ ∞ G U) (hu : ∀ y ∈ U, C.u y = max (G y) 0) :
    ∇ F x = ∇ G x := by
  simp only [gradient, h.fderiv_eq hx hU hxU hG hu]

theorem fderiv_fderiv_eq {x : E n} (hx : x ∈ W ∩ closure C.D) {U : Set (E n)} {G : E n → ℝ}
    (hU : IsOpen U) (hxU : x ∈ U) (hG : ContDiffOn ℝ ∞ G U) (hu : ∀ y ∈ U, C.u y = max (G y) 0) :
    fderiv ℝ (fderiv ℝ F) x = fderiv ℝ (fderiv ℝ G) x := by
  ext v w
  have := congrArg (fun T ↦ T ![v, w]) (h.jet x hx U G hU hxU hG hu 2)
  simpa [iteratedFDeriv_two_apply] using this

theorem hessNormal_eq {x : E n} (hx : x ∈ W ∩ closure C.D) {U : Set (E n)} {G : E n → ℝ}
    (hU : IsOpen U) (hxU : x ∈ U) (hG : ContDiffOn ℝ ∞ G U) (hu : ∀ y ∈ U, C.u y = max (G y) 0) :
    hessNormal F x = fderiv ℝ (fun y ↦ fderiv ℝ G y) x (∇ G x) (∇ G x) := by
  rw [hessNormal, h.gradient_eq hx hU hxU hG hu]
  exact congrArg (fun T ↦ T (∇ G x) (∇ G x)) (h.fderiv_fderiv_eq hx hU hxU hG hu)

theorem laplacian_eq_zero {x : E n} (hx : x ∈ W ∩ C.D) : Δ F x = 0 := by
  obtain ⟨U, hU, hxU, G, hG, hu, -, -, hΔ⟩ :=
    C.chart x ⟨subset_closure hx.2, Set.disjoint_left.1 h.disjoint_sing hx.1⟩
  have hFu : F =ᶠ[𝓝 x] C.u := (h.chart.eventuallyEq_of_mem hx.1 hx.2).symm
  have hGu : G =ᶠ[𝓝 x] C.u := by
    filter_upwards [hU.mem_nhds hxU, C.isOpen_D.mem_nhds hx.2] with y hyU hyD
    exact C.eq_of_mem_D hu hyU hyD
  have hGx : 0 < G x := by
    rw [C.eq_of_mem_D hu hxU hx.2]; exact C.D_subset_pos hx.2
  rw [(InnerProductSpace.laplacian_congr_nhds (hFu.trans hGu.symm)).self_of_nhds]
  exact hΔ x hxU hGx

theorem divergence_gradient_eq_zero {x : E n} (hx : x ∈ W ∩ closure C.D) :
    divergence (∇ F) x = 0 := by
  have hc : Continuous (divergence (∇ F)) :=
    continuous_divergence ((contDiff_gradient_of_contDiff h.contDiff).of_le one_le_infty)
  have hsub : W ∩ C.D ⊆ {y | divergence (∇ F) y = 0} := fun y hy ↦ by
    change divergence (∇ F) y = 0
    rw [divergence_gradient]; exact h.laplacian_eq_zero hy
  have hcl : closure (W ∩ C.D) ⊆ {y | divergence (∇ F) y = 0} :=
    (isClosed_eq hc continuous_const).closure_subset_iff.2 hsub
  exact hcl (h.isOpen.inter_closure hx)

/-- On `W`, `{F > 0}` and `D` agree, so integrals of densities vanishing off `W` agree. -/
theorem setIntegral_pos_eq {g : E n → ℝ} (hg : ∀ x ∉ W, g x = 0) :
    ∫ x in {x | 0 < F x}, g x = ∫ x in C.D, g x := by
  have hm : MeasurableSet {x | 0 < F x} :=
    (isOpen_lt continuous_const h.contDiff.continuous).measurableSet
  rw [← integral_indicator hm, ← integral_indicator C.isOpen_D.measurableSet]
  congr 1
  funext x
  by_cases hx : x ∈ W
  · have hiff := h.chart.mem_iff x hx
    by_cases hD : x ∈ C.D
    · rw [indicator_of_mem hD, indicator_of_mem (show x ∈ {x | 0 < F x} from hiff.1 hD)]
    · rw [indicator_of_notMem hD,
        indicator_of_notMem (show x ∉ {x | 0 < F x} from fun h' ↦ hD (hiff.2 h'))]
  · simp [indicator, hg x hx]

theorem fluxFunctional_pos_eq {Q : E n → E n} (hQ : ∀ x ∉ W, divergence Q x = 0) :
    fluxFunctional {x | 0 < F x} Q = fluxFunctional C.D Q := by
  simp only [fluxFunctional, h.setIntegral_pos_eq hQ]

end ConeData.IsCollar

/-! ### Boundary values for the energy density family -/

section Boundary

variable {F φ ζ χ : E n → ℝ}

theorem paramDeriv_energyDensity (hζ : ContDiff ℝ 1 ζ) (hF : ContDiff ℝ 2 F)
    (hφ : ContDiff ℝ 2 φ) (s : ℝ) (x : E n) :
    paramDeriv (energyDensity ζ F φ) s x = energyDensityDeriv ζ F φ s x :=
  paramDeriv_eq_of_hasDerivAt
    ((contDiff_energyDensity hζ hF hφ).differentiable one_ne_zero _)
    (hasDerivAt_energyDensity ζ F φ s x)

/-- **The normal component of `∂_s V_s` vanishes on the boundary.** At a point where `χ = 1`
and `|∇F| = 1`, `⟨∂_s V_s|_{s=0}, ∇F⟩ = 0` for the Hadamard field of the energy density
`ζ(1 + |∇F_s|²)`. -/
theorem inner_paramDeriv_hadamardField_eq_zero {x₀ : E n}
    (hV : DifferentiableAt ℝ (uncurry (hadamardField F φ (energyDensity ζ F φ) χ)) (0, x₀))
    (hχ : χ x₀ = 1) (hN : ‖∇ F x₀‖ = 1) :
    ⟪paramDeriv (hadamardField F φ (energyDensity ζ F φ) χ) 0 x₀, ∇ F x₀⟫ = 0 := by
  set a := ∇ F x₀ with ha_def
  set b := ∇ φ x₀ with hb_def
  have hl : HasDerivAt (fun t : ℝ ↦ a + t • b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  have hq : HasDerivAt (fun t : ℝ ↦ ‖a + t • b‖ ^ 2) (2 * ⟪a, b⟫) 0 := by
    simpa using hl.norm_sq
  have hr : HasDerivAt (fun t : ℝ ↦ ⟪a + t • b, a⟫) ⟪b, a⟫ 0 := by
    simpa using hl.inner ℝ (hasDerivAt_const (0 : ℝ) a)
  have hq0 : ‖a + (0 : ℝ) • b‖ ^ 2 = 1 := by simp [hN]
  have hr0 : ⟪a + (0 : ℝ) • b, a⟫ = 1 := by simp [hN]
  have hf := (((hq.const_add 1).div hq (by rw [hq0]; exact one_ne_zero)).mul hr).const_mul
    (ζ x₀ * φ x₀)
  have hfun : (fun t ↦ ⟪hadamardField F φ (energyDensity ζ F φ) χ t x₀, a⟫) =
      fun t ↦ ζ x₀ * φ x₀ * ((1 + ‖a + t • b‖ ^ 2) / ‖a + t • b‖ ^ 2 * ⟪a + t • b, a⟫) := by
    funext t
    simp only [hadamardField, energyDensity, gradParam, hχ, one_smul, real_inner_smul_left]
    ring
  have hd := (hasDerivAt_paramDeriv hV).inner ℝ (hasDerivAt_const (0 : ℝ) a)
  simp only [inner_zero_right, zero_add] at hd
  rw [hfun] at hd
  rw [hd.unique hf]
  simp only [Pi.div_apply, hq0, hr0]
  rw [real_inner_comm b a]
  ring

theorem mul_eq_of_eq_one_on_tsupport {ζ φ : E n → ℝ} (hζ1 : ∀ x ∈ tsupport φ, ζ x = 1) (y : E n) :
    ζ y * φ y = φ y := by
  by_cases hy : φ y = 0
  · rw [hy, mul_zero]
  · rw [hζ1 y (subset_tsupport _ hy), one_mul]

theorem tsupport_subset_of_eq_one {ζ φ : E n → ℝ} (hζ1 : ∀ x ∈ tsupport φ, ζ x = 1) :
    tsupport φ ⊆ tsupport ζ := fun x hx ↦
  subset_tsupport _ (by rw [mem_support, hζ1 x hx]; exact one_ne_zero)

/-- **The divergence of `V_0` on the boundary.** Near a boundary point `x₀ ∈ W` the Hadamard
field at `s = 0` is `φ (1 + |∇F|⁻²) ∇F`; with `ΔF = 0` and `|∇F| = 1` at `x₀`,
`div V_0(x₀) = 2⟨∇φ, ∇F⟩ - 2 D²F(∇F, ∇F) φ`. -/
theorem ConeData.IsCollar.divergence_hadamardField_eq {C : ConeData n} {W : Set (E n)}
    (h : C.IsCollar W F) (hφ : ContDiff ℝ ∞ φ) (hζ1 : ∀ x ∈ tsupport φ, ζ x = 1) {δ : ℝ}
    (hδ : 0 < δ) (hχ : ∀ x ∈ tsupport ζ, |F x| < δ → χ x = 1) {x₀ : E n}
    (hx₀ : x₀ ∈ W ∩ closure C.D) (hF0 : F x₀ = 0) :
    divergence (hadamardField F φ (energyDensity ζ F φ) χ 0) x₀ =
      2 * ⟪∇ φ x₀, ∇ F x₀⟫ - 2 * hessNormal F x₀ * φ x₀ := by
  have hN : ‖∇ F x₀‖ = 1 := h.norm_gradient x₀ hx₀.1 hF0
  have hgF := contDiff_gradient_of_contDiff h.contDiff
  have hgc : Continuous (∇ F) := hgF.continuous
  have hO : IsOpen ({y | |F y| < δ} ∩ {y | ∇ F y ≠ 0}) :=
    (isOpen_lt (continuous_abs.comp h.contDiff.continuous) continuous_const).inter
      (isOpen_ne_fun hgc continuous_const)
  have hx₀O : x₀ ∈ {y | |F y| < δ} ∩ {y | ∇ F y ≠ 0} :=
    ⟨by simp [hF0, hδ], fun h0 ↦ by rw [h0, norm_zero] at hN; exact zero_ne_one hN⟩
  have hev : hadamardField F φ (energyDensity ζ F φ) χ 0 =ᶠ[𝓝 x₀]
      fun y ↦ (φ y * (1 + (‖∇ F y‖ ^ 2)⁻¹)) • ∇ F y := by
    filter_upwards [hO.mem_nhds hx₀O] with y hy
    have hq : ‖∇ F y‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hy.2)
    by_cases hyζ : y ∈ tsupport ζ
    · simp only [hadamardField, hχ y hyζ hy.1, one_smul, energyDensity, gradParam, zero_smul,
        add_zero]
      congr 1
      rw [show ζ y * (1 + ‖∇ F y‖ ^ 2) * φ y = (ζ y * φ y) * (1 + ‖∇ F y‖ ^ 2) by ring,
        mul_eq_of_eq_one_on_tsupport hζ1 y]
      have h1 : (1 + ‖∇ F y‖ ^ 2) / ‖∇ F y‖ ^ 2 = 1 + (‖∇ F y‖ ^ 2)⁻¹ := by
        rw [add_div, div_self hq, one_div, add_comm]
      rw [mul_div_assoc, h1]
    · have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport
        fun h' ↦ hyζ (tsupport_subset_of_eq_one hζ1 h')
      rw [hadamardField_eq_zero (M := tsupport ζ) (fun s x hx ↦ energyDensity_eq_zero hx s) 0
        hyζ, hφy, zero_mul, zero_smul]
  have hdN : HasFDerivAt (∇ F) (fderiv ℝ (∇ F) x₀) x₀ :=
    ((hgF.differentiable (by simp)) x₀).hasFDerivAt
  have hq' := hdN.norm_sq
  have hq0 : ‖∇ F x₀‖ ^ 2 ≠ 0 := by rw [hN]; norm_num
  have hinv := (hasFDerivAt_inv hq0).comp x₀ hq'
  have hg := hinv.const_add 1
  have hdφ : HasFDerivAt φ (fderiv ℝ φ x₀) x₀ :=
    ((hφ.differentiable (by simp)) x₀).hasFDerivAt
  have hprod : HasFDerivAt (fun y ↦ φ y * (1 + (‖∇ F y‖ ^ 2)⁻¹)) _ x₀ := hdφ.mul hg
  rw [divergence_eq_traceCLM, hev.fderiv_eq, ← divergence_eq_traceCLM,
    divergence_smul hprod.differentiableAt hdN.differentiableAt,
    h.divergence_gradient_eq_zero hx₀, mul_zero, zero_add, hprod.fderiv]
  have h1 : fderiv ℝ φ x₀ (∇ F x₀) = ⟪∇ φ x₀, ∇ F x₀⟫ := by
    rw [← inner_gradient_eq_fderiv, real_inner_comm]
  have h2 : ⟪∇ F x₀, fderiv ℝ (∇ F) x₀ (∇ F x₀)⟫ = hessNormal F x₀ := by
    rw [real_inner_comm, inner_fderiv_gradient]; rfl
  simp [h1, h2, hN]
  ring

end Boundary

/-! ### The second variation on a collar -/

/-- **The stability inequality on a collar.** For `φ` supported where a cut-off `ζ` (supported
in the collar `W`) equals `1`,

  `-∫_D |∇φ|² ≤ Flux_D(D²F(∇F, ∇F) φ² ∇F)`,

i.e. `Flux_D(H φ² ∇F) ≤ ∫_D |∇φ|²` with `H = -D²F(∇F, ∇F)`. Proof: `Λ''(0) ≥ 0` for
`Λ(s) = ∫_{F + sφ > 0} ζ(1 + |∇(F + sφ)|²)`, and `Λ''(0) = 2∫_D|∇φ|² + 2 Flux_D(D²F(∇F,∇F)φ²∇F)`. -/
theorem ConeData.IsCollar.neg_integral_le_flux {C : ConeData n} {W : Set (E n)} {F : E n → ℝ}
    (h : C.IsCollar W F) {φ ζ : E n → ℝ} (hφ : ContDiff ℝ ∞ φ) (hζ : ContDiff ℝ ∞ ζ)
    (hζc : HasCompactSupport ζ) (hζW : tsupport ζ ⊆ W) (hζ1 : ∀ x ∈ tsupport φ, ζ x = 1) :
    -∫ x in C.D, ‖∇ φ x‖ ^ 2 ≤
      fluxFunctional C.D (fun x ↦ (hessNormal F x * φ x ^ 2) • ∇ F x) := by
  set M := tsupport ζ with hM_def
  have hM : IsCompact M := hζc
  have hφM : tsupport φ ⊆ M := tsupport_subset_of_eq_one hζ1
  have hφc : HasCompactSupport φ := hM.of_isClosed_subset (isClosed_tsupport _) hφM
  have hMS : Disjoint M C.Sing := h.disjoint_sing.mono_left hζW
  have hF1 : ContDiff ℝ 1 F := h.contDiff.of_le one_le_infty
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le one_le_infty
  set K := energyDensity ζ F φ with hK_def
  have hK : ContDiff ℝ ∞ (uncurry K) :=
    (hζ.comp contDiff_snd).mul (contDiff_const.add ((contDiff_norm_sq ℝ).comp
      (contDiff_gradParam_infty h.contDiff hφ)))
  have hKM : ∀ s, ∀ x ∉ M, K s x = 0 := fun s x hx ↦ energyDensity_eq_zero hx s
  have hreg : ∀ x ∈ M, F x = 0 → ∇ F x ≠ 0 := fun x hx h0 h1 ↦ by
    have := h.norm_gradient x (hζW hx) h0
    rw [h1, norm_zero] at this
    exact zero_ne_one this
  have hmin : IsLocalMin (superlevelIntegral F φ K) 0 :=
    Eventually.of_forall fun s ↦ C.superlevelIntegral_energyDensity_le hF1 hφ1 hφc h.isOpen
      h.chart.eq_max (hφM.trans hζW) hζ.continuous hζc hζ1 s
  obtain ⟨χ₁, χ₂, L, s₀, δ₁, δ₂, hs₀, hδ₁, hδ₂, -, hL, hLM, hχ₁1, hχ₂1, hLeq, hV1, hV2, hR⟩ :=
    nonneg_secondVariation h.contDiff hφ hM hreg hK hKM hmin
  set V1 := hadamardField F φ K χ₁ with hV1_def
  set V2 := hadamardField F φ L χ₂ with hV2_def
  set W0 := paramDeriv V1 0 with hW0_def
  have hO : IsOpen (Ioo (-s₀) s₀ ×ˢ (univ : Set (E n))) := isOpen_Ioo.prod isOpen_univ
  have h0O : ∀ x : E n, ((0 : ℝ), x) ∈ Ioo (-s₀) s₀ ×ˢ (univ : Set (E n)) :=
    fun x ↦ ⟨⟨by linarith, hs₀⟩, mem_univ _⟩
  have hV1at : ∀ x, ContDiffAt ℝ ∞ (uncurry V1) (0, x) := fun x ↦
    hV1.contDiffAt (hO.mem_nhds (h0O x))
  have hV1d : ∀ x, DifferentiableAt ℝ (uncurry V1) (0, x) := fun x ↦
    (hV1at x).differentiableAt (by simp)
  -- `W0 = ∂_s V_s|_{s=0}` is smooth and supported in `M`
  have hW0 : ContDiff ℝ ∞ W0 :=
    (contDiffOn_paramDeriv hO hV1).comp_contDiff (contDiff_const.prodMk contDiff_id) h0O
  have hW0M : ∀ x ∉ M, W0 x = 0 := fun x hx ↦
    paramDeriv_eq_zero_of_forall (hV1d x) fun t ↦ hadamardField_eq_zero hKM t hx
  have hW0supp : tsupport W0 ⊆ M :=
    closure_minimal (fun x hx ↦ by_contra fun h' ↦ hx (hW0M x h')) hM.isClosed
  have hW0c : HasCompactSupport W0 := hM.of_isClosed_subset (isClosed_tsupport _) hW0supp
  have hV2M : tsupport (V2 0) ⊆ M := tsupport_hadamardField_subset hM.isClosed hLM 0
  have hV2c : HasCompactSupport (V2 0) := hM.of_isClosed_subset (isClosed_tsupport _) hV2M
  -- the derivative of the rate density at `s = 0`
  have hLd : ∀ x, paramDeriv L 0 x = 2 * ‖∇ φ x‖ ^ 2 - divergence W0 x := by
    intro x
    refine paramDeriv_eq_of_hasDerivAt ((hL.differentiable (by simp)) _) ?_
    have hN : HasDerivAt (fun s ↦ gradParam F φ s x) (∇ φ x) 0 := by
      simpa [gradParam] using ((hasDerivAt_id (0 : ℝ)).smul_const (∇ φ x)).const_add (∇ F x)
    have ha : HasDerivAt (fun t ↦ energyDensityDeriv ζ F φ t x)
        (ζ x * (2 * (⟪gradParam F φ 0 x, 0⟫ + ⟪∇ φ x, ∇ φ x⟫))) 0 :=
      ((hN.inner ℝ (hasDerivAt_const (0 : ℝ) (∇ φ x))).const_mul 2).const_mul (ζ x)
    rw [inner_zero_right, zero_add] at ha
    have h1 := ha.sub (hasDerivAt_divergence_param ((hV1at x).of_le (by simp)))
    have hval : ζ x * (2 * ⟪∇ φ x, ∇ φ x⟫) = 2 * ‖∇ φ x‖ ^ 2 := by
      by_cases hx : x ∈ tsupport φ
      · rw [hζ1 x hx, real_inner_self_eq_norm_sq]; ring
      · rw [gradient_eq_zero_of_notMem hx]; simp
    rw [hval] at h1
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by linarith : -s₀ < 0) hs₀] with t ht
    rw [hLeq t ht x, rateDensity,
      paramDeriv_energyDensity (hζ.of_le one_le_infty) (h.contDiff.of_le ConeData.two_le_infty)
        (hφ.of_le ConeData.two_le_infty)]
    rfl
  -- the second variation as volume and flux terms on `D`
  have hgradW : ∀ x ∉ M, ‖∇ φ x‖ ^ 2 = 0 := fun x hx ↦ by
    rw [gradient_eq_zero_of_notMem fun h' ↦ hx (hφM h'), norm_zero]; norm_num
  have hdivW0 : ∀ x ∉ M, divergence W0 x = 0 := fun x hx ↦
    divergence_of_notMem_tsupport fun h' ↦ hx (hW0supp h')
  have hi1 : Integrable fun x ↦ 2 * ‖∇ φ x‖ ^ 2 :=
    integrable_of_eq_zero_off (continuous_const.mul
      ((contDiff_gradient_of_contDiff hφ).continuous.norm.pow 2)) hM
      fun x hx ↦ by rw [hgradW x hx, mul_zero]
  have hi2 := integrable_divergence (hW0.of_le one_le_infty) hW0c
  have hRval : hadamardRate F φ (paramDeriv L) V2 0 =
      2 * (∫ x in C.D, ‖∇ φ x‖ ^ 2) + fluxFunctional C.D W0 + fluxFunctional C.D (V2 0) := by
    simp only [hadamardRate, zero_mul, add_zero, hLd]
    rw [h.setIntegral_pos_eq fun x hx ↦ by
        rw [hgradW x fun h' ↦ hx (hζW h'), hdivW0 x fun h' ↦ hx (hζW h')]; ring,
      h.fluxFunctional_pos_eq fun x hx ↦
        divergence_of_notMem_tsupport fun h' ↦ hx (hζW (hV2M h')),
      integral_sub hi1.integrableOn hi2.integrableOn, integral_const_mul]
    simp only [fluxFunctional]
    ring
  -- the flux of `∂_s V_s|_{s=0}` vanishes
  have hbdW0 : ∀ x₀ ∈ frontier C.D ∩ (tsupport W0 ∪ tsupport (0 : E n → E n)), ∀ U G,
      x₀ ∈ U → IsBoundaryChart ∞ C.D C.u U G →
      ⟪W0 x₀, ∇ G x₀⟫ = ⟪(0 : E n → E n) x₀, ∇ G x₀⟫ := by
    intro x₀ hx₀ U G hxU hG
    have hx₀M : x₀ ∈ M := by
      rcases hx₀.2 with h' | h'
      · exact hW0supp h'
      · simp at h'
    have hx₀W := hζW hx₀M
    have hF0 := h.eq_zero_of_mem_frontier hx₀.1 hx₀W
    rw [← h.gradient_eq ⟨hx₀W, hx₀.1.1⟩ hG.isOpen hxU hG.contDiffOn hG.eq_max, Pi.zero_apply,
      inner_zero_left]
    exact inner_paramDeriv_hadamardField_eq_zero (hV1d x₀)
      (hχ₁1 x₀ hx₀M (by simp [hF0, hδ₁])) (h.norm_gradient x₀ hx₀W hF0)
  have hW0flux : fluxFunctional C.D W0 = 0 := by
    rw [C.fluxFunctional_congr_boundary (hW0.of_le one_le_infty) contDiff_const hW0c
      HasCompactSupport.zero (hMS.mono_left hW0supp) (by simp) hbdW0]
    simp [fluxFunctional, divergence]
  -- the flux of the second Hadamard field
  set Q : E n → E n := fun x ↦ (hessNormal F x * φ x ^ 2) • ∇ F x with hQ_def
  have hQ : ContDiff ℝ ∞ Q := ((contDiff_hessNormal h.contDiff).mul (hφ.pow 2)).smul
    (contDiff_gradient_of_contDiff h.contDiff)
  have hQsupp : tsupport Q ⊆ tsupport φ := closure_minimal (fun x hx ↦ by_contra fun h' ↦
    hx (by simp [hQ_def, image_eq_zero_of_notMem_tsupport h'])) (isClosed_tsupport _)
  have hQc : HasCompactSupport Q := hφc.of_isClosed_subset (isClosed_tsupport _) hQsupp
  have h2Qsupp : tsupport ((2 : ℝ) • Q) ⊆ tsupport Q := closure_minimal (fun x hx ↦
    subset_tsupport _ fun h0 ↦ hx (by simp [h0])) (isClosed_tsupport _)
  have h2Qc : HasCompactSupport ((2 : ℝ) • Q) :=
    hQc.of_isClosed_subset (isClosed_tsupport _) h2Qsupp
  have hbdV2 : ∀ x₀ ∈ frontier C.D ∩ (tsupport (V2 0) ∪ tsupport ((2 : ℝ) • Q)), ∀ U G,
      x₀ ∈ U → IsBoundaryChart ∞ C.D C.u U G →
      ⟪V2 0 x₀, ∇ G x₀⟫ = ⟪((2 : ℝ) • Q) x₀, ∇ G x₀⟫ := by
    intro x₀ hx₀ U G hxU hG
    have hx₀M : x₀ ∈ M := by
      rcases hx₀.2 with h' | h'
      · exact hV2M h'
      · exact hφM (hQsupp (h2Qsupp h'))
    have hx₀W := hζW hx₀M
    have hx₀cl : x₀ ∈ W ∩ closure C.D := ⟨hx₀W, hx₀.1.1⟩
    have hF0 := h.eq_zero_of_mem_frontier hx₀.1 hx₀W
    have hN := h.norm_gradient x₀ hx₀W hF0
    rw [← h.gradient_eq hx₀cl hG.isOpen hxU hG.contDiffOn hG.eq_max]
    have hdiv := h.divergence_hadamardField_eq hφ hζ1 hδ₁ hχ₁1 hx₀cl hF0
    have hL0 : L 0 x₀ = ζ x₀ * (2 * ⟪∇ F x₀, ∇ φ x₀⟫) -
        (2 * ⟪∇ φ x₀, ∇ F x₀⟫ - 2 * hessNormal F x₀ * φ x₀) := by
      rw [hLeq 0 ⟨by linarith, hs₀⟩ x₀, rateDensity,
        paramDeriv_energyDensity (hζ.of_le one_le_infty)
          (h.contDiff.of_le ConeData.two_le_infty) (hφ.of_le ConeData.two_le_infty), ← hdiv]
      simp [energyDensityDeriv, gradParam, hK_def]
    have hnn : ⟪∇ F x₀, ∇ F x₀⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hN]; norm_num
    simp only [hV2_def, hadamardField, hχ₂1 x₀ hx₀M (by simp [hF0, hδ₂]), one_smul, gradParam,
      zero_smul, add_zero, real_inner_smul_left, hnn, hN, hL0, Pi.smul_apply, hQ_def]
    by_cases hp : φ x₀ = 0
    · simp [hp]
    · rw [hζ1 x₀ (subset_tsupport _ hp), real_inner_comm (∇ φ x₀)]; ring
  have hV2flux : fluxFunctional C.D (V2 0) = 2 * fluxFunctional C.D Q := by
    rw [C.fluxFunctional_congr_boundary hV2 ((hQ.of_le one_le_infty).const_smul (2 : ℝ)) hV2c
      h2Qc (hMS.mono_left hV2M)
      ((h.disjoint_sing.mono_left hζW).mono_left ((h2Qsupp.trans hQsupp).trans hφM)) hbdV2]
    exact fluxFunctional_smul (hQ.of_le one_le_infty) 2
  rw [hRval, hW0flux, hV2flux] at hR
  linarith

/-! ### The stability statement -/

/-- **Volume-only stability** (the frozen statement): if `⟨Y, N⟩ + H φ² ≥ 0` at every regular
boundary point of `D`, read in every chart, then `∫_D div Y ≤ ∫_D |∇φ|²`. The test is first
localized to a collar of `closure D ∩ supp φ` (which changes neither side), then
`Flux_D(Y - D²F(∇F,∇F)φ²∇F) ≥ 0` by the sign of the flux and `-∫_D|∇φ|² ≤
Flux_D(D²F(∇F,∇F)φ²∇F)` by the second variation. -/
theorem stability_flux (n : ℕ) : StabilityStatement n := by
  intro C φ Y hφ hY hφc hYc hdisj hbd
  have hφS : Disjoint (tsupport φ) C.Sing := hdisj.mono_left subset_union_left
  have hYS : Disjoint (tsupport Y) C.Sing := hdisj.mono_left subset_union_right
  obtain ⟨W, F, hW, hKW, hWS, hF, hchart, -, hnorm, hjet⟩ := C.exists_collar hφc hφS
  have h : C.IsCollar W F := ⟨hF, hchart, hWS, hnorm, hjet⟩
  -- localize the test to the collar
  obtain ⟨ζ₁, hζ₁, hζ₁c, hζ₁W, -, hζ₁1⟩ :=
    exists_smooth_cutoff (hφc.inter_right isClosed_closure) hW hKW
  set ψ : E n → ℝ := fun x ↦ ζ₁ x * φ x with hψ_def
  have hψ : ContDiff ℝ ∞ ψ := hζ₁.mul hφ
  have hψζ₁ : tsupport ψ ⊆ tsupport ζ₁ := tsupport_mul_subset_left
  have hψφ : tsupport ψ ⊆ tsupport φ := tsupport_mul_subset_right
  have hψc : HasCompactSupport ψ := hζ₁c.of_isClosed_subset (isClosed_tsupport _) hψζ₁
  obtain ⟨ζ, hζ, hζc, hζW, -, hζ1⟩ := exists_smooth_cutoff hψc hW (hψζ₁.trans hζ₁W)
  have hψeq : ∀ x ∈ closure C.D, ψ x = φ x := by
    intro x hx
    by_cases hxφ : x ∈ tsupport φ
    · simp [hψ_def, hζ₁1 x ⟨hxφ, hx⟩]
    · simp [hψ_def, image_eq_zero_of_notMem_tsupport hxφ]
  have hgrad : ∀ x ∈ C.D, ∇ ψ x = ∇ φ x := fun x hx ↦ by
    have hev : ψ =ᶠ[𝓝 x] φ := by
      filter_upwards [C.isOpen_D.mem_nhds hx] with y hy
      exact hψeq y (subset_closure hy)
    simp only [gradient, hev.fderiv_eq]
  have hmain := h.neg_integral_le_flux hψ hζ hζc hζW hζ1
  have hint : ∫ x in C.D, ‖∇ ψ x‖ ^ 2 = ∫ x in C.D, ‖∇ φ x‖ ^ 2 :=
    setIntegral_congr_fun C.isOpen_D.measurableSet fun x hx ↦ by rw [hgrad x hx]
  rw [hint] at hmain
  -- the sign of the flux of `Y - D²F(∇F,∇F) ψ² ∇F`
  set Q : E n → E n := fun x ↦ (hessNormal F x * ψ x ^ 2) • ∇ F x with hQ_def
  have hQ : ContDiff ℝ 1 Q := (((contDiff_hessNormal hF).mul (hψ.pow 2)).smul
    (contDiff_gradient_of_contDiff hF)).of_le one_le_infty
  have hQsupp : tsupport Q ⊆ tsupport ψ := closure_minimal (fun x hx ↦ by_contra fun h' ↦
    hx (by simp [hQ_def, image_eq_zero_of_notMem_tsupport h'])) (isClosed_tsupport _)
  have hQc : HasCompactSupport Q := hψc.of_isClosed_subset (isClosed_tsupport _) hQsupp
  have hsupp : tsupport (Y - Q) ⊆ tsupport φ ∪ tsupport Y := fun x hx ↦ by
    rcases tsupport_sub_subset Y Q hx with h' | h'
    · exact Or.inr h'
    · exact Or.inl (hψφ (hQsupp h'))
  have hsign := C.fluxFunctional_nonneg (Q := Y - Q) (hY.sub hQ) (hYc.sub hQc)
    (Set.disjoint_of_subset_left hsupp hdisj) fun x₀ hx₀ U G hxU hG ↦ by
      have hx₀S : x₀ ∉ C.Sing := Set.disjoint_left.1 hdisj (hsupp hx₀.2)
      have hY0 := hbd x₀ ⟨hx₀.1, hx₀S⟩ U G hG.isOpen hxU hG.contDiffOn hG.eq_max
        fun x hx hpos ↦ (hG.mem_iff x hx).2 hpos
      have hψx : ψ x₀ = φ x₀ := hψeq x₀ hx₀.1.1
      rw [Pi.sub_apply, inner_sub_left]
      by_cases hp : ψ x₀ = 0
      · rw [← hψx, hp] at hY0
        simpa [hQ_def, hp] using hY0
      · have hx₀W : x₀ ∈ W := hζ₁W (hψζ₁ (subset_tsupport _ hp))
        have hx₀cl : x₀ ∈ W ∩ closure C.D := ⟨hx₀W, hx₀.1.1⟩
        have hF0 := h.eq_zero_of_mem_frontier hx₀.1 hx₀W
        have hN := h.norm_gradient x₀ hx₀W hF0
        have hgG := h.gradient_eq hx₀cl hG.isOpen hxU hG.contDiffOn hG.eq_max
        have hhG := h.hessNormal_eq hx₀cl hG.isOpen hxU hG.contDiffOn hG.eq_max
        have hnn : ⟪∇ G x₀, ∇ G x₀⟫ = 1 := by
          rw [real_inner_self_eq_norm_sq, ← hgG, hN]; norm_num
        simp only [hQ_def, real_inner_smul_left, hgG, hnn, hhG, hψx, mul_one]
        linarith
  rw [fluxFunctional_sub hY hQ hYc hQc] at hsign
  have hdivY : fluxFunctional C.D Y = -∫ x in C.D, divergence Y x := rfl
  linarith

/-- **Stability, boundary-trace form.** For any `C¹` compactly supported field `Q` away from the
singular set with `⟨Q, N⟩ = H φ²` at the regular boundary points of `D` (read in every chart,
`N = ∇F`, `H = -D²F(N, N)`), `Flux_D(Q) ≤ ∫_D |∇φ|²`. -/
theorem stability_flux_of_boundaryTrace {C : ConeData n} {φ : E n → ℝ} {Q : E n → E n}
    (hφ : ContDiff ℝ ∞ φ) (hQ : ContDiff ℝ 1 Q) (hφc : HasCompactSupport φ)
    (hQc : HasCompactSupport Q) (hS : Disjoint (tsupport φ ∪ tsupport Q) C.Sing)
    (hbd : ∀ x₀ ∈ frontier C.D \ C.Sing, ∀ (U : Set (E n)) (G : E n → ℝ), IsOpen U → x₀ ∈ U →
      ContDiffOn ℝ ∞ G U → (∀ x ∈ U, C.u x = max (G x) 0) → (∀ x ∈ U, 0 < G x → x ∈ C.D) →
      inner ℝ (Q x₀) (∇ G x₀) = -fderiv ℝ (fun y ↦ fderiv ℝ G y) x₀ (∇ G x₀) (∇ G x₀) * φ x₀ ^ 2) :
    fluxFunctional C.D Q ≤ ∫ x in C.D, ‖∇ φ x‖ ^ 2 := by
  have hnegsupp : tsupport (-Q) = tsupport Q := tsupport_neg Q
  have h := stability_flux n C φ (-Q) hφ hQ.neg hφc hQc.neg (by rwa [hnegsupp])
    fun x₀ hx₀ U G hU hxU hG hu hD ↦ by
      rw [Pi.neg_apply, inner_neg_left, hbd x₀ hx₀ U G hU hxU hG hu hD]
      linarith
  have hneg : fluxFunctional C.D (-Q) = -fluxFunctional C.D Q := fluxFunctional_neg hQ
  have hdiv : fluxFunctional C.D (-Q) = -∫ x in C.D, divergence (-Q) x := rfl
  linarith

end OnePhaseDimension
