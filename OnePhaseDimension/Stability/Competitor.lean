/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Stability.HadamardField
public import OnePhaseDimension.Stability.Gluing
public import EllipticBernoulli.Sobolev.Lattice
public import EllipticBernoulli.Sobolev.Lipschitz
public import EllipticBernoulli.Sobolev.Uniqueness
public import EllipticBernoulli.Sobolev.Energy

/-!
# Competitors from the collar and the minimality of the superlevel energy

Let `C : ConeData n`, and let `F` be a `C¹` function with `u = max F 0` on an open set `W`. For a
`C¹` compactly supported `φ` with support in `W` and `s ∈ ℝ`, the function

  `u_s = u + (max (F + s φ) 0 - max F 0)`

equals `max (F + s φ) 0` on `W` and `u` off the support of `φ`. It is an admissible competitor
for the local energy minimality of `u` (in `H¹_loc` with weak gradient `Gu + ∇(u_s - u)`), and
its energy on a ball differs from that of `u` only on the support of `φ`, where the energy
density is `1_{F_s > 0} (1 + |∇F_s|²)`.

## Main results

* `ae_differentiableAt_of_locallyLipschitz`: Rademacher's theorem for locally Lipschitz
  functions.
* `fderiv_max_zero`: the derivative of `max G 0` at its points of differentiability.
* `memH1Loc_posPart_of_contDiff`: `max G 0 ∈ H¹_loc` with weak gradient `1_{G > 0} ∇G`.
* `ConeData.memH1Loc_competitor`: admissibility of `u_s`.
* `ConeData.energyJ_competitor_eq`: `J(u_s; B) = ∫_T 1_{F_s > 0}(1 + |∇F_s|²) + (s-independent)`.
* `ConeData.integral_energy_le`: `∫_T 1_{F > 0}(1 + |∇F|²) ≤ ∫_T 1_{F_s > 0}(1 + |∇F_s|²)` on
  `T = tsupport φ`.
* `ConeData.superlevelIntegral_le`: the same in the form of `superlevelIntegral`, with densities
  `K_s = ζ (1 + |∇F_s|²)` for a cut-off `ζ ≡ 1` on `tsupport φ`;
  `ConeData.superlevelIntegral_energyDensity_le` with `K = energyDensity ζ F φ`.

## Differences from the source

The 2026-09-24 version uses the competitor `(F + εφ)₊` in the collar, `u + εφ` inside and `u`
elsewhere, compared on a ball with nonnegative competitors. We use `u + ((F + sφ)₊ - F₊)`, which
is the same function on the collar; the energy comparison is that of the local energy minimality
of `u` with real competitors.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace
open scoped ContDiff Gradient NNReal ENNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

/-! ### Differentiability of positive parts -/

/-- Rademacher's theorem for locally Lipschitz functions on `ℝⁿ`. -/
theorem ae_differentiableAt_of_locallyLipschitz {f : E n → ℝ} (hf : LocallyLipschitz f) :
    ∀ᵐ x, DifferentiableAt ℝ f x := by
  have h : ∀ k : ℕ, ∀ᵐ x, x ∈ ball (0 : E n) k → DifferentiableAt ℝ f x := by
    intro k
    have hl := hf.locallyLipschitzOn (s := closedBall (0 : E n) k)
    obtain ⟨K, hK⟩ := hl.exists_lipschitzOnWith_of_compact (isCompact_closedBall 0 k)
    filter_upwards [(hK.mono ball_subset_closedBall).ae_differentiableWithinAt_of_mem
      (μ := volume)] with x hx hxb
    exact (hx hxb).differentiableAt (isOpen_ball.mem_nhds hxb)
  filter_upwards [ae_all_iff.2 h] with x hx
  obtain ⟨k, hk⟩ := exists_nat_gt ‖x‖
  exact hx k (mem_ball_zero_iff.2 hk)

/-- The derivative of `max G 0` at a point where `G` is differentiable: `DG` on `{G > 0}`, `0`
elsewhere (on `{G = 0}` this is the value of `fderiv`, as `max G 0` has a local minimum). -/
theorem fderiv_max_zero {G : E n → ℝ} {x : E n} (hG : DifferentiableAt ℝ G x) :
    fderiv ℝ (fun y ↦ max (G y) 0) x = if 0 < G x then fderiv ℝ G x else 0 := by
  have hc := hG.continuousAt
  split_ifs with h
  · have : (fun y ↦ max (G y) 0) =ᶠ[𝓝 x] G := by
      filter_upwards [hc.eventually (lt_mem_nhds h)] with y hy
      exact max_eq_left hy.le
    exact this.fderiv_eq
  · rcases (not_lt.1 h).lt_or_eq with hlt | heq
    · have : (fun y ↦ max (G y) 0) =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [hc.eventually (gt_mem_nhds hlt)] with y hy
        exact max_eq_right hy.le
      rw [this.fderiv_eq]
      simp
    · have hmin : IsLocalMin (fun y ↦ max (G y) 0) x :=
        Eventually.of_forall fun y ↦ by
          simp only [heq, max_self]
          exact le_max_right _ _
      exact hmin.fderiv_eq_zero

theorem gradient_max_zero {G : E n → ℝ} {x : E n} (hG : DifferentiableAt ℝ G x) :
    ∇ (fun y ↦ max (G y) 0) x = if 0 < G x then ∇ G x else 0 := by
  simp only [gradient, fderiv_max_zero hG]
  split_ifs <;> simp

theorem locallyLipschitz_max_zero {G : E n → ℝ} (hG : ContDiff ℝ 1 G) :
    LocallyLipschitz fun y ↦ max (G y) 0 :=
  hG.locallyLipschitz.max_const 0

/-- **Weak gradient of a positive part.** For `G ∈ C¹`, `max G 0 ∈ H¹_loc` with weak gradient
`1_{G > 0} ∇G`. -/
theorem memH1Loc_posPart_of_contDiff {U : Set (E n)} (hU : IsOpen U) {G : E n → ℝ}
    (hG : ContDiff ℝ 1 G) : MemH1Loc U (fun y ↦ max (G y) 0) ({y | 0 < G y}.indicator (∇ G)) :=
  memH1Loc_posPart hU (memH1Loc_gradient_of_contDiff hU hG)

/-! ### The competitor -/

/-- The perturbation `max (F + s φ) 0 - max F 0`. -/
def posPartPerturb (F φ : E n → ℝ) (s : ℝ) (x : E n) : ℝ :=
  max (F x + s * φ x) 0 - max (F x) 0

section Perturb

variable {F φ : E n → ℝ} {s : ℝ}

theorem locallyLipschitz_posPartPerturb (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ) :
    LocallyLipschitz (posPartPerturb F φ s) :=
  (locallyLipschitz_max_zero (hF.add (contDiff_const.mul hφ))).sub (locallyLipschitz_max_zero hF)

theorem posPartPerturb_of_eq_zero {x : E n} (hx : φ x = 0) : posPartPerturb F φ s x = 0 := by
  simp [posPartPerturb, hx]

theorem posPartPerturb_eventuallyEq_zero {x : E n} (hx : x ∉ tsupport φ) :
    posPartPerturb F φ s =ᶠ[𝓝 x] fun _ ↦ 0 := by
  filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
  exact posPartPerturb_of_eq_zero hy

theorem gradient_posPartPerturb_of_notMem {x : E n} (hx : x ∉ tsupport φ) :
    ∇ (posPartPerturb F φ s) x = 0 := by
  rw [(posPartPerturb_eventuallyEq_zero hx).gradient_eq]
  simp [gradient]

theorem posPartPerturb_zero : posPartPerturb F φ 0 = fun _ ↦ 0 := by
  funext x; simp [posPartPerturb]

end Perturb

namespace ConeData

variable (C : ConeData n) {W : Set (E n)} {F φ : E n → ℝ}

/-- The competitor `u_s = u + (max (F + s φ) 0 - max F 0)`. -/
def competitor (F φ : E n → ℝ) (s : ℝ) (x : E n) : ℝ := C.u x + posPartPerturb F φ s x

variable {C}

theorem competitor_eq_max (hu : ∀ x ∈ W, C.u x = max (F x) 0) {x : E n} (hx : x ∈ W) (s : ℝ) :
    C.competitor F φ s x = max (F x + s * φ x) 0 := by
  simp only [competitor, posPartPerturb, hu x hx]; ring

theorem competitor_of_notMem {x : E n} (hx : x ∉ tsupport φ) (s : ℝ) :
    C.competitor F φ s x = C.u x := by
  simp [competitor, posPartPerturb_of_eq_zero (image_eq_zero_of_notMem_tsupport hx)]

/-- **Admissibility.** `u_s ∈ H¹_loc(ℝⁿ)` with weak gradient `Gu + ∇(u_s - u)`. -/
theorem memH1Loc_competitor {Gu : E n → E n} (hGu : MemH1Loc univ C.u Gu)
    (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ) (s : ℝ) :
    MemH1Loc univ (C.competitor F φ s) fun x ↦ Gu x + ∇ (posPartPerturb F φ s) x :=
  hGu.add (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ
    (locallyLipschitz_posPartPerturb hF hφ).locallyLipschitzOn)

end ConeData

/-! ### The energy density on the support of the perturbation -/

/-- The energy density `1_{F_s > 0} (1 + |∇F_s|²)` of `max (F + s φ) 0`. -/
def collarDensity (F φ : E n → ℝ) (s : ℝ) (x : E n) : ℝ :=
  {x | 0 < F x + s * φ x}.indicator (fun x ↦ 1 + ‖∇ (fun y ↦ F y + s * φ y) x‖ ^ 2) x

section Density

variable {F φ : E n → ℝ}

theorem collarDensity_nonneg (s : ℝ) (x : E n) : 0 ≤ collarDensity F φ s x := by
  unfold collarDensity
  exact indicator_nonneg (fun _ _ ↦ by positivity) _

theorem continuous_gradient_param (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ) (s : ℝ) :
    Continuous (∇ fun y ↦ F y + s * φ y) :=
  (toDual ℝ (E n)).symm.continuous.comp
    ((hF.add (contDiff_const.mul hφ)).continuous_fderiv one_ne_zero)

theorem measurable_collarDensity (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ) (s : ℝ) :
    Measurable (collarDensity F φ s) := by
  unfold collarDensity
  refine Measurable.indicator ?_ ?_
  · exact (continuous_const.add
      ((continuous_gradient_param hF hφ s).norm.pow 2)).measurable
  · exact (isOpen_lt continuous_const
      (hF.continuous.add (continuous_const.mul hφ.continuous))).measurableSet

theorem integrableOn_collarDensity (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ) (s : ℝ)
    {T : Set (E n)} (hT : IsCompact T) : IntegrableOn (collarDensity F φ s) T := by
  have hc : Continuous fun x ↦ 1 + ‖∇ (fun y ↦ F y + s * φ y) x‖ ^ 2 :=
    continuous_const.add ((continuous_gradient_param hF hφ s).norm.pow 2)
  refine (hc.continuousOn.integrableOn_compact hT).mono'
    (measurable_collarDensity hF hφ s).aestronglyMeasurable.restrict
    (Eventually.of_forall fun x ↦ ?_)
  unfold collarDensity
  rw [Real.norm_eq_abs, abs_of_nonneg (indicator_nonneg (fun _ _ ↦ by positivity) _)]
  exact indicator_le_self' (fun _ _ ↦ by positivity) x

/-- Off the support of `φ`, the collar density does not depend on `s`. -/
theorem collarDensity_of_notMem {x : E n} (hx : x ∉ tsupport φ) (s : ℝ) :
    collarDensity F φ s x = collarDensity F φ 0 x := by
  have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hev : ∀ t : ℝ, (fun y ↦ F y + t * φ y) =ᶠ[𝓝 x] F := fun t ↦ by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
    simp [hy]
  unfold collarDensity
  simp only [indicator_apply, Set.mem_ofPred_eq, hφx, mul_zero, add_zero,
    (hev s).gradient_eq, (hev 0).gradient_eq]

theorem integrable_mul_collarDensity (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ) (s : ℝ)
    {ζ : E n → ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) :
    Integrable fun x ↦ ζ x * collarDensity F φ s x := by
  have hc : Continuous fun x ↦ |ζ x| * (1 + ‖∇ (fun y ↦ F y + s * φ y) x‖ ^ 2) :=
    hζ.abs.mul (continuous_const.add ((continuous_gradient_param hF hφ s).norm.pow 2))
  have hcc : HasCompactSupport fun x ↦ |ζ x| * (1 + ‖∇ (fun y ↦ F y + s * φ y) x‖ ^ 2) :=
    (hζc.comp_left (g := fun r : ℝ ↦ |r|) abs_zero).mul_right
  refine (hc.integrable_of_hasCompactSupport hcc).mono'
    (hζ.measurable.mul (measurable_collarDensity hF hφ s)).aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (collarDensity_nonneg s x)]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  unfold collarDensity
  exact indicator_le_self' (fun _ _ ↦ by positivity) x

/-- The superlevel integral with density `ζ (1 + |∇F_s|²)` is `∫ ζ · collarDensity`. -/
theorem superlevelIntegral_eq_integral_collarDensity (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ)
    (ζ : E n → ℝ) (s : ℝ) :
    superlevelIntegral F φ (fun s x ↦ ζ x * (1 + ‖∇ (fun y ↦ F y + s * φ y) x‖ ^ 2)) s =
      ∫ x, ζ x * collarDensity F φ s x := by
  have hmeas : MeasurableSet {x | 0 < F x + s * φ x} :=
    (isOpen_lt continuous_const
      (hF.continuous.add (continuous_const.mul hφ.continuous))).measurableSet
  unfold superlevelIntegral collarDensity
  rw [← integral_indicator hmeas]
  congr 1
  funext x
  exact indicator_mul_right _ _ _

end Density

namespace ConeData

variable {C : ConeData n} {W : Set (E n)} {F φ : E n → ℝ}

/-- On the support of `φ`, the energy density of the competitor is a.e. the collar density. -/
theorem ae_energyDensity_competitor {Gu : E n → E n} (hGu : MemH1Loc univ C.u Gu)
    (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ) (hW : IsOpen W)
    (hu : ∀ x ∈ W, C.u x = max (F x) 0) (hφW : tsupport φ ⊆ W) (B : Set (E n))
    (hTB : tsupport φ ⊆ B) (s : ℝ) :
    ∀ᵐ x, x ∈ tsupport φ →
      ‖Gu x + ∇ (posPartPerturb F φ s) x‖ ^ 2 +
        (fun _ ↦ (1 : ℝ)) x ^ 2 * (posSet (C.competitor F φ s) B).indicator 1 x =
      collarDensity F φ s x := by
  set m : E n → ℝ := fun y ↦ max (F y) 0 with hm_def
  have hm : LocallyLipschitz m := locallyLipschitz_max_zero hF
  have hw : LocallyLipschitz (posPartPerturb F φ s) := locallyLipschitz_posPartPerturb hF hφ
  have hGm : ∀ᵐ x ∂(volume.restrict W), Gu x = ∇ m x :=
    hGu.1.ae_eq_of_eqOn isOpen_univ hW (subset_univ _)
      (memH1Loc_gradient_of_locallyLipschitzOn isOpen_univ hm.locallyLipschitzOn).1 hu
  rw [ae_restrict_iff' hW.measurableSet] at hGm
  filter_upwards [hGm, ae_differentiableAt_of_locallyLipschitz hm,
    ae_differentiableAt_of_locallyLipschitz hw]
    with x hGx hmx hwx hxT
  have hxW := hφW hxT
  have hGs : DifferentiableAt ℝ (fun y ↦ F y + s * φ y) x :=
    ((hF.add (contDiff_const.mul hφ)).differentiable one_ne_zero) x
  -- the gradient of the competitor
  have hsum : (fun y ↦ max (F y + s * φ y) 0) = fun y ↦ m y + posPartPerturb F φ s y := by
    funext y; simp [hm_def, posPartPerturb]
  have hgrad : Gu x + ∇ (posPartPerturb F φ s) x =
      if 0 < F x + s * φ x then ∇ (fun y ↦ F y + s * φ y) x else 0 := by
    rw [hGx hxW, ← gradient_max_zero (G := fun y ↦ F y + s * φ y) hGs, hsum]
    simp only [gradient]
    rw [fderiv_fun_add hmx hwx, map_add]
  have hpos : x ∈ posSet (C.competitor F φ s) B ↔ 0 < F x + s * φ x := by
    simp only [posSet, mem_ofPred_eq, competitor_eq_max hu hxW]
    constructor
    · rintro ⟨-, h⟩
      by_contra hle
      rw [max_eq_right (not_lt.1 hle)] at h
      exact lt_irrefl _ h
    · intro h
      exact ⟨hTB hxT, lt_max_of_lt_left h⟩
  unfold collarDensity
  rw [hgrad]
  by_cases h : 0 < F x + s * φ x
  · rw [ite_eq_left h, indicator_of_mem (hpos.2 h),
      indicator_of_mem (show x ∈ {x | 0 < F x + s * φ x} from h)]
    simp only [Pi.one_apply]
    ring
  · rw [ite_eq_right h, indicator_of_notMem (fun h' ↦ h (hpos.1 h')),
      indicator_of_notMem (show x ∉ {x | 0 < F x + s * φ x} from h)]
    simp

/-- **Energy of the competitor.** On a measurable set `B ⊇ tsupport φ`,
`J(u_s; B) = ∫_T 1_{F_s > 0}(1 + |∇F_s|²) + ∫_{B \ T} (|Gu|² + 1_{u > 0})`, `T = tsupport φ`;
the second term does not depend on `s`. -/
theorem energyJ_competitor_eq {Gu : E n → E n} (hGu : MemH1Loc univ C.u Gu)
    (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hW : IsOpen W)
    (hu : ∀ x ∈ W, C.u x = max (F x) 0) (hφW : tsupport φ ⊆ W) {B : Set (E n)}
    (hB : MeasurableSet B) (hTB : tsupport φ ⊆ B) (s : ℝ) :
    energyJ B (fun _ ↦ 1) (C.competitor F φ s) (fun x ↦ Gu x + ∇ (posPartPerturb F φ s) x) =
      ENNReal.ofReal (∫ x in tsupport φ, collarDensity F φ s x) +
        ∫⁻ x in B \ tsupport φ, ENNReal.ofReal
          (‖Gu x‖ ^ 2 + (fun _ ↦ (1 : ℝ)) x ^ 2 * (posSet C.u B).indicator 1 x) := by
  set T := tsupport φ with hT_def
  have hTc : IsCompact T := hφc
  have hTm : MeasurableSet T := (isClosed_tsupport φ).measurableSet
  unfold energyJ
  rw [← lintegral_inter_add_sdiff _ B hTm, inter_eq_right.2 hTB]
  congr 1
  · rw [ofReal_integral_eq_lintegral_ofReal (integrableOn_collarDensity hF hφ s hTc)
      (Eventually.of_forall fun x ↦ collarDensity_nonneg s x)]
    refine setLIntegral_congr_fun_ae hTm ?_
    filter_upwards [ae_energyDensity_competitor hGu hF hφ hW hu hφW B hTB s] with x hx hxT
    rw [hx hxT]
  · refine setLIntegral_congr_fun (hB.diff hTm) fun x hx ↦ ?_
    have h1 : ∇ (posPartPerturb F φ s) x = 0 := gradient_posPartPerturb_of_notMem hx.2
    have h2 : (posSet (C.competitor F φ s) B).indicator (1 : E n → ℝ) x =
        (posSet C.u B).indicator 1 x := by
      have hc := competitor_of_notMem (C := C) (F := F) hx.2 s
      have hiff : x ∈ posSet (C.competitor F φ s) B ↔ x ∈ posSet C.u B :=
        ⟨fun h ↦ ⟨h.1, hc ▸ h.2⟩, fun h ↦ ⟨h.1, hc.symm ▸ h.2⟩⟩
      by_cases h : x ∈ posSet C.u B
      · rw [indicator_of_mem (hiff.2 h), indicator_of_mem h]
      · rw [indicator_of_notMem (fun h' ↦ h (hiff.1 h')), indicator_of_notMem h]
    simp only [h1, h2, add_zero]

/-- **Minimality of the collar energy.** For every `s`,
`∫_T 1_{F > 0}(1 + |∇F|²) ≤ ∫_T 1_{F_s > 0}(1 + |∇F_s|²)` on `T = tsupport φ`. -/
theorem integral_energy_le (C : ConeData n) (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hW : IsOpen W) (hu : ∀ x ∈ W, C.u x = max (F x) 0)
    (hφW : tsupport φ ⊆ W) (s : ℝ) :
    ∫ x in tsupport φ, collarDensity F φ 0 x ≤ ∫ x in tsupport φ, collarDensity F φ s x := by
  obtain ⟨Gu, hGu, hmin⟩ := C.minimizer
  set T := tsupport φ with hT_def
  have hTc : IsCompact T := hφc
  have hTm : MeasurableSet T := (isClosed_tsupport φ).measurableSet
  obtain ⟨R₀, hR₀⟩ := hTc.isBounded.subset_ball (0 : E n)
  set R := max R₀ 1
  have hR : T ⊆ ball 0 R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  have hR0 : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  set B := ball (0 : E n) R
  have hE := fun s ↦ energyJ_competitor_eq hGu hF hφ hφc hW hu hφW measurableSet_ball hR s
  set X := ∫⁻ x in B \ T, ENNReal.ofReal
    (‖Gu x‖ ^ 2 + (fun _ ↦ (1 : ℝ)) x ^ 2 * (posSet C.u B).indicator 1 x)
  have hadm := memH1Loc_competitor (C := C) hGu hF hφ s
  have hle := (hmin 0 R hR0 (subset_univ _)).2.2.2 (C.competitor F φ s) _ hadm
    ((ae_restrict_iff' (MeasurableSet.univ.diff measurableSet_ball)).2
      (Eventually.of_forall fun x hx ↦ competitor_of_notMem (fun h ↦ hx.2 (hR h)) s))
    (Eventually.of_forall fun _ ↦ mem_univ _)
  have h0 : C.competitor F φ 0 = C.u := by
    funext x; simp [competitor, posPartPerturb_zero]
  have hG0 : (fun x ↦ Gu x + ∇ (posPartPerturb F φ 0) x) = Gu := by
    funext x; simp [posPartPerturb_zero, gradient]
  have hE0 := hE 0
  rw [h0, hG0] at hE0
  rw [hE0, hE s] at hle
  have hJ : energyJ B (fun _ ↦ (1 : ℝ)) C.u Gu < ⊤ := by
    refine energyJ_lt_top hGu ?_ (subset_univ _) (CQ := 1) (fun _ _ ↦ by simp)
    rw [closure_ball 0 hR0.ne']; exact isCompact_closedBall 0 R
  have hfin : X ≠ ⊤ := ne_top_of_le_ne_top hJ.ne (by rw [hE0]; exact le_add_self)
  have := (ENNReal.add_le_add_iff_right hfin).1 hle
  exact (ENNReal.ofReal_le_ofReal_iff (setIntegral_nonneg hTm fun x _ ↦
    collarDensity_nonneg s x)).1 this

/-- **Minimality in Hadamard form.** For a continuous compactly supported `ζ ≡ 1` on
`tsupport φ` and `K_s = ζ (1 + |∇F_s|²)`, `Λ(0) ≤ Λ(s)` for every `s`, where
`Λ(s) = ∫_{F_s > 0} K_s` (`superlevelIntegral`). -/
theorem superlevelIntegral_le (C : ConeData n) (hF : ContDiff ℝ 1 F) (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) (hW : IsOpen W) (hu : ∀ x ∈ W, C.u x = max (F x) 0)
    (hφW : tsupport φ ⊆ W) {ζ : E n → ℝ} (hζ : Continuous ζ) (hζc : HasCompactSupport ζ)
    (hζ1 : ∀ x ∈ tsupport φ, ζ x = 1) (s : ℝ) :
    superlevelIntegral F φ (fun s x ↦ ζ x * (1 + ‖∇ (fun y ↦ F y + s * φ y) x‖ ^ 2)) 0 ≤
      superlevelIntegral F φ (fun s x ↦ ζ x * (1 + ‖∇ (fun y ↦ F y + s * φ y) x‖ ^ 2)) s := by
  set T := tsupport φ
  have hTm : MeasurableSet T := (isClosed_tsupport φ).measurableSet
  have hsplit : ∀ t, ∫ x, ζ x * collarDensity F φ t x =
      (∫ x in T, collarDensity F φ t x) + ∫ x in Tᶜ, ζ x * collarDensity F φ 0 x := by
    intro t
    rw [← integral_add_compl hTm (integrable_mul_collarDensity hF hφ t hζ hζc)]
    congr 1
    · exact setIntegral_congr_fun hTm fun x hx ↦ by rw [hζ1 x hx, one_mul]
    · exact setIntegral_congr_fun hTm.compl fun x hx ↦ by rw [collarDensity_of_notMem hx t]
  rw [superlevelIntegral_eq_integral_collarDensity hF hφ,
    superlevelIntegral_eq_integral_collarDensity hF hφ, hsplit 0, hsplit s]
  have := C.integral_energy_le hF hφ hφc hW hu hφW s
  linarith

/-- **Minimality for the energy density family.** `Λ(0) ≤ Λ(s)` for
`Λ(s) = ∫_{F_s > 0} ζ (1 + |N_s|²)` (`K = energyDensity ζ F φ`). -/
theorem superlevelIntegral_energyDensity_le (C : ConeData n) (hF : ContDiff ℝ 1 F)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hW : IsOpen W)
    (hu : ∀ x ∈ W, C.u x = max (F x) 0) (hφW : tsupport φ ⊆ W) {ζ : E n → ℝ}
    (hζ : Continuous ζ) (hζc : HasCompactSupport ζ) (hζ1 : ∀ x ∈ tsupport φ, ζ x = 1) (s : ℝ) :
    superlevelIntegral F φ (energyDensity ζ F φ) 0 ≤
      superlevelIntegral F φ (energyDensity ζ F φ) s := by
  have he : energyDensity ζ F φ =
      fun s x ↦ ζ x * (1 + ‖∇ (fun y ↦ F y + s * φ y) x‖ ^ 2) := by
    funext s x
    rw [energyDensity, gradient_param_eq ((hF.differentiable one_ne_zero) x)
      ((hφ.differentiable one_ne_zero) x)]
  rw [he]
  exact C.superlevelIntegral_le hF hφ hφc hW hu hφW hζ hζc hζ1 s

end ConeData

end OnePhaseDimension
