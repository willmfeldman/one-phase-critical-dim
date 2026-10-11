/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Stability.ConeScaling
public import EllipticBernoulli.Classical.InnerVariationCalculus

/-!
# Integration by parts on the sphere

Spherical quantities are `0`-homogeneous functions on `ℝⁿ`, and spherical integrals are taken
against `σ = volume.toSphere`. For `0`-homogeneous functions the Euclidean gradient and
Laplacian at a unit vector are the spherical ones (`Geometry/Homogeneous`), so the following are
the spherical divergence theorem and Green identities.

Let `O ⊆ ℝⁿ` be open and `K ⊆ O` compact. A cut-off on the cone over `O` (`IsConeCutoff f K O`)
is a `0`-homogeneous `f`, `C²` on the open cone `{x ≠ 0 : x̂ ∈ O}`, vanishing at the unit vectors
off `K`. For such `f` and a `0`-homogeneous `g`, `C²` on the same cone:

* `integral_sphere_divergence_eq_zero`: `∫_S div P dσ = 0` for a tangential `(-1)`-homogeneous
  field `P`, `C¹` on the cone over `O` and vanishing on the cone over the complement of `K`;
* `integral_sphere_mul_laplacian_add_inner`: `∫_S (f Δg + ⟪∇f, ∇g⟫) dσ = 0`;
* `integral_sphere_mul_laplacian_add_inner'`: `∫_S (g Δf + ⟪∇f, ∇g⟫) dσ = 0`;
* `integral_sphere_laplacian_mul`: `∫_S (Δf) g dσ = ∫_S f Δg dσ`.

## Proof

Fix a radial bump `χ` supported in `[1, 3]`. The field `Y(x) = χ(|x|) P(x)` is `C¹` with compact
support on `ℝⁿ`, so `∫ div Y = 0`. Writing `Y = a(|x|) Z` with the `0`-homogeneous tangential
field `Z(x) = |x| P(x)` and `a(r) = χ(r)/r`, `div Y(x) = χ(|x|) |x|⁻² div P(x̂)`, and polar
integration separates `∫ div Y = (∫ r^{n-3} χ) ∫_S div P dσ`. The radial factor is positive.
The Green identities follow with `P = f ∇g` and `P = g ∇f`.
-/

open Set Filter Topology MeasureTheory Metric Function
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

/-! ### Homogeneity of the gradient -/

theorem IsZeroHomogeneous.differentiableAt_smul_iff {f : E n → ℝ} (hf : IsZeroHomogeneous f)
    {r : ℝ} (hr : 0 < r) {x : E n} :
    DifferentiableAt ℝ f (r • x) ↔ DifferentiableAt ℝ f x := by
  constructor
  · intro h
    have hfun : f = fun y ↦ f (r • y) := funext fun y ↦ (hf r hr y).symm
    rw [hfun]
    exact h.comp x ((differentiableAt_id).const_smul r)
  · intro h
    have hfun : f = fun y ↦ f (r⁻¹ • y) := funext fun y ↦ (hf r⁻¹ (inv_pos.2 hr) y).symm
    rw [hfun]
    have hx : r⁻¹ • r • x = x := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    exact (hx.symm ▸ h).comp (r • x) ((differentiableAt_id).const_smul r⁻¹)

/-- The gradient of a `0`-homogeneous scalar is `(-1)`-homogeneous. -/
theorem IsZeroHomogeneous.gradient_smul {f : E n → ℝ} (hf : IsZeroHomogeneous f) {r : ℝ}
    (hr : 0 < r) (x : E n) : ∇ f (r • x) = r⁻¹ • ∇ f x := by
  by_cases hd : DifferentiableAt ℝ f (r • x)
  · have h := hf.fderiv_eq_smul_fderiv_smul hr hd
    refine ext_inner_right ℝ fun v ↦ ?_
    rw [inner_gradient_left, real_inner_smul_left, inner_gradient_left, h]
    simp [hr.ne']
  · have hd' : ¬DifferentiableAt ℝ f x := fun h ↦ hd ((hf.differentiableAt_smul_iff hr).2 h)
    simp [gradient, fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']

/-- The gradient of a `0`-homogeneous scalar is tangential everywhere. -/
theorem IsZeroHomogeneous.inner_self_gradient {f : E n → ℝ} (hf : IsZeroHomogeneous f)
    (x : E n) : ⟪x, ∇ f x⟫ = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · exact hf.inner_gradient_self hd
  · simp [gradient, fderiv_zero_of_not_differentiableAt hd]

/-! ### Vanishing on cones -/

/-- A function vanishing on the cone over the complement of a closed set `K` vanishes near every
point of that cone. -/
theorem eventuallyEq_zero_of_cone {β : Type*} [Zero β] {P : E n → β} {K : Set (E n)}
    (hK : IsClosed K) (hP : ∀ x, x ≠ 0 → radialProj x ∉ K → P x = 0) {x : E n} (hx : x ≠ 0)
    (hxK : radialProj x ∉ K) : P =ᶠ[𝓝 x] 0 := by
  filter_upwards [(isOpen_cone hK.isOpen_compl).mem_nhds ⟨hx, hxK⟩] with y hy using hP y hy.1 hy.2

/-! ### Integrability on the sphere -/

/-- A function continuous at every unit vector is integrable on the sphere. -/
theorem integrable_sphere_of_continuousAt {F : E n → ℝ}
    (hF : ∀ u ∈ sphere (0 : E n) 1, ContinuousAt F u) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ F u) (volume : Measure (E n)).toSphere := by
  have hc : Continuous fun u : sphere (0 : E n) 1 ↦ F u :=
    continuous_iff_continuousAt.2 fun u ↦ (hF u u.2).comp continuous_subtype_val.continuousAt
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The indicator of an open set of a function continuous on it is measurable on the sphere. -/
theorem measurable_sphere_indicator {s : Set (E n)} (hs : IsOpen s) {F : E n → ℝ}
    (hF : ContinuousOn F s) :
    Measurable fun u : sphere (0 : E n) 1 ↦ s.indicator F u := by
  classical
  have hs' : IsOpen ((↑) ⁻¹' s : Set (sphere (0 : E n) 1)) := hs.preimage continuous_subtype_val
  have hF' : ContinuousOn (fun u : sphere (0 : E n) 1 ↦ F u) ((↑) ⁻¹' s) :=
    hF.comp continuous_subtype_val.continuousOn fun _ h ↦ h
  have h := hF'.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hs'.measurableSet
  convert h using 1
  funext u
  simp [Set.piecewise, Set.indicator]

/-! ### A radial bump -/

/-- A smooth radial bump, equal to `1` on `[3/2, 5/2]` and supported in `[1, 3]`. -/
def radialBump : ContDiffBump (2 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

theorem radialBump_eq_zero {r : ℝ} (hr : r ≤ 1 ∨ 3 ≤ r) : radialBump r = 0 := by
  by_contra h
  have hm : r ∈ support (radialBump : ℝ → ℝ) := h
  rw [ContDiffBump.support_eq, Real.ball_eq_Ioo] at hm
  simp only [radialBump, mem_Ioo] at hm
  rcases hr with hr | hr <;> linarith [hm.1, hm.2]

theorem radialBump_pos {r : ℝ} (h1 : 1 < r) (h3 : r < 3) : 0 < radialBump r := by
  refine radialBump.nonneg.lt_of_ne fun h ↦ ?_
  have hm : r ∈ support (radialBump : ℝ → ℝ) := by
    rw [ContDiffBump.support_eq, Real.ball_eq_Ioo]
    simp only [radialBump, mem_Ioo]
    constructor <;> linarith
  exact hm h.symm

/-- The radial factor `∫₀^∞ r^{n-1} χ(r) r⁻² dr` is positive. -/
theorem integral_radialBump_pos :
    0 < ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * (radialBump r / r ^ 2) := by
  set h : ℝ → ℝ := fun r ↦ r ^ (n - 1) * (radialBump r / r ^ 2)
  have hcont : Continuous h := by
    refine continuous_iff_continuousAt.2 fun r ↦ ?_
    rcases lt_or_ge r 1 with hr | hr
    · have : h =ᶠ[𝓝 r] fun _ ↦ 0 := by
        filter_upwards [gt_mem_nhds hr] with s hs
        simp [h, radialBump_eq_zero (Or.inl hs.le)]
      exact (continuousAt_congr this).2 continuousAt_const
    · have hr0 : r ^ 2 ≠ 0 := by positivity
      exact ((continuous_pow _).continuousAt).mul
        ((radialBump.contDiff (n := 0)).continuous.continuousAt.div
          (continuous_pow 2).continuousAt hr0)
  have hsupp : support h ⊆ Icc 1 3 := by
    intro r hr
    by_contra hr'
    rw [mem_Icc, not_and_or, not_le, not_le] at hr'
    exact hr (by simp [h, radialBump_eq_zero (hr'.imp le_of_lt le_of_lt)])
  have hcs : HasCompactSupport h :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hint : IntegrableOn h (Ioi 0) := (hcont.integrable_of_hasCompactSupport hcs).integrableOn
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
  · refine lt_of_lt_of_le ?_ (measure_mono (s := Ioo (1 : ℝ) 3) fun r hr ↦ ⟨?_, ?_⟩)
    · simp
    · have hr0 : 0 < r := by linarith [hr.1]
      exact (mul_pos (pow_pos hr0 _) (div_pos (radialBump_pos hr.1 hr.2) (by positivity))).ne'
    · exact lt_trans one_pos hr.1
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact mul_nonneg (pow_nonneg (le_of_lt hr) _) (div_nonneg radialBump.nonneg (sq_nonneg r))

/-! ### The spherical divergence theorem -/

/-- **Divergence theorem on the sphere.** Let `O` be open and `K ⊆ O` compact. If `P` is
tangential, `(-1)`-homogeneous, `C¹` on the cone over `O` and zero on the cone over `Kᶜ`, then
`∫_{S^{n-1}} div P dσ = 0`. -/
theorem integral_sphere_divergence_eq_zero [NeZero n] {P : E n → E n} {K O : Set (E n)}
    (hK : IsCompact K) (hKO : K ⊆ O)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, P (r • x) = r⁻¹ • P x) (htan : ∀ x, ⟪x, P x⟫ = 0)
    (hdiff : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 1 P x)
    (hzero : ∀ x, x ≠ 0 → radialProj x ∉ K → P x = 0) :
    ∫ u : sphere (0 : E n) 1, divergence P u ∂(volume : Measure (E n)).toSphere = 0 := by
  set χ : ℝ → ℝ := ⇑radialBump
  set Y : E n → E n := fun x ↦ χ ‖x‖ • P x with hY_def
  have hP0 : P 0 = 0 := by
    have h := hhom 2 two_pos 0
    rw [smul_zero] at h
    have h2 : (1 - 2⁻¹ : ℝ) • P 0 = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (by norm_num)
  have hPev : ∀ x, x ≠ 0 → radialProj x ∉ K → P =ᶠ[𝓝 x] 0 := fun x hx hxK ↦
    eventuallyEq_zero_of_cone hK.isClosed hzero hx hxK
  have hY0 : Y =ᶠ[𝓝 0] 0 := by
    filter_upwards [ball_mem_nhds (0 : E n) one_pos] with y hy
    rw [mem_ball_zero_iff] at hy
    simp [hY_def, χ, radialBump_eq_zero (Or.inl hy.le)]
  have hYC : ContDiff ℝ 1 Y := by
    refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
    by_cases hx : x = 0
    · subst hx
      exact contDiffAt_const.congr_of_eventuallyEq hY0
    by_cases hxO : radialProj x ∈ O
    · exact ((radialBump.contDiff.contDiffAt).comp x (contDiffAt_norm ℝ hx)).smul
        (hdiff x hx hxO)
    · have hxK : radialProj x ∉ K := fun h ↦ hxO (hKO h)
      refine contDiffAt_const (c := (0 : E n)).congr_of_eventuallyEq ?_
      filter_upwards [hPev x hx hxK] with y hy
      simp [hY_def, hy]
  have hYc : HasCompactSupport Y := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : E n) 3) fun x hx ↦ ?_
    rw [mem_closedBall_zero_iff, not_le] at hx
    simp [hY_def, χ, radialBump_eq_zero (Or.inr hx.le)]
  have hdiv0 : ∫ x, divergence Y x = 0 := by
    obtain ⟨L, hL⟩ := lipschitzWith_of_locallyLipschitz_of_hasCompactSupport
      (fun x ↦ hYC.locallyLipschitz x) hYc
    exact integral_divergence_eq_zero hL hYc
  -- the pointwise formula
  set ρ : ℝ → ℝ := fun r ↦ χ r / r ^ 2 with hρ_def
  have hdivP : ∀ θ : E n, ‖θ‖ = 1 → DifferentiableAt ℝ P θ := fun θ hθ ↦ by
    have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ
    by_cases hθO : radialProj θ ∈ O
    · exact (hdiff θ hθ0 hθO).differentiableAt one_ne_zero
    · exact (differentiableAt_const (0 : E n)).congr_of_eventuallyEq
        (hPev θ hθ0 fun h ↦ hθO (hKO h))
  have hpt : ∀ x : E n, divergence Y x = ρ ‖x‖ * divergence P (radialProj x) := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [divergence_congr hY0]
      simp [divergence, ρ, χ]
    set Z : E n → E n := fun y ↦ ‖y‖ • P y with hZ_def
    set a : ℝ → ℝ := fun r ↦ χ r / r with ha_def
    have hYZ : Y = fun y ↦ a ‖y‖ • Z y := by
      funext y
      by_cases hy : y = 0
      · subst hy; simp [hY_def, hZ_def, hP0]
      have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
      simp only [hY_def, hZ_def, ha_def, smul_smul]
      congr 1
      field_simp
    have hZh : IsZeroHomogeneous Z := fun r hr y ↦ by
      simp only [hZ_def, hhom r hr y, norm_smul, Real.norm_of_nonneg hr.le, smul_smul]
      congr 1
      field_simp
    have hZt : IsTangentialField Z := fun y ↦ by
      simp [hZ_def, real_inner_smul_right, htan y]
    have hZd : DifferentiableAt ℝ Z x := by
      by_cases hxO : radialProj x ∈ O
      · exact ((contDiffAt_norm ℝ hx (n := 1)).differentiableAt one_ne_zero).smul
          ((hdiff x hx hxO).differentiableAt one_ne_zero)
      · refine (differentiableAt_const (0 : E n)).congr_of_eventuallyEq ?_
        filter_upwards [hPev x hx fun h ↦ hxO (hKO h)] with y hy
        simp [hZ_def, hy]
    have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
    have had : DifferentiableAt ℝ a ‖x‖ :=
      ((radialBump.contDiff (n := 1)).differentiable one_ne_zero _).div differentiableAt_id hn
    rw [hYZ, divergence_scaled_tangential hZh hZt hx had hZd]
    -- `div Z = div P` at the unit vector `x̂`
    set θ := radialProj x
    have hθ : ‖θ‖ = 1 := norm_radialProj hx
    have hθ0 : θ ≠ 0 := by rintro h; rw [h] at hθ; simp at hθ
    have hdZ : divergence Z θ = divergence P θ := by
      rw [hZ_def, divergence_smul ((contDiffAt_norm ℝ hθ0 (n := 1)).differentiableAt one_ne_zero)
        (hdivP θ hθ), (hasFDerivAt_norm hθ0).fderiv, hθ, radialProj_of_norm_eq_one hθ]
      simp [htan θ]
    rw [hdZ]
    simp only [ha_def, hρ_def]
    field_simp
  -- polar separation
  have hcontY : Continuous fun x ↦ divergence Y x := by
    have h := hYC.continuous_fderiv one_ne_zero
    have heq : (fun x ↦ divergence Y x) = fun x ↦ ∑ i, ⟪stdOrthonormalBasis ℝ (E n) i,
        fderiv ℝ Y x (stdOrthonormalBasis ℝ (E n) i)⟫ :=
      funext fun x ↦ divergence_eq_sum_inner _ Y x
    rw [heq]
    fun_prop
  have hcsY : HasCompactSupport fun x ↦ divergence Y x := by
    refine (hYc.fderiv ℝ).mono fun x hx ↦ ?_
    intro h
    exact hx (by simp [divergence, h])
  have hint : Integrable fun x : E n ↦ ρ ‖x‖ * divergence P (radialProj x) := by
    have := hcontY.integrable_of_hasCompactSupport (μ := volume) hcsY
    simpa only [hpt] using this
  have hsep := integral_cone_separated (isZeroHomogeneous_comp_radialProj (divergence P)) ρ hint
  have hsph : ∫ u : sphere (0 : E n) 1, divergence P (radialProj (u : E n))
      ∂(volume : Measure (E n)).toSphere =
      ∫ u : sphere (0 : E n) 1, divergence P u ∂(volume : Measure (E n)).toSphere :=
    integral_congr_ae (ae_of_all _ fun u ↦ by
      simp only [radialProj_of_norm_eq_one (norm_eq_of_mem_sphere u)])
  rw [hsph] at hsep
  have hzero' : ∫ x : E n, ρ ‖x‖ * divergence P (radialProj x) = 0 := by
    simpa only [hpt] using hdiv0
  rw [hzero'] at hsep
  have hpos : 0 < ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ρ r := integral_radialBump_pos
  exact (mul_eq_zero.1 hsep.symm).resolve_left hpos.ne'

/-! ### Cut-offs on cones and Green identities -/

/-- A cut-off on the cone over an open set `O`: a `0`-homogeneous function, `C²` on the open cone
`{x ≠ 0 : x̂ ∈ O}`, vanishing at the unit vectors off a compact set `K ⊆ O`. -/
structure IsConeCutoff (f : E n → ℝ) (K O : Set (E n)) : Prop where
  isOpen : IsOpen O
  isCompact : IsCompact K
  subset : K ⊆ O
  homog : IsZeroHomogeneous f
  contDiffAt : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 f x
  eq_zero : ∀ x ∈ sphere (0 : E n) 1, x ∉ K → f x = 0

namespace IsConeCutoff

variable {f g : E n → ℝ} {K O : Set (E n)}

theorem eq_zero_of_cone (hf : IsConeCutoff f K O) {x : E n} (hx : x ≠ 0)
    (hxK : radialProj x ∉ K) : f x = 0 := by
  rw [← hf.homog.apply_radialProj hx]
  exact hf.eq_zero _ (mem_sphere_zero_iff_norm.2 (norm_radialProj hx)) hxK

theorem eventuallyEq_zero (hf : IsConeCutoff f K O) {x : E n} (hx : x ≠ 0)
    (hxK : radialProj x ∉ K) : f =ᶠ[𝓝 x] 0 :=
  eventuallyEq_zero_of_cone hf.isCompact.isClosed (fun _ hy hyK ↦ hf.eq_zero_of_cone hy hyK) hx
    hxK

theorem gradient_eq_zero (hf : IsConeCutoff f K O) {x : E n} (hx : x ≠ 0)
    (hxK : radialProj x ∉ K) : ∇ f x = 0 := by
  rw [(hf.eventuallyEq_zero hx hxK).gradient_eq]
  simp [gradient]

theorem laplacian_eq_zero (hf : IsConeCutoff f K O) {x : E n} (hx : x ≠ 0)
    (hxK : radialProj x ∉ K) : Δ f x = 0 := by
  rw [(InnerProductSpace.laplacian_congr_nhds (hf.eventuallyEq_zero hx hxK)).self_of_nhds]
  simp [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (stdOrthonormalBasis ℝ (E n))]

/-- A product of a cut-off with a `0`-homogeneous function `C²` on the cone is a cut-off. -/
theorem mul (hf : IsConeCutoff f K O) (hg : IsZeroHomogeneous g)
    (hgd : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 g x) :
    IsConeCutoff (fun x ↦ f x * g x) K O where
  isOpen := hf.isOpen
  isCompact := hf.isCompact
  subset := hf.subset
  homog r hr x := by simp only [hf.homog r hr x, hg r hr x]
  contDiffAt x hx hxO := (hf.contDiffAt x hx hxO).mul (hgd x hx hxO)
  eq_zero x hx hxK := by simp [hf.eq_zero x hx hxK]

end IsConeCutoff

section Green

variable {f g : E n → ℝ} {K O : Set (E n)}

theorem continuousAt_laplacian_of_contDiffAt {g : E n → ℝ} {x : E n}
    (hg : ContDiffAt ℝ 2 g x) : ContinuousAt (Δ g) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (stdOrthonormalBasis ℝ (E n))]
  have h := hg.continuousAt_iteratedFDeriv (k := 2) le_rfl
  exact tendsto_finsetSum _ fun i _ ↦
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E n) ℝ _).continuous.continuousAt.comp h

theorem continuousAt_gradient_of_contDiffAt {g : E n → ℝ} {x : E n}
    (hg : ContDiffAt ℝ 2 g x) : ContinuousAt (∇ g) x :=
  (contDiffAt_gradient (n := 1) (hg.of_le (by norm_num))).continuousAt

/-- The divergence of `f ∇g` at a unit vector. -/
private theorem divergence_smul_gradient_eq (hf : IsConeCutoff f K O)
    (hgd : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 g x) {u : E n} (hu : ‖u‖ = 1) :
    divergence (fun x ↦ f x • ∇ g x) u = f u * Δ g u + ⟪∇ f u, ∇ g u⟫ := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  by_cases huO : u ∈ O
  · have huO' : radialProj u ∈ O := by rwa [radialProj_of_norm_eq_one hu]
    have hg2 := hgd u hu0 huO'
    have hDg : DifferentiableAt ℝ (fderiv ℝ g) u :=
      (hg2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [divergence_smul ((hf.contDiffAt u hu0 huO').differentiableAt (by norm_num))
      (differentiableAt_gradient hDg), divergence_gradient g u, inner_gradient_left]
  · have huK : radialProj u ∉ K := by
      rw [radialProj_of_norm_eq_one hu]; exact fun h ↦ huO (hf.subset h)
    have hev : (fun x ↦ f x • ∇ g x) =ᶠ[𝓝 u] 0 := by
      filter_upwards [hf.eventuallyEq_zero hu0 huK] with y hy
      simp [hy]
    rw [divergence_congr hev, hf.gradient_eq_zero hu0 huK,
      show f u = 0 from (hf.eventuallyEq_zero hu0 huK).self_of_nhds]
    simp [divergence]

/-- The divergence of `g ∇f` at a unit vector. -/
private theorem divergence_smul_gradient_eq' (hf : IsConeCutoff f K O)
    (hgd : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 g x) {u : E n} (hu : ‖u‖ = 1) :
    divergence (fun x ↦ g x • ∇ f x) u = g u * Δ f u + ⟪∇ f u, ∇ g u⟫ := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  by_cases huO : u ∈ O
  · have huO' : radialProj u ∈ O := by rwa [radialProj_of_norm_eq_one hu]
    have hf2 := hf.contDiffAt u hu0 huO'
    have hDf : DifferentiableAt ℝ (fderiv ℝ f) u :=
      (hf2.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [divergence_smul ((hgd u hu0 huO').differentiableAt (by norm_num))
      (differentiableAt_gradient hDf), divergence_gradient f u, ← inner_gradient_left,
      real_inner_comm (∇ f u)]
  · have huK : radialProj u ∉ K := by
      rw [radialProj_of_norm_eq_one hu]; exact fun h ↦ huO (hf.subset h)
    have hev : (fun x ↦ g x • ∇ f x) =ᶠ[𝓝 u] 0 := by
      filter_upwards [(isOpen_cone hf.isCompact.isClosed.isOpen_compl).mem_nhds
        ⟨hu0, huK⟩] with y hy
      simp [hf.gradient_eq_zero hy.1 hy.2]
    rw [divergence_congr hev, hf.gradient_eq_zero hu0 huK, hf.laplacian_eq_zero hu0 huK]
    simp [divergence]

/-- **Spherical integration by parts**, first form:
`∫_S (f Δg + ⟪∇f, ∇g⟫) dσ = 0` for a cut-off `f` on the cone over `O` and a `0`-homogeneous `g`
that is `C²` on that cone. -/
theorem integral_sphere_mul_laplacian_add_inner [NeZero n] (hf : IsConeCutoff f K O)
    (hg : IsZeroHomogeneous g) (hgd : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 g x) :
    ∫ u : sphere (0 : E n) 1, (f u * Δ g u + ⟪∇ f u, ∇ g u⟫)
      ∂(volume : Measure (E n)).toSphere = 0 := by
  have h := integral_sphere_divergence_eq_zero (P := fun x ↦ f x • ∇ g x) hf.isCompact hf.subset
    (fun r hr x ↦ by rw [hf.homog r hr x, hg.gradient_smul hr x, smul_comm])
    (fun x ↦ by rw [real_inner_smul_right, hg.inner_self_gradient x, mul_zero])
    (fun x hx hxO ↦ ((hf.contDiffAt x hx hxO).of_le (by norm_num)).smul
      (contDiffAt_gradient (n := 1) ((hgd x hx hxO).of_le (by norm_num))))
    (fun x hx hxK ↦ by simp [hf.eq_zero_of_cone hx hxK])
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun u ↦
    (divergence_smul_gradient_eq hf hgd (norm_eq_of_mem_sphere u)).symm)

/-- **Spherical integration by parts**, second form:
`∫_S (g Δf + ⟪∇f, ∇g⟫) dσ = 0` for a cut-off `f` on the cone over `O` and a `0`-homogeneous `g`
that is `C²` on that cone. -/
theorem integral_sphere_mul_laplacian_add_inner' [NeZero n] (hf : IsConeCutoff f K O)
    (hg : IsZeroHomogeneous g) (hgd : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 g x) :
    ∫ u : sphere (0 : E n) 1, (g u * Δ f u + ⟪∇ f u, ∇ g u⟫)
      ∂(volume : Measure (E n)).toSphere = 0 := by
  have h := integral_sphere_divergence_eq_zero (P := fun x ↦ g x • ∇ f x) hf.isCompact hf.subset
    (fun r hr x ↦ by rw [hg r hr x, hf.homog.gradient_smul hr x, smul_comm])
    (fun x ↦ by rw [real_inner_smul_right, hf.homog.inner_self_gradient x, mul_zero])
    (fun x hx hxO ↦ ((hgd x hx hxO).of_le (by norm_num)).smul
      (contDiffAt_gradient (n := 1) ((hf.contDiffAt x hx hxO).of_le (by norm_num))))
    (fun x hx hxK ↦ by simp [hf.gradient_eq_zero hx hxK])
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun u ↦
    (divergence_smul_gradient_eq' hf hgd (norm_eq_of_mem_sphere u)).symm)

/-- `f Δg` is integrable on the sphere. -/
theorem integrable_sphere_mul_laplacian (hf : IsConeCutoff f K O)
    (hgd : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 g x) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ f u * Δ g u) (volume : Measure (E n)).toSphere := by
  refine integrable_sphere_of_continuousAt (F := fun x ↦ f x * Δ g x) fun u hu ↦ ?_
  have hu1 := mem_sphere_zero_iff_norm.1 hu
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  by_cases huO : u ∈ O
  · have huO' : radialProj u ∈ O := by rwa [radialProj_of_norm_eq_one hu1]
    exact (hf.contDiffAt u hu0 huO').continuousAt.mul
      (continuousAt_laplacian_of_contDiffAt (hgd u hu0 huO'))
  · have huK : radialProj u ∉ K := by
      rw [radialProj_of_norm_eq_one hu1]; exact fun h ↦ huO (hf.subset h)
    refine (continuousAt_congr ?_).2 (continuousAt_const (y := (0 : ℝ)))
    filter_upwards [hf.eventuallyEq_zero hu0 huK] with y hy
    simp [hy]

/-- `g Δf` is integrable on the sphere. -/
theorem integrable_sphere_mul_laplacian' (hf : IsConeCutoff f K O)
    (hgd : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 g x) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ g u * Δ f u) (volume : Measure (E n)).toSphere := by
  refine integrable_sphere_of_continuousAt (F := fun x ↦ g x * Δ f x) fun u hu ↦ ?_
  have hu1 := mem_sphere_zero_iff_norm.1 hu
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  by_cases huO : u ∈ O
  · have huO' : radialProj u ∈ O := by rwa [radialProj_of_norm_eq_one hu1]
    exact (hgd u hu0 huO').continuousAt.mul
      (continuousAt_laplacian_of_contDiffAt (hf.contDiffAt u hu0 huO'))
  · have huK : radialProj u ∉ K := by
      rw [radialProj_of_norm_eq_one hu1]; exact fun h ↦ huO (hf.subset h)
    refine (continuousAt_congr ?_).2 (continuousAt_const (y := (0 : ℝ)))
    filter_upwards [(isOpen_cone hf.isCompact.isClosed.isOpen_compl).mem_nhds
      ⟨hu0, huK⟩] with y hy
    simp [hf.laplacian_eq_zero hy.1 hy.2]

/-- `⟪∇f, ∇g⟫` is integrable on the sphere. -/
theorem integrable_sphere_inner_gradient (hf : IsConeCutoff f K O)
    (hgd : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 g x) :
    Integrable (fun u : sphere (0 : E n) 1 ↦ ⟪∇ f u, ∇ g u⟫) (volume : Measure (E n)).toSphere := by
  refine integrable_sphere_of_continuousAt (F := fun x ↦ ⟪∇ f x, ∇ g x⟫) fun u hu ↦ ?_
  have hu1 := mem_sphere_zero_iff_norm.1 hu
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  by_cases huO : u ∈ O
  · have huO' : radialProj u ∈ O := by rwa [radialProj_of_norm_eq_one hu1]
    exact (continuousAt_gradient_of_contDiffAt (hf.contDiffAt u hu0 huO')).inner
      (continuousAt_gradient_of_contDiffAt (hgd u hu0 huO'))
  · have huK : radialProj u ∉ K := by
      rw [radialProj_of_norm_eq_one hu1]; exact fun h ↦ huO (hf.subset h)
    refine (continuousAt_congr ?_).2 (continuousAt_const (y := (0 : ℝ)))
    filter_upwards [(isOpen_cone hf.isCompact.isClosed.isOpen_compl).mem_nhds
      ⟨hu0, huK⟩] with y hy
    simp [hf.gradient_eq_zero hy.1 hy.2]

/-- **Spherical Green identity**: `∫_S (Δf) g dσ = ∫_S f Δg dσ` for a cut-off `f` on the cone
over `O` and a `0`-homogeneous `g` that is `C²` on that cone. -/
theorem integral_sphere_laplacian_mul [NeZero n] (hf : IsConeCutoff f K O)
    (hg : IsZeroHomogeneous g)
    (hgd : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 g x) :
    ∫ u : sphere (0 : E n) 1, Δ f u * g u ∂(volume : Measure (E n)).toSphere =
      ∫ u : sphere (0 : E n) 1, f u * Δ g u ∂(volume : Measure (E n)).toSphere := by
  have h1 := integral_sphere_mul_laplacian_add_inner hf hg hgd
  have h2 := integral_sphere_mul_laplacian_add_inner' hf hg hgd
  rw [integral_add (integrable_sphere_mul_laplacian hf hgd)
    (integrable_sphere_inner_gradient hf hgd)] at h1
  rw [integral_add (integrable_sphere_mul_laplacian' hf hgd)
    (integrable_sphere_inner_gradient hf hgd)] at h2
  simp_rw [mul_comm (Δ f _)]
  linarith

/-- **Spherical integration by parts**: `∫_S ⟪∇f, ∇g⟫ dσ = -∫_S f Δg dσ`. -/
theorem integral_sphere_inner_gradient [NeZero n] (hf : IsConeCutoff f K O)
    (hg : IsZeroHomogeneous g)
    (hgd : ∀ x, x ≠ 0 → radialProj x ∈ O → ContDiffAt ℝ 2 g x) :
    ∫ u : sphere (0 : E n) 1, ⟪∇ f u, ∇ g u⟫ ∂(volume : Measure (E n)).toSphere =
      -∫ u : sphere (0 : E n) 1, f u * Δ g u ∂(volume : Measure (E n)).toSphere := by
  have h1 := integral_sphere_mul_laplacian_add_inner hf hg hgd
  rw [integral_add (integrable_sphere_mul_laplacian hf hgd)
    (integrable_sphere_inner_gradient hf hgd)] at h1
  linarith

end Green

end OnePhaseDimension
