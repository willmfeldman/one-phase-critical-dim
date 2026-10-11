/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Stability.ConeScaling
public import OnePhaseDimension.Stability.Hardy

/-!
# Radial separation and the spherical comparison

Let `D` be the selected component of a cone in `ℝ⁶`, `v` a scalar and `Z` a tangential vector
field, both `0`-homogeneous on `D`, smooth near the cone over a compact set
`K ⊆ closure D ∩ S⁵ \ Sing`, and vanishing on `closure D ∩ S⁵ \ K`. Suppose that at every regular
boundary point `θ ∈ K`, read through any chart `u = max F 0`,

  `⟪Z(θ), N⟫ + H v(θ)² ≥ 0`, with `N = ∇F(θ)` and `H = -D²F(θ)(N, N)`.

Then (`spherical_comparison`)

  `∫_{S⁵ ∩ D} div Z dσ ≤ ∫_{S⁵ ∩ D} (|∇v|² + 4 v²) dσ`,

with `dσ = volume.toSphere` and the Euclidean operators evaluated at unit vectors (for
`0`-homogeneous fields these are the spherical ones).

## Proof

For a radial profile `ζ` with compact support in `(0, ∞)`, test the volume-only stability
statement with `φ(x) = ζ(|x|) v(x̂)` and `Y(x) = |x|⁻¹ ζ(|x|)² Z(x̂)`, cut off smoothly near the
cone over `K` so that both are smooth on `ℝ⁶` with compact support away from the singular set.
On `D`,

  `div Y = |x|⁻² ζ² (div Z)(x̂)`,  `|∇φ|² = ζ'² v(x̂)² + |x|⁻² ζ² |∇v(x̂)|²`,

and at boundary points `⟪Y, N⟫ + H_E φ² = |x|⁻¹ ζ² (⟪Z, N⟫ + H v²)(x̂)`, since `N` is
`0`-homogeneous and `H_E(r θ) = r⁻¹ H(θ)`. Polar integration (`volume = r⁵ dr dσ`) gives the
separated inequality (`separated_inequality`)

  `(∫ r³ ζ²) ∫ div Z ≤ (∫ r³ ζ²) ∫ |∇v|² + (∫ r⁵ ζ'²) ∫ v²`.

For each `η > 0` the logarithmic profiles give `∫ r⁵ ζ'² ≤ (4 + η) ∫ r³ ζ²`. Dividing by
`∫ r³ ζ² > 0` gives the inequality with `4 + η`, and `η → 0` afterwards.

## General dimension

The argument is written for `ℝⁿ`, `n ≥ 3` (`spherical_comparison_of_three_le`): the polar weight is
`r^{n-1} dr`, the radial factors are `∫ r^{n-3} ζ²` and `∫ r^{n-1} ζ'²`, and the constant `4` is
replaced by `β² = ((n - 2)/2)²`. The statements for `ℝ⁶` are the case `n = 6`.

## Differences from the source

The 2026-09-24 version proves `∫_{∂Ω} H v² dσ ≤ ∫_Ω (|∇v|² + 4 v²)` and later combines it with the
divergence theorem on the link. We prove the combined volume-only form above directly from the
volume-only stability statement, so no surface measure appears. The angular test is `0`-homogeneous
only on `D`; the separated tests use its values at `x̂`, which agree with it on `D`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric Function
open scoped ContDiff Gradient RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

/-! ### The combined lemma -/

/-- **Combined stability–divergence lemma.** If `⟪Y, N⟫ + H_E φ² ≥ 0` on the regular boundary,
then `∫_D div Y ≤ ∫_D |∇φ|²`. This is the volume-only stability statement. -/
theorem integral_div_le_dirichlet (C : ConeData n) {φ : E n → ℝ} {Y : E n → E n}
    (hφ : ContDiff ℝ ∞ φ) (hY : ContDiff ℝ 1 Y) (hφc : HasCompactSupport φ)
    (hYc : HasCompactSupport Y) (hS : Disjoint (tsupport φ ∪ tsupport Y) C.Sing)
    (hbd : ∀ x₀ ∈ frontier C.D \ C.Sing, ∀ (U : Set (E n)) (F : E n → ℝ), IsOpen U → x₀ ∈ U →
      ContDiffOn ℝ ∞ F U → (∀ x ∈ U, C.u x = max (F x) 0) → (∀ x ∈ U, 0 < F x → x ∈ C.D) →
      0 ≤ ⟪Y x₀, ∇ F x₀⟫ - fderiv ℝ (fun y ↦ fderiv ℝ F y) x₀ (∇ F x₀) (∇ F x₀) * φ x₀ ^ 2) :
    ∫ x in C.D, divergence Y x ≤ ∫ x in C.D, ‖∇ φ x‖ ^ 2 :=
  stability_flux n C φ Y hφ hY hφc hYc hS hbd

/-! ### The radial support of a separated test -/

/-- The set `{r θ : r ∈ tsupport ζ, θ ∈ K}`. -/
def radialSupport (ζ : ℝ → ℝ) (K : Set (E n)) : Set (E n) :=
  (fun p : ℝ × E n ↦ p.1 • p.2) '' (tsupport ζ ×ˢ K)

theorem isCompact_radialSupport {ζ : ℝ → ℝ} {K : Set (E n)} (hζ : HasCompactSupport ζ)
    (hK : IsCompact K) : IsCompact (radialSupport ζ K) :=
  (hζ.isCompact.prod hK).image (continuous_fst.smul continuous_snd)

theorem mem_radialSupport_iff {ζ : ℝ → ℝ} {K : Set (E n)} (hζ0 : tsupport ζ ⊆ Ioi 0)
    (hKs : K ⊆ sphere 0 1) {x : E n} :
    x ∈ radialSupport ζ K ↔ x ≠ 0 ∧ ‖x‖ ∈ tsupport ζ ∧ radialProj x ∈ K := by
  constructor
  · rintro ⟨⟨r, θ⟩, ⟨hr, hθ⟩, rfl⟩
    have hr0 : 0 < r := hζ0 hr
    have hθ1 : ‖θ‖ = 1 := mem_sphere_zero_iff_norm.1 (hKs hθ)
    have hθ0 : θ ≠ 0 := by rintro rfl; simp at hθ1
    refine ⟨smul_ne_zero hr0.ne' hθ0, ?_, ?_⟩
    · rw [norm_smul, hθ1, mul_one, Real.norm_of_nonneg hr0.le]; exact hr
    · rw [radialProj_smul_of_pos hr0, radialProj_of_norm_eq_one hθ1]; exact hθ
  · rintro ⟨hx, hr, hθ⟩
    exact ⟨⟨‖x‖, radialProj x⟩, ⟨hr, hθ⟩, norm_smul_radialProj hx⟩

/-! ### Admissible angular tests -/

/-- An admissible angular test on the cone `C`: a scalar `v` and a vector field `Z`, smooth on an
open set `O` containing a compact set `K ⊆ S^{n-1}` away from the singular set, `0`-homogeneous
on `D`, `Z` tangential on `D`, and both vanishing on `closure D ∩ S^{n-1} \ K`. -/
structure IsSphericalTest (C : ConeData n) (v : E n → ℝ) (Z : E n → E n) (K O : Set (E n)) :
    Prop where
  isOpen : IsOpen O
  contDiffOn_v : ContDiffOn ℝ ∞ v O
  contDiffOn_Z : ContDiffOn ℝ 1 Z O
  homog_v : ∀ r : ℝ, 0 < r → ∀ x ∈ C.D, v (r • x) = v x
  homog_Z : ∀ r : ℝ, 0 < r → ∀ x ∈ C.D, Z (r • x) = Z x
  tangential : ∀ x ∈ C.D, ⟪x, Z x⟫ = 0
  isCompact : IsCompact K
  subset_sphere : K ⊆ sphere 0 1
  subset_open : K ⊆ O
  disjoint_sing : Disjoint K C.Sing
  eq_zero : ∀ x ∈ closure C.D ∩ sphere 0 1, x ∉ K → v x = 0 ∧ Z x = 0

/-- The boundary condition `⟪Z, N⟫ + H v² ≥ 0` at the regular boundary points of `K`, read
through any chart `u = max F 0`, with `N = ∇F` and `H = -D²F(N, N)`. -/
def SphericalBoundaryCondition (C : ConeData n) (v : E n → ℝ) (Z : E n → E n) (K : Set (E n)) :
    Prop :=
  ∀ x₀ ∈ frontier C.D ∩ K, ∀ (U : Set (E n)) (F : E n → ℝ), IsOpen U → x₀ ∈ U →
    ContDiffOn ℝ ∞ F U → (∀ x ∈ U, C.u x = max (F x) 0) → (∀ x ∈ U, 0 < F x → x ∈ C.D) →
    0 ≤ ⟪Z x₀, ∇ F x₀⟫ - fderiv ℝ (fun y ↦ fderiv ℝ F y) x₀ (∇ F x₀) (∇ F x₀) * v x₀ ^ 2

theorem indicator_radialProj_of_mem_sphere (C : ConeData n) (g : E n → ℝ) {u : E n}
    (hu : ‖u‖ = 1) : C.D.indicator (fun y ↦ g (radialProj y)) u = C.D.indicator g u := by
  simp only [indicator, radialProj_of_norm_eq_one hu]

theorem integral_sphere_indicator_radialProj (C : ConeData n) (g : E n → ℝ) :
    ∫ u : sphere (0 : E n) 1, C.D.indicator (fun y ↦ g (radialProj y)) u
        ∂(volume : Measure (E n)).toSphere =
      ∫ u : sphere (0 : E n) 1, C.D.indicator g u ∂(volume : Measure (E n)).toSphere :=
  integral_congr_ae (ae_of_all _ fun u ↦
    indicator_radialProj_of_mem_sphere C g (norm_eq_of_mem_sphere u))

namespace IsSphericalTest

variable {C : ConeData n} {v : E n → ℝ} {Z : E n → E n} {K O : Set (E n)}

theorem subset_cone (hT : IsSphericalTest C v Z K O) {ζ : ℝ → ℝ} (hζ0 : tsupport ζ ⊆ Ioi 0) :
    radialSupport ζ K ⊆ {x | x ≠ 0 ∧ radialProj x ∈ O} ∩ C.Singᶜ := by
  intro x hx
  obtain ⟨hx0, -, hθ⟩ := (mem_radialSupport_iff hζ0 hT.subset_sphere).1 hx
  refine ⟨⟨hx0, hT.subset_open hθ⟩, fun hS ↦ ?_⟩
  have := C.sing_smul _ (inv_pos.2 (norm_pos_iff.2 hx0)) x hS
  exact hT.disjoint_sing.notMem_of_mem_left hθ this

/-- A cut-off equal to `1` near the radial support and supported in the open cone over `O`, away
from the singular set. -/
theorem exists_cutoff (hT : IsSphericalTest C v Z K O) {ζ : ℝ → ℝ} (hζc : HasCompactSupport ζ)
    (hζ0 : tsupport ζ ⊆ Ioi 0) :
    ∃ χ : E n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ {x | x ≠ 0 ∧ radialProj x ∈ O} ∩ C.Singᶜ ∧
      ∀ x ∈ radialSupport ζ K, χ =ᶠ[𝓝 x] 1 := by
  have hKE := isCompact_radialSupport hζc hT.isCompact
  have hU : IsOpen ({x : E n | x ≠ 0 ∧ radialProj x ∈ O} ∩ C.Singᶜ) :=
    (isOpen_cone hT.isOpen).inter C.sing_closed.isOpen_compl
  obtain ⟨δ, hδ, hδU⟩ := hKE.exists_cthickening_subset_open hU (hT.subset_cone hζ0)
  obtain ⟨χ, hχ, hχc, hχU, -, hχ1⟩ := exists_smooth_cutoff hKE.cthickening hU hδU
  refine ⟨χ, hχ, hχc, hχU, fun x hx ↦ ?_⟩
  filter_upwards [isOpen_thickening.mem_nhds (self_subset_thickening hδ _ hx)] with y hy
  exact hχ1 y (thickening_subset_cthickening _ _ hy)

/-- Off the radial support, on `D`, either the profile vanishes to first order or the angular
data vanish. -/
theorem vanish_of_notMem (hT : IsSphericalTest C v Z K O) {ζ : ℝ → ℝ}
    (hζ0 : tsupport ζ ⊆ Ioi 0) {x : E n} (hx : x ∈ C.D) (hxK : x ∉ radialSupport ζ K) :
    (ζ ‖x‖ = 0 ∧ deriv ζ ‖x‖ = 0) ∨
      (v (radialProj x) = 0 ∧ Z (radialProj x) = 0 ∧ ∇ v (radialProj x) = 0 ∧
        divergence Z (radialProj x) = 0) := by
  have hx0 := C.ne_zero_of_mem_D hx
  rw [mem_radialSupport_iff hζ0 hT.subset_sphere] at hxK
  by_cases hr : ‖x‖ ∈ tsupport ζ
  · right
    have hθK : radialProj x ∉ K := fun h ↦ hxK ⟨hx0, hr, h⟩
    have hθD := C.radialProj_mem_D hx
    have hθ1 : ‖radialProj x‖ = 1 := norm_radialProj hx0
    have hθ := hT.eq_zero _ ⟨subset_closure hθD, mem_sphere_zero_iff_norm.2 hθ1⟩ hθK
    have hθK' : radialProj (radialProj x) ∉ K := by rwa [radialProj_of_norm_eq_one hθ1]
    have hv0 := C.eventuallyEq_zero_of_radialProj_notMem hT.homog_v hT.isCompact.isClosed
      (fun y hy hyK ↦ (hT.eq_zero y hy hyK).1) hθD hθK'
    have hZ0 := C.eventuallyEq_zero_of_radialProj_notMem hT.homog_Z hT.isCompact.isClosed
      (fun y hy hyK ↦ (hT.eq_zero y hy hyK).2) hθD hθK'
    refine ⟨hθ.1, hθ.2, ?_, ?_⟩
    · rw [hv0.gradient_eq]; simp [gradient]
    · rw [divergence_congr hZ0]; simp [divergence]
  · left
    refine ⟨image_eq_zero_of_notMem_tsupport hr, ?_⟩
    by_contra h
    exact hr (support_deriv_subset h)

end IsSphericalTest

/-! ### Radial separation -/

section SeparationGeneral

variable {C : ConeData n} {v : E n → ℝ} {Z : E n → E n} {K O : Set (E n)}

/-- **Radial separation (with both identities), `ℝⁿ` with `n ≥ 3`.** Let `β = (n - 2)/2`. For a
smooth profile `ζ` with compact support in `(0, ∞)`, with `A = ∫ r^{n-3} ζ²` and
`R = ∫ r^{n-1} ζ'²`:

* `A ∫ div Z ≤ A ∫ |∇v|² + R ∫ v²`;
* `A ∫ (|∇v|² + β² v²) = A ∫ |∇v|² + β² A ∫ v²` (the spherical integrals need not be known to be
  integrable; the identity is obtained through the Euclidean integrals). -/
theorem IsSphericalTest.separated_of_three_le (hn : 3 ≤ n) (hT : IsSphericalTest C v Z K O)
    (hbd : SphericalBoundaryCondition C v Z K) {ζ : ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζc : HasCompactSupport ζ) (hζ0 : tsupport ζ ⊆ Ioi 0) :
    (∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
        ∫ u : sphere (0 : E n) 1, C.D.indicator (divergence Z) u
          ∂(volume : Measure (E n)).toSphere ≤
      (∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2) u
            ∂(volume : Measure (E n)).toSphere +
        (∫ r in Ioi (0 : ℝ), r ^ (n - 1) * deriv ζ r ^ 2) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ v x ^ 2) u
            ∂(volume : Measure (E n)).toSphere ∧
    (∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
        ∫ u : sphere (0 : E n) 1, C.D.indicator
          (fun x ↦ ‖∇ v x‖ ^ 2 + ((n - 2 : ℝ) / 2) ^ 2 * v x ^ 2) u
          ∂(volume : Measure (E n)).toSphere =
      (∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2) u
            ∂(volume : Measure (E n)).toSphere +
        ((n - 2 : ℝ) / 2) ^ 2 * ((∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ v x ^ 2) u
            ∂(volume : Measure (E n)).toSphere) := by
  have : NeZero n := ⟨by omega⟩
  have hn13 : n - 1 = n - 3 + 2 := by omega
  -- the cut-off and the separated tests
  set KE := radialSupport ζ K with hKE_def
  set O' := {x : E n | x ≠ 0 ∧ radialProj x ∈ O}
  have hO' : IsOpen O' := isOpen_cone hT.isOpen
  have hmemKE := fun x ↦ mem_radialSupport_iff (x := x) hζ0 hT.subset_sphere
  obtain ⟨χ, hχ, hχc, hχU, hχ1⟩ := hT.exists_cutoff hζc hζ0
  have hχO' : tsupport χ ⊆ O' := hχU.trans inter_subset_left
  set a : ℝ → ℝ := fun r ↦ r⁻¹ * ζ r ^ 2 with ha_def
  set φ : E n → ℝ := fun x ↦ χ x * (ζ ‖x‖ * v (radialProj x)) with hφ_def
  set Y : E n → E n := fun x ↦ χ x • (a ‖x‖ • Z (radialProj x)) with hY_def
  have hθO : ∀ x ∈ O', ContDiffAt ℝ ∞ v (radialProj x) := fun x hx ↦
    hT.contDiffOn_v.contDiffAt (hT.isOpen.mem_nhds hx.2)
  have hθO1 : ∀ x ∈ O', ContDiffAt ℝ 1 Z (radialProj x) := fun x hx ↦
    hT.contDiffOn_Z.contDiffAt (hT.isOpen.mem_nhds hx.2)
  have hva : ∀ x ∈ O', ContDiffAt ℝ ∞ (fun y ↦ v (radialProj y)) x := fun x hx ↦
    (hθO x hx).comp x (contDiffAt_radialProj_of_ne_zero hx.1)
  have hZa : ∀ x ∈ O', ContDiffAt ℝ 1 (fun y ↦ Z (radialProj y)) x := fun x hx ↦
    (hθO1 x hx).comp x (contDiffAt_radialProj_of_ne_zero hx.1)
  have hζn : ∀ x : E n, x ≠ 0 → ContDiffAt ℝ ∞ (fun y : E n ↦ ζ ‖y‖) x := fun x hx ↦
    hζ.contDiffAt.comp x (contDiffAt_norm ℝ hx)
  have haC : ∀ r : ℝ, r ≠ 0 → ContDiffAt ℝ ∞ a r := fun r hr ↦
    (contDiffAt_inv ℝ hr).mul (hζ.contDiffAt.pow 2)
  have hφ : ContDiff ℝ ∞ φ := by
    refine contDiff_mul_of_tsupport_subset hO' hχ (fun x hx ↦ ?_) hχO'
    exact ((hζn x hx.1).mul (hva x hx)).contDiffWithinAt
  have hY : ContDiff ℝ 1 Y := by
    refine contDiff_smul_of_tsupport_subset hO' (hχ.of_le (by simp)) (fun x hx ↦ ?_) hχO'
    exact ((((haC _ (norm_ne_zero_iff.2 hx.1)).comp x (contDiffAt_norm ℝ hx.1)).of_le
      (by simp)).smul (hZa x hx)).contDiffWithinAt
  have hφc : HasCompactSupport φ := hχc.mul_right
  have hYc : HasCompactSupport Y := hχc.smul_right
  have hS : Disjoint (tsupport φ ∪ tsupport Y) C.Sing := by
    refine Set.disjoint_left.2 fun x hx hxS ↦ ?_
    have hxχ : x ∈ tsupport χ := hx.elim (fun h ↦ tsupport_mul_subset_left h)
      (fun h ↦ tsupport_smul_subset_left _ _ h)
    exact (hχU hxχ).2 hxS
  -- values on the radial support and away from it
  have hχ1x : ∀ x ∈ KE, χ x = 1 := fun x hx ↦ (hχ1 x hx).self_of_nhds
  have hφA : ∀ x ∈ KE, φ =ᶠ[𝓝 x] fun y ↦ ζ ‖y‖ * v (radialProj y) := fun x hx ↦ by
    filter_upwards [hχ1 x hx] with y hy
    simp [hφ_def, hy]
  have hYA : ∀ x ∈ KE, Y =ᶠ[𝓝 x] fun y ↦ a ‖y‖ • Z (radialProj y) := fun x hx ↦ by
    filter_upwards [hχ1 x hx] with y hy
    simp [hY_def, hy]
  have hKEc : IsClosed KE := (isCompact_radialSupport hζc hT.isCompact).isClosed
  have hzero : ∀ y ∈ C.D, y ∉ KE → φ y = 0 ∧ Y y = 0 := fun y hy hyK ↦ by
    rcases hT.vanish_of_notMem hζ0 hy hyK with h | h
    · simp [hφ_def, hY_def, ha_def, h.1]
    · simp [hφ_def, hY_def, h.1, h.2.1]
  have hB : ∀ x ∈ C.D, x ∉ KE → φ =ᶠ[𝓝 x] 0 ∧ Y =ᶠ[𝓝 x] 0 := fun x hx hxK ↦ by
    have hmem : C.D ∩ KEᶜ ∈ 𝓝 x := (C.isOpen_D.inter hKEc.isOpen_compl).mem_nhds ⟨hx, hxK⟩
    exact ⟨Filter.mem_of_superset hmem fun y hy ↦ (hzero y hy.1 hy.2).1,
      Filter.mem_of_superset hmem fun y hy ↦ (hzero y hy.1 hy.2).2⟩
  -- the boundary condition
  have hbdE : ∀ x₀ ∈ frontier C.D \ C.Sing, ∀ (U : Set (E n)) (F : E n → ℝ), IsOpen U →
      x₀ ∈ U → ContDiffOn ℝ ∞ F U → (∀ x ∈ U, C.u x = max (F x) 0) →
      (∀ x ∈ U, 0 < F x → x ∈ C.D) →
      0 ≤ ⟪Y x₀, ∇ F x₀⟫ - fderiv ℝ (fun y ↦ fderiv ℝ F y) x₀ (∇ F x₀) (∇ F x₀) * φ x₀ ^ 2 := by
    intro x₀ hx₀ U F hU hx₀U hF hu hD
    have hx0 : x₀ ≠ 0 := C.ne_zero_of_notMem_sing hx₀.2
    set r := ‖x₀‖ with hr_def
    have hr : 0 < r := norm_pos_iff.2 hx0
    set θ := radialProj x₀ with hθ_def
    have hθ1 : ‖θ‖ = 1 := norm_radialProj hx0
    have hrθ : r • θ = x₀ := norm_smul_radialProj hx0
    have hθfr : θ ∈ frontier C.D := C.smul_mem_frontier_D (inv_pos.2 hr) hx₀.1
    by_cases hKx : x₀ ∈ KE
    · have hθK : θ ∈ K := ((hmemKE x₀).1 hKx).2.2
      rw [← hrθ] at hx₀U
      obtain ⟨hV, hθV, hG, hGu, hGD, hgrad, hhess⟩ := C.rescale_chart hU hF hr hu hD hx₀U
      have h := hbd θ ⟨hθfr, hθK⟩ _ _ hV hθV hG hGu hGD
      rw [hgrad, hhess, hrθ] at h
      have hφx : φ x₀ = ζ r * v θ := by simp [hφ_def, hχ1x x₀ hKx, hr_def, hθ_def]
      have hYx : Y x₀ = a r • Z θ := by simp [hY_def, hχ1x x₀ hKx, hr_def, hθ_def]
      rw [hφx, hYx, real_inner_smul_left]
      set N := ∇ F x₀
      set h2 := fderiv ℝ (fun y ↦ fderiv ℝ F y) x₀ N N
      have key : a r * ⟪Z θ, N⟫ - h2 * (ζ r * v θ) ^ 2 =
          (r⁻¹ * ζ r ^ 2) * (⟪Z θ, N⟫ - r * h2 * v θ ^ 2) := by
        simp only [ha_def]
        field_simp
      rw [key]
      exact mul_nonneg (mul_nonneg (inv_nonneg.2 hr.le) (sq_nonneg _)) h
    · have h0 : φ x₀ = 0 ∧ Y x₀ = 0 := by
        rw [hmemKE] at hKx
        by_cases hr' : r ∈ tsupport ζ
        · have hθK : θ ∉ K := fun h ↦ hKx ⟨hx0, hr', h⟩
          have := hT.eq_zero θ ⟨frontier_subset_closure hθfr, mem_sphere_zero_iff_norm.2 hθ1⟩ hθK
          simp [hφ_def, hY_def, ← hθ_def, this.1, this.2]
        · have : ζ r = 0 := image_eq_zero_of_notMem_tsupport hr'
          simp [hφ_def, hY_def, ha_def, ← hr_def, this]
      rw [h0.1, h0.2]
      simp
  have hstab := integral_div_le_dirichlet C hφ hY hφc hYc hS hbdE
  -- pointwise identities on `D`
  have hg0 : ∀ x : E n, ∇ (0 : E n → ℝ) x = 0 := fun x ↦ by simp [gradient]
  have hd0 : ∀ x : E n, divergence (0 : E n → E n) x = 0 := fun x ↦ by simp [divergence]
  have hgradφ : ∀ x ∈ C.D, ‖∇ φ x‖ ^ 2 = deriv ζ ‖x‖ ^ 2 * v (radialProj x) ^ 2 +
      ζ ‖x‖ ^ 2 * ‖x‖⁻¹ ^ 2 * ‖∇ v (radialProj x)‖ ^ 2 := by
    intro x hx
    have hx0 := C.ne_zero_of_mem_D hx
    by_cases hKx : x ∈ KE
    · have hxO : x ∈ O' := (hT.subset_cone hζ0 hKx).1
      have h := normSq_grad_radial_times_zeroHom (isZeroHomogeneous_comp_radialProj v) hx0
        ((hζ.differentiable (by simp)) ‖x‖) ((hva x hxO).differentiableAt (by simp))
      rw [(hφA x hKx).gradient_eq, h,
        (C.eventuallyEq_comp_radialProj hT.homog_v (C.radialProj_mem_D hx)).gradient_eq]
    · rw [(hB x hx hKx).1.gradient_eq, hg0]
      rcases hT.vanish_of_notMem hζ0 hx hKx with h | h
      · simp [h.1, h.2]
      · simp [h.1, h.2.2.1]
  have hdivY : ∀ x ∈ C.D, divergence Y x =
      ‖x‖⁻¹ * ζ ‖x‖ ^ 2 * ‖x‖⁻¹ * divergence Z (radialProj x) := by
    intro x hx
    have hx0 := C.ne_zero_of_mem_D hx
    have hθD := C.radialProj_mem_D hx
    by_cases hKx : x ∈ KE
    · have hxO : x ∈ O' := (hT.subset_cone hζ0 hKx).1
      have htan : ⟪x, Z (radialProj x)⟫ = 0 := by
        nth_rewrite 1 [← norm_smul_radialProj hx0]
        rw [real_inner_smul_left, hT.tangential _ hθD, mul_zero]
      rw [divergence_congr (hYA x hKx), divergence_scaled_of_inner_eq_zero
        (isZeroHomogeneous_comp_radialProj Z) hx0 htan
        ((haC _ (norm_ne_zero_iff.2 hx0)).differentiableAt (by simp))
        ((hZa x hxO).differentiableAt (by simp)),
        divergence_congr (C.eventuallyEq_comp_radialProj hT.homog_Z hθD)]
    · rw [divergence_congr (hB x hx hKx).2, hd0]
      rcases hT.vanish_of_notMem hζ0 hx hKx with h | h
      · simp [h.1]
      · simp [h.2.2.2]
  set g₁ : E n → ℝ := fun x ↦ χ x * (deriv ζ ‖x‖ * v (radialProj x)) with hg₁_def
  set g₂ : E n → ℝ := fun x ↦ χ x * (ζ ‖x‖ * ‖x‖⁻¹ * v (radialProj x)) with hg₂_def
  have hχ0 : ContDiff ℝ 0 χ := hχ.of_le (by simp)
  have hg₁ : Continuous g₁ := by
    refine (contDiff_mul_of_tsupport_subset hO' hχ0 (contDiffOn_zero.2 fun x hx ↦ ?_)
      hχO').continuous
    exact (((hζ.continuous_deriv (by simp)).comp continuous_norm).continuousAt.mul
      (hva x hx).continuousAt).continuousWithinAt
  have hg₂ : Continuous g₂ := by
    refine (contDiff_mul_of_tsupport_subset hO' hχ0 (contDiffOn_zero.2 fun x hx ↦ ?_)
      hχO').continuous
    exact (((hζn x hx.1).continuousAt.mul
      (continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.2 hx.1))).mul
      (hva x hx).continuousAt).continuousWithinAt
  have hg₁sq : ∀ x ∈ C.D, g₁ x ^ 2 = deriv ζ ‖x‖ ^ 2 * v (radialProj x) ^ 2 := by
    intro x hx
    by_cases hKx : x ∈ KE
    · simp [hg₁_def, hχ1x x hKx, mul_pow]
    · rcases hT.vanish_of_notMem hζ0 hx hKx with h | h
      · simp [hg₁_def, h.2]
      · simp [hg₁_def, h.1]
  have hg₂sq : ∀ x ∈ C.D, g₂ x ^ 2 = ζ ‖x‖ ^ 2 * ‖x‖⁻¹ ^ 2 * v (radialProj x) ^ 2 := by
    intro x hx
    by_cases hKx : x ∈ KE
    · simp [hg₂_def, hχ1x x hKx, mul_pow]
    · rcases hT.vanish_of_notMem hζ0 hx hKx with h | h
      · simp [hg₂_def, h.1]
      · simp [hg₂_def, h.1]
  -- the separated integrands
  have hms : MeasurableSet C.D := C.isOpen_D.measurableSet
  set fdiv := C.D.indicator fun y ↦ divergence Z (radialProj y) with hfdiv
  set fv := C.D.indicator fun y ↦ v (radialProj y) ^ 2 with hfv
  set fg := C.D.indicator fun y ↦ ‖∇ v (radialProj y)‖ ^ 2 with hfg
  set fc := C.D.indicator fun y ↦
    ‖∇ v (radialProj y)‖ ^ 2 + ((n - 2 : ℝ) / 2) ^ 2 * v (radialProj y) ^ 2
    with hfc
  set ρd : ℝ → ℝ := fun r ↦ r⁻¹ * ζ r ^ 2 * r⁻¹ with hρd
  set ρ₁ : ℝ → ℝ := fun r ↦ deriv ζ r ^ 2 with hρ₁
  set ρ₂ : ℝ → ℝ := fun r ↦ ζ r ^ 2 * r⁻¹ ^ 2 with hρ₂
  have Ediv : C.D.indicator (divergence Y) = fun x ↦ ρd ‖x‖ * fdiv x := funext fun x ↦ by
    by_cases hx : x ∈ C.D
    · rw [indicator_of_mem hx, hdivY x hx, hfdiv, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hfdiv, indicator_of_notMem hx, mul_zero]
  have Egrad : C.D.indicator (fun x ↦ ‖∇ φ x‖ ^ 2) =
      fun x ↦ ρ₁ ‖x‖ * fv x + ρ₂ ‖x‖ * fg x := funext fun x ↦ by
    by_cases hx : x ∈ C.D
    · rw [indicator_of_mem hx, hgradφ x hx, hfv, hfg, indicator_of_mem hx, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hfv, hfg, indicator_of_notMem hx, indicator_of_notMem hx]
      ring
  have E₁ : C.D.indicator (fun x ↦ g₁ x ^ 2) = fun x ↦ ρ₁ ‖x‖ * fv x := funext fun x ↦ by
    by_cases hx : x ∈ C.D
    · rw [indicator_of_mem hx, hg₁sq x hx, hfv, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hfv, indicator_of_notMem hx, mul_zero]
  have E₂ : C.D.indicator (fun x ↦ g₂ x ^ 2) = fun x ↦ ρ₂ ‖x‖ * fv x := funext fun x ↦ by
    by_cases hx : x ∈ C.D
    · rw [indicator_of_mem hx, hg₂sq x hx, hfv, indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hfv, indicator_of_notMem hx, mul_zero]
  have Ec : (fun x ↦ ρ₂ ‖x‖ * fc x) =
      fun x ↦ ρ₂ ‖x‖ * fg x + ((n - 2 : ℝ) / 2) ^ 2 * (ρ₂ ‖x‖ * fv x) :=
    funext fun x ↦ by
      by_cases hx : x ∈ C.D
      · rw [hfc, hfg, hfv, indicator_of_mem hx, indicator_of_mem hx, indicator_of_mem hx]
        ring
      · rw [hfc, hfg, hfv, indicator_of_notMem hx, indicator_of_notMem hx,
          indicator_of_notMem hx]
        ring
  -- integrability
  have hsq : ∀ g : E n → ℝ, Continuous g → HasCompactSupport g →
      Integrable (C.D.indicator fun x ↦ g x ^ 2) := fun g hg hgc ↦
    ((hg.pow 2).integrable_of_hasCompactSupport
      (hgc.mono fun x hx h ↦ hx (by simp [h]))).indicator hms
  have hIdiv : Integrable fun x ↦ ρd ‖x‖ * fdiv x :=
    Ediv ▸ (integrable_divergence hY hYc).indicator hms
  have hI₁ : Integrable fun x ↦ ρ₁ ‖x‖ * fv x := E₁ ▸ hsq g₁ hg₁ hχc.mul_right
  have hI₂ : Integrable fun x ↦ ρ₂ ‖x‖ * fv x := E₂ ▸ hsq g₂ hg₂ hχc.mul_right
  have hIφ : Integrable (C.D.indicator fun x ↦ ‖∇ φ x‖ ^ 2) := by
    have hc : Continuous (∇ φ) :=
      continuousOn_univ.1 (continuousOn_gradient isOpen_univ hφ.contDiffOn (by simp))
    refine ((hc.norm.pow 2).integrable_of_hasCompactSupport ?_).indicator hms
    refine hφc.mono' fun x hx ↦ ?_
    by_contra h
    exact hx (by simp [gradient_eq_zero_of_notMem h])
  have hIg : Integrable fun x ↦ ρ₂ ‖x‖ * fg x := by
    have : (fun x ↦ ρ₂ ‖x‖ * fg x) =
        fun x ↦ C.D.indicator (fun x ↦ ‖∇ φ x‖ ^ 2) x - ρ₁ ‖x‖ * fv x :=
      funext fun x ↦ by rw [Egrad]; ring
    rw [this]
    exact hIφ.sub hI₁
  -- polar separation
  have hR : ∀ ρ : ℝ → ℝ, ∀ g : E n → ℝ,
      Integrable (fun x ↦ ρ ‖x‖ * C.D.indicator (fun y ↦ g (radialProj y)) x) →
      ∫ x, ρ ‖x‖ * C.D.indicator (fun y ↦ g (radialProj y)) x =
        (∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ρ r) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator g u ∂(volume : Measure (E n)).toSphere :=
    fun ρ g hint ↦ by
      rw [integral_cone_separated (C.isZeroHomogeneous_indicator g) ρ hint,
        integral_sphere_indicator_radialProj]
  have hA₁ : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ρd r = ∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ by
      simp only [hρd]; rw [hn13, pow_add]; field_simp
  have hA₂ : ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ρ₂ r = ∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ by
      simp only [hρ₂]; rw [hn13, pow_add]; field_simp
  have Ldiv : ∫ x in C.D, divergence Y x =
      (∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
        ∫ u : sphere (0 : E n) 1, C.D.indicator (divergence Z) u
          ∂(volume : Measure (E n)).toSphere := by
    rw [← integral_indicator hms, Ediv, hR ρd (divergence Z) hIdiv, hA₁]
  have Lgrad : ∫ x in C.D, ‖∇ φ x‖ ^ 2 =
      (∫ r in Ioi (0 : ℝ), r ^ (n - 1) * deriv ζ r ^ 2) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ v x ^ 2) u
            ∂(volume : Measure (E n)).toSphere +
        (∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2) u
            ∂(volume : Measure (E n)).toSphere := by
    rw [← integral_indicator hms, Egrad, integral_add hI₁ hIg, hR ρ₁ (fun x ↦ v x ^ 2) hI₁,
      hR ρ₂ (fun x ↦ ‖∇ v x‖ ^ 2) hIg, hA₂]
  have Lc : (∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
        ∫ u : sphere (0 : E n) 1, C.D.indicator
          (fun x ↦ ‖∇ v x‖ ^ 2 + ((n - 2 : ℝ) / 2) ^ 2 * v x ^ 2) u
          ∂(volume : Measure (E n)).toSphere =
      (∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2) u
            ∂(volume : Measure (E n)).toSphere +
        ((n - 2 : ℝ) / 2) ^ 2 * ((∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ v x ^ 2) u
            ∂(volume : Measure (E n)).toSphere) := by
    have hIc : Integrable fun x ↦ ρ₂ ‖x‖ * fc x := by
      rw [Ec]; exact hIg.add (hI₂.const_mul (((n - 2 : ℝ) / 2) ^ 2))
    have h := congrArg (fun f : E n → ℝ ↦ ∫ x, f x) Ec
    rw [integral_add hIg (hI₂.const_mul (((n - 2 : ℝ) / 2) ^ 2)), integral_const_mul,
      hR ρ₂ (fun x ↦ ‖∇ v x‖ ^ 2 + ((n - 2 : ℝ) / 2) ^ 2 * v x ^ 2) hIc,
      hR ρ₂ (fun x ↦ ‖∇ v x‖ ^ 2) hIg,
      hR ρ₂ (fun x ↦ v x ^ 2) hI₂, hA₂] at h
    exact h
  refine ⟨?_, Lc⟩
  rw [← Ldiv]
  linarith [hstab, Lgrad]

/-- **Separated inequality, `ℝⁿ` with `n ≥ 3`.** For a smooth profile `ζ` with compact support in
`(0, ∞)`,

  `(∫ r^{n-3} ζ²) ∫_{S^{n-1} ∩ D} div Z ≤`
  `(∫ r^{n-3} ζ²) ∫_{S^{n-1} ∩ D} |∇v|² + (∫ r^{n-1} ζ'²) ∫_{S^{n-1} ∩ D} v²`. -/
theorem separated_inequality_of_three_le (hn : 3 ≤ n) (hT : IsSphericalTest C v Z K O)
    (hbd : SphericalBoundaryCondition C v Z K) {ζ : ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζc : HasCompactSupport ζ) (hζ0 : tsupport ζ ⊆ Ioi 0) :
    (∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
        ∫ u : sphere (0 : E n) 1, C.D.indicator (divergence Z) u
          ∂(volume : Measure (E n)).toSphere ≤
      (∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2) u
            ∂(volume : Measure (E n)).toSphere +
        (∫ r in Ioi (0 : ℝ), r ^ (n - 1) * deriv ζ r ^ 2) *
          ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ v x ^ 2) u
            ∂(volume : Measure (E n)).toSphere :=
  (hT.separated_of_three_le hn hbd hζ hζc hζ0).1

/-- **Spherical comparison in `ℝⁿ`, `n ≥ 3`.** Let `β = (n - 2)/2`. For an admissible angular
test `(v, Z)` on the cone `C` in `ℝⁿ` satisfying `⟪Z, N⟫ + H v² ≥ 0` at the regular boundary
points of its support,

  `∫_{S^{n-1} ∩ D} div Z dσ ≤ ∫_{S^{n-1} ∩ D} (|∇v|² + β² v²) dσ`.

The inequality is first obtained for each fixed radial profile (with the constant
`∫ r^{n-1} ζ'² / ∫ r^{n-3} ζ²`), and the profile is then sent along the logarithmic cutoffs
`r^{-β} ψ(log r / k)`, whose ratio tends to `β²`. -/
theorem spherical_comparison_of_three_le (hn : 3 ≤ n) (hT : IsSphericalTest C v Z K O)
    (hbd : SphericalBoundaryCondition C v Z K) :
    ∫ u : sphere (0 : E n) 1, C.D.indicator (divergence Z) u
        ∂(volume : Measure (E n)).toSphere ≤
      ∫ u : sphere (0 : E n) 1, C.D.indicator
          (fun x ↦ ‖∇ v x‖ ^ 2 + ((n - 2 : ℝ) / 2) ^ 2 * v x ^ 2) u
        ∂(volume : Measure (E n)).toSphere := by
  set Sd := ∫ u : sphere (0 : E n) 1, C.D.indicator (divergence Z) u
    ∂(volume : Measure (E n)).toSphere
  set Sg := ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2) u
    ∂(volume : Measure (E n)).toSphere
  set Sv := ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ v x ^ 2) u
    ∂(volume : Measure (E n)).toSphere
  set Sc := ∫ u : sphere (0 : E n) 1, C.D.indicator
          (fun x ↦ ‖∇ v x‖ ^ 2 + ((n - 2 : ℝ) / 2) ^ 2 * v x ^ 2) u
    ∂(volume : Measure (E n)).toSphere
  have hSv : 0 ≤ Sv :=
    integral_nonneg fun u ↦ indicator_nonneg (fun x _ ↦ sq_nonneg (v x)) _
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set η := ε / (Sv + 1) with hη_def
  have hη : 0 < η := div_pos hε (by linarith)
  -- a fixed radial profile with ratio at most `4 + η`
  obtain ⟨ζ, hζ, hζc, hζ0, hA, hR⟩ := exists_radial_profile_pow_ratio_le (n - 3) hη
  have hc : (((n - 3 : ℕ) : ℝ) + 1) / 2 = ((n - 2 : ℝ) / 2) := by
    rw [Nat.cast_sub hn]; push_cast; ring
  rw [← Nat.sub_add_comm hn, show n + 2 - 3 = n - 1 by omega, hc] at hR
  obtain ⟨h1, h2⟩ := hT.separated_of_three_le hn hbd hζ hζc hζ0
  set A := ∫ r in Ioi (0 : ℝ), r ^ (n - 3) * ζ r ^ 2
  set R := ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * deriv ζ r ^ 2
  have hRS : R * Sv ≤ (((n - 2 : ℝ) / 2) ^ 2 + η) * A * Sv := mul_le_mul_of_nonneg_right hR hSv
  have hAS : A * Sd ≤ A * (Sc + η * Sv) := by nlinarith
  have hS : Sd ≤ Sc + η * Sv := le_of_mul_le_mul_left hAS hA
  have hηS : η * Sv ≤ ε := by
    rw [hη_def, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith

end SeparationGeneral

/-! ### The case `ℝ⁶` -/

section Separation

variable {C : ConeData 6} {v : E 6 → ℝ} {Z : E 6 → E 6} {K O : Set (E 6)}

theorem six_sub_two_div_two_sq : ((((6 : ℕ) : ℝ) - 2) / 2) ^ 2 = 4 := by norm_num

/-- **Radial separation (with both identities).** For a smooth profile `ζ` with compact support in
`(0, ∞)`, with `A = ∫ r³ ζ²` and `R = ∫ r⁵ ζ'²`:

* `A ∫ div Z ≤ A ∫ |∇v|² + R ∫ v²`;
* `A ∫ (|∇v|² + 4 v²) = A ∫ |∇v|² + 4 A ∫ v²` (the spherical integrals need not be known to be
  integrable; the identity is obtained through the Euclidean integrals). -/
theorem IsSphericalTest.separated (hT : IsSphericalTest C v Z K O)
    (hbd : SphericalBoundaryCondition C v Z K) {ζ : ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζc : HasCompactSupport ζ) (hζ0 : tsupport ζ ⊆ Ioi 0) :
    (∫ r in Ioi (0 : ℝ), r ^ 3 * ζ r ^ 2) *
        ∫ u : sphere (0 : E 6) 1, C.D.indicator (divergence Z) u
          ∂(volume : Measure (E 6)).toSphere ≤
      (∫ r in Ioi (0 : ℝ), r ^ 3 * ζ r ^ 2) *
          ∫ u : sphere (0 : E 6) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2) u
            ∂(volume : Measure (E 6)).toSphere +
        (∫ r in Ioi (0 : ℝ), r ^ 5 * deriv ζ r ^ 2) *
          ∫ u : sphere (0 : E 6) 1, C.D.indicator (fun x ↦ v x ^ 2) u
            ∂(volume : Measure (E 6)).toSphere ∧
    (∫ r in Ioi (0 : ℝ), r ^ 3 * ζ r ^ 2) *
        ∫ u : sphere (0 : E 6) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2 + 4 * v x ^ 2) u
          ∂(volume : Measure (E 6)).toSphere =
      (∫ r in Ioi (0 : ℝ), r ^ 3 * ζ r ^ 2) *
          ∫ u : sphere (0 : E 6) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2) u
            ∂(volume : Measure (E 6)).toSphere +
        4 * ((∫ r in Ioi (0 : ℝ), r ^ 3 * ζ r ^ 2) *
          ∫ u : sphere (0 : E 6) 1, C.D.indicator (fun x ↦ v x ^ 2) u
            ∂(volume : Measure (E 6)).toSphere) := by
  have h := hT.separated_of_three_le (by norm_num) hbd hζ hζc hζ0
  simp only [six_sub_two_div_two_sq] at h
  exact h

/-- **Separated inequality.** For a smooth profile `ζ` with compact support in `(0, ∞)`,

  `(∫ r³ ζ²) ∫_{S⁵ ∩ D} div Z ≤ (∫ r³ ζ²) ∫_{S⁵ ∩ D} |∇v|² + (∫ r⁵ ζ'²) ∫_{S⁵ ∩ D} v²`. -/
theorem separated_inequality (hT : IsSphericalTest C v Z K O)
    (hbd : SphericalBoundaryCondition C v Z K) {ζ : ℝ → ℝ} (hζ : ContDiff ℝ ∞ ζ)
    (hζc : HasCompactSupport ζ) (hζ0 : tsupport ζ ⊆ Ioi 0) :
    (∫ r in Ioi (0 : ℝ), r ^ 3 * ζ r ^ 2) *
        ∫ u : sphere (0 : E 6) 1, C.D.indicator (divergence Z) u
          ∂(volume : Measure (E 6)).toSphere ≤
      (∫ r in Ioi (0 : ℝ), r ^ 3 * ζ r ^ 2) *
          ∫ u : sphere (0 : E 6) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2) u
            ∂(volume : Measure (E 6)).toSphere +
        (∫ r in Ioi (0 : ℝ), r ^ 5 * deriv ζ r ^ 2) *
          ∫ u : sphere (0 : E 6) 1, C.D.indicator (fun x ↦ v x ^ 2) u
            ∂(volume : Measure (E 6)).toSphere :=
  separated_inequality_of_three_le (by norm_num) hT hbd hζ hζc hζ0

/-- **Spherical comparison.** For an admissible angular test `(v, Z)` on the cone `C` in `ℝ⁶`
satisfying `⟪Z, N⟫ + H v² ≥ 0` at the regular boundary points of its support,

  `∫_{S⁵ ∩ D} div Z dσ ≤ ∫_{S⁵ ∩ D} (|∇v|² + 4 v²) dσ`.

This is `spherical_comparison_of_three_le` with `n = 6`, `β = 2`. -/
theorem spherical_comparison (hT : IsSphericalTest C v Z K O)
    (hbd : SphericalBoundaryCondition C v Z K) :
    ∫ u : sphere (0 : E 6) 1, C.D.indicator (divergence Z) u
        ∂(volume : Measure (E 6)).toSphere ≤
      ∫ u : sphere (0 : E 6) 1, C.D.indicator (fun x ↦ ‖∇ v x‖ ^ 2 + 4 * v x ^ 2) u
        ∂(volume : Measure (E 6)).toSphere := by
  have h := spherical_comparison_of_three_le (by norm_num) hT hbd
  simp only [six_sub_two_div_two_sq] at h
  exact h

end Separation

end OnePhaseDimension
