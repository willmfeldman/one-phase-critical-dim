/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Stability.Spherical
public import OnePhaseDimension.Stability.Gluing
public import OnePhaseDimension.Flux.Boundary
public import OnePhaseDimension.Flux.Bounds
public import OnePhaseDimension.Cutoff.WeightedBochner
public import OnePhaseDimension.Cutoff.SuspendedCutoff
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth cut-offs, collars and the fields near the closure of the link

This file collects the ingredients of the cut-off argument that do not involve integration.

* `cutoffProfile`: the profile `ϑ(r) = smoothTransition (r - 1)`, smooth, with values in `[0, 1]`,
  `ϑ = 0` on `(-∞, 1]`, `ϑ = 1` on `[2, ∞)`, and `|ϑ'| ≤ L` (`exists_abs_deriv_cutoffProfile_le`).
* Continuity of `w` and smoothness of `f(A, p, g)` for the fields built from a smooth function
  (`continuousAt_fluxW`, `contDiffAt_fluxF`).
* `ConeData.exists_isCollar`: the collar extension, a smooth `F` on `ℝ⁶` that is a defining
  chart of the cone on the open set `W`. The fields of `F` agree with those of `u` near points
  whose radial projection lies in `D ∩ W` (`IsCollar.fluxZ_eventuallyEq` and its companions).
* `f ≥ ε*` on `closure D` wherever `w > 0` (`ConeData.IsCollar.fluxF_ge`).

## Differences from the source

The 2026-09-24 version evaluates the fields on the regular closure of the link through the smooth
one-sided extension of `u`. We use the fields of the collar function `F` (a smooth function on the
whole space), which agree with those of `u` on `D` by locality.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric Function
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### The profile -/

/-- The cut-off profile `ϑ(r) = smoothTransition (r - 1)`: `0` for `r ≤ 1`, `1` for `r ≥ 2`. -/
def cutoffProfile (r : ℝ) : ℝ := Real.smoothTransition (r - 1)

theorem contDiff_cutoffProfile : ContDiff ℝ ∞ cutoffProfile :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)

theorem cutoffProfile_eq_zero {r : ℝ} (hr : r ≤ 1) : cutoffProfile r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoffProfile_eq_one {r : ℝ} (hr : 2 ≤ r) : cutoffProfile r = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoffProfile_nonneg (r : ℝ) : 0 ≤ cutoffProfile r := Real.smoothTransition.nonneg _

theorem cutoffProfile_le_one (r : ℝ) : cutoffProfile r ≤ 1 := Real.smoothTransition.le_one _

theorem deriv_cutoffProfile_eq_zero {r : ℝ} (hr : r < 1 ∨ 2 < r) :
    deriv cutoffProfile r = 0 := by
  rcases hr with hr | hr
  · have h : cutoffProfile =ᶠ[𝓝 r] fun _ ↦ 0 := by
      filter_upwards [Iio_mem_nhds hr] with s hs using cutoffProfile_eq_zero (le_of_lt hs)
    rw [h.deriv_eq]; simp
  · have h : cutoffProfile =ᶠ[𝓝 r] fun _ ↦ 1 := by
      filter_upwards [Ioi_mem_nhds hr] with s hs using cutoffProfile_eq_one (le_of_lt hs)
    rw [h.deriv_eq]; simp

/-- `L_ϑ = sup |ϑ'| < ∞`. -/
theorem exists_abs_deriv_cutoffProfile_le :
    ∃ L, 0 ≤ L ∧ ∀ r, |deriv cutoffProfile r| ≤ L := by
  have hc : Continuous (deriv cutoffProfile) :=
    contDiff_cutoffProfile.continuous_deriv (by simp)
  have hs : HasCompactSupport (deriv cutoffProfile) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) fun r hr ↦ ?_
    simp only [mem_Icc, not_and_or, not_le] at hr
    exact deriv_cutoffProfile_eq_zero hr
  obtain ⟨L, hL⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max L 0, le_max_right _ _, fun r ↦ (Real.norm_eq_abs _ ▸ hL r).trans (le_max_left _ _)⟩

/-! ### Continuity of the fields of a smooth function -/

namespace Gen

section FieldContinuity

variable {n : ℕ} {c : Coeffs (n - 1)} {ε δ : ℝ} {F : E n → ℝ} {x : E n}

theorem fluxW_eventuallyEq_transported (hx : x ≠ 0) :
    fluxW F =ᶠ[𝓝 x]
      fun z ↦ normW (transTData F (radialProj x) (sphereFrame (radialProj x)) z) := by
  have hy := norm_radialProj hx
  filter_upwards [eventually_transport_defined_of_ne hx] with z hz
  exact fluxW_eq_transported hy hz.1 hz.2 (inner_sphereFrame hy)

/-- `w` is continuous at `x ≠ 0` if `F` is smooth at `x/|x|`. -/
theorem continuousAt_fluxW (hx : x ≠ 0) (hF : ContDiffAt ℝ ∞ F (radialProj x)) :
    ContinuousAt (fluxW F) x := by
  obtain ⟨-, hne⟩ := (eventually_transport_defined_of_ne hx).self_of_nhds
  refine ContinuousAt.congr ?_ (fluxW_eventuallyEq_transported hx).symm
  have hT : ContinuousAt (transTData F (radialProj x) (sphereFrame (radialProj x))) x :=
    (contDiffAt_pi.2 fun i ↦ contDiffAt_pi.2 fun j ↦
      contDiffAt_transJet hF hx hne 2 _).continuousAt
  exact (contDiff_sq2.continuous.sqrt).continuousAt.comp hT

/-- `f(A, p, g)` is smooth at `x ≠ 0` with `w(x) > 0` if `F` is smooth at `x/|x|`. -/
theorem contDiffAt_fluxF (hc : CertificateHolds (n - 1) ε δ c) (hx : x ≠ 0)
    (hF : ContDiffAt ℝ ∞ F (radialProj x)) (hw : 0 < fluxW F x) :
    ContDiffAt ℝ ∞ (fluxF c F) x := by
  set y := radialProj x
  have hy := norm_radialProj hx
  have hι := inner_sphereFrame hy
  obtain ⟨-, hne⟩ := (eventually_transport_defined_of_ne hx).self_of_nhds
  have hev : fluxF c F =ᶠ[𝓝 x] fun z ↦ c.f (normalizedA (transTData F y (sphereFrame y) z),
      transPData F y (sphereFrame y) z, transG F z) := by
    filter_upwards [eventually_transport_defined_of_ne hx] with z hz
    exact fluxF_eq_transported hy hz.1 hz.2 hι hc
  rw [fluxW_eq_transported hy hx hne hι] at hw
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact hc.smooth_f.contDiffAt.comp x ((contDiffAt_normalizedData
    (d := (transTData F y (sphereFrame y) x, transBData F y (sphereFrame y) x,
      transPData F y (sphereFrame y) x, transG F x)) (normW_pos_iff.1 hw)).comp x
    (contDiffAt_transData hF hx hne))

end FieldContinuity

end Gen

section FieldContinuity

variable {c : Coeffs} {F : E 6 → ℝ} {x : E 6}

theorem fluxW_eventuallyEq_transported (hx : x ≠ 0) :
    fluxW F =ᶠ[𝓝 x]
      fun z ↦ normW (transTData F (radialProj x) (sphereFrame (radialProj x)) z) :=
  Gen.fluxW_eventuallyEq_transported hx

/-- `w` is continuous at `x ≠ 0` if `F` is smooth at `x/|x|`. -/
theorem continuousAt_fluxW (hx : x ≠ 0) (hF : ContDiffAt ℝ ∞ F (radialProj x)) :
    ContinuousAt (fluxW F) x :=
  Gen.continuousAt_fluxW hx hF

/-- `f(A, p, g)` is smooth at `x ≠ 0` with `w(x) > 0` if `F` is smooth at `x/|x|`. -/
theorem contDiffAt_fluxF (hc : CertificateHolds c) (hx : x ≠ 0)
    (hF : ContDiffAt ℝ ∞ F (radialProj x)) (hw : 0 < fluxW F x) :
    ContDiffAt ℝ ∞ (fluxF c F) x :=
  Gen.contDiffAt_fluxF hc.toGen hx hF hw

end FieldContinuity

/-- The profile `ϑ` is a cut-off profile in the sense of `IsCutoffProfile`. -/
theorem exists_isCutoffProfile_cutoffProfile : ∃ L, IsCutoffProfile cutoffProfile L := by
  obtain ⟨L, -, hL⟩ := exists_abs_deriv_cutoffProfile_le
  exact ⟨L, contDiff_cutoffProfile.differentiable (by simp), cutoffProfile_nonneg,
    cutoffProfile_le_one, fun _ hr ↦ cutoffProfile_eq_zero hr, fun _ hr ↦ cutoffProfile_eq_one hr,
    hL⟩

/-! ### The collar -/

theorem ConeData.exists_isCollar {n : ℕ} (C : ConeData n) {K : Set (E n)} (hK : IsCompact K)
    (hKS : Disjoint K C.Sing) : ∃ W F, K ∩ closure C.D ⊆ W ∧ C.IsCollar W F := by
  obtain ⟨W, F, -, hKW, hWS, hF, hch, -, hgr, hjet⟩ := C.exists_collar hK hKS
  exact ⟨W, F, hKW, ⟨hF, hch, hWS, hgr, hjet⟩⟩

namespace ConeData.IsCollar

section General

variable {n : ℕ} {C : ConeData n} {W : Set (E n)} {F : E n → ℝ} (h : C.IsCollar W F)
include h

theorem notMem_sing {x : E n} (hx : x ∈ W) : x ∉ C.Sing :=
  Set.disjoint_left.1 h.disjoint_sing hx

/-- Near a point whose radial projection lies in `D ∩ W`, the germ of `u` at the radial
projection is that of `F`. -/
theorem eventually_germ {x : E n} (hx : x ≠ 0) (hxW : radialProj x ∈ W)
    (hxD : radialProj x ∈ C.D) : ∀ᶠ y in 𝓝 x, C.u =ᶠ[𝓝 (radialProj y)] F := by
  have hopen : IsOpen {y : E n | y ≠ 0 ∧ radialProj y ∈ W ∩ C.D} :=
    isOpen_cone (h.isOpen.inter C.isOpen_D)
  filter_upwards [hopen.mem_nhds ⟨hx, hxW, hxD⟩] with y hy
  exact h.chart.eventuallyEq_of_mem hy.2.1 hy.2.2

end General

end ConeData.IsCollar

namespace Gen.ConeData.IsCollar

variable {n : ℕ} {C : OnePhaseDimension.ConeData n} {W : Set (E n)} {F : E n → ℝ}
  (h : C.IsCollar W F)
include h

variable {c : Coeffs (n - 1)} {x : E n} (hx : x ≠ 0) (hxW : radialProj x ∈ W)
  (hxD : radialProj x ∈ C.D)
include hx hxW hxD

theorem fluxZ_eventuallyEq : fluxZ c F =ᶠ[𝓝 x] fluxZ c C.u := by
  filter_upwards [h.eventually_germ hx hxW hxD] with y hy using (fluxZ_congr hy).symm

theorem fluxH_eventuallyEq : fluxH c F =ᶠ[𝓝 x] fluxH c C.u := by
  filter_upwards [h.eventually_germ hx hxW hxD] with y hy using (fluxH_congr hy).symm

theorem fluxW_eventuallyEq : fluxW F =ᶠ[𝓝 x] fluxW C.u := by
  filter_upwards [h.eventually_germ hx hxW hxD] with y hy using (fluxW_congr hy).symm

theorem fluxF_eventuallyEq : fluxF c F =ᶠ[𝓝 x] fluxF c C.u := by
  filter_upwards [h.eventually_germ hx hxW hxD] with y hy using (fluxF_congr hy).symm

end Gen.ConeData.IsCollar

namespace ConeData.IsCollar

variable {C : ConeData 6} {W : Set (E 6)} {F : E 6 → ℝ} (h : C.IsCollar W F)
include h

variable {c : Coeffs} {x : E 6} (hx : x ≠ 0) (hxW : radialProj x ∈ W) (hxD : radialProj x ∈ C.D)
include hx hxW hxD

theorem fluxZ_eventuallyEq : fluxZ c F =ᶠ[𝓝 x] fluxZ c C.u :=
  Gen.ConeData.IsCollar.fluxZ_eventuallyEq h hx hxW hxD

theorem fluxH_eventuallyEq : fluxH c F =ᶠ[𝓝 x] fluxH c C.u :=
  Gen.ConeData.IsCollar.fluxH_eventuallyEq h hx hxW hxD

theorem fluxW_eventuallyEq : fluxW F =ᶠ[𝓝 x] fluxW C.u :=
  Gen.ConeData.IsCollar.fluxW_eventuallyEq h hx hxW hxD

theorem fluxF_eventuallyEq : fluxF c F =ᶠ[𝓝 x] fluxF c C.u :=
  Gen.ConeData.IsCollar.fluxF_eventuallyEq (c := c.toGen) h hx hxW hxD

end ConeData.IsCollar

/-! ### The spherical data at unit points of `D` -/

namespace ConeData

variable {n : ℕ} {C : ConeData n} {x : E n}

/-- The jet record of `u` at a unit regular point of `D`. -/
theorem isConeJet_of_mem (hx : x ∈ C.D) (hxS : x ∉ C.Sing) (h1 : ‖x‖ = 1) :
    ConeJets.IsConeJet C.u (ConeJets.ofHarmonicHomogeneous C.u x h1) := by
  obtain ⟨hu, hΔ⟩ := contDiffAt_u_and_eventually_laplacian hx hxS
  exact ConeJets.isConeJet_ofHarmonicHomogeneous h1 C.isOneHomogeneous_u
    ((hu.of_le (by simp) : ContDiffAt ℝ 4 C.u x).eventually (by simp)) hΔ

end ConeData

namespace Gen.ConeData

variable {n : ℕ} {C : OnePhaseDimension.ConeData n} {x : E n} {c : Coeffs (n - 1)} {ε δ : ℝ}

/-- `f ≥ ε` at unit regular points of `D` with `w > 0`, if `|∇u|² ≤ 1` there. -/
theorem fluxF_ge (hc : CertificateHolds (n - 1) ε δ c) (hx : x ∈ C.D) (hxS : x ∉ C.Sing)
    (h1 : ‖x‖ = 1) (hw : 0 < fluxW C.u x) (hs : ‖∇ C.u x‖ ^ 2 ≤ 1) :
    ε ≤ fluxF c C.u x := by
  have hJ := C.isConeJet_of_mem hx hxS h1
  have hw' : sq2 (ConeJets.ofHarmonicHomogeneous C.u x h1).T ≠ 0 := by
    have h3 := hJ.fluxW_self
    change fluxW C.u x = _ at h3
    rw [h3] at hw
    exact normW_pos_iff.1 hw
  have h4 := hJ.fluxF_self hc
  change fluxF c C.u x = _ at h4
  rw [h4]
  exact hc.f_ge _ _ _ hJ.isSTF2_normalizedA (sq2_normalizedA hw')
    (hJ.admissible_of_normSq_gradient_le hs)

namespace IsCollar

variable {W : Set (E n)} {F : E n → ℝ} (h : C.IsCollar W F)
include h

/-- `f ≥ ε` at the unit points of `W ∩ closure D` where `w > 0` (by continuity from `D`). -/
theorem fluxF_ge (hc : CertificateHolds (n - 1) ε δ c) (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1)
    (hxW : x ∈ W) (hxD : x ∈ closure C.D) (h1 : ‖x‖ = 1) (hw : 0 < fluxW F x) :
    ε ≤ fluxF c F x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at h1
  have hxr : radialProj x = x := radialProj_of_norm_eq_one h1
  have hFs : ∀ z, ContDiffAt ℝ ∞ F z := fun z ↦ h.contDiff.contDiffAt
  have hcont := (contDiffAt_fluxF hc hx0 (hFs _) hw).continuousAt
  have : (𝓝[C.D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hxD
  have hev : ∀ᶠ y in 𝓝 x, y ∈ C.D → ε ≤ fluxF c F y := by
    have hcone : IsOpen {y : E n | y ≠ 0 ∧ radialProj y ∈ W} := isOpen_cone h.isOpen
    filter_upwards [hcone.mem_nhds ⟨hx0, by rw [hxr]; exact hxW⟩,
      (continuousAt_fluxW hx0 (hFs _)).eventually (lt_mem_nhds hw)] with y hy hwy hyD
    set z := radialProj y
    have hz1 : ‖z‖ = 1 := norm_radialProj hy.1
    have hzD : z ∈ C.D := C.radialProj_mem_D hyD
    have hzz : radialProj z = z := radialProj_of_norm_eq_one hz1
    have hz0 : z ≠ 0 := by rintro h0; rw [h0, norm_zero] at hz1; exact zero_ne_one hz1
    have hFy : fluxF c F y = fluxF c F z :=
      ((isZeroHomogeneous_fluxF c F).apply_radialProj hy.1).symm
    have hWy : fluxW F y = fluxW F z := ((isZeroHomogeneous_fluxW F).apply_radialProj hy.1).symm
    have hzW' : radialProj z ∈ W := by rw [hzz]; exact hy.2
    have hzD' : radialProj z ∈ C.D := by rw [hzz]; exact hzD
    rw [hFy, (fluxF_eventuallyEq h hz0 hzW' hzD').self_of_nhds]
    rw [hWy, (fluxW_eventuallyEq h hz0 hzW' hzD').self_of_nhds] at hwy
    exact Gen.ConeData.fluxF_ge hc hzD (h.notMem_sing hy.2) hz1 hwy (hs z hzD)
  exact ge_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_iff.2 hev)

end IsCollar

end Gen.ConeData

namespace ConeData

variable {C : ConeData 6} {x : E 6}

/-- `f ≥ ε*` at unit regular points of `D` with `w > 0`, if `|∇u|² ≤ 1` there. -/
theorem fluxF_ge {c : Coeffs} (hc : CertificateHolds c) (hx : x ∈ C.D) (hxS : x ∉ C.Sing)
    (h1 : ‖x‖ = 1) (hw : 0 < fluxW C.u x) (hs : ‖∇ C.u x‖ ^ 2 ≤ 1) :
    εStar ≤ fluxF c C.u x :=
  Gen.ConeData.fluxF_ge hc.toGen hx hxS h1 hw hs

end ConeData

namespace ConeData.IsCollar

variable {C : ConeData 6} {W : Set (E 6)} {F : E 6 → ℝ} (h : C.IsCollar W F)
include h

/-- `f ≥ ε*` at the unit points of `W ∩ closure D` where `w > 0` (by continuity from `D`). -/
theorem fluxF_ge {c : Coeffs} (hc : CertificateHolds c) (hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1)
    {x : E 6} (hxW : x ∈ W) (hxD : x ∈ closure C.D) (h1 : ‖x‖ = 1) (hw : 0 < fluxW F x) :
    εStar ≤ fluxF c F x :=
  Gen.ConeData.IsCollar.fluxF_ge h hc.toGen hs hxW hxD h1 hw

end ConeData.IsCollar

end OnePhaseDimension
