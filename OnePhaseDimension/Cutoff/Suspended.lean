/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Cutoff.Original

/-!
# Exclusion of suspended cones

Let `W = O × ℝ` be the suspension of a cone `O` in `ℝ⁵` with `O.Sing = {0}`, and let `c` satisfy
the certificate. For the product cut-off `ξ_j(z) = ϑ(j w_o(π z)) ϑ(j |π z|/|z|)`
(`suspCutoff`), the integrated comparison holds for every `j`
(`integrated_comparison_susp`). The errors are dominated by `C ρ^{-2-2a} D_o(π θ)` and vanish
eventually, while the mass tends to `(∫₀^π sin^{71/25} t dt) I_o > 0`. This contradicts `ε* > 0`
(`false_of_suspension`).

To apply the integrated comparison, the factor `w_o` is read from a collar function `F_o` of `O`,
so that the cut-off is smooth across the side boundary; on the component of `W` it agrees, with
its gradient, with the cut-off built from `u_o` (`suspCutoff_collar_eventuallyEq`). The cut-off
vanishes near the axis `π z = 0`, so a collar of `W` over `{|π z| ≥ 1/j}` suffices for each `j`.

## Differences from the source

The 2026-09-24 version integrates by parts on the suspended link after truncating near the two
tips. We use the volume-only spherical comparison with a collar of `W` over the compact set
`{|π z|/|z| ≥ 1/j}` of the sphere, which already contains the support of `ξ_j`, so no truncation
is needed.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric Function
open scoped ContDiff Gradient RealInnerProductSpace Laplacian Real

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### The spherical Hessian norm of a smooth function -/

section SphHess

variable {n : ℕ}

theorem sphHessNorm_congr {u v : E n → ℝ} {x : E n} (h : u =ᶠ[𝓝 (radialProj x)] v) :
    sphHessNorm u x = sphHessNorm v x := by
  simp only [sphHessNorm, jetNormSq, (h.iteratedFDeriv ℝ 2).eq_of_nhds]

theorem contDiffAt_jetNormSq_two_radialProj {F : E n → ℝ} (hF : ContDiff ℝ ∞ F) {y : E n}
    (hy : y ≠ 0) (m : ℕ) :
    ContDiffAt ℝ m (fun z ↦ jetNormSq (EuclideanSpace.basisFun (Fin n) ℝ) 2 F (radialProj z)) y :=
  (contDiffAt_jetNormSq _ (k := 2) (m := m) (hF.contDiffAt.of_le (natCast_le_infty _))).comp y
    (contDiffAt_radialProj_of_ne_zero hy)

theorem continuousAt_sphHessNorm {F : E n → ℝ} (hF : ContDiff ℝ ∞ F) {y : E n} (hy : y ≠ 0) :
    ContinuousAt (sphHessNorm F) y :=
  (contDiffAt_jetNormSq_two_radialProj hF hy 0).continuousAt.sqrt

theorem contDiffAt_sphHessNorm {F : E n → ℝ} (hF : ContDiff ℝ ∞ F) {y : E n} (hy : y ≠ 0)
    (hw : 0 < sphHessNorm F y) : ContDiffAt ℝ ∞ (sphHessNorm F) y :=
  contDiffAt_infty.2 fun m ↦ (contDiffAt_jetNormSq_two_radialProj hF hy m).sqrt
    (Real.sqrt_pos.1 hw).ne'

end SphHess

/-! ### The tip region -/

/-- The part `{|π z|/|z| ≥ 1/j}` of the unit sphere. -/
def tipSet (j : ℕ) : Set (E 6) := sphere 0 1 ∩ {z | 1 ≤ (j : ℝ) * (‖dropLast z‖ / ‖z‖)}

/-- The support of the suspended cut-off: `closure D ∩ {|π z| ≥ 1/j, j w(π z) ≥ 1}`. -/
def suspSupport (D : Set (E 6)) (w : E 5 → ℝ) (j : ℕ) : Set (E 6) :=
  closure D ∩ (tipSet j ∩ {z | 1 ≤ (j : ℝ) * w (dropLast z)})

theorem continuousAt_tipRatio {z : E 6} (hz : z ≠ 0) :
    ContinuousAt (fun z : E 6 ↦ ‖dropLast z‖ / ‖z‖) z :=
  ((continuous_norm.comp dropLast.continuous).continuousAt).div continuous_norm.continuousAt
    (norm_ne_zero_iff.2 hz)

theorem dropLast_ne_zero_of_mem_tipSet {j : ℕ} {z : E 6} (hz : z ∈ tipSet j) :
    dropLast z ≠ 0 := by
  intro h
  have := hz.2
  simp only [mem_ofPred_eq, h, norm_zero, zero_div, mul_zero] at this
  exact absurd this (by norm_num)

theorem isCompact_tipSet (j : ℕ) : IsCompact (tipSet j) := by
  have hcl : IsClosed (tipSet j) :=
    ContinuousOn.preimage_isClosed_of_isClosed (fun z hz ↦ (continuousAt_const.mul
      (continuousAt_tipRatio (ne_zero_of_mem_sphere_one hz))).continuousWithinAt)
      isClosed_sphere isClosed_Ici
  exact (isCompact_sphere 0 1).of_isClosed_subset hcl inter_subset_left

theorem IsSuspension.disjoint_tipSet {W : ConeData 6} {O : ConeData 5} (hW : IsSuspension W O)
    (j : ℕ) : Disjoint (tipSet j) W.Sing := by
  rw [hW.sing_eq]
  exact Set.disjoint_left.2 fun z hz hzS ↦ dropLast_ne_zero_of_mem_tipSet hz hzS

theorem isZeroHomogeneous_suspCutoff (ϑ : ℝ → ℝ) (j : ℕ) {w : E 5 → ℝ}
    (hw : IsZeroHomogeneous w) : IsZeroHomogeneous (suspCutoff ϑ j w) := fun r hr z ↦ by
  simp only [suspCutoff, map_smul, hw r hr, norm_smul, Real.norm_of_nonneg hr.le,
    mul_div_mul_left _ _ hr.ne']

/-! ### The cut-off data on the suspension -/

section Data

variable {W : ConeData 6} {O : ConeData 5} (hW : IsSuspension W O) (hO : O.Sing = {0})
  {WO : Set (E 5)} {FO : E 5 → ℝ} (hcolO : O.IsCollar WO FO)
  (hWO : closure O.D ∩ sphere 0 1 ⊆ WO)

omit hW hO in
include hcolO hWO in
theorem sphHessNorm_collar_eventuallyEq {y : E 5} (hy : y ∈ O.D) :
    sphHessNorm FO =ᶠ[𝓝 y] sphHessNorm O.u := by
  have hy0 := O.ne_zero_of_mem_D hy
  have hyD := O.radialProj_mem_D hy
  filter_upwards [hcolO.eventually_germ hy0
    (hWO ⟨subset_closure hyD, mem_sphere_zero_iff_norm.2 (norm_radialProj hy0)⟩) hyD]
    with y' h' using (sphHessNorm_congr h').symm

omit hO in
include hW hcolO hWO in
/-- On the component of `W`, the cut-off built from the collar of `O` agrees near every point
with the cut-off built from `u_o`. -/
theorem suspCutoff_collar_eventuallyEq (ϑ : ℝ → ℝ) (j : ℕ) {z : E 6} (hz : z ∈ W.D) :
    suspCutoff ϑ j (sphHessNorm FO) =ᶠ[𝓝 z] suspCutoff ϑ j (sphHessNorm O.u) := by
  have h := (sphHessNorm_collar_eventuallyEq hcolO hWO (hW.mem_D_iff.1 hz)).comp_tendsto
    dropLast.continuous.continuousAt
  filter_upwards [h] with z' hz'
  simp only [comp_apply] at hz'
  simp only [suspCutoff, hz']

omit hO in
include hW hcolO hWO in
theorem indicator_cutoffMass_collar (ϑ : ℝ → ℝ) (j : ℕ) :
    W.D.indicator (cutoffMass W.u (suspCutoff ϑ j (sphHessNorm FO))) =
      W.D.indicator (cutoffMass W.u (suspCutoff ϑ j (sphHessNorm O.u))) := by
  funext z
  by_cases hz : z ∈ W.D
  · simp only [indicator_of_mem hz, cutoffMass,
      (suspCutoff_collar_eventuallyEq hW hcolO hWO ϑ j hz).self_of_nhds]
  · simp only [indicator_of_notMem hz]

omit hO in
include hW hcolO hWO in
theorem indicator_cutoffError_collar (c : Coeffs) (ϑ : ℝ → ℝ) (j : ℕ) :
    W.D.indicator (cutoffError c W.u (suspCutoff ϑ j (sphHessNorm FO))) =
      W.D.indicator (cutoffError c W.u (suspCutoff ϑ j (sphHessNorm O.u))) := by
  funext z
  by_cases hz : z ∈ W.D
  · have h := suspCutoff_collar_eventuallyEq hW hcolO hWO ϑ j hz
    simp only [indicator_of_mem hz, cutoffError, h.self_of_nhds, h.gradient_eq]
  · simp only [indicator_of_notMem hz]

include hW hO hcolO hWO in
/-- The cut-off data on the suspension, for a collar `(Wj, Fj)` of `W` over the tip region. -/
theorem isCutoffData_susp {c : Coeffs} (hc : CertificateHolds c) {Wj : Set (E 6)}
    {Fj : E 6 → ℝ} (hcol : W.IsCollar Wj Fj) (j : ℕ) (hWj : tipSet j ∩ closure W.D ⊆ Wj) :
    IsCutoffData W Wj Fj (suspSupport W.D (sphHessNorm FO) j)
      (suspCutoff cutoffProfile j (sphHessNorm FO)) where
  homog := isZeroHomogeneous_suspCutoff _ _ (isZeroHomogeneous_sphHessNorm FO)
  isCompact := by
    have hcl : IsClosed (tipSet j ∩ {z | 1 ≤ (j : ℝ) * sphHessNorm FO (dropLast z)}) :=
      ContinuousOn.preimage_isClosed_of_isClosed (fun z hz ↦ (continuousAt_const.mul
        ((continuousAt_sphHessNorm hcolO.contDiff (dropLast_ne_zero_of_mem_tipSet hz)).comp
          dropLast.continuous.continuousAt)).continuousWithinAt)
        (isCompact_tipSet j).isClosed isClosed_Ici
    exact (isCompact_tipSet j).of_isClosed_subset (isClosed_closure.inter hcl)
      fun z hz ↦ hz.2.1
  subset_sphere := fun _ hz ↦ hz.2.1.1
  subset_closure := fun _ hz ↦ hz.1
  subset_W := fun _ hz ↦ hWj ⟨hz.2.1, hz.1⟩
  fluxW_pos := fun z hz ↦ by
    have hz1 : ‖z‖ = 1 := mem_sphere_zero_iff_norm.1 hz.2.1.1
    have hz0 := ne_zero_of_mem_sphere_one hz.2.1.1
    have hzW : z ∈ Wj := hWj ⟨hz.2.1, hz.1⟩
    by_cases hzD : z ∈ W.D
    · have hzr := radialProj_of_norm_eq_one hz1
      have hπD := hW.mem_D_iff.1 hzD
      have hw0 : 0 < sphHessNorm FO (dropLast z) := by
        have h1 : 1 ≤ (j : ℝ) * sphHessNorm FO (dropLast z) := hz.2.2
        by_contra h
        have h0 : sphHessNorm FO (dropLast z) = 0 :=
          le_antisymm (not_lt.1 h) (sphHessNorm_nonneg _ _)
        rw [h0, mul_zero] at h1
        exact absurd h1 (by norm_num)
      rw [(hcol.fluxW_eventuallyEq hz0 (by rw [hzr]; exact hzW)
          (by rw [hzr]; exact hzD)).self_of_nhds, hW.fluxW_suspension hO hzD hz1,
        ← (sphHessNorm_collar_eventuallyEq hcolO hWO hπD).self_of_nhds]
      exact mul_pos (inv_pos.2 (hW.norm_dropLast_pos hzD)) hw0
    · exact (hW.boundary_signed_flux_pos hO hc hcol.isOpen hzW hcol.contDiff.contDiffOn
        hcol.chart.eq_max (fun y hy hp ↦ (hcol.chart.mem_iff y hy).2 hp) hcol.norm_gradient
        (fun y hy hp ↦ hcol.laplacian_eq_zero ⟨hy, (hcol.chart.mem_iff y hy).2 hp⟩) hz.1 hzD
        hz1).1
  smooth := fun z hz ↦ by
    have hz0 := ne_zero_of_mem_sphere_one hz.2.1.1
    have hπ := dropLast_ne_zero_of_mem_tipSet hz.2.1
    have hw0 : 0 < sphHessNorm FO (dropLast z) := by
      have h1 : 1 ≤ (j : ℝ) * sphHessNorm FO (dropLast z) := hz.2.2
      by_contra h
      have h0 : sphHessNorm FO (dropLast z) = 0 :=
        le_antisymm (not_lt.1 h) (sphHessNorm_nonneg _ _)
      rw [h0, mul_zero] at h1
      exact absurd h1 (by norm_num)
    have hcw : ContinuousAt (fun z ↦ sphHessNorm FO (dropLast z)) z :=
      (continuousAt_sphHessNorm hcolO.contDiff hπ).comp dropLast.continuous.continuousAt
    filter_upwards [isOpen_ne.mem_nhds hz0,
      dropLast.continuous.continuousAt.eventually_ne hπ, hcw.eventually (lt_mem_nhds hw0)]
      with z' hz0' hπ' hw'
    have h1 : ContDiffAt ℝ ∞ (fun z ↦ cutoffProfile (j * sphHessNorm FO (dropLast z))) z' :=
      contDiff_cutoffProfile.contDiffAt.comp z' (contDiffAt_const.mul
        ((contDiffAt_sphHessNorm hcolO.contDiff hπ' hw').comp z' dropLast.contDiff.contDiffAt))
    have h2 : ContDiffAt ℝ ∞ (fun z : E 6 ↦ cutoffProfile (j * (‖dropLast z‖ / ‖z‖))) z' :=
      contDiff_cutoffProfile.contDiffAt.comp z' (contDiffAt_const.mul
        (((contDiffAt_norm ℝ hπ').comp z' dropLast.contDiff.contDiffAt).div
          (contDiffAt_norm ℝ hz0') (norm_ne_zero_iff.2 hz0')))
    exact h1.mul h2
  eventually_zero := fun z hz hzK ↦ by
    have hz0 := ne_zero_of_mem_sphere_one hz.2
    by_cases ht : 1 ≤ (j : ℝ) * (‖dropLast z‖ / ‖z‖)
    · have hzt : z ∈ tipSet j := ⟨hz.2, ht⟩
      have hπ := dropLast_ne_zero_of_mem_tipSet hzt
      have hlt : (j : ℝ) * sphHessNorm FO (dropLast z) < 1 := by
        by_contra h
        exact hzK ⟨hz.1, hzt, not_lt.1 h⟩
      have hcw : ContinuousAt (fun z ↦ (j : ℝ) * sphHessNorm FO (dropLast z)) z :=
        continuousAt_const.mul ((continuousAt_sphHessNorm hcolO.contDiff hπ).comp
          dropLast.continuous.continuousAt)
      filter_upwards [hcw.eventually (gt_mem_nhds hlt)] with z' hz'
      simp only [suspCutoff, Pi.zero_apply]
      rw [cutoffProfile_eq_zero (r := (j : ℝ) * sphHessNorm FO (dropLast z')) hz'.le, zero_mul]
    · have hct : ContinuousAt (fun z : E 6 ↦ (j : ℝ) * (‖dropLast z‖ / ‖z‖)) z :=
        continuousAt_const.mul (continuousAt_tipRatio hz0)
      filter_upwards [hct.eventually (gt_mem_nhds (not_le.1 ht))] with z' hz'
      simp only [suspCutoff, Pi.zero_apply]
      rw [cutoffProfile_eq_zero (r := (j : ℝ) * (‖dropLast z'‖ / ‖z'‖)) hz'.le, mul_zero]

end Data

/-! ### Positivity of the mass on the original link -/

/-- **`I_o > 0`**: `∫_{D ∩ S^{n-1}} w^{2a} dσ > 0`, because `D²u ≢ 0` on `D`. -/
theorem ConeData.integral_wSq_rpow_pos {n : ℕ} (C : ConeData n) (hS : C.Sing = {0}) :
    0 < ∫ y : sphere (0 : E n) 1, C.D.indicator (fun x ↦ C.wSq x ^ aExp) y
      ∂(volume : Measure (E n)).toSphere := by
  set σ := (volume : Measure (E n)).toSphere
  obtain ⟨x, hxD, hx2⟩ := C.nonflat
  have hx0 := C.ne_zero_of_mem_D hxD
  have hJx : 0 < jetNormSq (stdOrthonormalBasis ℝ (E n)) 2 C.u x :=
    lt_of_le_of_ne (jetNormSq_nonneg _ _ _ _)
      fun h ↦ hx2 (iteratedFDeriv_two_eq_zero_of_jetNormSq_eq_zero _ h.symm)
  have hrel := C.jetNormSq_radialProj hS (stdOrthonormalBasis ℝ (E n)) 2 hxD
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  have hwx : 0 < C.wSq x := by
    have h4 : 0 < ‖x‖ ^ 2 * C.wSq x := by
      change 0 < ‖x‖ ^ 2 * jetNormSq (stdOrthonormalBasis ℝ (E n)) 2 C.u (radialProj x)
      rw [← hrel]; positivity
    exact pos_of_mul_pos_right h4 (by positivity)
  set S : Set (sphere (0 : E n) 1) := (↑) ⁻¹' {x | x ∈ C.D ∧ 0 < C.wSq x}
  have hSo : IsOpen S := (C.isOpen_wSq_pos hS).preimage continuous_subtype_val
  have hSn : S.Nonempty := ⟨⟨radialProj x, mem_sphere_zero_iff_norm.2 (norm_radialProj hx0)⟩,
    C.radialProj_mem_D hxD, by rw [C.wSq_radialProj]; exact hwx⟩
  have hsub : S ⊆ Function.support fun u : sphere (0 : E n) 1 ↦
      C.D.indicator (fun x ↦ C.wSq x ^ aExp) u := by
    intro u hu
    rw [Function.mem_support, indicator_of_mem hu.1]
    exact (Real.rpow_pos_of_pos hu.2 _).ne'
  rw [integral_pos_iff_support_of_nonneg
    (fun u ↦ indicator_nonneg (fun x _ ↦ Real.rpow_nonneg (C.wSq_nonneg x) _) _)
    (C.integrable_wSq_rpow hS (by norm_num [aExp]))]
  exact (hSo.measure_pos σ hSn).trans_le (measure_mono hsub)

/-! ### The limits on the suspension -/

section Limits

variable {W : ConeData 6} {O : ConeData 5} (hW : IsSuspension W O) (hO : O.Sing = {0})
include hW hO

/-- **The integrated comparison on the suspension**, for the cut-off `ξ_j` built from `u_o`,
together with the integrability of the two sides. -/
theorem integrated_comparison_susp {c : Coeffs} (hc : CertificateHolds c) (j : ℕ) :
    (εStar * ∫ u : sphere (0 : E 6) 1,
        W.D.indicator (cutoffMass W.u (suspCutoff cutoffProfile j (sphHessNorm O.u))) u
        ∂(volume : Measure (E 6)).toSphere ≤
      ∫ u : sphere (0 : E 6) 1,
        W.D.indicator (cutoffError c W.u (suspCutoff cutoffProfile j (sphHessNorm O.u))) u
        ∂(volume : Measure (E 6)).toSphere) ∧
    Integrable (fun u : sphere (0 : E 6) 1 ↦
        W.D.indicator (cutoffMass W.u (suspCutoff cutoffProfile j (sphHessNorm O.u))) u)
      (volume : Measure (E 6)).toSphere ∧
    Integrable (fun u : sphere (0 : E 6) 1 ↦
        W.D.indicator (cutoffError c W.u (suspCutoff cutoffProfile j (sphHessNorm O.u))) u)
      (volume : Measure (E 6)).toSphere := by
  obtain ⟨WO, FO, hWO', hcolO⟩ := O.exists_isCollar (isCompact_sphere (0 : E 5) 1)
    (by rw [hO]; exact Set.disjoint_singleton_right.2 (by simp))
  have hWO : closure O.D ∩ sphere 0 1 ⊆ WO := fun x hx ↦ hWO' ⟨hx.2, hx.1⟩
  obtain ⟨Wj, Fj, hWj, hcol⟩ := W.exists_isCollar (isCompact_tipSet j) (hW.disjoint_tipSet j)
  have hs : ∀ y ∈ W.D, ‖∇ W.u y‖ ^ 2 ≤ 1 := fun y hy ↦ (hW.sSq_lt_one hO hy).le
  have hsign : BoundarySign c W := fun U G x₀ hU hx hG hu hD hgr hΔ hx₀ hx₀D h1 ↦
    hW.boundary_signed_flux_nonneg hO hc hU hx hG hu hD hgr hΔ hx₀ hx₀D h1
  have hξ := isCutoffData_susp hW hO hcolO hWO hc hcol j hWj
  have h1 := hξ.integrated_comparison hc hcol hs hsign
  have h2 := hξ.integrable_mass hcol
  have h3 := hξ.integrable_error hc hcol hs
  rw [indicator_cutoffMass_collar hW hcolO hWO,
    indicator_cutoffError_collar hW hcolO hWO] at h1
  rw [indicator_cutoffMass_collar hW hcolO hWO] at h2
  rw [indicator_cutoffError_collar hW hcolO hWO] at h3
  exact ⟨h1, h2, h3⟩

/-- On the sphere, `1_D w̃^{2a} = ρ^{-2a} 1_{D_o} w_o^{2a}(π θ)`. -/
theorem indicator_fluxW_rpow_susp {θ : E 6} (hθ : ‖θ‖ = 1) :
    W.D.indicator (fun x ↦ fluxW W.u x ^ (2 * aExp)) θ =
      ‖dropLast θ‖ ^ (-(2 * aExp)) * O.D.indicator (fun x ↦ O.wSq x ^ aExp) (dropLast θ) := by
  by_cases hD : θ ∈ W.D
  · rw [indicator_of_mem hD, indicator_of_mem (hW.mem_D_iff.1 hD),
      hW.fluxW_rpow_suspension hO hD hθ]
  · rw [indicator_of_notMem hD, indicator_of_notMem (fun h ↦ hD (hW.mem_D_iff.2 h)), mul_zero]

/-- **The suspended mass converges** to `∫ ρ^{-2a} 1_{D_o} w_o^{2a}(π θ)`. -/
theorem tendsto_integral_mass_susp {c : Coeffs} (hc : CertificateHolds c) {L : ℝ}
    (hϑ : IsCutoffProfile cutoffProfile L) :
    Tendsto (fun j : ℕ ↦ ∫ u : sphere (0 : E 6) 1,
        W.D.indicator (cutoffMass W.u (suspCutoff cutoffProfile j (sphHessNorm O.u))) u
        ∂(volume : Measure (E 6)).toSphere) atTop
      (𝓝 (∫ θ : sphere (0 : E 6) 1, ‖dropLast θ‖ ^ (-(2 * aExp)) *
        O.D.indicator (fun x ↦ O.wSq x ^ aExp) (dropLast θ)
        ∂(volume : Measure (E 6)).toSphere)) := by
  refine tendsto_integral_of_dominated_convergence _
    (fun j ↦ (integrated_comparison_susp hW hO hc j).2.1.aestronglyMeasurable)
    (integrable_suspension_mass O hO) (fun j ↦ ae_of_all _ fun u ↦ ?_)
    (ae_of_all _ fun u ↦ ?_)
  · have h1 := norm_eq_of_mem_sphere u
    rw [← indicator_fluxW_rpow_susp hW hO h1]
    by_cases hD : (u : E 6) ∈ W.D
    · have hr := Real.rpow_nonneg (fluxW_nonneg W.u u) (2 * aExp)
      rw [indicator_of_mem hD, indicator_of_mem hD, Real.norm_eq_abs, cutoffMass,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) hr)]
      exact mul_le_of_le_one_left hr
        (pow_le_one₀ (suspCutoff_nonneg hϑ j _ u) (suspCutoff_le_one hϑ j _ u))
    · simp [indicator_of_notMem hD]
  · have h1 := norm_eq_of_mem_sphere u
    rw [← indicator_fluxW_rpow_susp hW hO h1]
    by_cases hD : (u : E 6) ∈ W.D
    · simp only [indicator_of_mem hD]
      by_cases hw : sphHessNorm O.u (dropLast u) = 0
      · have hf : fluxW W.u u = 0 := by rw [hW.fluxW_suspension hO hD h1, hw, mul_zero]
        have h0 : (0 : ℝ) ^ (2 * aExp) = 0 := Real.zero_rpow (by norm_num [aExp])
        simp only [cutoffMass, hf, h0, mul_zero]
        exact tendsto_const_nhds
      · have hwpos : 0 < sphHessNorm O.u (dropLast u) :=
          lt_of_le_of_ne (sphHessNorm_nonneg _ _) (Ne.symm hw)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hW.errors_eventually_zero_susp hO hϑ hD hwpos] with j hj
        simp [cutoffMass, hj.1]
    · simp only [indicator_of_notMem hD]
      exact tendsto_const_nhds

/-- **The suspended errors vanish in the limit.** -/
theorem tendsto_integral_error_susp {c : Coeffs} (hc : CertificateHolds c) {L : ℝ}
    (hϑ : IsCutoffProfile cutoffProfile L) :
    Tendsto (fun j : ℕ ↦ ∫ u : sphere (0 : E 6) 1,
        W.D.indicator (cutoffError c W.u (suspCutoff cutoffProfile j (sphHessNorm O.u))) u
        ∂(volume : Measure (E 6)).toSphere) atTop (𝓝 0) := by
  obtain ⟨Cf, hCf, hfb⟩ := IsSuspension.exists_fieldBound_const hc
  obtain ⟨M₀, -, hMb⟩ := O.exists_wSq_bSq_le hO
  have hM : ∀ z ∈ W.D, sphHessNorm O.u (dropLast z) ≤ √M₀ := fun z hz ↦ by
    have hπD := hW.mem_D_iff.1 hz
    have hπ0 := O.ne_zero_of_mem_D hπD
    rw [← sphHessNorm_radialProj, O.sphHessNorm_eq_sqrt_wSq]
    exact Real.sqrt_le_sqrt (hMb _ (O.radialProj_mem_D hπD) (norm_radialProj hπ0)).1
  set Cs := Cf ^ 2 * ((2 * L) ^ 2 + 4 * (1 + √M₀ + √3) * (2 * L))
  have hCs : 0 ≤ Cs := by have := hϑ.L_nonneg; positivity
  have h := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure (E 6)).toSphere) (f := fun _ ↦ (0 : ℝ))
    (fun θ : sphere (0 : E 6) 1 ↦ Cs * (‖dropLast θ‖ ^ (-(2 + 2 * aExp)) *
      O.D.indicator (O.dominatorO aExp) (dropLast θ)))
    (fun j ↦ (integrated_comparison_susp hW hO hc j).2.2.aestronglyMeasurable)
    ((integrable_suspension_dominator O hO).const_mul Cs)
    (fun j ↦ ae_of_all _ fun u ↦ ?_) (ae_of_all _ fun u ↦ ?_)
  · simpa using h
  · have h1 := norm_eq_of_mem_sphere u
    by_cases hD : (u : E 6) ∈ W.D
    · set ξ := suspCutoff cutoffProfile j (sphHessNorm O.u)
      have hπD := hW.mem_D_iff.1 hD
      have hρ := hW.norm_dropLast_pos hD
      rw [indicator_of_mem hD, indicator_of_mem hπD, Real.norm_eq_abs]
      have key := hW.errors_le_susp hO hϑ hCf j hD h1 (hM u hD) (hfb O W hW hO u hD h1)
      set E1 := fluxH c W.u u ^ 2 * ‖∇ ξ u‖ ^ 2
      set E2 := 2 * ξ u * fluxH c W.u u * ⟪∇ (fluxH c W.u) u, ∇ ξ u⟫
      set E3 := -2 * ξ u * ⟪fluxZ c W.u u, ∇ ξ u⟫
      have hE : cutoffError c W.u ξ u = E1 + E2 + E3 := by
        simp only [cutoffError, E1, E2, E3]; ring
      have habs : |cutoffError c W.u ξ u| ≤ |E1| + |E2| + |E3| := by
        rw [hE]
        exact (abs_add_le _ _).trans (by linarith [abs_add_le E1 E2])
      have hρpow : ‖dropLast (u : E 6)‖ ^ (2 - 2 * aExp) =
          ‖dropLast (u : E 6)‖ ^ (-(2 + 2 * aExp)) * ‖dropLast (u : E 6)‖ ^ 4 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hρ]
        congr 1
        push_cast
        ring
      rw [hρpow] at key
      have key' : ‖dropLast (u : E 6)‖ ^ 4 * (|E1| + |E2| + |E3|) ≤
          ‖dropLast (u : E 6)‖ ^ 4 * (Cs * (‖dropLast (u : E 6)‖ ^ (-(2 + 2 * aExp)) *
            O.dominatorO aExp (dropLast u))) := by
        refine key.trans_eq ?_
        ring
      exact habs.trans (le_of_mul_le_mul_left key' (by positivity))
    · rw [indicator_of_notMem hD, norm_zero]
      exact mul_nonneg hCs (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
        (indicator_nonneg (fun x _ ↦ O.dominatorO_nonneg _ x) _))
  · by_cases hD : (u : E 6) ∈ W.D
    · simp only [indicator_of_mem hD]
      refine tendsto_const_nhds.congr' ?_
      by_cases hw : sphHessNorm O.u (dropLast u) = 0
      · refine Eventually.of_forall fun j ↦ ?_
        have hev := hW.suspCutoff_eventuallyEq_zero hO hϑ hD hw j
        have hg : ∇ (suspCutoff cutoffProfile j (sphHessNorm O.u)) u = 0 := by
          rw [hev.gradient_eq]; simp [gradient]
        exact (cutoffError_eq_zero hg).symm
      · have hwpos : 0 < sphHessNorm O.u (dropLast u) :=
          lt_of_le_of_ne (sphHessNorm_nonneg _ _) (Ne.symm hw)
        filter_upwards [hW.errors_eventually_zero_susp hO hϑ hD hwpos] with j hj
        exact (cutoffError_eq_zero hj.2).symm
    · simp only [indicator_of_notMem hD]
      exact tendsto_const_nhds

end Limits

/-- **No suspended cone.** If the certificate holds, there is no suspension `W = O × ℝ` of a cone
`O` in `ℝ⁵` with `O.Sing = {0}`. -/
theorem false_of_suspension {c : Coeffs} (hc : CertificateHolds c) (O : ConeData 5)
    (hO : O.Sing = {0}) (W : ConeData 6) (hW : IsSuspension W O) : False := by
  obtain ⟨L, hϑ⟩ := exists_isCutoffProfile_cutoffProfile
  have hlim := le_of_tendsto_of_tendsto'
    ((tendsto_integral_mass_susp hW hO hc hϑ).const_mul εStar)
    (tendsto_integral_error_susp hW hO hc hϑ) fun j ↦ (integrated_comparison_susp hW hO hc j).1
  rw [integral_suspension_mass O hO] at hlim
  have := mul_pos εStar_pos (mul_pos (integral_sin_rpow_pos (by norm_num : (0 : ℝ) ≤ 71 / 25))
    (O.integral_wSq_rpow_pos hO))
  linarith

end OnePhaseDimension
