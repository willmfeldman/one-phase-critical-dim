/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.Suspension
public import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-!
# The suspended measure formula

Write a unit vector of `ℝ⁶ = ℝ⁵ × ℝ` as `θ = (ρ y, c)` with `ρ = |π θ|`, `y ∈ S⁴` and `c = θ₆`,
where `π = dropLast`. In the suspension coordinates `ρ = sin t`, `c = cos t`, `t ∈ (0, π)`, the
surface measure of `S⁵` is `sin⁴t dt dσ₄(y)` (`lintegral_sphere_suspension`):

  `∫_{S⁵} a(|π θ|, θ₆) b(π θ / |π θ|) dσ₅ = ∫₀^π a(sin t, cos t) sin⁴t dt · ∫_{S⁴} b dσ₄`

for measurable `a, b ≥ 0`, with Mathlib's surface measures `volume.toSphere`. The normalization
constant is `1`: both sides are read off from the same radial weights. The real-valued version
for nonnegative `a, b` is `integral_sphere_suspension`.

## Proof

Test both sides with `G(z) = χ(|z|) a(|π z|/|z|, z₆/|z|) b(π z / |π z|)`, `χ = 1_{[0,1)}`.
Polar coordinates on `ℝ⁶` give `∫ G = (∫₀^∞ r⁵ χ) ∫_{S⁵} a b`. Fubini over `ℝ⁶ = ℝ × ℝ⁵`, polar
coordinates on `ℝ⁵` and then Mathlib's `polarCoord` in the half-plane `{(s, ρ) : ρ > 0}`, with
`s = r cos t` and `ρ = r sin t`, give `∫ G = (∫₀^∞ r⁵ χ) ∫₀^π a(sin t, cos t) sin⁴t dt ∫_{S⁴} b`.
Cancel the radial factor `∫₀^1 r⁵ dr = 1/6`.

## Differences from the source

The 2026-09-24 version reads `dV = ρ⁴ dt dV_o` from the warped metric `dt² + sin²t ds²_{S⁴}`. We
derive the formula from polar coordinates on `ℝ⁶` and on `ℝ⁵`, Fubini, and polar coordinates in a
half-plane.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Function Filter Topology Set Metric MeasureTheory EllipticBernoulli
open scoped ENNReal Real

@[expose] public noncomputable section

namespace OnePhaseDimension

/-! ### Polar coordinates for Lebesgue integrals -/

section Polar

variable {n : ℕ}

/-- Integration against the radial measure `volumeIoiPow k` is integration on `(0, ∞)` against
`r ^ k`. -/
theorem lintegral_volumeIoiPow (k : ℕ) {h : ℝ → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ r : Ioi (0 : ℝ), h r ∂(Measure.volumeIoiPow k) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ k) * h r := by
  have key := lintegral_withDensity_eq_lintegral_mul (volume.comap Subtype.val)
    (by fun_prop : Measurable fun r : Ioi (0 : ℝ) ↦ ENNReal.ofReal ((r : ℝ) ^ k))
    (hh.comp measurable_subtype_coe)
  simp only [comp_apply] at key
  rw [Measure.volumeIoiPow, key]
  exact lintegral_subtype_comap measurableSet_Ioi (fun r ↦ ENNReal.ofReal (r ^ k) * h r)

/-- **Polar coordinates** for Lebesgue integrals on `ℝⁿ`:
`∫⁻ f = ∫⁻_{S^{n-1} × (0, ∞)} f(r u) d(σ ⊗ r^{n-1} dr)`. -/
theorem lintegral_eq_lintegral_sphere_prod [NeZero n] (f : E n → ℝ≥0∞) :
    ∫⁻ x, f x =
      ∫⁻ p : sphere (0 : E n) 1 × Ioi (0 : ℝ), f ((p.2 : ℝ) • (p.1 : E n))
        ∂((volume : Measure (E n)).toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
  have : Nontrivial (E n) := by
    have : 0 < Module.finrank ℝ (E n) := by rw [finrank_E]; exact Nat.pos_of_neZero n
    exact Module.nontrivial_of_finrank_pos this
  have hmp := (volume : Measure (E n)).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_E] at hmp
  have hemb := (homeomorphUnitSphereProd (E n)).measurableEmbedding
  set g : sphere (0 : E n) 1 × Ioi (0 : ℝ) → ℝ≥0∞ := fun p ↦ f ((p.2 : ℝ) • (p.1 : E n))
  have hg : ∀ x : ({0}ᶜ : Set (E n)), g (homeomorphUnitSphereProd (E n) x) = f x := by
    intro x
    have hx : ‖(x : E n)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
    simp [g, smul_smul, hx]
  calc ∫⁻ x, f x = ∫⁻ x in ({0}ᶜ : Set (E n)), f x := by rw [restrict_compl_singleton]
    _ = ∫⁻ x : ({0}ᶜ : Set (E n)), f x ∂(volume.comap Subtype.val) :=
        (lintegral_subtype_comap (measurableSet_singleton _).compl f).symm
    _ = ∫⁻ x : ({0}ᶜ : Set (E n)), g (homeomorphUnitSphereProd (E n) x)
          ∂(volume.comap Subtype.val) := by simp only [hg]
    _ = _ := hmp.lintegral_comp_emb hemb g

end Polar

/-! ### `ℝ⁶ = ℝ × ℝ⁵` -/

/-- The splitting `z ↦ (z₆, π z)` of `ℝ⁶` as `ℝ × ℝ⁵`. -/
def lastDropLast (z : E 6) : ℝ × E 5 := (z (Fin.last 5), dropLast z)

theorem measurePreserving_lastDropLast :
    MeasurePreserving lastDropLast (volume : Measure (E 6))
      ((volume : Measure ℝ).prod (volume : Measure (E 5))) := by
  have h1 := PiLp.volume_preserving_ofLp (Fin 6)
  have h2 := volume_preserving_piFinSuccAbove (fun _ : Fin 6 ↦ ℝ) (Fin.last 5)
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (PiLp.volume_preserving_toLp (Fin 5))
  have h := (h3.comp h2).comp h1
  convert h using 1
  funext z
  simp only [lastDropLast, comp_apply, MeasurableEquiv.piFinSuccAbove_apply]
  refine Prod.ext rfl ?_
  ext j
  simp only [dropLast_apply]
  simp only [Prod.map_apply, id, Fin.insertNthEquiv_symm_apply, Fin.removeNth,
    Fin.succAbove_last]

/-! ### The radial test function -/

/-- The radial cutoff `χ = 1_{(-∞, 1)}`. -/
def unitCutoff : ℝ → ℝ≥0∞ := (Iio (1 : ℝ)).indicator 1

theorem measurable_unitCutoff : Measurable unitCutoff :=
  measurable_one.indicator measurableSet_Iio

/-- `∫₀^∞ r⁵ χ(r) dr = 1/6`, in the form used below. -/
theorem lintegral_unitCutoff_volumeIoiPow :
    ∫⁻ r : Ioi (0 : ℝ), unitCutoff r ∂(Measure.volumeIoiPow 5) = ENNReal.ofReal (1 / 6) := by
  have h : (fun r : Ioi (0 : ℝ) ↦ unitCutoff r) =
      (Iio (⟨1, one_pos⟩ : Ioi (0 : ℝ))).indicator 1 := by
    funext r
    simp only [unitCutoff, indicator, mem_Iio, Pi.one_apply]
    rfl
  rw [h, lintegral_indicator_one measurableSet_Iio, Measure.volumeIoiPow_apply_Iio]
  norm_num

/-! ### The half-plane integral -/

section HalfPlane

variable {a : ℝ → ℝ → ℝ≥0∞}

/-- The integrand `K(s, ρ) = χ(√(ρ² + s²)) a(ρ/√(ρ² + s²), s/√(ρ² + s²))` on the `(s, ρ)`-plane. -/
def halfPlaneKernel (a : ℝ → ℝ → ℝ≥0∞) (p : ℝ × ℝ) : ℝ≥0∞ :=
  unitCutoff √(p.2 ^ 2 + p.1 ^ 2) *
    a (p.2 / √(p.2 ^ 2 + p.1 ^ 2)) (p.1 / √(p.2 ^ 2 + p.1 ^ 2))

theorem measurable_halfPlaneKernel (ha : Measurable (uncurry a)) :
    Measurable (halfPlaneKernel a) := by
  unfold halfPlaneKernel
  refine (measurable_unitCutoff.comp (by fun_prop)).mul ?_
  exact ha.comp (Measurable.prodMk (by fun_prop) (by fun_prop))

theorem halfPlaneKernel_polarCoord_symm {r t : ℝ} (hr : 0 < r) :
    halfPlaneKernel a (polarCoord.symm (r, t)) = unitCutoff r * a (Real.sin t) (Real.cos t) := by
  have hR : √((r * Real.sin t) ^ 2 + (r * Real.cos t) ^ 2) = r := by
    rw [show (r * Real.sin t) ^ 2 + (r * Real.cos t) ^ 2 = r ^ 2 by
      rw [mul_pow, mul_pow, ← mul_add, Real.sin_sq_add_cos_sq, mul_one], Real.sqrt_sq hr.le]
  simp only [halfPlaneKernel, polarCoord, OpenPartialHomeomorph.coe_mk_symm,
    PartialEquiv.coe_symm_mk, hR]
  rw [mul_div_cancel_left₀ _ hr.ne', mul_div_cancel_left₀ _ hr.ne']

/-- **The half-plane integral** in polar coordinates `s = r cos t`, `ρ = r sin t`:
`∫_ℝ ∫_{ρ > 0} ρ⁴ K(s, ρ) dρ ds = (∫_{r > 0} r⁵ χ(r) dr) ∫₀^π a(sin t, cos t) sin⁴t dt`. -/
theorem lintegral_halfPlane (ha : Measurable (uncurry a)) :
    ∫⁻ s : ℝ, ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ 4) * halfPlaneKernel a (s, ρ) =
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ 5) * unitCutoff r) *
        ∫⁻ t in Ioo 0 π, a (Real.sin t) (Real.cos t) * ENNReal.ofReal (Real.sin t ^ 4) := by
  set L : ℝ × ℝ → ℝ≥0∞ := {p : ℝ × ℝ | 0 < p.2}.indicator
    fun p ↦ ENNReal.ofReal (p.2 ^ 4) * halfPlaneKernel a p with hL
  have hLm : Measurable L :=
    (((by fun_prop : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.2 ^ 4))).mul
      (measurable_halfPlaneKernel ha)).indicator (measurableSet_lt measurable_const measurable_snd)
  have h1 : ∀ s : ℝ, ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ 4) * halfPlaneKernel a (s, ρ) =
      ∫⁻ ρ, L (s, ρ) := by
    intro s
    rw [← lintegral_indicator measurableSet_Ioi]
    rfl
  simp_rw [h1]
  rw [← lintegral_prod _ hLm.aemeasurable, ← Measure.volume_eq_prod,
    ← lintegral_comp_polarCoord_symm]
  have h2 : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 • L (polarCoord.symm p) =
      ENNReal.ofReal (p.1 ^ 5) * unitCutoff p.1 *
        (Ioo 0 π).indicator (fun t ↦ a (Real.sin t) (Real.cos t) *
          ENNReal.ofReal (Real.sin t ^ 4)) p.2 := by
    rintro ⟨r, t⟩ ⟨hr, ht⟩
    simp only [mem_Ioi] at hr
    simp only [mem_Ioo] at ht
    have hsym : polarCoord.symm (r, t) = (r * Real.cos t, r * Real.sin t) := rfl
    by_cases hpos : 0 < t
    · have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi hpos ht.2
      have hmem : (polarCoord.symm (r, t)) ∈ {p : ℝ × ℝ | 0 < p.2} := by
        rw [hsym]; exact mul_pos hr hs
      rw [hL, indicator_of_mem hmem, indicator_of_mem (show t ∈ Ioo 0 π from ⟨hpos, ht.2⟩),
        halfPlaneKernel_polarCoord_symm hr, hsym, smul_eq_mul]
      simp only
      rw [mul_pow, ENNReal.ofReal_mul (by positivity),
        show r ^ 5 = r * r ^ 4 by ring, ENNReal.ofReal_mul hr.le]
      ring
    · have hs : Real.sin t ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le (not_lt.1 hpos) ht.1.le
      have hnmem : (polarCoord.symm (r, t)) ∉ {p : ℝ × ℝ | 0 < p.2} := by
        rw [hsym]
        simp only [mem_ofPred_eq, not_lt]
        exact mul_nonpos_of_nonneg_of_nonpos hr.le hs
      rw [hL, indicator_of_notMem hnmem, indicator_of_notMem (fun h ↦ hpos h.1)]
      simp
  rw [setLIntegral_congr_fun polarCoord.open_target.measurableSet h2]
  have hf : Measurable fun r : ℝ ↦ ENNReal.ofReal (r ^ 5) * unitCutoff r :=
    (by fun_prop : Measurable fun r : ℝ ↦ ENNReal.ofReal (r ^ 5)).mul measurable_unitCutoff
  have hg0 : Measurable fun t : ℝ ↦ a (Real.sin t) (Real.cos t) :=
    ha.comp (Real.measurable_sin.prodMk Real.measurable_cos)
  have hg : Measurable ((Ioo 0 π).indicator fun t : ℝ ↦ a (Real.sin t) (Real.cos t) *
      ENNReal.ofReal (Real.sin t ^ 4)) :=
    (hg0.mul (by fun_prop)).indicator measurableSet_Ioo
  have hprod := lintegral_prod_mul (μ := volume.restrict (Ioi (0 : ℝ)))
    (ν := volume.restrict (Ioo (-π) π)) hf.aemeasurable hg.aemeasurable
  have htarget : polarCoord.target = Ioi (0 : ℝ) ×ˢ Ioo (-π) π := rfl
  rw [htarget, Measure.volume_eq_prod, ← Measure.prod_restrict]
  refine hprod.trans ?_
  congr 1
  rw [lintegral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
    inter_eq_left.2 (Ioo_subset_Ioo (by linarith [Real.pi_pos]) le_rfl)]

end HalfPlane

/-! ### The two evaluations of the test integral -/

section TestIntegral

variable {a : ℝ → ℝ → ℝ≥0∞} {b : E 5 → ℝ≥0∞}

theorem measurable_radialProj {n : ℕ} : Measurable (radialProj : E n → E n) :=
  (measurable_norm.inv).smul measurable_id

/-- The test function `G(z) = χ(|z|) a(|π z|/|z|, z₆/|z|) b(π z / |π z|)` on `ℝ⁶`. -/
def suspensionTest (a : ℝ → ℝ → ℝ≥0∞) (b : E 5 → ℝ≥0∞) (z : E 6) : ℝ≥0∞ :=
  unitCutoff ‖z‖ * a (‖dropLast z‖ / ‖z‖) (z (Fin.last 5) / ‖z‖) * b (radialProj (dropLast z))

/-- The angular integrand `F(θ) = a(|π θ|, θ₆) b(π θ / |π θ|)`. -/
def suspensionAngular (a : ℝ → ℝ → ℝ≥0∞) (b : E 5 → ℝ≥0∞) (θ : E 6) : ℝ≥0∞ :=
  a ‖dropLast θ‖ (θ (Fin.last 5)) * b (radialProj (dropLast θ))

theorem measurable_suspensionAngular (ha : Measurable (uncurry a)) (hb : Measurable b) :
    Measurable (suspensionAngular a b) := by
  unfold suspensionAngular
  refine (ha.comp (Measurable.prodMk ?_ ?_)).mul (hb.comp (measurable_radialProj.comp ?_))
  · exact measurable_norm.comp dropLast.continuous.measurable
  · exact (measurable_pi_apply _).comp (PiLp.continuous_ofLp 2 _).measurable
  · exact dropLast.continuous.measurable

/-- Polar coordinates on `ℝ⁶`: `∫ G = (∫_{S⁵} F dσ) (∫_{r > 0} r⁵ χ(r) dr)`. -/
theorem lintegral_suspensionTest_polar (ha : Measurable (uncurry a)) (hb : Measurable b) :
    ∫⁻ z, suspensionTest a b z =
      (∫⁻ θ : sphere (0 : E 6) 1, suspensionAngular a b θ ∂(volume : Measure (E 6)).toSphere) *
        ∫⁻ r : Ioi (0 : ℝ), unitCutoff r ∂(Measure.volumeIoiPow 5) := by
  rw [lintegral_eq_lintegral_sphere_prod]
  have h : ∀ p : sphere (0 : E 6) 1 × Ioi (0 : ℝ),
      suspensionTest a b ((p.2 : ℝ) • (p.1 : E 6)) =
        suspensionAngular a b p.1 * unitCutoff p.2 := by
    rintro ⟨⟨θ, hθ⟩, ⟨r, hr⟩⟩
    simp only [mem_sphere_iff_norm, sub_zero] at hθ
    simp only [mem_Ioi] at hr
    have hn : ‖r • θ‖ = r := by rw [norm_smul, hθ, mul_one, Real.norm_of_nonneg hr.le]
    simp only [suspensionTest, suspensionAngular, hn, map_smul, norm_smul,
      Real.norm_of_nonneg hr.le, PiLp.smul_apply, smul_eq_mul, radialProj_smul_of_pos hr]
    rw [mul_div_cancel_left₀ _ hr.ne', mul_div_cancel_left₀ _ hr.ne']
    ring
  simp_rw [h]
  exact lintegral_prod_mul
    ((measurable_suspensionAngular ha hb).comp measurable_subtype_coe).aemeasurable
    (measurable_unitCutoff.comp measurable_subtype_coe).aemeasurable


/-- `|z| = √(|π z|² + z₆²)`. -/
theorem norm_eq_sqrt_dropLast (z : E 6) :
    ‖z‖ = √(‖dropLast z‖ ^ 2 + z (Fin.last 5) ^ 2) := by
  rw [← norm_sq_eq_dropLast, Real.sqrt_sq (norm_nonneg _)]

/-- Fubini over `ℝ⁶ = ℝ × ℝ⁵` and polar coordinates on `ℝ⁵`:
`∫ G = (∫_{S⁴} b dσ) ∫_ℝ ∫_{ρ > 0} ρ⁴ K(s, ρ) dρ ds`. -/
theorem lintegral_suspensionTest_fubini (ha : Measurable (uncurry a)) (hb : Measurable b) :
    ∫⁻ z, suspensionTest a b z =
      (∫⁻ y : sphere (0 : E 5) 1, b y ∂(volume : Measure (E 5)).toSphere) *
        ∫⁻ s : ℝ, ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ 4) * halfPlaneKernel a (s, ρ) := by
  set H : ℝ × E 5 → ℝ≥0∞ := fun p ↦ halfPlaneKernel a (p.1, ‖p.2‖) * b (radialProj p.2)
    with hH
  have hHm : Measurable H :=
    ((measurable_halfPlaneKernel ha).comp (measurable_fst.prodMk measurable_snd.norm)).mul
      (hb.comp (measurable_radialProj.comp measurable_snd))
  have hG : ∀ z, suspensionTest a b z = H (lastDropLast z) := by
    intro z
    simp only [suspensionTest, hH, lastDropLast, halfPlaneKernel, ← norm_eq_sqrt_dropLast]
  simp_rw [hG]
  rw [measurePreserving_lastDropLast.lintegral_comp hHm, lintegral_prod _ hHm.aemeasurable]
  have hinner : ∀ s : ℝ, ∫⁻ x : E 5, H (s, x) =
      (∫⁻ y : sphere (0 : E 5) 1, b y ∂(volume : Measure (E 5)).toSphere) *
        ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ 4) * halfPlaneKernel a (s, ρ) := by
    intro s
    rw [lintegral_eq_lintegral_sphere_prod]
    have h : ∀ p : sphere (0 : E 5) 1 × Ioi (0 : ℝ), H (s, (p.2 : ℝ) • (p.1 : E 5)) =
        b p.1 * halfPlaneKernel a (s, p.2) := by
      rintro ⟨⟨y, hy⟩, ⟨r, hr⟩⟩
      simp only [mem_sphere_iff_norm, sub_zero] at hy
      simp only [mem_Ioi] at hr
      simp only [hH, norm_smul, hy, mul_one, Real.norm_of_nonneg hr.le,
        radialProj_smul_of_pos hr, radialProj_of_norm_eq_one hy]
      ring
    simp_rw [h]
    refine (lintegral_prod_mul (f := fun y : sphere (0 : E 5) 1 ↦ b y)
      (g := fun r : Ioi (0 : ℝ) ↦ halfPlaneKernel a (s, r))
      (hb.comp measurable_subtype_coe).aemeasurable
      (((measurable_halfPlaneKernel ha).comp (measurable_const.prodMk measurable_id)).comp
        measurable_subtype_coe).aemeasurable).trans ?_
    congr 1
    exact lintegral_volumeIoiPow 4
      ((measurable_halfPlaneKernel ha).comp (measurable_const.prodMk measurable_id))
  simp_rw [hinner]
  refine lintegral_const_mul _ ?_
  have hm : Measurable fun p : ℝ × ℝ ↦ (Ioi (0 : ℝ)).indicator
      (fun ρ ↦ ENNReal.ofReal (ρ ^ 4) * halfPlaneKernel a (p.1, ρ)) p.2 := by
    have : (fun p : ℝ × ℝ ↦ (Ioi (0 : ℝ)).indicator
        (fun ρ ↦ ENNReal.ofReal (ρ ^ 4) * halfPlaneKernel a (p.1, ρ)) p.2) =
        {p : ℝ × ℝ | 0 < p.2}.indicator
          (fun p ↦ ENNReal.ofReal (p.2 ^ 4) * halfPlaneKernel a p) := by
      funext p
      simp only [indicator, mem_Ioi, mem_ofPred_eq]
    rw [this]
    exact (((by fun_prop : Measurable fun p : ℝ × ℝ ↦ ENNReal.ofReal (p.2 ^ 4))).mul
      (measurable_halfPlaneKernel ha)).indicator (measurableSet_lt measurable_const measurable_snd)
  have := hm.lintegral_prod_right' (ν := (volume : Measure ℝ))
  simp_rw [lintegral_indicator measurableSet_Ioi] at this
  exact this

end TestIntegral

/-! ### The measure formula -/

/-- **The suspended measure formula.** For measurable `a : ℝ × ℝ → [0, ∞]` and `b : ℝ⁵ → [0, ∞]`,

  `∫_{S⁵} a(|π θ|, θ₆) b(π θ/|π θ|) dσ₅(θ) = ∫₀^π a(sin t, cos t) sin⁴t dt · ∫_{S⁴} b dσ₄`,

with `π = dropLast` and `σ = volume.toSphere`. -/
theorem lintegral_sphere_suspension {a : ℝ → ℝ → ℝ≥0∞} (ha : Measurable (uncurry a))
    {b : E 5 → ℝ≥0∞} (hb : Measurable b) :
    ∫⁻ θ : sphere (0 : E 6) 1, a ‖dropLast θ‖ ((θ : E 6) (Fin.last 5)) *
        b (radialProj (dropLast θ)) ∂(volume : Measure (E 6)).toSphere =
      (∫⁻ t in Ioo 0 π, a (Real.sin t) (Real.cos t) * ENNReal.ofReal (Real.sin t ^ 4)) *
        ∫⁻ y : sphere (0 : E 5) 1, b y ∂(volume : Measure (E 5)).toSphere := by
  have h1 := lintegral_suspensionTest_polar ha hb
  rw [lintegral_suspensionTest_fubini ha hb, lintegral_halfPlane ha,
    ← lintegral_volumeIoiPow 5 measurable_unitCutoff, lintegral_unitCutoff_volumeIoiPow] at h1
  have hX0 : ENNReal.ofReal (1 / 6) ≠ 0 := by simp
  have hXt : ENNReal.ofReal (1 / 6) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2 : (∫⁻ θ : sphere (0 : E 6) 1, suspensionAngular a b θ
      ∂(volume : Measure (E 6)).toSphere) * ENNReal.ofReal (1 / 6) =
      ((∫⁻ t in Ioo 0 π, a (Real.sin t) (Real.cos t) * ENNReal.ofReal (Real.sin t ^ 4)) *
        ∫⁻ y : sphere (0 : E 5) 1, b y ∂(volume : Measure (E 5)).toSphere) *
          ENNReal.ofReal (1 / 6) := by
    rw [← h1]; ring
  exact (ENNReal.mul_left_inj hX0 hXt).1 h2

/-- **The suspended measure formula, real form**, for measurable `a, b ≥ 0`:
`∫_{S⁵} a(|π θ|, θ₆) b(π θ/|π θ|) dσ₅ = ∫₀^π a(sin t, cos t) sin⁴t dt · ∫_{S⁴} b dσ₄`. -/
theorem integral_sphere_suspension {a : ℝ → ℝ → ℝ} (ha : Measurable (uncurry a))
    (ha0 : ∀ ρ c, 0 ≤ a ρ c) {b : E 5 → ℝ} (hb : Measurable b) (hb0 : ∀ y, 0 ≤ b y) :
    ∫ θ : sphere (0 : E 6) 1, a ‖dropLast θ‖ ((θ : E 6) (Fin.last 5)) *
        b (radialProj (dropLast θ)) ∂(volume : Measure (E 6)).toSphere =
      (∫ t in Ioo 0 π, a (Real.sin t) (Real.cos t) * Real.sin t ^ 4) *
        ∫ y : sphere (0 : E 5) 1, b y ∂(volume : Measure (E 5)).toSphere := by
  have hF : Measurable fun θ : sphere (0 : E 6) 1 ↦ a ‖dropLast θ‖ ((θ : E 6) (Fin.last 5)) *
      b (radialProj (dropLast θ)) := by
    refine (ha.comp (Measurable.prodMk ?_ ?_)).mul
      (hb.comp (measurable_radialProj.comp (dropLast.continuous.measurable.comp
        measurable_subtype_coe)))
    · exact measurable_norm.comp (dropLast.continuous.measurable.comp measurable_subtype_coe)
    · exact ((measurable_pi_apply _).comp (PiLp.continuous_ofLp 2 _).measurable).comp
        measurable_subtype_coe
  have hA : Measurable fun t : ℝ ↦ a (Real.sin t) (Real.cos t) * Real.sin t ^ 4 :=
    (ha.comp (Real.measurable_sin.prodMk Real.measurable_cos)).mul (by fun_prop)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun θ ↦ mul_nonneg (ha0 _ _) (hb0 _))
      hF.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun t ↦ mul_nonneg (ha0 _ _)
      (by positivity)) hA.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun y ↦ hb0 _)
      (hb.comp measurable_subtype_coe).aestronglyMeasurable,
    ← ENNReal.toReal_mul]
  congr 1
  simp_rw [ENNReal.ofReal_mul (ha0 _ _)]
  exact lintegral_sphere_suspension (a := fun ρ c ↦ ENNReal.ofReal (a ρ c))
    (ENNReal.measurable_ofReal.comp ha) (b := fun y ↦ ENNReal.ofReal (b y))
    (ENNReal.measurable_ofReal.comp hb)

/-! ### Integrability of the suspended weights -/

theorem radialProj_radialProj {n : ℕ} (x : E n) : radialProj (radialProj x) = radialProj x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radialProj]
  · exact radialProj_of_norm_eq_one (norm_radialProj hx)

/-- `ρ^p b(π θ)` is integrable on `S⁵` when `p + 4 ≥ 0` and `b ≥ 0` is `0`-homogeneous and
integrable on `S⁴`: by the measure formula its integral is `∫₀^π sin^{p+4}t dt ∫_{S⁴} b`. -/
theorem integrable_sphere_suspension_rpow {p : ℝ} (hp : 0 ≤ p + 4) {b : E 5 → ℝ}
    (hb : Measurable b) (hb0 : ∀ y, 0 ≤ b y) (hbr : ∀ x, b (radialProj x) = b x)
    (hbi : Integrable (fun y : sphere (0 : E 5) 1 ↦ b y) (volume : Measure (E 5)).toSphere) :
    Integrable (fun θ : sphere (0 : E 6) 1 ↦ ‖dropLast θ‖ ^ p * b (dropLast θ))
      (volume : Measure (E 6)).toSphere := by
  have hπ : Measurable fun θ : sphere (0 : E 6) 1 ↦ dropLast θ :=
    dropLast.continuous.measurable.comp measurable_subtype_coe
  have hm : Measurable fun θ : sphere (0 : E 6) 1 ↦ ‖dropLast θ‖ ^ p * b (dropLast θ) :=
    ((measurable_norm.comp hπ).pow_const p).mul (hb.comp hπ)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have hnorm : ∀ θ : sphere (0 : E 6) 1, ‖‖dropLast θ‖ ^ p * b (dropLast θ)‖ₑ =
      ENNReal.ofReal (‖dropLast θ‖ ^ p) * ENNReal.ofReal (b (radialProj (dropLast θ))) := by
    intro θ
    rw [hbr, Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (hb0 _)),
      ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _)]
  simp only [HasFiniteIntegral, hnorm]
  have key := lintegral_sphere_suspension (a := fun ρ _ ↦ ENNReal.ofReal (ρ ^ p))
    (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const p))
    (b := fun y ↦ ENNReal.ofReal (b y)) (ENNReal.measurable_ofReal.comp hb)
  rw [key]
  refine ENNReal.mul_lt_top ?_ ?_
  · calc ∫⁻ t in Ioo 0 π, ENNReal.ofReal (Real.sin t ^ p) * ENNReal.ofReal (Real.sin t ^ 4)
        ≤ ∫⁻ _t in Ioo 0 π, 1 := by
          refine setLIntegral_mono measurable_const fun t ht ↦ ?_
          have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _), ← Real.rpow_natCast,
            ← Real.rpow_add hs, ← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (Real.rpow_le_one hs.le (Real.sin_le_one t) (by
            push_cast; linarith))
      _ < ⊤ := by simp
  · have h := hbi.2
    simp only [HasFiniteIntegral] at h
    convert h using 2 with y
    funext y
    rw [Real.enorm_eq_ofReal (hb0 _)]

theorem measurable_indicator_of_continuousOn {n : ℕ} {s : Set (E n)} (hs : IsOpen s)
    {F : E n → ℝ} (hF : ContinuousOn F s) : Measurable (s.indicator F) := by
  classical
  convert hF.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) hs.measurableSet using 1
  funext x
  simp [Set.piecewise, Set.indicator]

namespace ConeData

variable {n : ℕ} (C : ConeData n)

theorem mem_D_radialProj_iff {x : E n} : radialProj x ∈ C.D ↔ x ∈ C.D := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [radialProj]
  · exact C.smul_mem_D_iff (inv_pos.2 (norm_pos_iff.2 hx))

theorem wSq_radialProj (x : E n) : C.wSq (radialProj x) = C.wSq x := by
  simp only [wSq, radialProj_radialProj]

theorem bSq_radialProj (x : E n) : C.bSq (radialProj x) = C.bSq x := by
  simp only [bSq, radialProj_radialProj]

/-- `x ↦ 1_D(x) D_o(x)` is `0`-homogeneous. -/
theorem indicator_dominatorO_radialProj (a : ℝ) (x : E n) :
    C.D.indicator (C.dominatorO a) (radialProj x) = C.D.indicator (C.dominatorO a) x := by
  by_cases hx : x ∈ C.D
  · rw [indicator_of_mem ((C.mem_D_radialProj_iff).2 hx), indicator_of_mem hx]
    simp only [dominatorO, wSq_radialProj, bSq_radialProj]
  · rw [indicator_of_notMem (fun h ↦ hx ((C.mem_D_radialProj_iff).1 h)), indicator_of_notMem hx]

/-- `x ↦ 1_D(x) w(x)^{2a}` is `0`-homogeneous. -/
theorem indicator_wSq_rpow_radialProj (a : ℝ) (x : E n) :
    C.D.indicator (fun y ↦ C.wSq y ^ a) (radialProj x) = C.D.indicator (fun y ↦ C.wSq y ^ a) x := by
  by_cases hx : x ∈ C.D
  · rw [indicator_of_mem ((C.mem_D_radialProj_iff).2 hx), indicator_of_mem hx, wSq_radialProj]
  · rw [indicator_of_notMem (fun h ↦ hx ((C.mem_D_radialProj_iff).1 h)), indicator_of_notMem hx]

variable (hS : C.Sing = {0})
include hS

theorem measurable_indicator_dominatorO (a : ℝ) : Measurable (C.D.indicator (C.dominatorO a)) := by
  have heq : C.D.indicator (C.dominatorO a) = {x | x ∈ C.D ∧ 0 < C.wSq x}.indicator
      (fun x ↦ C.wSq x ^ a * (1 + √(C.bSq x) / √(C.wSq x)) ^ 2) := by
    funext x
    by_cases hx : x ∈ C.D
    · by_cases hw : 0 < C.wSq x
      · rw [indicator_of_mem hx,
          indicator_of_mem (show x ∈ {x | x ∈ C.D ∧ 0 < C.wSq x} from ⟨hx, hw⟩)]
        simp [dominatorO, hw]
      · rw [indicator_of_mem hx, indicator_of_notMem (fun h ↦ hw h.2)]
        simp [dominatorO, hw]
    · rw [indicator_of_notMem hx, indicator_of_notMem (fun h ↦ hx h.1)]
  rw [heq]
  refine measurable_indicator_of_continuousOn (C.isOpen_wSq_pos hS) fun x hx ↦ ?_
  have hw := (C.continuousOn_wSq hS).continuousAt (C.isOpen_D.mem_nhds hx.1)
  have hb := (C.continuousOn_bSq hS).continuousAt (C.isOpen_D.mem_nhds hx.1)
  exact ((hw.rpow_const (Or.inl hx.2.ne')).mul ((continuousAt_const.add
    (hb.sqrt.div hw.sqrt (Real.sqrt_pos.2 hx.2).ne')).pow 2)).continuousWithinAt

theorem measurable_indicator_wSq_rpow {a : ℝ} (ha : 0 < a) :
    Measurable (C.D.indicator fun x ↦ C.wSq x ^ a) :=
  measurable_indicator_of_continuousOn C.isOpen_D fun _ hx ↦
    (((C.continuousOn_wSq hS).continuousAt (C.isOpen_D.mem_nhds hx)).rpow_const
      (Or.inr ha.le)).continuousWithinAt

end ConeData

/-- `2 - 2a = 21/25`. -/
theorem two_sub_two_aExp : 2 - 2 * aExp = 21 / 25 := by norm_num [aExp]

/-- `4 - 2a = 71/25`. -/
theorem four_sub_two_aExp : 4 - 2 * aExp = 71 / 25 := by norm_num [aExp]

/-- **The suspended dominator is integrable**: `ρ^{-2-2a} D_o(π θ)` is integrable on `S⁵`,
since `ρ^{-2-2a} ρ⁴ = ρ^{21/25}` is bounded and `D_o` is integrable on the link. -/
theorem integrable_suspension_dominator (O : ConeData 5) (hO : O.Sing = {0}) :
    Integrable (fun θ : sphere (0 : E 6) 1 ↦
        ‖dropLast θ‖ ^ (-(2 + 2 * aExp)) * O.D.indicator (O.dominatorO aExp) (dropLast θ))
      (volume : Measure (E 6)).toSphere :=
  integrable_sphere_suspension_rpow (by norm_num [aExp]) (O.measurable_indicator_dominatorO hO _)
    (fun _ ↦ indicator_nonneg (fun x _ ↦ O.dominatorO_nonneg _ x) _)
    (O.indicator_dominatorO_radialProj _)
    (O.integrable_dominatorO hO one_half_lt_aExp aExp_lt_one)

/-- **The suspended mass is integrable**: `ρ^{-2a} w_o^{2a}(π θ)` (that is, `w̃^{2a}`) is
integrable on `S⁵`. -/
theorem integrable_suspension_mass (O : ConeData 5) (hO : O.Sing = {0}) :
    Integrable (fun θ : sphere (0 : E 6) 1 ↦
        ‖dropLast θ‖ ^ (-(2 * aExp)) * O.D.indicator (fun x ↦ O.wSq x ^ aExp) (dropLast θ))
      (volume : Measure (E 6)).toSphere :=
  integrable_sphere_suspension_rpow (by norm_num [aExp])
    (O.measurable_indicator_wSq_rpow hO (by norm_num [aExp]))
    (fun _ ↦ indicator_nonneg (fun x _ ↦ Real.rpow_nonneg (O.wSq_nonneg x) _) _)
    (O.indicator_wSq_rpow_radialProj _)
    (O.integrable_wSq_rpow hO (by norm_num [aExp]))

end OnePhaseDimension
