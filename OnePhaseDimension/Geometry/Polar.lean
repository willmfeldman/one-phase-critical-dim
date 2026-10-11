/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.Homogeneous
public import OnePhaseDimension.Vendor.TauCeti.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Polar integration of separated functions

Spherical integrals are taken against Mathlib's surface measure `volume.toSphere` on the unit
sphere: the spherical integral of a `0`-homogeneous function `f` is
`∫ u : sphere 0 1, f u ∂(volume.toSphere)`.

* `integral_cone_separated`: for a `0`-homogeneous `f` and a radial profile `ρ`,
  `∫_{ℝⁿ} ρ(|x|) f(x) dx = (∫₀^∞ r^{n-1} ρ(r) dr) · ∫_{S^{n-1}} f dσ`.
* `measurePreserving_sphereMap`: `volume.toSphere` is invariant under linear isometries, and
  `integral_toSphere_comp_linearIsometryEquiv` is the corresponding change of variables.
-/

open MeasureTheory Metric Set
open scoped Pointwise

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

theorem finrank_E (n : ℕ) : Module.finrank ℝ (E n) = n := finrank_euclideanSpace_fin

/-- **Polar separation.** For a `0`-homogeneous `f` and a radial profile `ρ` such that
`x ↦ ρ(|x|) f(x)` is integrable,
`∫ ρ(|x|) f(x) dx = (∫_{(0, ∞)} r^{n-1} ρ(r) dr) · ∫_{S^{n-1}} f d(volume.toSphere)`. -/
theorem integral_cone_separated [NeZero n] {f : E n → ℝ} (hf : IsZeroHomogeneous f) (ρ : ℝ → ℝ)
    (hint : Integrable fun x : E n ↦ ρ ‖x‖ * f x) :
    ∫ x : E n, ρ ‖x‖ * f x =
      (∫ r in Ioi (0 : ℝ), r ^ (n - 1) * ρ r) *
        ∫ u : sphere (0 : E n) 1, f u ∂(volume : Measure (E n)).toSphere := by
  have : Nontrivial (E n) := by
    have : 0 < Module.finrank ℝ (E n) := by rw [finrank_E]; exact Nat.pos_of_neZero n
    exact Module.nontrivial_of_finrank_pos this
  rw [TauCeti.integral_eq_integral_Ioi_integral_toSphere _ hint, finrank_E, ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) ↦ ?_
  have hu : ∀ u : sphere (0 : E n) 1, ρ ‖r • (u : E n)‖ * f (r • (u : E n)) = ρ r * f u := by
    intro u
    rw [norm_smul, norm_eq_of_mem_sphere u, mul_one, Real.norm_of_nonneg hr.le, hf r hr]
  simp_rw [hu, integral_const_mul, smul_eq_mul]
  ring

/-- A linear isometry restricted to the unit sphere. -/
def sphereMap (R : E n ≃ₗᵢ[ℝ] E n) (u : sphere (0 : E n) 1) : sphere (0 : E n) 1 :=
  ⟨R u, by simp [norm_eq_of_mem_sphere u]⟩

@[simp] theorem coe_sphereMap (R : E n ≃ₗᵢ[ℝ] E n) (u : sphere (0 : E n) 1) :
    (sphereMap R u : E n) = R u := rfl

theorem continuous_sphereMap (R : E n ≃ₗᵢ[ℝ] E n) : Continuous (sphereMap R) :=
  (R.continuous.comp continuous_subtype_val).subtype_mk _

/-- **Rotation invariance of the surface measure.** -/
theorem measurePreserving_sphereMap (R : E n ≃ₗᵢ[ℝ] E n) :
    MeasurePreserving (sphereMap R) (volume : Measure (E n)).toSphere
      (volume : Measure (E n)).toSphere := by
  have hmeas := (continuous_sphereMap R).measurable
  refine ⟨hmeas, ?_⟩
  ext s hs
  rw [Measure.map_apply hmeas hs, Measure.toSphere_apply' _ (hmeas hs),
    Measure.toSphere_apply' _ hs]
  congr 1
  have himg : (Ioo (0 : ℝ) 1 • ((↑) '' (sphereMap R ⁻¹' s)) : Set (E n)) =
      R.toMeasurableEquiv ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext x
    simp only [mem_smul, mem_image, mem_preimage, LinearIsometryEquiv.coe_toMeasurableEquiv]
    constructor
    · rintro ⟨t, ht, _, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨t, ht, R u, ⟨sphereMap R u, hu, rfl⟩, by simp⟩
    · rintro ⟨t, ht, _, ⟨w, hw, rfl⟩, hx⟩
      refine ⟨t, ht, R.symm w, ⟨⟨R.symm w, by simp [norm_eq_of_mem_sphere w]⟩, ?_, rfl⟩, ?_⟩
      · have : sphereMap R ⟨R.symm w, by simp [norm_eq_of_mem_sphere w]⟩ = w :=
          Subtype.ext (by simp)
        rw [this]
        exact hw
      · rw [← map_smul, hx, LinearIsometryEquiv.symm_apply_apply]
  rw [himg, (R.measurePreserving : MeasurePreserving R.toMeasurableEquiv volume volume)
    |>.measure_preimage_equiv]

theorem toSphere_map_linearIsometryEquiv (R : E n ≃ₗᵢ[ℝ] E n) :
    Measure.map (sphereMap R) (volume : Measure (E n)).toSphere =
      (volume : Measure (E n)).toSphere :=
  (measurePreserving_sphereMap R).map_eq

/-- Change of variables on the sphere under a linear isometry. -/
theorem integral_toSphere_comp_linearIsometryEquiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (R : E n ≃ₗᵢ[ℝ] E n) (f : E n → F) :
    ∫ u : sphere (0 : E n) 1, f (R u) ∂(volume : Measure (E n)).toSphere =
      ∫ u : sphere (0 : E n) 1, f u ∂(volume : Measure (E n)).toSphere := by
  have hinj : Function.Injective (sphereMap R) := fun u v h ↦
    Subtype.ext (R.injective (congrArg Subtype.val h))
  have hemb : MeasurableEmbedding (sphereMap R) :=
    ((continuous_sphereMap R).isClosedEmbedding hinj).measurableEmbedding
  exact (measurePreserving_sphereMap R).integral_comp hemb fun u ↦ f u

end OnePhaseDimension
