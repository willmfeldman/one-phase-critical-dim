/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Stability.SecondVariation
public import OnePhaseDimension.Geometry.Polar

/-!
# Dilation invariance of the cone data

For `C : ConeData n` and `r > 0`:

* the selected component, its closure and its frontier are invariant under `x ↦ r x`, the
  singular set is invariant, and `0 ∉ D`;
* the radial projection `x̂ = x/|x|` satisfies `(r x)^ = x̂`, and is smooth away from `0`;
* a chart `u = max F 0` at `r x₀` rescales to the chart `G(y) = r⁻¹ F(r y)` at `x₀`, with
  `∇G(x₀) = ∇F(r x₀)` and `D²G(x₀) = r D²F(r x₀)`. In particular the boundary mean curvature
  `H_E = -D²F(N, N)` scales as `H_E(r x₀) = r⁻¹ H_E(x₀)`;
* the divergence of `a(|x|) Z(x)` for a `0`-homogeneous `Z` tangential at `x` (a pointwise
  version of `divergence_scaled_tangential`).
-/

open Set Filter Topology MeasureTheory Metric Function
open scoped ContDiff Gradient RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

/-! ### The radial projection -/

theorem radialProj_smul_of_pos {r : ℝ} (hr : 0 < r) (x : E n) :
    radialProj (r • x) = radialProj x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  simp only [radialProj, norm_smul, Real.norm_of_nonneg hr.le, smul_smul]
  congr 1
  field_simp

theorem norm_smul_radialProj {x : E n} (hx : x ≠ 0) : ‖x‖ • radialProj x = x := by
  rw [radialProj, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]

theorem contDiffAt_radialProj_of_ne_zero {x : E n} (hx : x ≠ 0) {k : WithTop ℕ∞} :
    ContDiffAt ℝ k radialProj x :=
  ((contDiffAt_norm ℝ hx).inv (norm_ne_zero_iff.2 hx)).smul contDiffAt_id

theorem continuousOn_radialProj : ContinuousOn (radialProj : E n → E n) {x | x ≠ 0} :=
  fun _ hx ↦ (contDiffAt_radialProj_of_ne_zero (k := 0) hx).continuousAt.continuousWithinAt

/-- The open cone `{x ≠ 0 : x̂ ∈ O}` over an open set `O`. -/
theorem isOpen_cone {O : Set (E n)} (hO : IsOpen O) : IsOpen {x : E n | x ≠ 0 ∧ radialProj x ∈ O} :=
  continuousOn_radialProj.isOpen_inter_preimage isOpen_ne hO

/-- Composing with the radial projection gives a `0`-homogeneous function. -/
theorem isZeroHomogeneous_comp_radialProj {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (f : E n → β) : IsZeroHomogeneous fun x ↦ f (radialProj x) :=
  fun _ hr x ↦ by simp only [radialProj_smul_of_pos hr]

/-! ### Dilation invariance of `D` -/

namespace ConeData

variable (C : ConeData n)

theorem u_zero : C.u 0 = 0 := by
  have h := C.homog 2 two_pos 0
  rw [smul_zero] at h
  linarith

theorem zero_notMem_D : (0 : E n) ∉ C.D := fun h ↦ by
  have := C.D_subset_pos h
  simp [C.u_zero] at this

theorem ne_zero_of_mem_D {x : E n} (hx : x ∈ C.D) : x ≠ 0 :=
  ne_of_mem_of_not_mem hx C.zero_notMem_D

theorem smul_mem_D_of_pos {r : ℝ} (hr : 0 < r) {x : E n} (hx : x ∈ C.D) : r • x ∈ C.D := by
  have hpos : ∀ t : ℝ, 0 < t → ∀ y : E n, 0 < C.u y → 0 < C.u (t • y) := fun t ht y hy ↦ by
    rw [C.homog t ht]; exact mul_pos ht hy
  have hbase : r • C.base ∈ connectedComponentIn {x | 0 < C.u x} C.base := by
    have hseg : IsPreconnected ((fun t : ℝ ↦ t • C.base) '' uIcc 1 r) :=
      isPreconnected_uIcc.image _ (continuous_id.smul continuous_const).continuousOn
    refine hseg.subset_connectedComponentIn ⟨1, left_mem_uIcc, one_smul ℝ _⟩ ?_
      ⟨r, right_mem_uIcc, rfl⟩
    rintro _ ⟨t, ht, rfl⟩
    have htpos : 0 < t := (lt_inf_iff.2 ⟨one_pos, hr⟩).trans_le ht.1
    exact hpos t htpos _ C.base_pos
  rw [C.D_eq] at hx ⊢
  rw [connectedComponentIn_eq hbase]
  have himg : IsPreconnected
      ((fun y : E n ↦ r • y) '' connectedComponentIn {x | 0 < C.u x} C.base) :=
    isPreconnected_connectedComponentIn.image _ (continuous_const_smul r).continuousOn
  refine himg.subset_connectedComponentIn ⟨C.base, mem_connectedComponentIn C.base_pos, rfl⟩ ?_
    ⟨x, hx, rfl⟩
  rintro _ ⟨y, hy, rfl⟩
  exact hpos r hr y (connectedComponentIn_subset {x | 0 < C.u x} C.base hy)

theorem smul_mem_D_iff {r : ℝ} (hr : 0 < r) {x : E n} : r • x ∈ C.D ↔ x ∈ C.D := by
  refine ⟨fun h ↦ ?_, C.smul_mem_D_of_pos hr⟩
  have := C.smul_mem_D_of_pos (inv_pos.2 hr) h
  rwa [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at this

theorem smul_mem_closure_D {r : ℝ} (hr : 0 < r) {x : E n} (hx : x ∈ closure C.D) :
    r • x ∈ closure C.D := by
  have h := image_closure_subset_closure_image (f := fun y : E n ↦ r • y) (s := C.D)
    (continuous_const_smul r) ⟨x, hx, rfl⟩
  exact closure_mono (by rintro _ ⟨y, hy, rfl⟩; exact C.smul_mem_D_of_pos hr hy) h

theorem smul_mem_frontier_D {r : ℝ} (hr : 0 < r) {x : E n} (hx : x ∈ frontier C.D) :
    r • x ∈ frontier C.D := by
  rw [C.isOpen_D.frontier_eq] at hx ⊢
  exact ⟨C.smul_mem_closure_D hr hx.1, fun h ↦ hx.2 ((C.smul_mem_D_iff hr).1 h)⟩

theorem smul_mem_sing_iff {r : ℝ} (hr : 0 < r) {x : E n} : r • x ∈ C.Sing ↔ x ∈ C.Sing := by
  refine ⟨fun h ↦ ?_, C.sing_smul r hr x⟩
  have := C.sing_smul r⁻¹ (inv_pos.2 hr) _ h
  rwa [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at this

theorem radialProj_mem_D {x : E n} (hx : x ∈ C.D) : radialProj x ∈ C.D :=
  C.smul_mem_D_of_pos (inv_pos.2 (norm_pos_iff.2 (C.ne_zero_of_mem_D hx))) hx

theorem ne_zero_of_notMem_sing {x : E n} (hx : x ∉ C.Sing) : x ≠ 0 :=
  fun h ↦ hx (h ▸ C.zero_mem_sing)

/-- A function `0`-homogeneous on `D` agrees on `D` with its `0`-homogeneous extension. -/
theorem apply_radialProj_of_mem_D {β : Type*} {f : E n → β}
    (hf : ∀ r : ℝ, 0 < r → ∀ x ∈ C.D, f (r • x) = f x) {x : E n} (hx : x ∈ C.D) :
    f (radialProj x) = f x :=
  hf _ (inv_pos.2 (norm_pos_iff.2 (C.ne_zero_of_mem_D hx))) x hx

theorem eventuallyEq_comp_radialProj {β : Type*} {f : E n → β}
    (hf : ∀ r : ℝ, 0 < r → ∀ x ∈ C.D, f (r • x) = f x) {x : E n} (hx : x ∈ C.D) :
    (fun y ↦ f (radialProj y)) =ᶠ[𝓝 x] f := by
  filter_upwards [C.isOpen_D.mem_nhds hx] with y hy
  exact C.apply_radialProj_of_mem_D hf hy

/-- A function `0`-homogeneous on `D` that vanishes on `closure D ∩ S^{n-1} \ K` vanishes near
every point `x ∈ D` with `x̂ ∉ K`. -/
theorem eventuallyEq_zero_of_radialProj_notMem {β : Type*} [Zero β] {f : E n → β}
    (hf : ∀ r : ℝ, 0 < r → ∀ x ∈ C.D, f (r • x) = f x) {K : Set (E n)} (hK : IsClosed K)
    (hsupp : ∀ x ∈ closure C.D ∩ sphere 0 1, x ∉ K → f x = 0) {x : E n} (hx : x ∈ C.D)
    (hxK : radialProj x ∉ K) : f =ᶠ[𝓝 x] 0 := by
  have hopen : IsOpen ({y : E n | y ≠ 0 ∧ radialProj y ∈ Kᶜ} ∩ C.D) :=
    (isOpen_cone hK.isOpen_compl).inter C.isOpen_D
  filter_upwards [hopen.mem_nhds ⟨⟨C.ne_zero_of_mem_D hx, hxK⟩, hx⟩] with y hy
  rw [← C.apply_radialProj_of_mem_D hf hy.2]
  exact hsupp _ ⟨subset_closure (C.radialProj_mem_D hy.2),
    mem_sphere_zero_iff_norm.2 (norm_radialProj (C.ne_zero_of_mem_D hy.2))⟩ hy.1.2

/-- The `0`-homogeneous indicator `x ↦ 1_D(x) g(x̂)`. -/
theorem isZeroHomogeneous_indicator (g : E n → ℝ) :
    IsZeroHomogeneous (C.D.indicator fun y ↦ g (radialProj y)) := by
  intro r hr x
  by_cases hx : x ∈ C.D
  · rw [indicator_of_mem ((C.smul_mem_D_iff hr).2 hx), indicator_of_mem hx,
      radialProj_smul_of_pos hr]
  · rw [indicator_of_notMem (mt (C.smul_mem_D_iff hr).1 hx), indicator_of_notMem hx]

end ConeData

/-! ### Rescaled charts -/

section Rescale

variable {F : E n → ℝ} {U : Set (E n)} {r : ℝ}

theorem hasFDerivAt_rescale (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hr : 0 < r) {y : E n}
    (hy : r • y ∈ U) :
    HasFDerivAt (fun z ↦ r⁻¹ * F (r • z)) (fderiv ℝ F (r • y)) y := by
  have hd : DifferentiableAt ℝ F (r • y) :=
    (hF.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)
  have h := (hd.hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul r)).const_mul r⁻¹
  refine h.congr_fderiv ?_
  ext v
  simp [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hr.ne']

/-- **Rescaled chart.** If `u = max F 0` on `U` is a chart at `r x₀`, then
`G(y) = r⁻¹ F(r y)` is a chart at `x₀` on `r⁻¹ U`, with `∇G(x₀) = ∇F(r x₀)` and
`D²G(x₀)(v, w) = r D²F(r x₀)(v, w)`. -/
theorem ConeData.rescale_chart (C : ConeData n) (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hr : 0 < r) (hu : ∀ x ∈ U, C.u x = max (F x) 0) (hD : ∀ x ∈ U, 0 < F x → x ∈ C.D)
    {x₀ : E n} (hx₀ : r • x₀ ∈ U) :
    IsOpen ((fun y : E n ↦ r • y) ⁻¹' U) ∧ x₀ ∈ (fun y : E n ↦ r • y) ⁻¹' U ∧
      ContDiffOn ℝ ∞ (fun z ↦ r⁻¹ * F (r • z)) ((fun y : E n ↦ r • y) ⁻¹' U) ∧
      (∀ x ∈ (fun y : E n ↦ r • y) ⁻¹' U, C.u x = max (r⁻¹ * F (r • x)) 0) ∧
      (∀ x ∈ (fun y : E n ↦ r • y) ⁻¹' U, 0 < r⁻¹ * F (r • x) → x ∈ C.D) ∧
      ∇ (fun z ↦ r⁻¹ * F (r • z)) x₀ = ∇ F (r • x₀) ∧
      ∀ v w, fderiv ℝ (fun y ↦ fderiv ℝ (fun z ↦ r⁻¹ * F (r • z)) y) x₀ v w =
        r * fderiv ℝ (fun y ↦ fderiv ℝ F y) (r • x₀) v w := by
  set V := (fun y : E n ↦ r • y) ⁻¹' U
  have hcont : Continuous fun y : E n ↦ r • y := continuous_const_smul r
  have hV : IsOpen V := hU.preimage hcont
  have hfd : ∀ y ∈ V, fderiv ℝ (fun z ↦ r⁻¹ * F (r • z)) y = fderiv ℝ F (r • y) :=
    fun y hy ↦ (hasFDerivAt_rescale hU hF hr hy).fderiv
  refine ⟨hV, hx₀, ?_, fun x hx ↦ ?_, fun x hx hpos ↦ ?_, ?_, fun v w ↦ ?_⟩
  · exact contDiffOn_const.mul (hF.comp (contDiff_const_smul r).contDiffOn fun y hy ↦ hy)
  · have h := C.homog r hr x
    rw [hu _ hx] at h
    have hu' : C.u x = r⁻¹ * max (F (r • x)) 0 := by
      rw [h, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
    rw [hu', mul_max_of_nonneg _ _ (inv_nonneg.2 hr.le), mul_zero]
  · have : 0 < F (r • x) := by
      have := mul_pos hr hpos
      rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
    exact (C.smul_mem_D_iff hr).1 (hD _ hx this)
  · simp only [gradient, hfd x₀ hx₀]
  · have hev : (fun y ↦ fderiv ℝ (fun z ↦ r⁻¹ * F (r • z)) y) =ᶠ[𝓝 x₀]
        fun y ↦ fderiv ℝ F (r • y) := by
      filter_upwards [hV.mem_nhds hx₀] with y hy
      exact hfd y hy
    have hd2 : DifferentiableAt ℝ (fun y ↦ fderiv ℝ F y) (r • x₀) := by
      have h1 := (hF.contDiffAt (hU.mem_nhds hx₀)).fderiv_right (m := 1) (by simp)
      exact h1.differentiableAt one_ne_zero
    have h2 : HasFDerivAt (fun y ↦ fderiv ℝ F (r • y))
        ((fderiv ℝ (fun y ↦ fderiv ℝ F y) (r • x₀)).comp (r • ContinuousLinearMap.id ℝ (E n)))
        x₀ :=
      hd2.hasFDerivAt.comp x₀ ((hasFDerivAt_id x₀).const_smul r)
    rw [hev.fderiv_eq, h2.fderiv]
    simp [smul_eq_mul]

end Rescale

/-! ### Divergence of a radially scaled field -/

/-- **Scaling of the divergence, pointwise.** For `Y(x) = a(|x|) Z(x)` with `Z` `0`-homogeneous
and `⟪x, Z(x)⟫ = 0`, `div Y(x) = a(|x|) |x|⁻¹ (div Z)(x̂)`. -/
theorem divergence_scaled_of_inner_eq_zero {Z : E n → E n} (hZ : IsZeroHomogeneous Z)
    {a : ℝ → ℝ} {x : E n} (hx : x ≠ 0) (hZt : ⟪x, Z x⟫ = 0)
    (ha : DifferentiableAt ℝ a ‖x‖) (hd : DifferentiableAt ℝ Z x) :
    divergence (fun y ↦ a ‖y‖ • Z y) x = a ‖x‖ * ‖x‖⁻¹ * divergence Z (radialProj x) := by
  have hA : HasFDerivAt (fun y : E n ↦ a ‖y‖)
      ((fderiv ℝ a ‖x‖).comp (realInnerCLM (radialProj x))) x :=
    ha.hasFDerivAt.comp x (hasFDerivAt_norm hx)
  have hprod : HasFDerivAt (fun y ↦ a ‖y‖ • Z y) _ x := hA.smul hd.hasFDerivAt
  have hrad : ⟪radialProj x, Z x⟫ = 0 := by
    rw [radialProj, real_inner_smul_left, hZt, mul_zero]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  set c : E n →L[ℝ] ℝ := (fderiv ℝ a ‖x‖).comp (realInnerCLM (radialProj x))
  have htr :
      LinearMap.trace ℝ (E n) (c.smulRight (Z x) : E n →ₗ[ℝ] E n) = 0 := by
    have h := LinearMap.trace_smulRight (c : E n →ₗ[ℝ] ℝ) (Z x)
    refine (Eq.trans ?_ h).trans ?_
    · rfl
    · simp [c, hrad]
  rw [hZ.divergence_radialProj hx hd, divergence, hprod.fderiv,
    ContinuousLinearMap.toLinearMap_add, map_add, ContinuousLinearMap.toLinearMap_smul, map_smul,
    ← divergence, htr, smul_eq_mul, add_zero]
  field_simp

theorem divergence_congr {Z₁ Z₂ : E n → E n} {x : E n} (h : Z₁ =ᶠ[𝓝 x] Z₂) :
    divergence Z₁ x = divergence Z₂ x := by
  rw [divergence, divergence, h.fderiv_eq]

end OnePhaseDimension
