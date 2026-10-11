/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Cutoff.Comparison
public import OnePhaseDimension.Statements.CertificateGen
public import OnePhaseDimension.Statements.Exclusion

/-!
# Exclusion of cones with an isolated singularity

Let `C` be a cone in `ℝⁿ`, `n ≥ 3`, with `C.Sing = {0}` and let `c` satisfy the certificate on
`ℝ^{n-1}` with constants `ε > 0`, `δ ≥ 0`. With a collar `(W, F)` of `C` over the unit sphere and
the cut-offs `ξ_j = ϑ((j + 1) w)` (`Gen.origCutoff`, with `w` built from `F`), the integrated
comparison gives, for every `j`,

  `ε ∫_{D ∩ S^{n-1}} ξ_j² w^{2a} dσ ≤ ∫_{D ∩ S^{n-1}} E_j dσ`,

where `E_j` is the sum of the three cut-off errors. As `j → ∞`:

* `|E_j| ≤ C_F²(κ² + 4Kκ) D_o` (`Gen.abs_cutoffError_origCutoff_le`), with `D_o` integrable, and
  `E_j → 0` pointwise on `D ∩ S^{n-1}`, so `∫ E_j → 0` (`Gen.tendsto_integral_error_orig`);
* `ξ_j² w^{2a} ↑ w^{2a}`, so the left side tends to `ε I_o` (`Gen.tendsto_integral_mass_orig`);
* `I_o = ∫_{D ∩ S^{n-1}} w^{2a} dσ > 0` because `D²u ≢ 0` (`Gen.integral_mass_pos_orig`).

This contradicts `ε > 0` (`Gen.false_of_origCone`). The five-dimensional statements (`n = 6`,
`ε = ε*`, ending in `false_of_origCone6`) are the instances at `n = 6`.

## Differences from the source

The 2026-09-24 version uses the cut-offs `ϑ(j w_o)` for `j ≥ 3` on the link. We use
`ϑ((j + 1) w)` for `j ≥ 0`, with `w` read from the smooth collar function so that the cut-off is
smooth across the free boundary; on `D` it agrees with `ϑ((j + 1) w_o)`. The gradient bound
`|∇ξ_j| ≤ κ |B|/w` uses `|∇√(w²)| ≤ |B|`.

The 2026-09-24 version carries out the argument on `ℝ⁶` only, with the Hardy constant `4` of `S⁵`
and the constants `ε*, δ*`. We carry it out on `ℝⁿ`, `n ≥ 3`, with the Hardy constant
`((n - 2)/2)²` of `S^{n-1}` and the constants `ε, δ` of a certificate on `ℝ^{n-1}`; the steps are
the same.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric Function
open scoped ContDiff Gradient RealInnerProductSpace Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

theorem ne_zero_of_mem_sphere_one {n : ℕ} {x : E n} (hx : x ∈ sphere (0 : E n) 1) : x ≠ 0 := by
  rintro rfl; simp at hx

theorem eventually_two_lt_mul {w : ℝ} (hw : 0 < w) :
    ∀ᶠ j : ℕ in atTop, 2 < ((j + 1 : ℕ) : ℝ) * w := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / w)
  filter_upwards [eventually_ge_atTop N] with j hj
  have hNj : (N : ℝ) ≤ j := by exact_mod_cast hj
  have h2 : 2 < N * w := by rwa [div_lt_iff₀ hw] at hN
  push_cast
  nlinarith

namespace Gen

variable {n : ℕ}

/-! ### The spherical norms at a cone jet -/

/-- At a cone jet, `w` is the spherical Hessian norm. -/
theorem fluxW_eq_sphHessNorm_of_isConeJet {u : E n → ℝ} {J : ConeJets n}
    (h : ConeJets.IsConeJet u J) : fluxW u J.x₀ = sphHessNorm u J.x₀ := by
  rw [h.fluxW_self, normW, sq2, h.sphHessNorm_eq]

/-- At a cone jet, `|B|` is the spherical norm of the third derivative. -/
theorem fluxBNorm_eq_sphBNorm_of_isConeJet {u : E n → ℝ} {J : ConeJets n}
    (h : ConeJets.IsConeJet u J) : fluxBNorm u J.x₀ = sphBNorm u J.x₀ := by
  have hx0 : J.x₀ ≠ 0 := by
    intro h0
    have := h.norm_x₀
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hr := radialProj_of_norm_eq_one h.norm_x₀
  rw [fluxBNorm_eq_of_frame hx0 (by rw [hr]; exact h.inner_ι), hr, h.sphBNorm_eq]
  congr 1
  simp only [sq3, frameB, h.B_eq]

/-! ### The cut-off -/

/-- The cut-off `ξ_j = ϑ((j + 1) w)` on an original cone, with `w` built from `F`. -/
def origCutoff (F : E n → ℝ) (j : ℕ) (x : E n) : ℝ :=
  cutoffProfile (((j + 1 : ℕ) : ℝ) * fluxW F x)

/-- The set `closure D ∩ S^{n-1} ∩ {(j + 1) w ≥ 1}` outside of which `ξ_j` vanishes. -/
def origSupport (C : OnePhaseDimension.ConeData n) (F : E n → ℝ) (j : ℕ) : Set (E n) :=
  closure C.D ∩ sphere 0 1 ∩ {x | 1 ≤ ((j + 1 : ℕ) : ℝ) * fluxW F x}

theorem isZeroHomogeneous_origCutoff (F : E n → ℝ) (j : ℕ) :
    IsZeroHomogeneous (origCutoff F j) := fun r hr x ↦ by
  simp only [origCutoff, isZeroHomogeneous_fluxW F r hr x]

theorem origCutoff_nonneg (F : E n → ℝ) (j : ℕ) (x : E n) : 0 ≤ origCutoff F j x :=
  cutoffProfile_nonneg _

theorem origCutoff_le_one (F : E n → ℝ) (j : ℕ) (x : E n) : origCutoff F j x ≤ 1 :=
  cutoffProfile_le_one _

section Smooth

variable {F : E n → ℝ} (hF : ContDiff ℝ ∞ F)
include hF

theorem continuousAt_scaled_fluxW {x : E n} (hx : x ≠ 0) (j : ℕ) :
    ContinuousAt (fun y ↦ ((j + 1 : ℕ) : ℝ) * fluxW F y) x :=
  continuousAt_const.mul (continuousAt_fluxW hx hF.contDiffAt)

theorem origCutoff_eventuallyEq_zero {x : E n} (hx : x ≠ 0) {j : ℕ}
    (hlt : ((j + 1 : ℕ) : ℝ) * fluxW F x < 1) : origCutoff F j =ᶠ[𝓝 x] 0 := by
  filter_upwards [(continuousAt_scaled_fluxW hF hx j).eventually (gt_mem_nhds hlt)] with y hy
  exact cutoffProfile_eq_zero hy.le

theorem origCutoff_eventuallyEq_one {x : E n} (hx : x ≠ 0) {j : ℕ}
    (hgt : 2 < ((j + 1 : ℕ) : ℝ) * fluxW F x) : origCutoff F j =ᶠ[𝓝 x] 1 := by
  filter_upwards [(continuousAt_scaled_fluxW hF hx j).eventually (lt_mem_nhds hgt)] with y hy
  exact cutoffProfile_eq_one hy.le

theorem isCompact_origSupport (C : OnePhaseDimension.ConeData n) (j : ℕ) :
    IsCompact (origSupport C F j) := by
  have hcl : IsClosed (sphere (0 : E n) 1 ∩
      (fun y ↦ ((j + 1 : ℕ) : ℝ) * fluxW F y) ⁻¹' Ici 1) :=
    ContinuousOn.preimage_isClosed_of_isClosed (fun y hy ↦
      (continuousAt_scaled_fluxW hF (ne_zero_of_mem_sphere_one hy) j).continuousWithinAt)
      isClosed_sphere isClosed_Ici
  have heq : origSupport C F j = closure C.D ∩ (sphere (0 : E n) 1 ∩
      (fun y ↦ ((j + 1 : ℕ) : ℝ) * fluxW F y) ⁻¹' Ici 1) := by
    ext x; simp [origSupport, and_assoc]
  refine (isCompact_sphere (0 : E n) 1).of_isClosed_subset ?_ fun x hx ↦ hx.1.2
  rw [heq]
  exact isClosed_closure.inter hcl

end Smooth

theorem fluxW_pos_of_mem_origSupport {C : OnePhaseDimension.ConeData n} {F : E n → ℝ} {j : ℕ}
    {x : E n} (hx : x ∈ origSupport C F j) : 0 < fluxW F x := by
  have h1 : 1 ≤ ((j + 1 : ℕ) : ℝ) * fluxW F x := hx.2
  by_contra h
  have h0 : fluxW F x = 0 := le_antisymm (not_lt.1 h) (fluxW_nonneg F x)
  rw [h0, mul_zero] at h1
  exact absurd h1 (by norm_num)

/-- The cut-off data of an original cone. -/
theorem isCutoffData_orig {C : OnePhaseDimension.ConeData n} {W : Set (E n)} {F : E n → ℝ}
    (hcol : C.IsCollar W F) (hWs : closure C.D ∩ sphere 0 1 ⊆ W) (j : ℕ) :
    IsCutoffData C W F (origSupport C F j) (origCutoff F j) where
  homog := isZeroHomogeneous_origCutoff F j
  isCompact := isCompact_origSupport hcol.contDiff C j
  subset_sphere := fun _ hx ↦ hx.1.2
  subset_closure := fun _ hx ↦ hx.1.1
  subset_W := fun _ hx ↦ hWs hx.1
  fluxW_pos := fun _ hx ↦ fluxW_pos_of_mem_origSupport hx
  smooth := fun x hx ↦ by
    have hx0 := ne_zero_of_mem_sphere_one hx.1.2
    have hw := fluxW_pos_of_mem_origSupport hx
    filter_upwards [isOpen_ne.mem_nhds hx0, (continuousAt_fluxW hx0
      hcol.contDiff.contDiffAt).eventually (lt_mem_nhds hw)] with y hy0 hyw
    exact contDiff_cutoffProfile.contDiffAt.comp y
      (contDiffAt_const.mul (contDiffAt_fluxW hy0 hcol.contDiff.contDiffAt hyw))
  eventually_zero := fun x hx hxK ↦ by
    have hlt : ((j + 1 : ℕ) : ℝ) * fluxW F x < 1 := by
      by_contra h
      exact hxK ⟨hx, not_lt.1 h⟩
    exact origCutoff_eventuallyEq_zero hcol.contDiff (ne_zero_of_mem_sphere_one hx.2) hlt

/-! ### The errors -/

/-- `|E| ≤ h²|∇ξ|² + 2ξ|h||∇h||∇ξ| + 2ξ|Z||∇ξ|` for `ξ ≥ 0`. -/
theorem abs_cutoffError_le (c : Coeffs (n - 1)) (u ξ : E n → ℝ) (x : E n) (hξ0 : 0 ≤ ξ x) :
    |cutoffError c u ξ x| ≤ fluxH c u x ^ 2 * ‖∇ ξ x‖ ^ 2 +
      2 * ξ x * |fluxH c u x| * ‖∇ (fluxH c u) x‖ * ‖∇ ξ x‖ +
      2 * ξ x * ‖fluxZ c u x‖ * ‖∇ ξ x‖ := by
  have e1 : |fluxH c u x ^ 2 * ‖∇ ξ x‖ ^ 2| = fluxH c u x ^ 2 * ‖∇ ξ x‖ ^ 2 :=
    abs_of_nonneg (by positivity)
  have e2 : |2 * ξ x * fluxH c u x * ⟪∇ (fluxH c u) x, ∇ ξ x⟫| ≤
      2 * ξ x * |fluxH c u x| * ‖∇ (fluxH c u) x‖ * ‖∇ ξ x‖ := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hξ0,
      mul_assoc _ ‖_‖]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
  have e3 : |2 * ξ x * ⟪fluxZ c u x, ∇ ξ x⟫| ≤ 2 * ξ x * ‖fluxZ c u x‖ * ‖∇ ξ x‖ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hξ0,
      mul_assoc _ ‖_‖]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
  unfold cutoffError
  calc _ ≤ |fluxH c u x ^ 2 * ‖∇ ξ x‖ ^ 2 + 2 * ξ x * fluxH c u x * ⟪∇ (fluxH c u) x, ∇ ξ x⟫|
        + |2 * ξ x * ⟪fluxZ c u x, ∇ ξ x⟫| := abs_sub _ _
    _ ≤ _ := by
        have := abs_add_le (fluxH c u x ^ 2 * ‖∇ ξ x‖ ^ 2)
          (2 * ξ x * fluxH c u x * ⟪∇ (fluxH c u) x, ∇ ξ x⟫)
        linarith

/-- The errors vanish where `∇ξ = 0`. -/
theorem cutoffError_eq_zero {c : Coeffs (n - 1)} {u ξ : E n → ℝ} {x : E n} (h : ∇ ξ x = 0) :
    cutoffError c u ξ x = 0 := by
  simp [cutoffError, h]

section Original

variable {C : OnePhaseDimension.ConeData n} (hS : C.Sing = {0}) {W : Set (E n)} {F : E n → ℝ}
  (hcol : C.IsCollar W F) (hWs : closure C.D ∩ sphere 0 1 ⊆ W)
include hS hcol hWs

omit hS hcol in
theorem mem_W_of_mem_D {x : E n} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) : x ∈ W :=
  hWs ⟨subset_closure hx, mem_sphere_zero_iff_norm.2 h1⟩

omit hS in
/-- On `D ∩ S^{n-1}`, the collar's `w` is that of `u`. -/
theorem fluxW_collar_eq {x : E n} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    fluxW F x = fluxW C.u x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at h1
  have hxr := radialProj_of_norm_eq_one h1
  exact (ConeData.IsCollar.fluxW_eventuallyEq hcol hx0 (by rw [hxr]; exact mem_W_of_mem_D hWs hx h1)
    (by rw [hxr]; exact hx)).self_of_nhds

omit hcol hWs in
theorem fluxW_eq_sphHessNorm_of_mem {x : E n} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    fluxW C.u x = sphHessNorm C.u x :=
  fluxW_eq_sphHessNorm_of_isConeJet (C.isConeJet_of_mem_D hS hx h1)

omit hcol hWs in
theorem fluxBNorm_eq_sphBNorm_of_mem {x : E n} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    fluxBNorm C.u x = sphBNorm C.u x :=
  fluxBNorm_eq_sphBNorm_of_isConeJet (C.isConeJet_of_mem_D hS hx h1)

/-- Near a unit point of `D`, the collar's `w` is `√(w²)`. -/
theorem fluxW_collar_eventuallyEq_sqrt {x : E n} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    fluxW F =ᶠ[𝓝 x] fun y ↦ √(C.wSq y) := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at h1
  have hxr := radialProj_of_norm_eq_one h1
  filter_upwards [ConeData.IsCollar.fluxW_eventuallyEq hcol hx0
    (by rw [hxr]; exact mem_W_of_mem_D hWs hx h1)
    (by rw [hxr]; exact hx), C.isOpen_D.mem_nhds hx] with y hy hyD
  have hy0 := C.ne_zero_of_mem_D hyD
  have hzD := C.radialProj_mem_D hyD
  have hz1 := norm_radialProj hy0
  rw [hy, ← (isZeroHomogeneous_fluxW C.u).apply_radialProj hy0,
    fluxW_eq_sphHessNorm_of_mem hS hzD hz1, sphHessNorm_radialProj, C.sphHessNorm_eq_sqrt_wSq]

/-- **The cut-off gradient bound** `|∇ξ_j| ≤ κ |B|/w` at unit points of `D` with `w > 0`. -/
theorem norm_gradient_origCutoff_le {L : ℝ} (hϑ : IsCutoffProfile cutoffProfile L) (j : ℕ)
    {x : E n} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) (hw : 0 < C.wSq x) :
    ‖∇ (origCutoff F j) x‖ ≤ 2 * L * (√(C.bSq x) / √(C.wSq x)) := by
  have hev : origCutoff F j =ᶠ[𝓝 x] fun y ↦ cutoffProfile (((j + 1 : ℕ) : ℝ) * √(C.wSq y)) := by
    filter_upwards [fluxW_collar_eventuallyEq_sqrt hS hcol hWs hx h1] with y hy
    simp only [origCutoff, hy]
  have hf := (C.differentiableAt_sqrt_wSq hS hx hw).hasFDerivAt
  have hA := (hϑ.differentiable (((j + 1 : ℕ) : ℝ) * √(C.wSq x))).hasDerivAt.comp_hasFDerivAt x
    (hf.const_mul ((j + 1 : ℕ) : ℝ))
  have hfd : fderiv ℝ (fun y ↦ cutoffProfile (((j + 1 : ℕ) : ℝ) * √(C.wSq y))) x =
      deriv cutoffProfile (((j + 1 : ℕ) : ℝ) * √(C.wSq x)) •
        (((j + 1 : ℕ) : ℝ) • fderiv ℝ (fun y ↦ √(C.wSq y)) x) := hA.fderiv
  rw [hev.gradient_eq, norm_gradient_eq_norm_fderiv, hfd, norm_smul, norm_smul,
    Real.norm_eq_abs, Real.norm_natCast, ← mul_assoc]
  have hs := Real.sqrt_pos.2 hw
  have hk := hϑ.abs_deriv_mul_le hs (j + 1)
  have hfn := C.norm_fderiv_sqrt_wSq_le hS hx hw
  rw [h1, inv_one, one_mul] at hfn
  calc |deriv cutoffProfile (((j + 1 : ℕ) : ℝ) * √(C.wSq x))| * ((j + 1 : ℕ) : ℝ) *
        ‖fderiv ℝ (fun y ↦ √(C.wSq y)) x‖ ≤ (2 * L / √(C.wSq x)) * √(C.bSq x) :=
        mul_le_mul hk hfn (norm_nonneg _) (div_nonneg (by linarith [hϑ.L_nonneg]) hs.le)
    _ = 2 * L * (√(C.bSq x) / √(C.wSq x)) := by ring

/-- **The non-suspended domination** (`cut:nonsuspended-domination`):
`|E_j| ≤ C_F²(κ² + 4Kκ) D_o` with `κ = 2L` and `K = 1 + M_o`. -/
theorem abs_cutoffError_origCutoff_le {c : Coeffs (n - 1)} {L Cf M : ℝ}
    (hϑ : IsCutoffProfile cutoffProfile L) (hCf : 1 ≤ Cf)
    (hfb : ∀ x ∈ C.D, ‖x‖ = 1 → 0 < fluxW C.u x →
      |fluxH c C.u x| ≤ Cf * fluxW C.u x ^ aExp ∧
      ‖∇ (fluxH c C.u) x‖ ≤
        Cf * fluxW C.u x ^ aExp * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x) ∧
      ‖fluxZ c C.u x‖ ≤
        Cf * fluxW C.u x ^ (2 * aExp) * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x))
    (hM : ∀ x ∈ C.D, ‖x‖ = 1 → sphHessNorm C.u x ≤ M) (j : ℕ) {x : E n} (hx : x ∈ C.D)
    (h1 : ‖x‖ = 1) :
    |cutoffError c C.u (origCutoff F j) x| ≤
      Cf ^ 2 * ((2 * L) ^ 2 + 4 * (1 + M) * (2 * L)) * C.dominatorO aExp x := by
  have hL := hϑ.L_nonneg
  have hM0 : 0 ≤ M := (sphHessNorm_nonneg _ _).trans (hM x hx h1)
  have hx0 : x ≠ 0 := by rintro rfl; simp at h1
  have hWx := fluxW_collar_eq hcol hWs hx h1
  have hwx := fluxW_eq_sphHessNorm_of_mem hS hx h1
  set ξ := origCutoff F j
  by_cases hw : sphHessNorm C.u x = 0
  · have hev : ξ =ᶠ[𝓝 x] 0 :=
      origCutoff_eventuallyEq_zero hcol.contDiff hx0 (by rw [hWx, hwx, hw, mul_zero]; norm_num)
    have hg : ∇ ξ x = 0 := by rw [hev.gradient_eq]; simp [gradient]
    rw [cutoffError_eq_zero hg, abs_zero]
    have := C.dominatorO_nonneg aExp x
    have : 0 ≤ (2 * L) ^ 2 + 4 * (1 + M) * (2 * L) := by positivity
    positivity
  have hwpos : 0 < sphHessNorm C.u x := lt_of_le_of_ne (sphHessNorm_nonneg _ _) (Ne.symm hw)
  have hwSq : 0 < C.wSq x := by
    rw [C.sphHessNorm_eq_sqrt_wSq] at hwpos; exact Real.sqrt_pos.1 hwpos
  have hbx := fluxBNorm_eq_sphBNorm_of_mem hS hx h1
  obtain ⟨hh, hgh, hZ⟩ := hfb x hx h1 (by rw [hwx]; exact hwpos)
  rw [hwx] at hh
  rw [hwx, hbx] at hgh hZ
  have hgξ := norm_gradient_origCutoff_le hS hcol hWs hϑ j hx h1 hwSq
  rw [← C.sphHessNorm_eq_sqrt_wSq, ← C.sphBNorm_eq_sqrt_bSq] at hgξ
  set w := sphHessNorm C.u x
  set b := sphBNorm C.u x / w
  have hb : 0 ≤ b := div_nonneg (sphBNorm_nonneg _ _) hwpos.le
  have hN : 1 + w + b ≤ (1 + M) * 1⁻¹ * (1 + b) := by
    have := hM x hx h1
    rw [inv_one, mul_one]; nlinarith
  have key := errors_le_aux (ρ := 1) (w := w) (b := b) (C := Cf) (K := 1 + M) (κ := 2 * L)
    (a := aExp) (h := fluxH c C.u x) (gh := ‖∇ (fluxH c C.u) x‖) (Z := ‖fluxZ c C.u x‖)
    (N := 1 + w + b) (ξ := ξ x) (gξ := ‖∇ ξ x‖) one_pos hwpos hb hCf (by linarith)
    (by linarith) (origCutoff_le_one F j x) (norm_nonneg _)
    (by rw [inv_one, mul_one]; linarith) (by rwa [inv_one, one_mul]) (norm_nonneg _)
    (by rwa [inv_one, one_mul]) (norm_nonneg _) (by rwa [inv_one, one_mul]) hN
  rw [C.dominatorO_eq hwpos]
  have hE := abs_cutoffError_le c C.u ξ x (origCutoff_nonneg F j x)
  simp only [one_pow, one_mul, Real.one_rpow] at key
  linarith

/-! ### The limits -/

omit hS in
theorem integrable_mass_limit_orig :
    Integrable (fun u : sphere (0 : E n) 1 ↦
      C.D.indicator (fun x ↦ fluxW C.u x ^ (2 * aExp)) u) (volume : Measure (E n)).toSphere :=
  C.integrable_sphere_indicator_of_eq (g := fun x ↦ fluxW F x ^ (2 * aExp))
    (fun x hx ↦ (continuousAt_fluxW (ne_zero_of_mem_sphere_one hx.2)
      hcol.contDiff.contDiffAt).rpow_const (Or.inr (by norm_num [aExp])))
    fun x hx ↦ by
      simp only [fluxW_collar_eq hcol hWs hx.1 (mem_sphere_zero_iff_norm.1 hx.2)]

omit hS in
/-- **The mass converges**: `∫ ξ_j² w^{2a} → I_o = ∫ w^{2a}`. -/
theorem tendsto_integral_mass_orig :
    Tendsto (fun j : ℕ ↦ ∫ u : sphere (0 : E n) 1, C.D.indicator (cutoffMass C.u (origCutoff F j)) u
        ∂(volume : Measure (E n)).toSphere) atTop
      (𝓝 (∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ fluxW C.u x ^ (2 * aExp)) u
        ∂(volume : Measure (E n)).toSphere)) := by
  refine tendsto_integral_of_dominated_convergence _
    (fun j ↦ ((isCutoffData_orig hcol hWs j).integrable_mass hcol).aestronglyMeasurable)
    (integrable_mass_limit_orig hcol hWs) (fun j ↦ ae_of_all _ fun u ↦ ?_)
    (ae_of_all _ fun u ↦ ?_)
  · by_cases hD : (u : E n) ∈ C.D
    · have hr := Real.rpow_nonneg (fluxW_nonneg C.u u) (2 * aExp)
      rw [indicator_of_mem hD, indicator_of_mem hD, Real.norm_eq_abs, cutoffMass,
        abs_of_nonneg (mul_nonneg (sq_nonneg _) hr)]
      exact mul_le_of_le_one_left hr
        (pow_le_one₀ (origCutoff_nonneg F j u) (origCutoff_le_one F j u))
    · simp [indicator_of_notMem hD]
  · by_cases hD : (u : E n) ∈ C.D
    · simp only [indicator_of_mem hD]
      have h1 := norm_eq_of_mem_sphere u
      by_cases hw : fluxW C.u u = 0
      · have h0 : (0 : ℝ) ^ (2 * aExp) = 0 := Real.zero_rpow (by norm_num [aExp])
        simp only [cutoffMass, hw, h0, mul_zero]
        exact tendsto_const_nhds
      · have hwpos : 0 < fluxW C.u u := lt_of_le_of_ne (fluxW_nonneg _ _) (Ne.symm hw)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_two_lt_mul hwpos] with j hj
        have hξ : origCutoff F j u = 1 :=
          cutoffProfile_eq_one (by rw [fluxW_collar_eq hcol hWs hD h1]; exact hj.le)
        simp [cutoffMass, hξ]
    · simp only [indicator_of_notMem hD]
      exact tendsto_const_nhds

/-- **The errors vanish in the limit**: `∫ E_j → 0`. -/
theorem tendsto_integral_error_orig [NeZero n] {c : Coeffs (n - 1)} {ε δ : ℝ}
    (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) :
    Tendsto (fun j : ℕ ↦ ∫ u : sphere (0 : E n) 1,
        C.D.indicator (cutoffError c C.u (origCutoff F j)) u
        ∂(volume : Measure (E n)).toSphere) atTop (𝓝 0) := by
  obtain ⟨L, hϑ⟩ := exists_isCutoffProfile_cutoffProfile
  obtain ⟨Cf, hCf, hfb⟩ := ConeData.exists_fieldBound_const_orig hc hε
  obtain ⟨M₀, -, hMb⟩ := C.exists_wSq_bSq_le hS
  have hM : ∀ x ∈ C.D, ‖x‖ = 1 → sphHessNorm C.u x ≤ √M₀ := fun x hx h1 ↦ by
    rw [C.sphHessNorm_eq_sqrt_wSq]; exact Real.sqrt_le_sqrt (hMb x hx h1).1
  have hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1 := fun y hy ↦ C.sSq_le_one hS hy
  set Cb := Cf ^ 2 * ((2 * L) ^ 2 + 4 * (1 + √M₀) * (2 * L))
  have h := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure (E n)).toSphere) (f := fun _ ↦ (0 : ℝ))
    (fun u : sphere (0 : E n) 1 ↦ Cb * C.D.indicator (C.dominatorO aExp) u)
    (fun j ↦ ((isCutoffData_orig hcol hWs j).integrable_error hc hε hcol hs).aestronglyMeasurable)
    ((C.integrable_dominatorO hS one_half_lt_aExp aExp_lt_one).const_mul Cb)
    (fun j ↦ ae_of_all _ fun u ↦ ?_) (ae_of_all _ fun u ↦ ?_)
  · simpa using h
  · by_cases hD : (u : E n) ∈ C.D
    · rw [indicator_of_mem hD, indicator_of_mem hD, Real.norm_eq_abs]
      exact abs_cutoffError_origCutoff_le hS hcol hWs hϑ hCf (hfb C hS) hM j hD
        (norm_eq_of_mem_sphere u)
    · simp [indicator_of_notMem hD]
  · by_cases hD : (u : E n) ∈ C.D
    · simp only [indicator_of_mem hD]
      have h1 := norm_eq_of_mem_sphere u
      have hu0 : (u : E n) ≠ 0 := ne_zero_of_mem_sphere_one u.2
      have hWu := fluxW_collar_eq hcol hWs hD h1
      refine tendsto_const_nhds.congr' ?_
      by_cases hw : fluxW C.u u = 0
      · refine Eventually.of_forall fun j ↦ ?_
        have hev : origCutoff F j =ᶠ[𝓝 (u : E n)] 0 :=
          origCutoff_eventuallyEq_zero hcol.contDiff hu0 (by rw [hWu, hw, mul_zero]; norm_num)
        have hg : ∇ (origCutoff F j) u = 0 := by rw [hev.gradient_eq]; simp [gradient]
        exact (cutoffError_eq_zero hg).symm
      · have hwpos : 0 < fluxW C.u u := lt_of_le_of_ne (fluxW_nonneg _ _) (Ne.symm hw)
        filter_upwards [eventually_two_lt_mul hwpos] with j hj
        have hev : origCutoff F j =ᶠ[𝓝 (u : E n)] 1 :=
          origCutoff_eventuallyEq_one hcol.contDiff hu0 (by rw [hWu]; exact hj)
        have hg : ∇ (origCutoff F j) u = 0 := by rw [hev.gradient_eq]; simp [gradient]
        exact (cutoffError_eq_zero hg).symm
    · simp only [indicator_of_notMem hD]
      exact tendsto_const_nhds

/-- **`I_o > 0`**: the Hessian of `u` does not vanish identically on `D`. -/
theorem integral_mass_pos_orig :
    0 < ∫ u : sphere (0 : E n) 1, C.D.indicator (fun x ↦ fluxW C.u x ^ (2 * aExp)) u
      ∂(volume : Measure (E n)).toSphere := by
  set σ := (volume : Measure (E n)).toSphere
  obtain ⟨x, hxD, hx2⟩ := C.nonflat
  have hx0 := C.ne_zero_of_mem_D hxD
  set y := radialProj x
  have hyD : y ∈ C.D := C.radialProj_mem_D hxD
  have hy1 : ‖y‖ = 1 := norm_radialProj hx0
  -- `w(y) > 0`
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
  have hwy : 0 < fluxW F y := by
    rw [fluxW_collar_eq hcol hWs hyD hy1, fluxW_eq_sphHessNorm_of_mem hS hyD hy1,
      C.sphHessNorm_eq_sqrt_wSq, C.wSq_radialProj]
    exact Real.sqrt_pos.2 hwx
  -- an open set of the sphere on which the integrand is positive
  set O' := {z : E n | z ∈ C.D ∧ z ≠ 0 ∧ 0 < fluxW F z}
  have hO' : IsOpen O' := by
    refine isOpen_iff_mem_nhds.2 fun z hz ↦ ?_
    filter_upwards [C.isOpen_D.mem_nhds hz.1, isOpen_ne.mem_nhds hz.2.1,
      (continuousAt_fluxW hz.2.1 hcol.contDiff.contDiffAt).eventually (lt_mem_nhds hz.2.2)]
      with z' h1 h2 h3
    exact ⟨h1, h2, h3⟩
  set S : Set (sphere (0 : E n) 1) := (↑) ⁻¹' O'
  have hSo : IsOpen S := hO'.preimage continuous_subtype_val
  have hy0 : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; exact zero_ne_one hy1
  have hSn : S.Nonempty := ⟨⟨y, mem_sphere_zero_iff_norm.2 hy1⟩, hyD, hy0, hwy⟩
  have hsub : S ⊆ Function.support fun u : sphere (0 : E n) 1 ↦
      C.D.indicator (fun x ↦ fluxW C.u x ^ (2 * aExp)) u := by
    intro u hu
    have h1 := norm_eq_of_mem_sphere u
    rw [Function.mem_support, indicator_of_mem hu.1, ← fluxW_collar_eq hcol hWs hu.1 h1]
    exact (Real.rpow_pos_of_pos hu.2.2 _).ne'
  rw [integral_pos_iff_support_of_nonneg
    (fun u ↦ indicator_nonneg (fun x _ ↦ Real.rpow_nonneg (fluxW_nonneg _ _) _) _)
    (integrable_mass_limit_orig hcol hWs)]
  exact (hSo.measure_pos σ hSn).trans_le (measure_mono hsub)

end Original

/-- **No cone with an isolated singularity.** If certificate data on `ℝ^{n-1}` satisfy the
certificate with constants `ε > 0` and `δ ≥ 0`, there is no cone `C` in `ℝⁿ`, `n ≥ 3`, with
`C.Sing = {0}`. -/
theorem false_of_origCone (hn : 3 ≤ n) {c : Coeffs (n - 1)} {ε δ : ℝ}
    (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (C : OnePhaseDimension.ConeData n) (hS : C.Sing = {0}) : False := by
  have : NeZero n := ⟨by omega⟩
  obtain ⟨W, F, hWs', hcol⟩ := C.exists_isCollar (isCompact_sphere (0 : E n) 1)
    (by rw [hS]; exact Set.disjoint_singleton_right.2 (by simp))
  have hWs : closure C.D ∩ sphere 0 1 ⊆ W := fun x hx ↦ hWs' ⟨hx.2, hx.1⟩
  have hs : ∀ y ∈ C.D, ‖∇ C.u y‖ ^ 2 ≤ 1 := fun y hy ↦ C.sSq_le_one hS hy
  have hsign : BoundarySign c C := fun U G x₀ hU hx hG hu hD hgr hΔ hx₀ hx₀D h1 ↦
    ConeData.boundary_signed_flux_nonneg hS hc hε hδ hU hx hG hu hD hgr hΔ hx₀ hx₀D h1
  have hcmp := fun j ↦
    (isCutoffData_orig hcol hWs j).integrated_comparison hn hc hε hcol hs hsign
  have hlim := le_of_tendsto_of_tendsto' ((tendsto_integral_mass_orig hcol hWs).const_mul ε)
    (tendsto_integral_error_orig hS hcol hWs hc hε) hcmp
  have := mul_pos hε (integral_mass_pos_orig hS hcol hWs)
  linarith

/-- **Exclusion of cones with an isolated singularity** in `ℝⁿ`, `n ≥ 3`, from the certificate
on `ℝ^{n-1}`. -/
theorem origConeExclusion_of_certificate (hn : 3 ≤ n) :
    CertificateStatement (n - 1) → OrigConeExclusionStatement n := by
  rintro ⟨ε, δ, hε, hδ, c, hc⟩ C hS
  exact false_of_origCone hn hc hε hδ.le C hS

end Gen

/-! ### The instance `n = 6` -/

/-- The cut-off `ξ_j = ϑ((j + 1) w)` on an original cone, with `w` built from `F`. -/
def origCutoff (F : E 6 → ℝ) (j : ℕ) (x : E 6) : ℝ :=
  cutoffProfile (((j + 1 : ℕ) : ℝ) * fluxW F x)

/-- The set `closure D ∩ S⁵ ∩ {(j + 1) w ≥ 1}` outside of which `ξ_j` vanishes. -/
def origSupport (C : ConeData 6) (F : E 6 → ℝ) (j : ℕ) : Set (E 6) :=
  closure C.D ∩ sphere 0 1 ∩ {x | 1 ≤ ((j + 1 : ℕ) : ℝ) * fluxW F x}

theorem origCutoff_eq_gen (F : E 6 → ℝ) (j : ℕ) : origCutoff F j = Gen.origCutoff F j :=
  rfl

theorem origSupport_eq_gen (C : ConeData 6) (F : E 6 → ℝ) (j : ℕ) :
    origSupport C F j = Gen.origSupport C F j :=
  rfl

theorem isZeroHomogeneous_origCutoff (F : E 6 → ℝ) (j : ℕ) :
    IsZeroHomogeneous (origCutoff F j) :=
  Gen.isZeroHomogeneous_origCutoff F j

theorem origCutoff_nonneg (F : E 6 → ℝ) (j : ℕ) (x : E 6) : 0 ≤ origCutoff F j x :=
  cutoffProfile_nonneg _

theorem origCutoff_le_one (F : E 6 → ℝ) (j : ℕ) (x : E 6) : origCutoff F j x ≤ 1 :=
  cutoffProfile_le_one _

section Smooth

variable {F : E 6 → ℝ} (hF : ContDiff ℝ ∞ F)
include hF

theorem continuousAt_scaled_fluxW {x : E 6} (hx : x ≠ 0) (j : ℕ) :
    ContinuousAt (fun y ↦ ((j + 1 : ℕ) : ℝ) * fluxW F y) x :=
  Gen.continuousAt_scaled_fluxW hF hx j

theorem origCutoff_eventuallyEq_zero {x : E 6} (hx : x ≠ 0) {j : ℕ}
    (hlt : ((j + 1 : ℕ) : ℝ) * fluxW F x < 1) : origCutoff F j =ᶠ[𝓝 x] 0 :=
  Gen.origCutoff_eventuallyEq_zero hF hx hlt

theorem origCutoff_eventuallyEq_one {x : E 6} (hx : x ≠ 0) {j : ℕ}
    (hgt : 2 < ((j + 1 : ℕ) : ℝ) * fluxW F x) : origCutoff F j =ᶠ[𝓝 x] 1 :=
  Gen.origCutoff_eventuallyEq_one hF hx hgt

theorem isCompact_origSupport (C : ConeData 6) (j : ℕ) : IsCompact (origSupport C F j) :=
  Gen.isCompact_origSupport hF C j

end Smooth

theorem fluxW_pos_of_mem_origSupport {C : ConeData 6} {F : E 6 → ℝ} {j : ℕ} {x : E 6}
    (hx : x ∈ origSupport C F j) : 0 < fluxW F x :=
  Gen.fluxW_pos_of_mem_origSupport hx

/-- The cut-off data of an original cone. -/
theorem isCutoffData_orig {C : ConeData 6} {W : Set (E 6)} {F : E 6 → ℝ}
    (hcol : C.IsCollar W F) (hWs : closure C.D ∩ sphere 0 1 ⊆ W) (j : ℕ) :
    IsCutoffData C W F (origSupport C F j) (origCutoff F j) :=
  let h := Gen.isCutoffData_orig hcol hWs j
  ⟨h.homog, h.isCompact, h.subset_sphere, h.subset_closure, h.subset_W, h.fluxW_pos, h.smooth,
    h.eventually_zero⟩

/-- `|E| ≤ h²|∇ξ|² + 2ξ|h||∇h||∇ξ| + 2ξ|Z||∇ξ|` for `ξ ≥ 0`. -/
theorem abs_cutoffError_le (c : Coeffs) (u ξ : E 6 → ℝ) (x : E 6) (hξ0 : 0 ≤ ξ x) :
    |cutoffError c u ξ x| ≤ fluxH c u x ^ 2 * ‖∇ ξ x‖ ^ 2 +
      2 * ξ x * |fluxH c u x| * ‖∇ (fluxH c u) x‖ * ‖∇ ξ x‖ +
      2 * ξ x * ‖fluxZ c u x‖ * ‖∇ ξ x‖ :=
  Gen.abs_cutoffError_le (n := 6) c.toGen u ξ x hξ0

/-- The errors vanish where `∇ξ = 0`. -/
theorem cutoffError_eq_zero {c : Coeffs} {u ξ : E 6 → ℝ} {x : E 6} (h : ∇ ξ x = 0) :
    cutoffError c u ξ x = 0 := by
  simp [cutoffError, h]

section Original

variable {C : ConeData 6} (hS : C.Sing = {0}) {W : Set (E 6)} {F : E 6 → ℝ}
  (hcol : C.IsCollar W F) (hWs : closure C.D ∩ sphere 0 1 ⊆ W)
include hS hcol hWs

omit hS hcol in
theorem mem_W_of_mem_D {x : E 6} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) : x ∈ W :=
  Gen.mem_W_of_mem_D hWs hx h1

omit hS in
/-- On `D ∩ S⁵`, the collar's `w` is that of `u`. -/
theorem fluxW_collar_eq {x : E 6} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    fluxW F x = fluxW C.u x :=
  Gen.fluxW_collar_eq hcol hWs hx h1

omit hcol hWs in
theorem fluxW_eq_sphHessNorm_of_mem {x : E 6} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    fluxW C.u x = sphHessNorm C.u x :=
  Gen.fluxW_eq_sphHessNorm_of_mem hS hx h1

omit hcol hWs in
theorem fluxBNorm_eq_sphBNorm_of_mem {x : E 6} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    fluxBNorm C.u x = sphBNorm C.u x :=
  Gen.fluxBNorm_eq_sphBNorm_of_mem hS hx h1

/-- Near a unit point of `D`, the collar's `w` is `√(w²)`. -/
theorem fluxW_collar_eventuallyEq_sqrt {x : E 6} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) :
    fluxW F =ᶠ[𝓝 x] fun y ↦ √(C.wSq y) :=
  Gen.fluxW_collar_eventuallyEq_sqrt hS hcol hWs hx h1

/-- **The cut-off gradient bound** `|∇ξ_j| ≤ κ |B|/w` at unit points of `D` with `w > 0`. -/
theorem norm_gradient_origCutoff_le {L : ℝ} (hϑ : IsCutoffProfile cutoffProfile L) (j : ℕ)
    {x : E 6} (hx : x ∈ C.D) (h1 : ‖x‖ = 1) (hw : 0 < C.wSq x) :
    ‖∇ (origCutoff F j) x‖ ≤ 2 * L * (√(C.bSq x) / √(C.wSq x)) :=
  Gen.norm_gradient_origCutoff_le hS hcol hWs hϑ j hx h1 hw

/-- **The non-suspended domination** (`cut:nonsuspended-domination`):
`|E_j| ≤ C_F²(κ² + 4Kκ) D_o` with `κ = 2L` and `K = 1 + M_o`. -/
theorem abs_cutoffError_origCutoff_le {c : Coeffs} {L Cf M : ℝ}
    (hϑ : IsCutoffProfile cutoffProfile L) (hCf : 1 ≤ Cf)
    (hfb : ∀ x ∈ C.D, ‖x‖ = 1 → 0 < fluxW C.u x →
      |fluxH c C.u x| ≤ Cf * fluxW C.u x ^ aExp ∧
      ‖∇ (fluxH c C.u) x‖ ≤
        Cf * fluxW C.u x ^ aExp * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x) ∧
      ‖fluxZ c C.u x‖ ≤
        Cf * fluxW C.u x ^ (2 * aExp) * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x))
    (hM : ∀ x ∈ C.D, ‖x‖ = 1 → sphHessNorm C.u x ≤ M) (j : ℕ) {x : E 6} (hx : x ∈ C.D)
    (h1 : ‖x‖ = 1) :
    |cutoffError c C.u (origCutoff F j) x| ≤
      Cf ^ 2 * ((2 * L) ^ 2 + 4 * (1 + M) * (2 * L)) * C.dominatorO aExp x :=
  Gen.abs_cutoffError_origCutoff_le (c := c.toGen) hS hcol hWs hϑ hCf hfb hM j hx h1

/-! ### The limits -/

omit hS in
theorem integrable_mass_limit_orig :
    Integrable (fun u : sphere (0 : E 6) 1 ↦
      C.D.indicator (fun x ↦ fluxW C.u x ^ (2 * aExp)) u) (volume : Measure (E 6)).toSphere :=
  Gen.integrable_mass_limit_orig hcol hWs

omit hS in
/-- **The mass converges**: `∫ ξ_j² w^{2a} → I_o = ∫ w^{2a}`. -/
theorem tendsto_integral_mass_orig :
    Tendsto (fun j : ℕ ↦ ∫ u : sphere (0 : E 6) 1, C.D.indicator (cutoffMass C.u (origCutoff F j)) u
        ∂(volume : Measure (E 6)).toSphere) atTop
      (𝓝 (∫ u : sphere (0 : E 6) 1, C.D.indicator (fun x ↦ fluxW C.u x ^ (2 * aExp)) u
        ∂(volume : Measure (E 6)).toSphere)) :=
  Gen.tendsto_integral_mass_orig hcol hWs

/-- **The errors vanish in the limit**: `∫ E_j → 0`. -/
theorem tendsto_integral_error_orig {c : Coeffs} (hc : CertificateHolds c) :
    Tendsto (fun j : ℕ ↦ ∫ u : sphere (0 : E 6) 1,
        C.D.indicator (cutoffError c C.u (origCutoff F j)) u
        ∂(volume : Measure (E 6)).toSphere) atTop (𝓝 0) :=
  Gen.tendsto_integral_error_orig hS hcol hWs hc.toGen εStar_pos

/-- **`I_o > 0`**: the Hessian of `u` does not vanish identically on `D`. -/
theorem integral_mass_pos_orig :
    0 < ∫ u : sphere (0 : E 6) 1, C.D.indicator (fun x ↦ fluxW C.u x ^ (2 * aExp)) u
      ∂(volume : Measure (E 6)).toSphere :=
  Gen.integral_mass_pos_orig hS hcol hWs

end Original

/-- **No original cone in `ℝ⁶`.** If the certificate holds, there is no cone `C` in `ℝ⁶` with
`C.Sing = {0}`. -/
theorem false_of_origCone6 {c : Coeffs} (hc : CertificateHolds c) (C : ConeData 6)
    (hS : C.Sing = {0}) : False :=
  Gen.false_of_origCone (by norm_num) hc.toGen εStar_pos δStar_pos.le C hS

end OnePhaseDimension
