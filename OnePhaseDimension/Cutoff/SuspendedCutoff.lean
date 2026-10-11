/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Cutoff.SuspendedMeasure

/-!
# The product cutoff on the suspension and its dominations

Let `W = O × ℝ` be the suspension of a cone `O` in `ℝ⁵` with `O.Sing = {0}`, `π = dropLast`,
`w_o = |D²u_o(x̂)|` and `b_o = |B_o|/w_o`. Fix a profile `ϑ` (`IsCutoffProfile ϑ L`): `0 ≤ ϑ ≤ 1`,
`ϑ = 0` on `(-∞, 1]`, `ϑ = 1` on `[2, ∞)` and `|ϑ'| ≤ L`; put `κ = 2L`. The product cutoff is

  `ξ_j(z) = ϑ(j w_o(π z)) ϑ(j |π z|/|z|)`,

that is `ξ_j = α_j(y) β_j(t)` with `α_j = ϑ(j w_o)`, `β_j = ϑ(j sin t)` in the suspension
coordinates `z = (sin t · y, cos t)`. At a unit point `z` of the component of `W`, with
`ρ = |π z|`:

* `norm_gradient_suspCutoff_le`: `|∇ξ_j(z)| ≤ κ ρ⁻¹ (1 + b_o)`;
* `errors_le_susp`: for the three cutoff errors `E₁ = h²|∇ξ|²`, `E₂ = 2ξh⟨∇h, ∇ξ⟩` and
  `E₃ = -2ξ⟨Z, ∇ξ⟩`, with field bounds of constant `C_F ≥ 1` and `w_o ≤ M_o`,
  `ρ⁴(|E₁| + |E₂| + |E₃|) ≤ C_F²(κ² + 4K_sκ) ρ^{2-2a} D_o(π z)`, `K_s = 1 + M_o + √3`;
* `suspCutoff_eventually_eq_one`: where `w_o > 0`, `ξ_j = 1` near `z` for all large `j`, so the
  errors vanish eventually (`errors_eventually_zero_susp`); where `w_o = 0`, `ξ_j = 0` near `z`
  (`suspCutoff_eventuallyEq_zero`).

## Differences from the source

The 2026-09-24 version uses the exact orthogonal identity
`|∇ξ_j|² = α_j²|β_j'|² + sin⁻²t β_j²|∇_o α_j|²` from the warped metric. We bound the ambient
gradient of the product by the triangle inequality, `|∇ξ_j| ≤ |∇α_j| + |∇β_j|`, which gives the
same bound `κ ρ⁻¹ (1 + b_o)`. The tip factor is `ϑ(j|π z|/|z|)`, whose gradient at a unit point has
norm `|ϑ'| j |cos t|`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Function Filter Topology Set Metric MeasureTheory EllipticBernoulli
open scoped ContDiff RealInnerProductSpace Gradient Real

@[expose] public noncomputable section

namespace OnePhaseDimension

/-! ### The profile -/

/-- A cutoff profile: `ϑ` differentiable, `0 ≤ ϑ ≤ 1`, `ϑ = 0` on `(-∞, 1]`, `ϑ = 1` on
`[2, ∞)` and `|ϑ'| ≤ L`. -/
structure IsCutoffProfile (ϑ : ℝ → ℝ) (L : ℝ) : Prop where
  differentiable : Differentiable ℝ ϑ
  nonneg : ∀ r, 0 ≤ ϑ r
  le_one : ∀ r, ϑ r ≤ 1
  eq_zero : ∀ r ≤ 1, ϑ r = 0
  eq_one : ∀ r, 2 ≤ r → ϑ r = 1
  abs_deriv_le : ∀ r, |deriv ϑ r| ≤ L

namespace IsCutoffProfile

variable {ϑ : ℝ → ℝ} {L : ℝ} (hϑ : IsCutoffProfile ϑ L)
include hϑ

theorem L_nonneg : 0 ≤ L := (abs_nonneg _).trans (hϑ.abs_deriv_le 0)

/-- `ϑ'` vanishes outside `(1, 2)`. -/
theorem deriv_eq_zero_of_notMem {r : ℝ} (hr : r ∉ Ioo 1 2) : deriv ϑ r = 0 := by
  rcases le_or_gt r 1 with h1 | h1
  · have hmin : IsLocalMin ϑ r := by
      filter_upwards with s
      rw [hϑ.eq_zero r h1]
      exact hϑ.nonneg s
    exact hmin.deriv_eq_zero
  · have h2 : 2 ≤ r := by
      by_contra h
      exact hr ⟨h1, not_le.1 h⟩
    have hmax : IsLocalMax ϑ r := by
      filter_upwards with s
      rw [hϑ.eq_one r h2]
      exact hϑ.le_one s
    exact hmax.deriv_eq_zero

/-- `|ϑ'(j s)| j ≤ 2L/s` for `s > 0`: where `ϑ'(j s) ≠ 0`, `j s < 2`. -/
theorem abs_deriv_mul_le {s : ℝ} (hs : 0 < s) (j : ℕ) :
    |deriv ϑ (j * s)| * j ≤ 2 * L / s := by
  by_cases h : j * s ∈ Ioo 1 2
  · have hj : (j : ℝ) ≤ 2 / s := by
      rw [le_div_iff₀ hs]; exact h.2.le
    calc |deriv ϑ (j * s)| * j ≤ L * (2 / s) :=
          mul_le_mul (hϑ.abs_deriv_le _) hj (Nat.cast_nonneg j) hϑ.L_nonneg
      _ = 2 * L / s := by ring
  · rw [hϑ.deriv_eq_zero_of_notMem h, abs_zero, zero_mul]
    exact div_nonneg (mul_nonneg zero_le_two hϑ.L_nonneg) hs.le

end IsCutoffProfile

/-! ### The cutoff -/

/-- The product cutoff `ξ_j(z) = ϑ(j w(π z)) ϑ(j |π z|/|z|)` on `ℝ⁶`. -/
def suspCutoff (ϑ : ℝ → ℝ) (j : ℕ) (w : E 5 → ℝ) (z : E 6) : ℝ :=
  ϑ (j * w (dropLast z)) * ϑ (j * (‖dropLast z‖ / ‖z‖))

theorem suspCutoff_nonneg {ϑ : ℝ → ℝ} {L : ℝ} (hϑ : IsCutoffProfile ϑ L) (j : ℕ) (w : E 5 → ℝ)
    (z : E 6) : 0 ≤ suspCutoff ϑ j w z :=
  mul_nonneg (hϑ.nonneg _) (hϑ.nonneg _)

theorem suspCutoff_le_one {ϑ : ℝ → ℝ} {L : ℝ} (hϑ : IsCutoffProfile ϑ L) (j : ℕ)
    (w : E 5 → ℝ) (z : E 6) : suspCutoff ϑ j w z ≤ 1 :=
  (mul_le_mul (hϑ.le_one _) (hϑ.le_one _) (hϑ.nonneg _) zero_le_one).trans_eq (mul_one 1)

/-! ### The tip factor -/

section Tip

variable {z : E 6}

/-- The derivative of `q(z) = |π z|/|z|`. -/
theorem hasFDerivAt_tipRatio (hz : z ≠ 0) (hπ : dropLast z ≠ 0) :
    HasFDerivAt (fun z : E 6 ↦ ‖dropLast z‖ / ‖z‖)
      (‖dropLast z‖ • ((-(‖z‖ ^ 2)⁻¹) • innerSL ℝ (radialProj z)) +
        ‖z‖⁻¹ • (innerSL ℝ (radialProj (dropLast z))).comp dropLast) z := by
  have h1 : HasFDerivAt (fun z : E 6 ↦ ‖dropLast z‖)
      ((innerSL ℝ (radialProj (dropLast z))).comp dropLast) z :=
    (hasFDerivAt_norm hπ).comp z dropLast.hasFDerivAt
  have h2 : HasFDerivAt (fun z : E 6 ↦ ‖z‖⁻¹)
      ((-(‖z‖ ^ 2)⁻¹) • innerSL ℝ (radialProj z)) z :=
    (hasDerivAt_inv (norm_ne_zero_iff.2 hz)).comp_hasFDerivAt z (hasFDerivAt_norm hz)
  exact h1.mul h2

/-- `|∇q(z)| ≤ 1` at a unit point (in fact `|∇q|² = 1 - ρ²`). -/
theorem norm_fderiv_tipRatio_le (hz1 : ‖z‖ = 1) (hπ : dropLast z ≠ 0) :
    ‖‖dropLast z‖ • ((-(‖z‖ ^ 2)⁻¹) • innerSL ℝ (radialProj z)) +
        ‖z‖⁻¹ • (innerSL ℝ (radialProj (dropLast z))).comp dropLast‖ ≤ 1 := by
  set ρ := ‖dropLast z‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.2 hπ
  set y := radialProj (dropLast z)
  have hy1 : ‖y‖ = 1 := norm_radialProj hπ
  have hrz : radialProj z = z := radialProj_of_norm_eq_one hz1
  set g : E 6 := dropLast.adjoint y - ρ • z
  have hyz : ⟪dropLast.adjoint y, z⟫ = ρ := by
    rw [ContinuousLinearMap.adjoint_inner_left]
    have : dropLast z = ρ • y := (norm_smul_radialProj hπ).symm
    rw [this, real_inner_smul_right, real_inner_self_eq_norm_sq, hy1]
    ring
  have hg : ‖g‖ ^ 2 ≤ 1 := by
    rw [norm_sub_sq_real, real_inner_smul_right, hyz, norm_smul, Real.norm_of_nonneg hρ.le, hz1,
      norm_dropLast_adjoint, hy1]
    nlinarith [sq_nonneg ρ]
  have hg1 : ‖g‖ ≤ 1 := by nlinarith [norm_nonneg g]
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v ↦ ?_
  have hv : (‖dropLast z‖ • ((-(‖z‖ ^ 2)⁻¹) • innerSL ℝ (radialProj z)) +
      ‖z‖⁻¹ • (innerSL ℝ (radialProj (dropLast z))).comp dropLast) v = ⟪g, v⟫ := by
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul, hz1, hrz, g,
      inner_sub_left, real_inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
    norm_num
    ring
  rw [hv, Real.norm_eq_abs]
  calc |⟪g, v⟫| ≤ ‖g‖ * ‖v‖ := abs_real_inner_le_norm g v
    _ ≤ 1 * ‖v‖ := by gcongr

end Tip

/-! ### The gradient of `w = √(w²)` -/

namespace ConeData

variable {n : ℕ} (C : ConeData n) (hS : C.Sing = {0})
include hS

theorem differentiableAt_sqrt_wSq {x : E n} (hx : x ∈ C.D) (hw : 0 < C.wSq x) :
    DifferentiableAt ℝ (fun y ↦ √(C.wSq y)) x :=
  ((C.contDiffAt_wSq hS (C.ne_zero_of_mem_D hx) (C.radialProj_mem_D hx) 1).differentiableAt
    one_ne_zero).sqrt hw.ne'

/-- **`|∇w| ≤ |B|`, scaled**: `|∇w(x)| ≤ |x|⁻¹ |B|(x)` on `{w > 0} ∩ D`. -/
theorem norm_fderiv_sqrt_wSq_le {x : E n} (hx : x ∈ C.D) (hw : 0 < C.wSq x) :
    ‖fderiv ℝ (fun y ↦ √(C.wSq y)) x‖ ≤ ‖x‖⁻¹ * √(C.bSq x) := by
  have hx0 := C.ne_zero_of_mem_D hx
  set y := radialProj x
  have hy : y ∈ C.D := C.radialProj_mem_D hx
  have hy1 : ‖y‖ = 1 := norm_radialProj hx0
  have hwy : C.wSq y = C.wSq x := C.isZeroHomogeneous_wSq.apply_radialProj hx0
  have hby : C.bSq y = C.bSq x := C.isZeroHomogeneous_bSq.apply_radialProj hx0
  have hhom : IsZeroHomogeneous fun y ↦ √(C.wSq y) :=
    fun r hr z ↦ by simp only [C.isZeroHomogeneous_wSq r hr z]
  have hd := C.differentiableAt_sqrt_wSq hS hx hw
  have hrel := hhom.fderiv_radialProj hx0 hd
  have hwy' : 0 < C.wSq y := hwy ▸ hw
  have hdW : HasFDerivAt C.wSq (fderiv ℝ C.wSq y) y :=
    ((C.contDiffAt_wSq hS (C.ne_zero_of_mem_D hy) (C.radialProj_mem_D hy) 1).differentiableAt
      one_ne_zero).hasFDerivAt
  have hsq := hdW.sqrt hwy'.ne'
  have hfy : ‖fderiv ℝ (fun y ↦ √(C.wSq y)) y‖ ≤ √(C.bSq x) := by
    rw [hsq.fderiv, norm_smul, ← norm_gradient_eq_norm_fderiv]
    have hG := C.norm_gradient_wSq_sq_le hS hy hy1
    rw [hwy, hby] at hG
    rw [hwy]
    have hs := Real.sqrt_pos.2 hw
    have hb0 : 0 ≤ C.bSq x := by rw [← hby]; exact C.bSq_nonneg hS hy hy1
    have hG' : ‖∇ C.wSq y‖ ≤ 2 * √(C.wSq x) * √(C.bSq x) := by
      have h4 : (2 * √(C.wSq x) * √(C.bSq x)) ^ 2 = 4 * C.wSq x * C.bSq x := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hw.le, Real.sq_sqrt hb0]; ring
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (h4 ▸ hG)
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 1 / (2 * √(C.wSq x)) * ‖∇ C.wSq y‖
        ≤ 1 / (2 * √(C.wSq x)) * (2 * √(C.wSq x) * √(C.bSq x)) := by gcongr
      _ = √(C.bSq x) := by field_simp
  have hn : ‖fderiv ℝ (fun y ↦ √(C.wSq y)) x‖ = ‖x‖⁻¹ * ‖fderiv ℝ (fun y ↦ √(C.wSq y)) y‖ := by
    rw [hrel, norm_smul, Real.norm_of_nonneg (norm_nonneg _), ← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0), one_mul]
  rw [hn]
  exact mul_le_mul_of_nonneg_left hfy (inv_nonneg.2 (norm_nonneg _))

end ConeData

/-! ### The gradient bound -/

theorem suspCutoff_sphHessNorm_eq (O : ConeData 5) (ϑ : ℝ → ℝ) (j : ℕ) :
    suspCutoff ϑ j (sphHessNorm O.u) =
      fun z ↦ ϑ (j * √(O.wSq (dropLast z))) * ϑ (j * (‖dropLast z‖ / ‖z‖)) := by
  funext z
  rw [suspCutoff, O.sphHessNorm_eq_sqrt_wSq]


namespace IsSuspension

variable {W : ConeData 6} {O : ConeData 5} (hW : IsSuspension W O) (hO : O.Sing = {0})
  {ϑ : ℝ → ℝ} {L : ℝ} (hϑ : IsCutoffProfile ϑ L)
include hW hO hϑ

/-- Where `w_o(π z) = 0`, the cutoff vanishes near `z`. -/
theorem suspCutoff_eventuallyEq_zero {z : E 6} (hz : z ∈ W.D)
    (hw : sphHessNorm O.u (dropLast z) = 0) (j : ℕ) :
    suspCutoff ϑ j (sphHessNorm O.u) =ᶠ[𝓝 z] fun _ ↦ 0 := by
  have hx : dropLast z ∈ O.D := hW.mem_D_iff.1 hz
  have hcont : ContinuousAt (fun z ↦ (j : ℝ) * √(O.wSq (dropLast z))) z :=
    continuousAt_const.mul (((O.continuousOn_wSq hO).continuousAt
      (O.isOpen_D.mem_nhds hx)).sqrt.comp dropLast.continuous.continuousAt)
  rw [O.sphHessNorm_eq_sqrt_wSq] at hw
  have hlt : ∀ᶠ z' in 𝓝 z, (j : ℝ) * √(O.wSq (dropLast z')) < 1 :=
    hcont.eventually (gt_mem_nhds (by simp only [hw, mul_zero]; exact one_pos))
  rw [suspCutoff_sphHessNorm_eq]
  filter_upwards [hlt] with z' hz'
  rw [hϑ.eq_zero _ hz'.le, zero_mul]

/-- **The cutoff gradient bound** `|∇ξ_j| ≤ κ ρ⁻¹ (1 + b_o)` with `κ = 2L`, at a unit point of
the component of the suspension, `ρ = |π z|`. -/
theorem norm_gradient_suspCutoff_le (j : ℕ) {z : E 6} (hz : z ∈ W.D) (hz1 : ‖z‖ = 1) :
    ‖∇ (suspCutoff ϑ j (sphHessNorm O.u)) z‖ ≤
      2 * L * ‖dropLast z‖⁻¹ *
        (1 + sphBNorm O.u (dropLast z) / sphHessNorm O.u (dropLast z)) := by
  have hx : dropLast z ∈ O.D := hW.mem_D_iff.1 hz
  have hπ : dropLast z ≠ 0 := hW.dropLast_ne_zero hz
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz1
  set ρ := ‖dropLast z‖ with hρdef
  have hρ : 0 < ρ := norm_pos_iff.2 hπ
  have hL := hϑ.L_nonneg
  have hq0 : 0 ≤ sphBNorm O.u (dropLast z) / sphHessNorm O.u (dropLast z) :=
    div_nonneg (sphBNorm_nonneg _ _) (sphHessNorm_nonneg _ _)
  have hRHS : 0 ≤ 2 * L * ρ⁻¹ *
      (1 + sphBNorm O.u (dropLast z) / sphHessNorm O.u (dropLast z)) := by positivity
  by_cases hw : sphHessNorm O.u (dropLast z) = 0
  · rw [(hW.suspCutoff_eventuallyEq_zero hO hϑ hz hw j).gradient_eq]
    simpa using hRHS
  have hwpos : 0 < O.wSq (dropLast z) := by
    have := lt_of_le_of_ne (sphHessNorm_nonneg O.u (dropLast z)) (Ne.symm hw)
    rw [O.sphHessNorm_eq_sqrt_wSq] at this
    exact Real.sqrt_pos.1 this
  set w := √(O.wSq (dropLast z)) with hwdef
  have hw' : 0 < w := Real.sqrt_pos.2 hwpos
  -- the tip factor
  have hq := hasFDerivAt_tipRatio hz0 hπ
  set dq := ‖dropLast z‖ • ((-(‖z‖ ^ 2)⁻¹) • innerSL ℝ (radialProj z)) +
      ‖z‖⁻¹ • (innerSL ℝ (radialProj (dropLast z))).comp dropLast
  have hdq : ‖dq‖ ≤ 1 := norm_fderiv_tipRatio_le hz1 hπ
  have hqz : ‖dropLast z‖ / ‖z‖ = ρ := by rw [hz1, div_one]
  have hB := (hϑ.differentiable ((j : ℝ) * (‖dropLast z‖ / ‖z‖))).hasDerivAt.comp_hasFDerivAt z
    (hq.const_mul (j : ℝ))
  -- the original factor
  have hf := (O.differentiableAt_sqrt_wSq hO hx hwpos).hasFDerivAt.comp z dropLast.hasFDerivAt
  have hA := (hϑ.differentiable ((j : ℝ) * w)).hasDerivAt.comp_hasFDerivAt z
    (hf.const_mul (j : ℝ))
  have hprod : HasFDerivAt ((fun z ↦ ϑ (j * √(O.wSq (dropLast z)))) *
      fun z ↦ ϑ (j * (‖dropLast z‖ / ‖z‖))) _ z := hA.mul hB
  rw [suspCutoff_sphHessNorm_eq, norm_gradient_eq_norm_fderiv]
  change ‖fderiv ℝ ((fun z ↦ ϑ (j * √(O.wSq (dropLast z)))) *
    fun z ↦ ϑ (j * (‖dropLast z‖ / ‖z‖))) z‖ ≤ _
  rw [hprod.fderiv]
  simp only [comp_apply, hqz]
  -- bounds on the two pieces
  have hdA : ‖deriv ϑ (j * w) • ((j : ℝ) •
      (fderiv ℝ (fun y ↦ √(O.wSq y)) (dropLast z)).comp dropLast)‖ ≤
      2 * L * ρ⁻¹ * (sphBNorm O.u (dropLast z) / sphHessNorm O.u (dropLast z)) := by
    have hfn := O.norm_fderiv_sqrt_wSq_le hO hx hwpos
    have hcomp : ‖(fderiv ℝ (fun y ↦ √(O.wSq y)) (dropLast z)).comp dropLast‖ ≤
        ρ⁻¹ * √(O.bSq (dropLast z)) := by
      have h0 := norm_nonneg (fderiv ℝ (fun y ↦ √(O.wSq y)) (dropLast z))
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      nlinarith [opNorm_dropLast_le]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_natCast, ← mul_assoc]
    have hk := hϑ.abs_deriv_mul_le hw' j
    rw [O.sphBNorm_eq_sqrt_bSq, O.sphHessNorm_eq_sqrt_wSq, ← hwdef]
    calc |deriv ϑ (j * w)| * j * ‖(fderiv ℝ (fun y ↦ √(O.wSq y)) (dropLast z)).comp dropLast‖
        ≤ (2 * L / w) * (ρ⁻¹ * √(O.bSq (dropLast z))) :=
          mul_le_mul hk hcomp (norm_nonneg _) (by positivity)
      _ = 2 * L * ρ⁻¹ * (√(O.bSq (dropLast z)) / w) := by ring
  have hdB : ‖deriv ϑ (j * ρ) • ((j : ℝ) • dq)‖ ≤ 2 * L * ρ⁻¹ := by
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_natCast, ← mul_assoc]
    calc |deriv ϑ (j * ρ)| * j * ‖dq‖ ≤ (2 * L / ρ) * 1 :=
          mul_le_mul (hϑ.abs_deriv_mul_le hρ j) hdq (norm_nonneg _) (by positivity)
      _ = 2 * L * ρ⁻¹ := by ring
  have hA1 : ‖ϑ (j * w)‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hϑ.nonneg _)]; exact hϑ.le_one _
  have hB1 : ‖ϑ (j * ρ)‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hϑ.nonneg _)]; exact hϑ.le_one _
  calc ‖ϑ (j * w) • (deriv ϑ (j * ρ) • ((j : ℝ) • dq)) +
        ϑ (j * ρ) • (deriv ϑ (j * w) • ((j : ℝ) •
          (fderiv ℝ (fun y ↦ √(O.wSq y)) (dropLast z)).comp dropLast))‖
      ≤ 1 * (2 * L * ρ⁻¹) + 1 * (2 * L * ρ⁻¹ *
          (sphBNorm O.u (dropLast z) / sphHessNorm O.u (dropLast z))) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul]
        · exact mul_le_mul hA1 hdB (norm_nonneg _) zero_le_one
        · exact mul_le_mul hB1 hdA (norm_nonneg _) zero_le_one
    _ = _ := by ring

end IsSuspension

/-! ### Eventual vanishing -/

namespace IsSuspension

variable {W : ConeData 6} {O : ConeData 5} (hW : IsSuspension W O) (hO : O.Sing = {0})
  {ϑ : ℝ → ℝ} {L : ℝ} (hϑ : IsCutoffProfile ϑ L)
include hW hO hϑ

/-- **Eventual vanishing.** Where `w_o(π z) > 0`, `ξ_j = 1` near `z` for all large `j`. -/
theorem suspCutoff_eventually_eq_one {z : E 6} (hz : z ∈ W.D)
    (hw : 0 < sphHessNorm O.u (dropLast z)) :
    ∀ᶠ j : ℕ in atTop, suspCutoff ϑ j (sphHessNorm O.u) =ᶠ[𝓝 z] fun _ ↦ 1 := by
  have hx : dropLast z ∈ O.D := hW.mem_D_iff.1 hz
  have hπ : dropLast z ≠ 0 := hW.dropLast_ne_zero hz
  have hz0 : z ≠ 0 := fun h ↦ hπ (by rw [h, map_zero])
  rw [O.sphHessNorm_eq_sqrt_wSq] at hw
  set w0 := √(O.wSq (dropLast z))
  set q0 := ‖dropLast z‖ / ‖z‖
  have hq0 : 0 < q0 := div_pos (norm_pos_iff.2 hπ) (norm_pos_iff.2 hz0)
  have h1 : ContinuousAt (fun z ↦ √(O.wSq (dropLast z))) z :=
    ((O.continuousOn_wSq hO).continuousAt (O.isOpen_D.mem_nhds hx)).sqrt.comp
      dropLast.continuous.continuousAt
  have h2 : ContinuousAt (fun z : E 6 ↦ ‖dropLast z‖ / ‖z‖) z :=
    ((continuous_norm.comp dropLast.continuous).continuousAt).div continuous_norm.continuousAt
      (norm_ne_zero_iff.2 hz0)
  have e1 : ∀ᶠ z' in 𝓝 z, w0 / 2 < √(O.wSq (dropLast z')) :=
    h1.eventually (lt_mem_nhds (half_lt_self hw))
  have e2 : ∀ᶠ z' in 𝓝 z, q0 / 2 < ‖dropLast z'‖ / ‖z'‖ :=
    h2.eventually (lt_mem_nhds (half_lt_self hq0))
  filter_upwards [eventually_ge_atTop ⌈max (4 / w0) (4 / q0)⌉₊] with j hj
  have hj' : max (4 / w0) (4 / q0) ≤ j := (Nat.le_ceil _).trans (by exact_mod_cast hj)
  rw [suspCutoff_sphHessNorm_eq]
  filter_upwards [e1, e2] with z' hz1 hz2
  have hA : 2 ≤ (j : ℝ) * √(O.wSq (dropLast z')) := by
    have : 4 / w0 ≤ j := (le_max_left _ _).trans hj'
    have h4 : 4 / w0 * (w0 / 2) = 2 := by field_simp; norm_num
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 4) hw]
  have hB : 2 ≤ (j : ℝ) * (‖dropLast z'‖ / ‖z'‖) := by
    have : 4 / q0 ≤ j := (le_max_right _ _).trans hj'
    have h4 : 4 / q0 * (q0 / 2) = 2 := by field_simp; norm_num
    nlinarith [div_pos (by norm_num : (0 : ℝ) < 4) hq0]
  rw [hϑ.eq_one _ hA, hϑ.eq_one _ hB, mul_one]

/-- **The errors vanish eventually**: where `w_o(π z) > 0`, for all large `j`, `ξ_j(z) = 1` and
`∇ξ_j(z) = 0`, so `E₁ = E₂ = E₃ = 0` at `z`. -/
theorem errors_eventually_zero_susp {z : E 6} (hz : z ∈ W.D)
    (hw : 0 < sphHessNorm O.u (dropLast z)) :
    ∀ᶠ j : ℕ in atTop, suspCutoff ϑ j (sphHessNorm O.u) z = 1 ∧
      ∇ (suspCutoff ϑ j (sphHessNorm O.u)) z = 0 := by
  filter_upwards [hW.suspCutoff_eventually_eq_one hO hϑ hz hw] with j hj
  refine ⟨hj.self_of_nhds, ?_⟩
  rw [hj.gradient_eq]
  simp [gradient]

end IsSuspension

/-! ### The domination -/

/-- The algebra of the domination: with `W = ρ⁻¹ w`, `|h| ≤ C W^a`, `|∇h| ≤ C W^a N`,
`|Z| ≤ C W^{2a} N`, `N ≤ K ρ⁻¹ (1 + b)`, `ξ ≤ 1` and `|∇ξ| ≤ κ ρ⁻¹ (1 + b)`,
`ρ⁴ (h²|∇ξ|² + 2ξ|h||∇h||∇ξ| + 2ξ|Z||∇ξ|) ≤ C²(κ² + 4Kκ) ρ^{2-2a} w^{2a} (1 + b)²`. -/
theorem errors_le_aux {ρ w b C K κ a h gh Z N ξ gξ : ℝ} (hρ : 0 < ρ) (hw : 0 < w) (hb : 0 ≤ b)
    (hC : 1 ≤ C) (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hξ1 : ξ ≤ 1) (hgξ0 : 0 ≤ gξ)
    (hgξ : gξ ≤ κ * ρ⁻¹ * (1 + b)) (hh : |h| ≤ C * (ρ⁻¹ * w) ^ a) (hgh0 : 0 ≤ gh)
    (hgh : gh ≤ C * (ρ⁻¹ * w) ^ a * N) (hZ0 : 0 ≤ Z) (hZ : Z ≤ C * (ρ⁻¹ * w) ^ (2 * a) * N)
    (hN : N ≤ K * ρ⁻¹ * (1 + b)) :
    ρ ^ 4 * (h ^ 2 * gξ ^ 2 + 2 * ξ * |h| * gh * gξ + 2 * ξ * Z * gξ) ≤
      C ^ 2 * (κ ^ 2 + 4 * K * κ) * ρ ^ (2 - 2 * a) * (w ^ (2 * a) * (1 + b) ^ 2) := by
  set P := (ρ⁻¹ * w) ^ a with hP
  set R := ρ⁻¹ * (1 + b) with hR
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by positivity) a
  have hR0 : 0 ≤ R := by positivity
  have hC0 : 0 ≤ C := by linarith
  have hP2 : (ρ⁻¹ * w) ^ (2 * a) = P ^ 2 := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    ring_nf
  rw [hP2] at hZ
  have hgξ' : gξ ≤ κ * R := by rw [hR]; linarith
  have hN' : N ≤ K * R := by rw [hR]; linarith
  have hhabs : |h| * |h| ≤ (C * P) * (C * P) :=
    mul_le_mul hh hh (abs_nonneg _) (by positivity)
  have e1 : h ^ 2 * gξ ^ 2 ≤ C ^ 2 * κ ^ 2 * (P ^ 2 * R ^ 2) := by
    have : gξ * gξ ≤ (κ * R) * (κ * R) := mul_le_mul hgξ' hgξ' hgξ0 (by positivity)
    have hh2 : h ^ 2 = |h| * |h| := by rw [← sq, sq_abs]
    calc h ^ 2 * gξ ^ 2 = (|h| * |h|) * (gξ * gξ) := by rw [hh2]; ring
      _ ≤ ((C * P) * (C * P)) * ((κ * R) * (κ * R)) :=
          mul_le_mul hhabs this (by positivity) (by positivity)
      _ = _ := by ring
  have hgh' : gh ≤ C * P * (K * R) :=
    hgh.trans (mul_le_mul_of_nonneg_left hN' (by positivity))
  have hZ' : Z ≤ C * P ^ 2 * (K * R) :=
    hZ.trans (mul_le_mul_of_nonneg_left hN' (by positivity))
  have e2 : 2 * ξ * |h| * gh * gξ ≤ 2 * C ^ 2 * K * κ * (P ^ 2 * R ^ 2) := by
    calc 2 * ξ * |h| * gh * gξ ≤ 2 * 1 * (C * P) * (C * P * (K * R)) * (κ * R) := by
          gcongr
      _ = _ := by ring
  have e3 : 2 * ξ * Z * gξ ≤ 2 * C ^ 2 * K * κ * (P ^ 2 * R ^ 2) := by
    calc 2 * ξ * Z * gξ ≤ 2 * 1 * (C * P ^ 2 * (K * R)) * (κ * R) := by gcongr
      _ = 2 * C * K * κ * (P ^ 2 * R ^ 2) := by ring
      _ ≤ _ := by
          have : C ≤ C ^ 2 := by nlinarith
          gcongr
  have hsum : h ^ 2 * gξ ^ 2 + 2 * ξ * |h| * gh * gξ + 2 * ξ * Z * gξ ≤
      C ^ 2 * (κ ^ 2 + 4 * K * κ) * (P ^ 2 * R ^ 2) := by nlinarith
  have hconv : ρ ^ 4 * (P ^ 2 * R ^ 2) = ρ ^ (2 - 2 * a) * (w ^ (2 * a) * (1 + b) ^ 2) := by
    rw [← hP2, Real.mul_rpow (by positivity) hw.le, Real.inv_rpow hρ.le,
      Real.rpow_sub hρ, Real.rpow_two, hR]
    field_simp
  calc ρ ^ 4 * (h ^ 2 * gξ ^ 2 + 2 * ξ * |h| * gh * gξ + 2 * ξ * Z * gξ)
      ≤ ρ ^ 4 * (C ^ 2 * (κ ^ 2 + 4 * K * κ) * (P ^ 2 * R ^ 2)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [show ρ ^ 4 * (C ^ 2 * (κ ^ 2 + 4 * K * κ) * (P ^ 2 * R ^ 2)) =
          C ^ 2 * (κ ^ 2 + 4 * K * κ) * (ρ ^ 4 * (P ^ 2 * R ^ 2)) by ring, hconv]; ring

namespace IsSuspension

variable {W : ConeData 6} {O : ConeData 5} (hW : IsSuspension W O) (hO : O.Sing = {0})
  {ϑ : ℝ → ℝ} {L : ℝ} (hϑ : IsCutoffProfile ϑ L)
include hW hO hϑ

/-- **The suspended domination** (`cut:suspended-domination`). At a unit point `z` of the
component of the suspension, with `ρ = |π z|`, `ξ = ξ_j`, field bounds of constant `C_F ≥ 1`
(where `w̃ > 0`) and `w_o(π z) ≤ M_o`, the three cutoff errors
`E₁ = h²|∇ξ|²`, `E₂ = 2ξh⟨∇h, ∇ξ⟩`, `E₃ = -2ξ⟨Z, ∇ξ⟩` satisfy

  `ρ⁴(|E₁| + |E₂| + |E₃|) ≤ C_F²(κ² + 4K_sκ) ρ^{2-2a} D_o(π z)`,

with `κ = 2L` and `K_s = 1 + M_o + √3`. Where `w_o(π z) = 0` the left side is `0`. -/
theorem errors_le_susp {c : Coeffs} {Cf M : ℝ} (hCf : 1 ≤ Cf) (j : ℕ) {z : E 6}
    (hz : z ∈ W.D) (hz1 : ‖z‖ = 1) (hM : sphHessNorm O.u (dropLast z) ≤ M)
    (hF : 0 < fluxW W.u z →
      |fluxH c W.u z| ≤ Cf * fluxW W.u z ^ aExp ∧
      ‖∇ (fluxH c W.u) z‖ ≤
        Cf * fluxW W.u z ^ aExp * (1 + fluxW W.u z + fluxBNorm W.u z / fluxW W.u z) ∧
      ‖fluxZ c W.u z‖ ≤
        Cf * fluxW W.u z ^ (2 * aExp) * (1 + fluxW W.u z + fluxBNorm W.u z / fluxW W.u z)) :
    ‖dropLast z‖ ^ 4 *
        (|fluxH c W.u z ^ 2 * ‖∇ (suspCutoff ϑ j (sphHessNorm O.u)) z‖ ^ 2| +
          |2 * suspCutoff ϑ j (sphHessNorm O.u) z * fluxH c W.u z *
            ⟪∇ (fluxH c W.u) z, ∇ (suspCutoff ϑ j (sphHessNorm O.u)) z⟫| +
          |-2 * suspCutoff ϑ j (sphHessNorm O.u) z *
            ⟪fluxZ c W.u z, ∇ (suspCutoff ϑ j (sphHessNorm O.u)) z⟫|) ≤
      Cf ^ 2 * ((2 * L) ^ 2 + 4 * (1 + M + √3) * (2 * L)) *
        ‖dropLast z‖ ^ (2 - 2 * aExp) * O.dominatorO aExp (dropLast z) := by
  have hρ : 0 < ‖dropLast z‖ := hW.norm_dropLast_pos hz
  have hL := hϑ.L_nonneg
  have hM0 : 0 ≤ M := (sphHessNorm_nonneg _ _).trans hM
  set ξ := suspCutoff ϑ j (sphHessNorm O.u)
  by_cases hw : sphHessNorm O.u (dropLast z) = 0
  · have hev := hW.suspCutoff_eventuallyEq_zero hO hϑ hz hw j
    have hξz : ξ z = 0 := hev.self_of_nhds
    have hgz : ∇ ξ z = 0 := by rw [hev.gradient_eq]; simp [gradient]
    rw [hξz, hgz]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      abs_zero, inner_zero_right, zero_mul, add_zero]
    have := O.dominatorO_nonneg aExp (dropLast z)
    positivity
  have hwpos : 0 < sphHessNorm O.u (dropLast z) :=
    lt_of_le_of_ne (sphHessNorm_nonneg _ _) (Ne.symm hw)
  have hfw := hW.fluxW_suspension hO hz hz1
  have hfw0 : 0 < fluxW W.u z := by rw [hfw]; positivity
  obtain ⟨hh, hgh, hZ⟩ := hF hfw0
  have hN := hW.suspension_K_bound hO hz hz1 hwpos hM
  have hgξ := hW.norm_gradient_suspCutoff_le hO hϑ j hz hz1
  rw [hfw] at hh hgh hZ hN
  have key := errors_le_aux (ρ := ‖dropLast z‖) (w := sphHessNorm O.u (dropLast z))
    (b := sphBNorm O.u (dropLast z) / sphHessNorm O.u (dropLast z)) (C := Cf)
    (K := 1 + M + √3) (κ := 2 * L) (a := aExp) (ξ := ξ z) (gξ := ‖∇ ξ z‖)
    hρ hwpos (div_nonneg (sphBNorm_nonneg _ _) hwpos.le) hCf (by positivity) (by positivity)
    (suspCutoff_le_one hϑ j _ z) (norm_nonneg _)
    (by linarith [hgξ]) hh (norm_nonneg _) hgh (norm_nonneg _) hZ (by linarith [hN])
  rw [O.dominatorO_eq hwpos]
  refine le_trans ?_ (key.trans_eq (by ring))
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hξ0 := suspCutoff_nonneg hϑ j (sphHessNorm O.u) z
  have e1 : |fluxH c W.u z ^ 2 * ‖∇ ξ z‖ ^ 2| = fluxH c W.u z ^ 2 * ‖∇ ξ z‖ ^ 2 :=
    abs_of_nonneg (by positivity)
  have e2 : |2 * ξ z * fluxH c W.u z * ⟪∇ (fluxH c W.u) z, ∇ ξ z⟫| ≤
      2 * ξ z * |fluxH c W.u z| * ‖∇ (fluxH c W.u) z‖ * ‖∇ ξ z‖ := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg hξ0,
      mul_assoc _ ‖_‖]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
  have e3 : |-2 * ξ z * ⟪fluxZ c W.u z, ∇ ξ z⟫| ≤ 2 * ξ z * ‖fluxZ c W.u z‖ * ‖∇ ξ z‖ := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hξ0, mul_assoc _ ‖_‖]
    exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
  linarith

end IsSuspension

/-! ### The suspended mass -/

/-- `w̃^{2a} = ρ^{-2a} w_o^{2a}` at a unit point of the component of the suspension. -/
theorem IsSuspension.fluxW_rpow_suspension {W : ConeData 6} {O : ConeData 5}
    (hW : IsSuspension W O) (hO : O.Sing = {0}) {z : E 6} (hz : z ∈ W.D) (hz1 : ‖z‖ = 1) :
    fluxW W.u z ^ (2 * aExp) = ‖dropLast z‖ ^ (-(2 * aExp)) * O.wSq (dropLast z) ^ aExp := by
  have hρ := hW.norm_dropLast_pos hz
  rw [hW.fluxW_suspension hO hz hz1, O.sphHessNorm_eq_sqrt_wSq,
    Real.mul_rpow (inv_nonneg.2 hρ.le) (Real.sqrt_nonneg _), Real.inv_rpow hρ.le,
    ← Real.rpow_neg hρ.le, Real.sqrt_eq_rpow, ← Real.rpow_mul (O.wSq_nonneg _)]
  ring_nf

/-- **The suspended mass**: `∫_{S⁵} ρ^{-2a} w_o^{2a}(π θ) dσ₅ = ∫₀^π sin^{71/25}t dt · I_o`
with `I_o = ∫_{S⁴} 1_{D_o} w_o^{2a} dσ₄` and `4 - 2a = 71/25`. -/
theorem integral_suspension_mass (O : ConeData 5) (hO : O.Sing = {0}) :
    ∫ θ : sphere (0 : E 6) 1,
        ‖dropLast θ‖ ^ (-(2 * aExp)) * O.D.indicator (fun x ↦ O.wSq x ^ aExp) (dropLast θ)
        ∂(volume : Measure (E 6)).toSphere =
      (∫ t in Ioo 0 π, Real.sin t ^ (71 / 25 : ℝ)) *
        ∫ y : sphere (0 : E 5) 1, O.D.indicator (fun x ↦ O.wSq x ^ aExp) y
          ∂(volume : Measure (E 5)).toSphere := by
  have h := integral_sphere_suspension (a := fun ρ _ ↦ |ρ| ^ (-(2 * aExp)))
    ((continuous_abs.measurable.comp measurable_fst).pow_const _)
    (fun _ _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
    (b := O.D.indicator fun x ↦ O.wSq x ^ aExp)
    (O.measurable_indicator_wSq_rpow hO (by norm_num [aExp]))
    (fun _ ↦ indicator_nonneg (fun x _ ↦ Real.rpow_nonneg (O.wSq_nonneg x) _) _)
  simp only [abs_norm, O.indicator_wSq_rpow_radialProj] at h
  rw [h]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
  rw [abs_of_pos hs, ← Real.rpow_natCast, ← Real.rpow_add hs]
  norm_num [aExp]

/-- `∫₀^π sin^p t dt > 0` for `p ≥ 0`. -/
theorem integral_sin_rpow_pos {p : ℝ} (hp : 0 ≤ p) : 0 < ∫ t in Ioo 0 π, Real.sin t ^ p := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le Real.pi_pos.le]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ (fun t ht ↦ ?_) Real.pi_pos
  · exact (Real.continuous_sin.rpow_const fun _ ↦ Or.inr hp).intervalIntegrable _ _
  · exact Real.rpow_pos_of_pos (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2) p

end OnePhaseDimension
