/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Statements.Cone
public import EllipticBernoulli.Sobolev.Energy
public import EllipticBernoulli.Sobolev.Lipschitz
public import EllipticBernoulli.Sobolev.Uniqueness
public import EllipticBernoulli.Sobolev.SobolevInequality
public import EllipticBernoulli.Flatness.TestCalculus
public import EllipticBernoulli.Flatness.Barriers
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The half-space solution

For a unit vector `e`, the half-space solution `h(x) = max ⟪x, e⟫ 0` is a global minimizer of the
one-phase energy, and it satisfies every field of the cone interface except nonflatness: it is
continuous, nonnegative and one-homogeneous, its positivity set `{⟪x, e⟫ > 0}` is connected, and
at every point it has the smooth one-sided chart `F = ⟪·, e⟫`.

Minimality is proved by calibration. For a competitor `v` agreeing with `h` off a ball `B`,
replace `v` by `w = v₊`; then pointwise `|∇w|² + 1_{w > 0} ≥ 2 ⟪∇w, e⟫`, and
`∫_B ⟪∇w, e⟫ = ∫_B ⟪∇h, e⟫` because `w - h` vanishes off `B`. Finally
`|∇h|² + 1_{h > 0} = 2 ⟪∇h, e⟫`.

## Main results

* `isLocalEnergyMinimizer_halfSpaceSol`: the half-space solution is a global minimizer.
* `connectedComponentIn_halfSpaceSol`: its positivity set is the connected half-space.
* `halfSpaceSol_coneData_fields`: the fields of the cone interface other than nonflatness, with
  singular set `{0}`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian RealInnerProductSpace ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ}

/-- The half-space solution `x ↦ max ⟪x, e⟫ 0`. -/
def halfSpaceSol (e : E d) (x : E d) : ℝ := max ⟪x, e⟫ 0

/-- The weak gradient `1_{⟪x, e⟫ > 0} e` of the half-space solution. -/
def halfSpaceGrad (e : E d) : E d → E d := {y | 0 < ⟪y, e⟫}.indicator fun _ ↦ e

theorem memH1Loc_halfSpaceSol (e : E d) : MemH1Loc univ (halfSpaceSol e) (halfSpaceGrad e) := by
  have h := memH1Loc_posPart isOpen_univ (memH1Loc_gradient_of_contDiff isOpen_univ
    (contDiff_id.inner ℝ contDiff_const : ContDiff ℝ 1 fun y : E d ↦ ⟪y, e⟫))
  have hG : ∇ (fun y : E d ↦ ⟪y, e⟫) = fun _ ↦ e := funext (gradient_inner_const e)
  have hG' : halfSpaceGrad e = {y | 0 < ⟪y, e⟫}.indicator (∇ fun y : E d ↦ ⟪y, e⟫) := by
    rw [hG]; rfl
  rw [hG']
  exact h

/-- **Vanishing mean of the gradient.** If `z ∈ H¹_loc(ℝᵈ)` with weak gradient `G` vanishes a.e.
off the ball `B`, then `∫_B ⟪G, v⟫ = 0` for every direction `v`. -/
theorem setIntegral_inner_eq_zero_of_ae_eq_zero_off_ball {z : E d → ℝ} {G : E d → E d}
    (hz : HasWeakGradient univ z G) {x₀ : E d} {r : ℝ} (hr : 0 < r)
    (h0 : ∀ᵐ y ∂(volume.restrict (ball x₀ r)ᶜ), z y = 0) (v : E d) :
    ∫ y in ball x₀ r, ⟪G y, v⟫ = 0 := by
  have hO : (∀ᵐ y ∂(volume.restrict (closedBall x₀ r)ᶜ), z y = 0) :=
    ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 ball_subset_closedBall) h0
  have hG0 := hz.ae_eq_zero_of_ae_eq_zero_on isClosed_closedBall.isOpen_compl (subset_univ _) hO
  let φ : ContDiffBump x₀ := ⟨r + 1, r + 2, by linarith, by linarith⟩
  have hφ1 : ∀ y ∈ closedBall x₀ (r + 1), φ y = 1 := fun y hy ↦ φ.one_of_mem_closedBall hy
  have h := hz.integral_eq φ.contDiff φ.hasCompactSupport (subset_univ _) v
  have hl : ∫ y, z y * fderiv ℝ φ y v = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [ae_restrict_iff' measurableSet_ball.compl] at h0
    filter_upwards [h0] with y hy
    by_cases hyB : y ∈ ball x₀ r
    · have hev : (φ : E d → ℝ) =ᶠ[𝓝 y] fun _ ↦ 1 := by
        filter_upwards [isOpen_ball.mem_nhds (mem_ball.2 (lt_of_lt_of_le (mem_ball.1 hyB)
          (by linarith : r ≤ r + 1)))] with y' hy'
        exact hφ1 y' (ball_subset_closedBall hy')
      simp [hev.fderiv_eq]
    · simp [hy hyB]
  rw [hl] at h
  have hr' : ∫ y, ⟪G y, v⟫ * φ y = ∫ y in closedBall x₀ r, ⟪G y, v⟫ := by
    rw [← integral_indicator measurableSet_closedBall]
    refine integral_congr_ae ?_
    rw [ae_restrict_iff' isClosed_closedBall.isOpen_compl.measurableSet] at hG0
    filter_upwards [hG0] with y hy
    by_cases hyB : y ∈ closedBall x₀ r
    · rw [indicator_of_mem hyB, hφ1 y (closedBall_subset_closedBall (by linarith) hyB), mul_one]
    · rw [indicator_of_notMem hyB, hy hyB, inner_zero_left, zero_mul]
  rw [setIntegral_congr_set (ball_ae_eq_closedBall x₀ hr)]
  linarith

/-- Integrability of `⟪G, e⟫` on a ball for an `H¹_loc` gradient. -/
theorem integrableOn_inner_ball {f : E d → ℝ} {G : E d → E d} (hf : MemH1Loc univ f G)
    (x₀ : E d) (r : ℝ) (e : E d) : IntegrableOn (fun y ↦ ⟪G y, e⟫) (ball x₀ r) := by
  have hK := (hf.2 (closedBall x₀ r) (subset_univ _) (isCompact_closedBall x₀ r)).2
  have : IsFiniteMeasure (volume.restrict (closedBall x₀ r)) :=
    isFiniteMeasure_restrict.2 measure_closedBall_lt_top.ne
  exact IntegrableOn.mono_set ((hK.integrable one_le_two).inner_const e) ball_subset_closedBall

/-- **Minimality of the half-space solution** (calibration by the constant field `e`). -/
theorem isLocalEnergyMinimizer_halfSpaceSol {e : E d} (he : ‖e‖ = 1) :
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) (halfSpaceSol e) := by
  have hee : ⟪e, e⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  refine ⟨halfSpaceGrad e, memH1Loc_halfSpaceSol e, fun x₀ r hr _ ↦
    ⟨memH1Loc_halfSpaceSol e, fun _ _ ↦ rfl, fun _ _ ↦ mem_univ _, fun v Gv hv hvB _ ↦ ?_⟩⟩
  refine le_trans ?_ (energyJ_posPart_le _ _ v Gv)
  set Gw := {y | 0 < v y}.indicator Gv with hGw
  have hw : MemH1Loc univ (fun y ↦ max (v y) 0) Gw := memH1Loc_posPart isOpen_univ hv
  -- `w - h` vanishes off the ball
  have hz : ∀ᵐ y ∂(volume.restrict (ball x₀ r)ᶜ), max (v y) 0 - halfSpaceSol e y = 0 := by
    rw [compl_eq_univ_sdiff]
    filter_upwards [hvB] with y hy
    rw [hy, halfSpaceSol, max_eq_left (le_max_right _ _), sub_self]
  have hint := setIntegral_inner_eq_zero_of_ae_eq_zero_off_ball
    (hw.sub (memH1Loc_halfSpaceSol e)).1 hr hz e
  have hIw := integrableOn_inner_ball hw x₀ r e
  have hIh := integrableOn_inner_ball (memH1Loc_halfSpaceSol e) x₀ r e
  have hEq : ∫ y in ball x₀ r, ⟪halfSpaceGrad e y, e⟫ = ∫ y in ball x₀ r, ⟪Gw y, e⟫ := by
    simp_rw [inner_sub_left] at hint
    rw [integral_sub hIw hIh] at hint
    linarith
  -- the energy of `h`
  have hEh : energyJ (ball x₀ r) (fun _ ↦ 1) (halfSpaceSol e) (halfSpaceGrad e) =
      ENNReal.ofReal (∫ y in ball x₀ r, 2 * ⟪halfSpaceGrad e y, e⟫) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hIh.const_mul 2) (Eventually.of_forall fun y ↦ ?_)]
    · unfold energyJ
      refine setLIntegral_congr_fun measurableSet_ball fun y hy ↦ ?_
      congr 1
      by_cases hp : 0 < ⟪y, e⟫
      · have hmem : y ∈ posSet (halfSpaceSol e) (ball x₀ r) :=
          ⟨hy, lt_max_of_lt_left hp⟩
        simp [halfSpaceGrad, hp, indicator_of_mem hmem, he]
        norm_num
      · have hmem : y ∉ posSet (halfSpaceSol e) (ball x₀ r) := fun h ↦
          hp (by simpa [halfSpaceSol] using h.2)
        simp [halfSpaceGrad, hp, indicator_of_notMem hmem]
    · by_cases hp : 0 < ⟪y, e⟫ <;> simp [halfSpaceGrad, hp]
  -- the lower bound for `w`
  have hEw : ∫⁻ y in ball x₀ r, ENNReal.ofReal (2 * ⟪Gw y, e⟫) ≤
      energyJ (ball x₀ r) (fun _ ↦ 1) (fun y ↦ max (v y) 0) Gw := by
    unfold energyJ
    refine setLIntegral_mono' measurableSet_ball fun y hy ↦ ENNReal.ofReal_le_ofReal ?_
    by_cases hp : 0 < v y
    · have hmem : y ∈ posSet (fun y ↦ max (v y) 0) (ball x₀ r) := ⟨hy, lt_max_of_lt_left hp⟩
      rw [indicator_of_mem hmem]
      have h1 : ⟪Gw y, e⟫ ≤ ‖Gw y‖ := by
        simpa [he] using real_inner_le_norm (Gw y) e
      simp only [Pi.one_apply, one_pow, one_mul]
      nlinarith [sq_nonneg (‖Gw y‖ - 1)]
    · have h0 : Gw y = 0 := by simp [hGw, hp]
      rw [h0, inner_zero_left, mul_zero]
      have : 0 ≤ (posSet (fun y ↦ max (v y) 0) (ball x₀ r)).indicator (1 : E d → ℝ) y :=
        indicator_nonneg (fun _ _ ↦ zero_le_one) y
      positivity
  have hI2 : Integrable (fun y ↦ 2 * ⟪Gw y, e⟫) (volume.restrict (ball x₀ r)) :=
    hIw.const_mul 2
  calc energyJ (ball x₀ r) (fun _ ↦ 1) (halfSpaceSol e) (halfSpaceGrad e)
      = ENNReal.ofReal (∫ y in ball x₀ r, 2 * ⟪Gw y, e⟫) := by
        rw [hEh, integral_const_mul, integral_const_mul, hEq]
    _ ≤ ENNReal.ofReal (∫ y in ball x₀ r, max (2 * ⟪Gw y, e⟫) 0) :=
        ENNReal.ofReal_le_ofReal (integral_mono hI2 hI2.pos_part fun _ ↦ le_max_left _ _)
    _ = ∫⁻ y in ball x₀ r, ENNReal.ofReal (2 * ⟪Gw y, e⟫) := by
        rw [ofReal_integral_eq_lintegral_ofReal hI2.pos_part
          (Eventually.of_forall fun _ ↦ le_max_right _ _)]
        refine lintegral_congr fun y ↦ ?_
        rcases le_total (2 * ⟪Gw y, e⟫) 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
        · rw [max_eq_left h]
    _ ≤ _ := hEw

theorem halfSpaceSol_nonneg (e x : E d) : 0 ≤ halfSpaceSol e x := le_max_right _ _

theorem continuous_halfSpaceSol (e : E d) : Continuous (halfSpaceSol e) :=
  (continuous_id.inner continuous_const).max continuous_const

theorem halfSpaceSol_smul (e : E d) {r : ℝ} (hr : 0 < r) (x : E d) :
    halfSpaceSol e (r • x) = r * halfSpaceSol e x := by
  rw [halfSpaceSol, halfSpaceSol, real_inner_smul_left, mul_max_of_nonneg _ _ hr.le, mul_zero]

theorem setOf_halfSpaceSol_pos (e : E d) :
    {x | 0 < halfSpaceSol e x} = {x | 0 < ⟪x, e⟫} := by
  ext x
  simp [halfSpaceSol]

/-- The positivity set of the half-space solution is the connected half-space. -/
theorem connectedComponentIn_halfSpaceSol {e : E d} (he : ‖e‖ = 1) :
    connectedComponentIn {x | 0 < halfSpaceSol e x} e = {x | 0 < ⟪x, e⟫} := by
  rw [setOf_halfSpaceSol_pos]
  have hlin : IsLinearMap ℝ fun x : E d ↦ ⟪x, e⟫ :=
    ⟨fun x y ↦ inner_add_left x y e, fun c x ↦ real_inner_smul_left x e c⟩
  refine ((convex_halfSpace_gt hlin 0).isPreconnected).connectedComponentIn ?_
  simp [he]

/-- **The half-space witness.** The half-space solution satisfies every field of the cone
interface except nonflatness, with base point `e` and singular set `{0}`. -/
theorem halfSpaceSol_coneData_fields {e : E d} (he : ‖e‖ = 1) :
    (∀ x, 0 ≤ halfSpaceSol e x) ∧ Continuous (halfSpaceSol e) ∧
      (∀ r : ℝ, 0 < r → ∀ x, halfSpaceSol e (r • x) = r * halfSpaceSol e x) ∧
      IsLocalEnergyMinimizer univ (fun _ ↦ 1) (halfSpaceSol e) ∧ 0 < halfSpaceSol e e ∧
      IsClosed ({0} : Set (E d)) ∧
      (∀ r : ℝ, 0 < r → ∀ x ∈ ({0} : Set (E d)), r • x ∈ ({0} : Set (E d))) ∧
      ∀ x₀ ∈ closure (connectedComponentIn {x | 0 < halfSpaceSol e x} e) \ {0},
        ∃ U : Set (E d), IsOpen U ∧ x₀ ∈ U ∧
          ∃ F : E d → ℝ, ContDiffOn ℝ ∞ F U ∧ (∀ x ∈ U, halfSpaceSol e x = max (F x) 0) ∧
            (∀ x ∈ U, 0 < F x → x ∈ connectedComponentIn {x | 0 < halfSpaceSol e x} e) ∧
            (∀ x ∈ U, F x = 0 → ‖∇ F x‖ = 1) ∧ (∀ x ∈ U, 0 < F x → Δ F x = 0) := by
  refine ⟨halfSpaceSol_nonneg e, continuous_halfSpaceSol e, fun r hr x ↦ halfSpaceSol_smul e hr x,
    isLocalEnergyMinimizer_halfSpaceSol he, ?_, isClosed_singleton, ?_, fun x₀ _ ↦ ?_⟩
  · simp [halfSpaceSol, he]
  · rintro r - x rfl
    simp
  refine ⟨univ, isOpen_univ, mem_univ _, fun y ↦ ⟪y, e⟫,
    (contDiff_id.inner ℝ contDiff_const).contDiffOn, fun x _ ↦ rfl, fun x _ hx ↦ ?_,
    fun x _ _ ↦ by rw [gradient_inner_const, he], fun x _ _ ↦ ?_⟩
  · rw [connectedComponentIn_halfSpaceSol he]
    exact hx
  · simpa using laplacian_mul_inner_add e 1 0 x

end OnePhaseDimension
