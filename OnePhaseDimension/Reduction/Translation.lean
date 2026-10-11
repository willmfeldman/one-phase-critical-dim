/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Regular
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Translation invariance of an off-origin blowup

Let `u` be one-homogeneous and locally Lipschitz, and let `x₀` be a zero of `u`. Every blowup
limit `U` of `u` at `x₀` is invariant under translation along `x₀`: `U(y + t x₀) = U(y)`.

## Proof

For `r > 0` small and `r' = r / (1 + r t)`, homogeneity gives the exact identity
`u_r(y + t x₀) = u_{r'}(y)` for the rescalings `u_r(y) = u(x₀ + r y) / r`. Since
`1 / r' = 1 / r + t`,
`u_{r'}(y) - u_r(y) = (u(x₀ + r' y) - u(x₀ + r y)) / r' + t u(x₀ + r y)`, and the first term is
at most `L |r t| |y|` by the Lipschitz bound near `x₀`, while the second tends to `t u(x₀) = 0`.
So both rescalings have the same limit along the chosen sequence.

## Differences from the source

The 2026-09-24 version bounds `|u_{r'}(y) - u_r(y)| ≤ 2LM|t|r` using the Lipschitz bound for
both terms. We use the exact identity `1/r' - 1/r = t`, bound the first term by the Lipschitz
constant and the second by continuity of `u` at `x₀`. Only pointwise convergence of the
rescalings is used.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology Metric

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ}

/-- A zero of a continuous nonnegative function at the boundary of its positivity set. -/
theorem eq_zero_of_mem_freeBoundary {u : E d → ℝ} (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x)
    {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u univ) : u x₀ = 0 := by
  refine le_antisymm (not_lt.1 fun hpos ↦ ?_) (hnn x₀)
  have hopen : IsOpen (posSet u univ) := by
    have : posSet u univ = u ⁻¹' Ioi 0 := by ext x; simp [posSet]
    rw [this]
    exact isOpen_Ioi.preimage hc
  have : x₀ ∈ interior (posSet u univ) := hopen.interior_eq.symm ▸ ⟨mem_univ _, hpos⟩
  exact hx₀.1.2 this

/-- The rescaling identity `u_r(y + t x₀) = u_{r'}(y)`, `r' = r / (1 + r t)`, for a
one-homogeneous `u`. -/
theorem blowup_add_smul_eq {u : E d → ℝ} (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x)
    (x₀ y : E d) {r t : ℝ} (hr : 0 < r) (hrt : 0 < 1 + r * t) :
    blowup u x₀ r (y + t • x₀) = blowup u x₀ (r / (1 + r * t)) y := by
  set r' := r / (1 + r * t) with hr'
  have hrr' : (1 + r * t) * r' = r := by rw [hr']; field_simp
  have hr'pos : 0 < r' := div_pos hr hrt
  have hpt : x₀ + r • (y + t • x₀) = (1 + r * t) • (x₀ + r' • y) := by
    rw [show (1 + r * t) • (x₀ + r' • y) = (1 + r * t) • x₀ + ((1 + r * t) * r') • y by
      rw [smul_add, smul_smul], hrr', smul_add, smul_smul, add_smul, one_smul]
    abel
  unfold blowup
  rw [hpt, hhom _ hrt]
  field_simp
  linear_combination (u (x₀ + r' • y)) * hrr'

/-- **Translation invariance of an off-origin blowup.** If `u` is one-homogeneous and locally
Lipschitz, `u x₀ = 0`, and `U` is a blowup limit of `u` at `x₀`, then `U(y + t x₀) = U(y)`. -/
theorem blowup_translation_invariant {u : E d → ℝ}
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x) (hlip : LocallyLipschitz u)
    {x₀ : E d} (hx₀ : u x₀ = 0) {U : E d → ℝ} (hU : IsBlowupLimit u x₀ U) (y : E d) (t : ℝ) :
    U (y + t • x₀) = U y := by
  obtain ⟨r, hr, hr0, hconv⟩ := hU
  have hconv' := hconv.tendstoLocallyUniformlyOn (s := univ)
  have h1 := hconv'.tendsto_at (mem_univ (y + t • x₀))
  have h2 := hconv'.tendsto_at (mem_univ y)
  -- the Lipschitz neighbourhood of `x₀`
  obtain ⟨K, s, hs, hK⟩ := hlip x₀
  -- convergence of the auxiliary quantities
  have hrt0 : Tendsto (fun n ↦ r n * t) atTop (𝓝 0) := by
    simpa using hr0.mul_const t
  set r' : ℕ → ℝ := fun n ↦ r n / (1 + r n * t) with hr'_def
  have hr'0 : Tendsto r' atTop (𝓝 0) := by
    have := hr0.div (tendsto_const_nhds.add hrt0) (by norm_num : (1 : ℝ) + 0 ≠ 0)
    rw [zero_div] at this
    exact this
  have hpt : ∀ ρ : ℕ → ℝ, Tendsto ρ atTop (𝓝 0) → Tendsto (fun n ↦ x₀ + ρ n • y) atTop (𝓝 x₀) :=
    fun ρ hρ ↦ by simpa using tendsto_const_nhds.add (hρ.smul_const y)
  have hev₁ : ∀ᶠ n in atTop, 0 < 1 + r n * t :=
    hrt0.eventually (lt_mem_nhds (by norm_num : (-1 : ℝ) < 0)) |>.mono fun n hn ↦ by linarith
  have hev₂ : ∀ᶠ n in atTop, x₀ + r n • y ∈ s := (hpt r hr0).eventually hs
  have hev₃ : ∀ᶠ n in atTop, x₀ + r' n • y ∈ s := (hpt r' hr'0).eventually hs
  -- the difference of the two rescalings tends to zero
  have hbound : Tendsto (fun n ↦ (K : ℝ) * |r n * t| * ‖y‖ + |t| * |u (x₀ + r n • y)|) atTop
      (𝓝 0) := by
    have hu : Tendsto (fun n ↦ u (x₀ + r n • y)) atTop (𝓝 0) := by
      rw [← hx₀]
      exact (hlip.continuous.tendsto x₀).comp (hpt r hr0)
    have := ((tendsto_const_nhds (x := (K : ℝ))).mul hrt0.abs).mul_const ‖y‖ |>.add
      ((tendsto_const_nhds (x := |t|)).mul hu.abs)
    simpa using this
  have hdiff : Tendsto (fun n ↦ blowup u x₀ (r n) (y + t • x₀) - blowup u x₀ (r n) y) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [hev₁, hev₂, hev₃] with n hn₁ hn₂ hn₃
    have hrn := hr n
    have hr'n : 0 < r' n := div_pos hrn hn₁
    rw [blowup_add_smul_eq hhom x₀ y hrn hn₁]
    change ‖u (x₀ + r' n • y) / r' n - u (x₀ + r n • y) / r n‖ ≤ _
    have hinv : 1 / r' n = 1 / r n + t := by
      rw [hr'_def]
      field_simp
    have hsplit : u (x₀ + r' n • y) / r' n - u (x₀ + r n • y) / r n =
        (u (x₀ + r' n • y) - u (x₀ + r n • y)) / r' n + t * u (x₀ + r n • y) := by
      have e1 : u (x₀ + r' n • y) / r' n = u (x₀ + r' n • y) * (1 / r' n) := by ring
      have e2 : u (x₀ + r n • y) / r n = u (x₀ + r n • y) * (1 / r n) := by ring
      have e3 : (u (x₀ + r' n • y) - u (x₀ + r n • y)) / r' n =
          (u (x₀ + r' n • y) - u (x₀ + r n • y)) * (1 / r' n) := by ring
      rw [e1, e2, e3, hinv]
      ring
    have hlipb : |u (x₀ + r' n • y) - u (x₀ + r n • y)| ≤ K * (|r' n - r n| * ‖y‖) := by
      have := hK.dist_le_mul _ hn₃ _ hn₂
      rw [Real.dist_eq, dist_eq_norm] at this
      rwa [show x₀ + r' n • y - (x₀ + r n • y) = (r' n - r n) • y by rw [sub_smul]; abel,
        norm_smul, Real.norm_eq_abs] at this
    have hrr : |r' n - r n| = r' n * |r n * t| := by
      have : r' n - r n = -(r' n * (r n * t)) := by
        rw [hr'_def]
        field_simp
        ring
      rw [this, abs_neg, abs_mul, abs_of_pos hr'n]
    rw [hsplit, Real.norm_eq_abs]
    calc |(u (x₀ + r' n • y) - u (x₀ + r n • y)) / r' n + t * u (x₀ + r n • y)|
        ≤ |(u (x₀ + r' n • y) - u (x₀ + r n • y)) / r' n| + |t * u (x₀ + r n • y)| :=
          abs_add_le _ _
      _ ≤ K * |r n * t| * ‖y‖ + |t| * |u (x₀ + r n • y)| := by
          rw [abs_div, abs_of_pos hr'n, abs_mul]
          gcongr
          rw [div_le_iff₀ hr'n]
          calc |u (x₀ + r' n • y) - u (x₀ + r n • y)| ≤ K * (|r' n - r n| * ‖y‖) := hlipb
            _ = K * |r n * t| * ‖y‖ * r' n := by rw [hrr]; ring
  have hlim := h1.sub h2
  exact sub_eq_zero.1 (tendsto_nhds_unique hlim hdiff)

/-- The translation invariance of blowups in the form used by the regularity argument: for a
continuous, nonnegative, one-homogeneous global minimizer in `ℝⁿ`, `n ≥ 2`, the locally Lipschitz
representative is the function itself. -/
theorem blowupTranslationInvariance_holds : BlowupTranslationInvariance := by
  intro n hn u hc hnn hmin hhom x₀ hx₀ U₀ hU₀ y t
  obtain ⟨v, hvu, hlip, -, -, -⟩ :=
    Registry.exists_continuous_representative hn (Eventually.of_forall hnn) hmin
  have hv : v = u :=
    (Continuous.ae_eq_iff_eq MeasureTheory.volume hlip.continuous hc).1 hvu
  subst hv
  exact blowup_translation_invariant hhom hlip (eq_zero_of_mem_freeBoundary hc hnn hx₀) hU₀ y t

end OnePhaseDimension
