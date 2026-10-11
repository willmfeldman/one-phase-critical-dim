/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Stability.Hadamard

/-!
# The Hadamard field

For `F_s = F + s φ` and a density family `K_s`, the Hadamard formula needs a `C¹` field `V_s`
with `⟨∇F_s, V_s⟩ = φ K_s` on a strip `{0 < F_s < δ}`. We construct

  `V_s = χ · (K_s φ / |N_s|²) N_s`,  `N_s = ∇F + s ∇φ = ∇F_s`,

with `χ` a smooth cut-off equal to `1` near the zero set of `F` in the support `M` of the
densities and supported where `∇F ≠ 0`, and check all hypotheses of `HadamardHyp` on
`[-s₀, s₀]` for some `s₀ > 0`, provided `∇F ≠ 0` on `{F = 0} ∩ M`.

## Main results

* `hadamardField`: the field `V_s`.
* `exists_hadamardHyp`: the hypotheses of the Hadamard formula hold for `V_s`.
* `inner_hadamardField`: `⟨N_s, V_s⟩ = χ K_s φ`.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace Function
open scoped ContDiff Gradient NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

/-- The gradient `N_s = ∇F + s ∇φ` of `F_s = F + s φ`. -/
def gradParam (F φ : E n → ℝ) (s : ℝ) (x : E n) : E n := ∇ F x + s • ∇ φ x

/-- The Hadamard field `V_s = χ · (K_s φ / |N_s|²) N_s`. -/
def hadamardField (F φ : E n → ℝ) (K : ℝ → E n → ℝ) (χ : E n → ℝ) (s : ℝ) (x : E n) : E n :=
  χ x • ((K s x * φ x / ‖gradParam F φ s x‖ ^ 2) • gradParam F φ s x)

section Field

variable {F φ : E n → ℝ} {K K' : ℝ → E n → ℝ} {χ : E n → ℝ}

theorem inner_hadamardField {s : ℝ} {x : E n} (hN : gradParam F φ s x ≠ 0) :
    ⟪gradParam F φ s x, hadamardField F φ K χ s x⟫ = χ x * (K s x * φ x) := by
  unfold hadamardField
  rw [inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
  have : ‖gradParam F φ s x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hN)
  field_simp

/-- `D F_s (v) = ⟨N_s, v⟩`. -/
theorem fderiv_param_apply {x : E n} (hF : DifferentiableAt ℝ F x) (hφ : DifferentiableAt ℝ φ x)
    (s : ℝ) (v : E n) :
    fderiv ℝ (fun y ↦ F y + s * φ y) x v = ⟪gradParam F φ s x, v⟫ := by
  rw [fderiv_fun_add hF (hφ.const_mul s), fderiv_const_mul hφ]
  simp only [gradParam, add_apply, smul_apply, smul_eq_mul, inner_add_left, inner_smul_left,
    conj_trivial, gradient, toDual_symm_apply]

theorem contDiff_gradient_of_two {G : E n → ℝ} (hG : ContDiff ℝ 2 G) : ContDiff ℝ 1 (∇ G) :=
  (toDual ℝ (E n)).symm.contDiff.comp (hG.fderiv_right (m := 1) le_rfl)

theorem contDiff_gradParam (hF : ContDiff ℝ 2 F) (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 1 fun p : ℝ × E n ↦ gradParam F φ p.1 p.2 :=
  ((contDiff_gradient_of_two hF).comp contDiff_snd).add
    (contDiff_fst.smul ((contDiff_gradient_of_two hφ).comp contDiff_snd))

/-- **The Hadamard field satisfies the Hadamard hypotheses.** Let `F, φ ∈ C²`, let `K` be jointly
`C¹` with `s`-derivative `K'` (jointly continuous), vanishing off the compact set `M`, and let
`∇F ≠ 0` on `{F = 0} ∩ M`. Then there are a smooth cut-off `χ` and `s₀, δ > 0` such that the
Hadamard field `V_s = χ (K_s φ / |N_s|²) N_s` satisfies `HadamardHyp` on `[-s₀, s₀]` with strip
width `δ`, `N_s ≠ 0` on `tsupport χ`, and `χ = 1` at the points of `M` with `|F_s| < δ`. -/
theorem exists_hadamardHyp (hF : ContDiff ℝ 2 F) (hφ : ContDiff ℝ 2 φ)
    (hK : ContDiff ℝ 1 (uncurry K)) (hK' : Continuous (uncurry K'))
    (hKd : ∀ s x, HasDerivAt (fun s ↦ K s x) (K' s x) s) {M : Set (E n)} (hM : IsCompact M)
    (hKM : ∀ s, ∀ x ∉ M, K s x = 0) (hreg : ∀ x ∈ M, F x = 0 → ∇ F x ≠ 0) :
    ∃ (χ : E n → ℝ) (s₀ δ : ℝ), 0 < s₀ ∧ ContDiff ℝ ∞ χ ∧
      HadamardHyp F φ K K' (hadamardField F φ K χ) M (-s₀) s₀ δ ∧
      (∀ s ∈ Icc (-s₀) s₀, ∀ x ∈ tsupport χ, gradParam F φ s x ≠ 0) ∧
      ∀ s ∈ Icc (-s₀) s₀, ∀ x ∈ M, |F x + s * φ x| < δ → χ x = 1 := by
  have hFc := hF.continuous
  have hφc := hφ.continuous
  have hgF : Continuous (∇ F) := (contDiff_gradient_of_two hF).continuous
  have hgφ : Continuous (∇ φ) := (contDiff_gradient_of_two hφ).continuous
  -- the zero set and a neighbourhood where `∇F ≠ 0`
  set Z := M ∩ {x | F x = 0} with hZ_def
  have hZ : IsCompact Z := hM.inter_right (isClosed_eq hFc continuous_const)
  have hO : IsOpen {x | ∇ F x ≠ 0} := isOpen_ne_fun hgF continuous_const
  obtain ⟨ε, hε, hεO⟩ := hZ.exists_cthickening_subset_open hO fun x hx ↦ hreg x hx.1 hx.2
  set Y := cthickening ε Z with hY_def
  have hY : IsCompact Y := hZ.cthickening
  obtain ⟨c, hc, hcY⟩ := hY.exists_forall_le' (f := fun x ↦ ‖∇ F x‖) hgF.norm.continuousOn
    (a := 0) fun x hx ↦ norm_pos_iff.2 (hεO hx)
  obtain ⟨Λ₀, hΛ₀⟩ := hY.exists_bound_of_continuousOn hgφ.continuousOn
  set Λ := max Λ₀ 0 + 1 with hΛ_def
  have hΛ : 0 < Λ := by positivity
  have hΛY : ∀ x ∈ Y, ‖∇ φ x‖ ≤ Λ := fun x hx ↦
    (hΛ₀ x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  -- away from the zero set, `|F|` is bounded below on `M`
  set M' := M \ thickening (ε / 2) Z with hM'_def
  have hM' : IsCompact M' := hM.diff isOpen_thickening
  obtain ⟨η₀, hη₀, hη₀M'⟩ := hM'.exists_forall_le' (f := fun x ↦ |F x|) hFc.abs.continuousOn
    (a := 0) fun x hx ↦ abs_pos.2 fun h0 ↦ hx.2
      (self_subset_thickening (half_pos hε) Z ⟨hx.1, h0⟩)
  obtain ⟨Φ₀, hΦ₀⟩ := hM.exists_bound_of_continuousOn hφc.continuousOn
  set Φ := max Φ₀ 0 + 1 with hΦ_def
  have hΦ : 0 < Φ := by positivity
  have hΦM : ∀ x ∈ M, |φ x| ≤ Φ := fun x hx ↦ by
    have := hΦ₀ x hx
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  set s₀ := min (c / (4 * Λ)) (η₀ / (4 * Φ)) with hs₀_def
  have hs₀ : 0 < s₀ := lt_min (by positivity) (by positivity)
  set δ := η₀ / 2 with hδ_def
  have hδ : 0 < δ := half_pos hη₀
  -- the cut-off
  obtain ⟨χ, hχ, hχc, hχU, hχ01, hχ1⟩ := exists_smooth_cutoff (hZ.cthickening (r := ε / 2))
    isOpen_thickening (cthickening_subset_thickening' hε (half_lt_self hε) Z)
  have hχY : tsupport χ ⊆ Y := hχU.trans (thickening_subset_cthickening ε Z)
  -- `N_s ≠ 0` on `Y` for `|s| < 2 s₀`
  have hNY : ∀ s, |s| < 2 * s₀ → ∀ x ∈ Y, c / 2 ≤ ‖gradParam F φ s x‖ := by
    intro s hs x hx
    have h1 : ‖s • ∇ φ x‖ ≤ c / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have h2 : 2 * s₀ ≤ c / (2 * Λ) := by
        have : s₀ ≤ c / (4 * Λ) := min_le_left _ _
        rw [show c / (2 * Λ) = 2 * (c / (4 * Λ)) by field_simp; ring]
        linarith
      calc |s| * ‖∇ φ x‖ ≤ (c / (2 * Λ)) * Λ :=
            mul_le_mul (hs.le.trans h2) (hΛY x hx) (norm_nonneg _) (by positivity)
        _ = c / 2 := by field_simp
    have h3 : ‖∇ F x‖ ≤ ‖∇ F x + s • ∇ φ x‖ + ‖s • ∇ φ x‖ :=
      calc ‖∇ F x‖ = ‖(∇ F x + s • ∇ φ x) - s • ∇ φ x‖ := by rw [add_sub_cancel_right]
        _ ≤ _ := norm_sub_le _ _
    unfold gradParam
    linarith [hcY x hx]
  -- `χ = 1` on the strip
  have hstripχ : ∀ s ∈ Icc (-s₀) s₀, ∀ x ∈ M, |F x + s * φ x| < δ → χ x = 1 := by
    intro s hs x hxM hx
    refine hχ1 x (thickening_subset_cthickening (ε / 2) Z ?_)
    by_contra hxT
    have h1 := hη₀M' x ⟨hxM, hxT⟩
    have h2 : |s * φ x| ≤ s₀ * Φ := by
      rw [abs_mul]
      exact mul_le_mul (abs_le.2 ⟨by linarith [hs.1], hs.2⟩) (hΦM x hxM) (abs_nonneg _)
        hs₀.le
    have h3 : s₀ * Φ ≤ η₀ / 4 := by
      have : s₀ ≤ η₀ / (4 * Φ) := min_le_right _ _
      calc s₀ * Φ ≤ η₀ / (4 * Φ) * Φ := mul_le_mul_of_nonneg_right this hΦ.le
        _ = η₀ / 4 := by field_simp
    have h4 : |F x| ≤ |F x + s * φ x| + |s * φ x| := by
      have := abs_sub (F x + s * φ x) (s * φ x)
      simpa using this
    linarith
  -- joint regularity of `Ψ(s, x) = V_s(x)`
  have hN := contDiff_gradParam hF hφ
  set Ψ : ℝ × E n → E n := fun p ↦ hadamardField F φ K χ p.1 p.2 with hΨ_def
  have hΨ : ∀ p : ℝ × E n, |p.1| < 2 * s₀ → ContDiffAt ℝ 1 Ψ p := by
    intro p hp
    by_cases hx : p.2 ∈ tsupport χ
    · have hNp : gradParam F φ p.1 p.2 ≠ 0 := fun h ↦ by
        have := hNY p.1 hp p.2 (hχY hx)
        rw [h, norm_zero] at this
        linarith
      have hnum : ContDiffAt ℝ 1 (fun p : ℝ × E n ↦ K p.1 p.2 * φ p.2) p :=
        hK.contDiffAt.mul ((hφ.of_le (by norm_num)).comp contDiff_snd).contDiffAt
      have hden : ContDiffAt ℝ 1 (fun p : ℝ × E n ↦ ‖gradParam F φ p.1 p.2‖ ^ 2) p :=
        ((contDiff_norm_sq ℝ).comp hN).contDiffAt
      have hg := (hnum.div hden (pow_ne_zero 2 (norm_ne_zero_iff.2 hNp))).smul hN.contDiffAt
      exact ((hχ.of_le (by exact_mod_cast le_top)).comp contDiff_snd).contDiffAt.smul hg
    · refine (contDiffAt_const (c := (0 : E n))).congr_of_eventuallyEq ?_
      have h0 := notMem_tsupport_iff_eventuallyEq.1 hx
      filter_upwards [continuous_snd.continuousAt.tendsto.eventually h0] with q hq
      simp [hΨ_def, hadamardField, hq]
  have hIcc : ∀ s ∈ Icc (-s₀) s₀, |s| < 2 * s₀ := fun s hs ↦
    (abs_le.2 ⟨by linarith [hs.1], hs.2⟩).trans_lt (by linarith)
  have hVs : ∀ s ∈ Icc (-s₀) s₀, ContDiff ℝ 1 (hadamardField F φ K χ s) := by
    intro s hs
    refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
    exact (hΨ (s, x) (hIcc s hs)).comp x (contDiffAt_const.prodMk contDiffAt_id)
  -- the support
  have htsupp : ∀ s ∈ Icc (-s₀) s₀, tsupport (hadamardField F φ K χ s) ⊆ M := by
    intro s _
    refine closure_minimal (fun x hx ↦ ?_) hM.isClosed
    by_contra hxM
    exact hx (by simp [hadamardField, hKM s x hxM])
  -- bounded divergence
  set P : Set (ℝ × E n) := Ioo (-(2 * s₀)) (2 * s₀) ×ˢ univ with hP_def
  have hP : IsOpen P := isOpen_Ioo.prod isOpen_univ
  have hΨP : ContDiffOn ℝ 1 Ψ P := fun p hp ↦
    (hΨ p (abs_lt.2 ⟨hp.1.1, hp.1.2⟩)).contDiffWithinAt
  have hcont := hΨP.continuousOn_fderiv_of_isOpen hP le_rfl
  have hQ : IsCompact (Icc (-s₀) s₀ ×ˢ M) := isCompact_Icc.prod hM
  have hQP : Icc (-s₀) s₀ ×ˢ M ⊆ P := fun p hp ↦
    ⟨abs_lt.1 (hIcc p.1 hp.1), mem_univ _⟩
  obtain ⟨A, hA⟩ := hQ.exists_bound_of_continuousOn (hcont.mono hQP)
  set L : E n →L[ℝ] ℝ × E n := (0 : E n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (E n))
  set Bd := ‖(traceCLM : (E n →L[ℝ] E n) →L[ℝ] ℝ)‖ * (max A 0 * ‖L‖)
  have hbd : ∀ s ∈ Icc (-s₀) s₀, ∀ x, |divergence (hadamardField F φ K χ s) x| ≤ Bd := by
    intro s hs x
    by_cases hxM : x ∈ M
    · have hd : HasFDerivAt (hadamardField F φ K χ s) ((fderiv ℝ Ψ (s, x)).comp L) x := by
        have h1 : HasFDerivAt (fun y : E n ↦ (s, y)) L x :=
          (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
        exact ((hΨ (s, x) (hIcc s hs)).differentiableAt one_ne_zero).hasFDerivAt.comp x h1
      rw [divergence_eq_traceCLM, hd.fderiv, ← Real.norm_eq_abs]
      refine (traceCLM.le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact (hA (s, x) ⟨hs, hxM⟩).trans (le_max_left _ _)
    · rw [divergence_of_notMem_tsupport fun h ↦ hxM (htsupp s hs h), abs_zero]
      positivity
  -- the strip identity
  have hstrip : ∀ s ∈ Icc (-s₀) s₀, ∀ x, 0 < F x + s * φ x → F x + s * φ x < δ →
      fderiv ℝ (fun y ↦ F y + s * φ y) x (hadamardField F φ K χ s x) = φ x * K s x := by
    intro s hs x h0 h1
    by_cases hxM : x ∈ M
    · have hχx : χ x = 1 := hstripχ s hs x hxM (abs_lt.2 ⟨by linarith, h1⟩)
      have hxT : x ∈ tsupport χ :=
        subset_tsupport _ (by rw [Function.mem_support, hχx]; exact one_ne_zero)
      have hNx : gradParam F φ s x ≠ 0 := fun h ↦ by
        have := hNY s (hIcc s hs) x (hχY hxT)
        rw [h, norm_zero] at this
        linarith
      rw [fderiv_param_apply ((hF.differentiable (by norm_num)) x)
        ((hφ.differentiable (by norm_num)) x), inner_hadamardField hNx, hχx]
      ring
    · have hV0 : hadamardField F φ K χ s x = 0 := by simp [hadamardField, hKM s x hxM]
      rw [hV0, map_zero, hKM s x hxM, mul_zero]
  refine ⟨χ, s₀, δ, hs₀, hχ, ⟨hF.of_le (by norm_num), hφ.of_le (by norm_num), hM, hK.continuous,
    hK', hKd, hKM, by linarith, hδ, hVs, htsupp, ⟨Bd, hbd⟩, hstrip⟩, fun s hs x hx h ↦ ?_,
    hstripχ⟩
  have := hNY s (hIcc s hs) x (hχY hx)
  rw [h, norm_zero] at this
  linarith

theorem gradient_param_eq {x : E n} (hF : DifferentiableAt ℝ F x) (hφ : DifferentiableAt ℝ φ x)
    (s : ℝ) : ∇ (fun y ↦ F y + s * φ y) x = gradParam F φ s x := by
  simp only [gradient, gradParam]
  rw [fderiv_fun_add hF (hφ.const_mul s), fderiv_const_mul hφ, map_add, map_smul]

/-! ### The energy density family -/

/-- The energy density `K_s = ζ (1 + |N_s|²)` of `F_s = F + s φ`, localized by `ζ`. -/
def energyDensity (ζ F φ : E n → ℝ) (s : ℝ) (x : E n) : ℝ :=
  ζ x * (1 + ‖gradParam F φ s x‖ ^ 2)

/-- Its `s`-derivative `K'_s = 2 ζ ⟨N_s, ∇φ⟩`. -/
def energyDensityDeriv (ζ F φ : E n → ℝ) (s : ℝ) (x : E n) : ℝ :=
  ζ x * (2 * ⟪gradParam F φ s x, ∇ φ x⟫)

theorem contDiff_energyDensity {ζ : E n → ℝ} (hζ : ContDiff ℝ 1 ζ) (hF : ContDiff ℝ 2 F)
    (hφ : ContDiff ℝ 2 φ) : ContDiff ℝ 1 (uncurry (energyDensity ζ F φ)) :=
  (hζ.comp contDiff_snd).mul (contDiff_const.add ((contDiff_norm_sq ℝ).comp
    (contDiff_gradParam hF hφ)))

theorem continuous_energyDensityDeriv {ζ : E n → ℝ} (hζ : Continuous ζ) (hF : ContDiff ℝ 2 F)
    (hφ : ContDiff ℝ 2 φ) : Continuous (uncurry (energyDensityDeriv ζ F φ)) :=
  (hζ.comp continuous_snd).mul (continuous_const.mul
    ((contDiff_gradParam hF hφ).continuous.inner
      ((contDiff_gradient_of_two hφ).continuous.comp continuous_snd)))

theorem hasDerivAt_energyDensity (ζ F φ : E n → ℝ) (s : ℝ) (x : E n) :
    HasDerivAt (fun s ↦ energyDensity ζ F φ s x) (energyDensityDeriv ζ F φ s x) s := by
  have h1 : HasDerivAt (fun s ↦ gradParam F φ s x) (∇ φ x) s := by
    simpa [gradParam] using ((hasDerivAt_id s).smul_const (∇ φ x)).const_add (∇ F x)
  exact ((h1.norm_sq).const_add 1).const_mul (ζ x)

theorem energyDensity_eq_zero {ζ : E n → ℝ} {x : E n} (hx : x ∉ tsupport ζ) (s : ℝ) :
    energyDensity ζ F φ s x = 0 := by
  simp [energyDensity, image_eq_zero_of_notMem_tsupport hx]

end Field

end OnePhaseDimension
