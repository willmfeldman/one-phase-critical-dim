/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.SuspensionMinimality
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Minimality of a translation-invariant factor

If `U(y, s) = v(y)` is a global minimizer of the one-phase energy in `ℝ^{k+1} = ℝᵏ × ℝ`, then
`v` is a global minimizer in `ℝᵏ`.

## Proof

Almost every slice of `U` lies in `H¹_loc(ℝᵏ)`, and every slice is `v`, so `v ∈ H¹_loc(ℝᵏ)`.
Suppose a competitor `q` for `v` on a ball `B` has `J(q; B) + δ = J(v; B)` with `δ > 0`, and let
`ψ = q - v`. For a smooth plateau `η_L` equal to `1` on `[-L, L]` and to `0` outside
`(-L - 1, L + 1)`, with `|η_L'| ≤ C₀` independent of `L`, the function
`V_L(y, s) = U(y, s) + η_L(s) ψ(y)` is a competitor for `U` on a large ball `𝓑_L`. Slice by slice:

* for `|s| ≤ L` the slice of `V_L` is `q`, so its slice energy is that of `U` minus `δ`;
* for `L < |s| < L + 1` its slice energy exceeds that of `U` by at most
  `C₁ = ∫_B |∇v|² + |∇q|² + C₀² ψ² + 1`, by convexity;
* elsewhere the two slices agree.

Integrating, `J(V_L; 𝓑_L) + 2Lδ ≤ J(U; 𝓑_L) + 2C₁`, which contradicts the minimality of `U` for
large `L`. All energies are compared as finite elements of `ℝ≥0∞`.

## Main results

* `isLocalEnergyMinimizer_of_prod_invariant`: the factor of a suspended minimizer is a minimizer.
* `factorMinimality_holds`: the same in the form used by the regularity argument.

## Differences from the source

The 2026-09-24 version assumes `v ∈ H¹_loc` and compares with nonnegative competitors; it uses a
piecewise linear cutoff `η_L` and the energy difference `-2Lδ + C`. We derive `v ∈ H¹_loc` from
the slices of `U`, use real competitors agreeing with `v` off the ball (no sign condition), a
smooth cutoff `η_L(s) = h(L + 1 - s) h(L + 1 + s)` built from the smooth transition function `h`
(so that the product rule for weak gradients applies), and compare the energies slice by slice in
`ℝ≥0∞`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient RealInnerProductSpace ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### A smooth plateau -/

section Plateau

open Real

theorem deriv_smoothTransition_eq_zero {x : ℝ} (hx : x ≤ 0 ∨ 1 ≤ x) :
    deriv smoothTransition x = 0 := by
  rcases hx with hx | hx
  · refine IsLocalMin.deriv_eq_zero (Eventually.of_forall fun y ↦ ?_)
    rw [smoothTransition.zero_of_nonpos hx]
    exact smoothTransition.nonneg y
  · refine IsLocalMax.deriv_eq_zero (Eventually.of_forall fun y ↦ ?_)
    rw [smoothTransition.one_of_one_le hx]
    exact smoothTransition.le_one y

theorem exists_bound_deriv_smoothTransition : ∃ M, 0 ≤ M ∧ ∀ x, |deriv smoothTransition x| ≤ M := by
  have hc : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  have hcs : HasCompactSupport (deriv smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx ↦ ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    exact deriv_smoothTransition_eq_zero (hx.imp le_of_lt le_of_lt)
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hc
  exact ⟨max C 0, le_max_right _ _, fun x ↦ (hC x).trans (le_max_left _ _)⟩

/-- The plateau `η_L(s) = h(L + 1 - s) h(L + 1 + s)`: smooth, `1` on `[-L, L]`, `0` outside
`(-L - 1, L + 1)`. -/
def plateau (L s : ℝ) : ℝ := smoothTransition (L + 1 - s) * smoothTransition (L + 1 + s)

theorem contDiff_plateau (L : ℝ) : ContDiff ℝ ∞ (plateau L) :=
  (smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).mul
    (smoothTransition.contDiff.comp (contDiff_const.add contDiff_id))

theorem hasDerivAt_plateau (L s : ℝ) :
    HasDerivAt (plateau L) (-deriv smoothTransition (L + 1 - s) * smoothTransition (L + 1 + s) +
      smoothTransition (L + 1 - s) * deriv smoothTransition (L + 1 + s)) s := by
  have hd : ∀ x, HasDerivAt smoothTransition (deriv smoothTransition x) x := fun x ↦
    ((smoothTransition.contDiff (n := 1)).differentiable (by norm_num) x).hasDerivAt
  have h1 : HasDerivAt (fun s ↦ smoothTransition (L + 1 - s))
      (deriv smoothTransition (L + 1 - s) * (-1)) s :=
    (hd _).comp s ((hasDerivAt_id s).const_sub (L + 1))
  have h2 : HasDerivAt (fun s ↦ smoothTransition (L + 1 + s))
      (deriv smoothTransition (L + 1 + s) * 1) s :=
    (hd _).comp s ((hasDerivAt_id s).const_add (L + 1))
  exact (h1.mul h2).congr_deriv (by ring)

theorem plateau_eq_one {L s : ℝ} (hs : |s| ≤ L) : plateau L s = 1 := by
  rw [abs_le] at hs
  rw [plateau, smoothTransition.one_of_one_le (by linarith),
    smoothTransition.one_of_one_le (by linarith), mul_one]

theorem plateau_eq_zero {L s : ℝ} (hs : L + 1 ≤ |s|) : plateau L s = 0 := by
  rcases le_abs'.1 hs with h | h
  · rw [plateau, smoothTransition.zero_of_nonpos (x := L + 1 + s) (by linarith), mul_zero]
  · rw [plateau, smoothTransition.zero_of_nonpos (x := L + 1 - s) (by linarith), zero_mul]

theorem deriv_plateau_eq_zero {L s : ℝ} (hs : |s| ≤ L ∨ L + 1 ≤ |s|) :
    deriv (plateau L) s = 0 := by
  rw [(hasDerivAt_plateau L s).deriv]
  rcases hs with hs | hs
  · rw [abs_le] at hs
    rw [deriv_smoothTransition_eq_zero (Or.inr (by linarith)),
      deriv_smoothTransition_eq_zero (x := L + 1 + s) (Or.inr (by linarith))]
    ring
  · rcases le_abs'.1 hs with h | h
    · rw [deriv_smoothTransition_eq_zero (x := L + 1 + s) (Or.inl (by linarith)),
        smoothTransition.zero_of_nonpos (x := L + 1 + s) (by linarith)]
      ring
    · rw [deriv_smoothTransition_eq_zero (x := L + 1 - s) (Or.inl (by linarith)),
        smoothTransition.zero_of_nonpos (x := L + 1 - s) (by linarith)]
      ring

theorem plateau_nonneg (L s : ℝ) : 0 ≤ plateau L s :=
  mul_nonneg (smoothTransition.nonneg _) (smoothTransition.nonneg _)

theorem plateau_le_one (L s : ℝ) : plateau L s ≤ 1 := by
  unfold plateau
  nlinarith [smoothTransition.nonneg (L + 1 - s), smoothTransition.le_one (L + 1 - s),
    smoothTransition.nonneg (L + 1 + s), smoothTransition.le_one (L + 1 + s)]

theorem abs_deriv_plateau_le {M : ℝ} (hM : ∀ x, |deriv smoothTransition x| ≤ M) (L s : ℝ) :
    |deriv (plateau L) s| ≤ 2 * M := by
  rw [(hasDerivAt_plateau L s).deriv]
  have h1 := hM (L + 1 - s)
  have h2 := hM (L + 1 + s)
  have a1 : |smoothTransition (L + 1 + s)| ≤ 1 := by
    rw [abs_of_nonneg (smoothTransition.nonneg _)]; exact smoothTransition.le_one _
  have a2 : |smoothTransition (L + 1 - s)| ≤ 1 := by
    rw [abs_of_nonneg (smoothTransition.nonneg _)]; exact smoothTransition.le_one _
  calc _ ≤ |-deriv smoothTransition (L + 1 - s) * smoothTransition (L + 1 + s)| +
        |smoothTransition (L + 1 - s) * deriv smoothTransition (L + 1 + s)| := abs_add_le _ _
    _ = |deriv smoothTransition (L + 1 - s)| * |smoothTransition (L + 1 + s)| +
        |smoothTransition (L + 1 - s)| * |deriv smoothTransition (L + 1 + s)| := by
        rw [abs_mul, abs_mul, abs_neg]
    _ ≤ M * 1 + 1 * M := by
        gcongr
        · exact le_trans (abs_nonneg _) h1
    _ = 2 * M := by ring

end Plateau

variable {k : ℕ}

/-- The gradient of `x ↦ η(x_{k+1})`. -/
theorem gradient_comp_last {η : ℝ → ℝ} (hη : Differentiable ℝ η) (x : E (k + 1)) :
    ∇ (fun x : E (k + 1) ↦ η (x (Fin.last k))) x = deriv η (x (Fin.last k)) • lastVec k := by
  set P : E (k + 1) →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last k)
  have h : HasFDerivAt (fun x : E (k + 1) ↦ η (P x)) (deriv η (P x) • P) x :=
    (hη (P x)).hasDerivAt.comp_hasFDerivAt x P.hasFDerivAt
  refine (hasGradientAt_iff_hasFDerivAt.2 (h.congr_fderiv ?_)).gradient
  ext w
  simp [P, lastVec, EuclideanSpace.inner_single_left]

/-! ### Energy integrands and slices -/

/-- The energy with unit coefficient as a lower integral over the whole space. -/
theorem energyJ_one_eq_lintegral {d : ℕ} {V : Set (E d)} (hV : MeasurableSet V) (w : E d → ℝ)
    (G : E d → E d) :
    energyJ V (fun _ ↦ 1) w G = ∫⁻ x, V.indicator
      (fun x ↦ ENNReal.ofReal (‖G x‖ ^ 2 + (Ioi (0 : ℝ)).indicator 1 (w x))) x := by
  rw [energyJ_one_eq hV, lintegral_indicator hV]

theorem aemeasurable_energyIntegrand {d : ℕ} {V : Set (E d)} (hV : MeasurableSet V)
    {w : E d → ℝ} {G : E d → E d} (h : MemH1Loc univ w G) :
    AEMeasurable (V.indicator
      fun x ↦ ENNReal.ofReal (‖G x‖ ^ 2 + (Ioi (0 : ℝ)).indicator 1 (w x))) := by
  have hG : AEStronglyMeasurable G volume :=
    (locallyIntegrableOn_univ.1 h.1.2.1).aestronglyMeasurable
  have hw : AEMeasurable w volume :=
    (locallyIntegrableOn_univ.1 h.1.1).aestronglyMeasurable.aemeasurable
  exact (((hG.norm.aemeasurable.pow_const 2).add
    ((measurable_const.indicator measurableSet_Ioi).comp_aemeasurable hw)).ennreal_ofReal).indicator
    hV

/-- The factor `v` of a minimizer `v ∘ π` lies in `H¹_loc`. -/
theorem exists_memH1Loc_of_prod {v : E k → ℝ} {GU : E (k + 1) → E (k + 1)}
    (h : MemH1Loc univ (fun x ↦ v (projInit k x)) GU) : ∃ Gv, MemH1Loc univ v Gv := by
  obtain ⟨s, hs⟩ := (ae_memH1Loc_slice h).exists
  simp only [projInit_joinLast] at hs
  exact ⟨_, hs⟩

/-- `max(a, b)² ≤ a² + b²` for `a, b ≥ 0`, through the convex combination. -/
theorem sq_norm_convex_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a b : F) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ‖a + t • (b - a)‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have hx : a + t • (b - a) = (1 - t) • a + t • b := by
    rw [smul_sub, sub_smul, one_smul]; abel
  have h1 : ‖a + t • (b - a)‖ ≤ (1 - t) * ‖a‖ + t * ‖b‖ := by
    rw [hx]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
      abs_of_nonneg ht0]
  have h2 : (1 - t) * ‖a‖ + t * ‖b‖ ≤ max ‖a‖ ‖b‖ := by
    nlinarith [le_max_left ‖a‖ ‖b‖, le_max_right ‖a‖ ‖b‖]
  have h3 : max ‖a‖ ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rcases le_total ‖a‖ ‖b‖ with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg ‖a‖]
    · rw [max_eq_left h]; nlinarith [sq_nonneg ‖b‖]
  have h0 : 0 ≤ ‖a + t • (b - a)‖ := norm_nonneg _
  nlinarith

/-! ### Minimality of the factor -/

/-- **Minimality of a translation-invariant factor.** If `x ↦ v(π x)` is a global minimizer of the
one-phase energy in `ℝ^{k+1}`, then `v` is a global minimizer in `ℝᵏ`. -/
theorem isLocalEnergyMinimizer_of_prod_invariant {v : E k → ℝ}
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) (fun x ↦ v (projInit k x))) :
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) v := by
  obtain ⟨GU', hGU', hm⟩ := hmin
  obtain ⟨Gv, hGv⟩ := exists_memH1Loc_of_prod hGU'
  refine ⟨Gv, hGv, fun yc r hr _ ↦ ⟨hGv, fun _ _ ↦ rfl, fun _ _ ↦ mem_univ _,
    fun q Gq hq hqoff _ ↦ ?_⟩⟩
  set B := ball yc r with hB_def
  by_contra hlt
  push Not at hlt
  -- finiteness and the gap `δ`
  have hBc : IsCompact (closure B) := isBounded_ball.isCompact_closure
  have hJv : energyJ B (fun _ ↦ 1) v Gv < ⊤ :=
    energyJ_lt_top hGv hBc (subset_univ _) (CQ := 1) fun _ _ ↦ by simp
  set δ := energyJ B (fun _ ↦ 1) v Gv - energyJ B (fun _ ↦ 1) q Gq with hδ_def
  have hδ0 : δ ≠ 0 := (tsub_pos_of_lt hlt).ne'
  have hδtop : δ ≠ ⊤ := (lt_of_le_of_lt tsub_le_self hJv).ne
  have hqδ : energyJ B (fun _ ↦ 1) q Gq + δ = energyJ B (fun _ ↦ 1) v Gv :=
    add_tsub_cancel_of_le hlt.le
  -- the difference `ψ = q - v`
  set ψ : E k → ℝ := fun y ↦ q y - v y with hψ_def
  set Gψ : E k → E k := fun y ↦ Gq y - Gv y with hGψ_def
  have hψ : MemH1Loc univ ψ Gψ := hq.sub hGv
  have hgood : ∀ᵐ y, y ∉ B → ψ y = 0 ∧ Gψ y = 0 := by
    have h1 : ∀ᵐ y, y ∉ B → ψ y = 0 := by
      have := hqoff
      rw [ae_restrict_iff' (MeasurableSet.univ.diff measurableSet_ball)] at this
      filter_upwards [this] with y hy hyB
      simp [hψ_def, hy ⟨mem_univ _, hyB⟩]
    have h2 := HasWeakGradient.ae_eq_zero_of_eq_zero isOpen_univ hψ.1
    rw [Measure.restrict_univ] at h2
    filter_upwards [h1, h2] with y hy1 hy2 hyB
    exact ⟨hy1 hyB, hy2 (hy1 hyB)⟩
  -- the constant `C₁`
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_smoothTransition
  set C₀ := 2 * M
  set g : E k → ℝ := fun y ↦ ‖Gv y‖ ^ 2 + ‖Gq y‖ ^ 2 + C₀ ^ 2 * ψ y ^ 2 + 1 with hg_def
  set C₁ : ℝ≥0∞ := ∫⁻ y in B, ENNReal.ofReal (g y) with hC₁_def
  have hC₁ : C₁ ≠ ⊤ := by
    have hK := isCompact_closedBall yc r
    have hfin : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
    have hsq : ∀ {F : Type} [NormedAddCommGroup F] {f : E k → F},
        MemLp f 2 (volume.restrict (closedBall yc r)) →
          Integrable (fun y ↦ ‖f y‖ ^ 2) (volume.restrict B) := fun hf ↦
      ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf).mono_measure
        (Measure.restrict_mono ball_subset_closedBall le_rfl)
    have i1 := hsq (hGv.2 _ (subset_univ _) hK).2
    have i2 := hsq (hq.2 _ (subset_univ _) hK).2
    have i3 := hsq (hψ.2 _ (subset_univ _) hK).1
    have hint : Integrable g (volume.restrict B) := by
      refine ((i1.add i2).add (i3.const_mul (C₀ ^ 2))).add (integrable_const 1) |>.congr ?_
      filter_upwards with y
      simp [hg_def, Real.norm_eq_abs, sq_abs]
    exact hint.lintegral_lt_top.ne
  -- the length `L`
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top hC₁ hδ0)
  set L : ℝ := (N : ℝ)
  have hL0 : 0 ≤ L := Nat.cast_nonneg N
  set η := plateau L
  have hη : ContDiff ℝ ∞ η := contDiff_plateau L
  have hηd : Differentiable ℝ η := hη.differentiable (by simp)
  -- the competitor `V`
  have hηc : ContDiff ℝ ∞ (fun x : E (k + 1) ↦ η (x (Fin.last k))) :=
    hη.comp (EuclideanSpace.proj (Fin.last k) : E (k + 1) →L[ℝ] ℝ).contDiff
  have hU := memH1Loc_comp_projInit (k := k) hGv
  have hV := hU.add ((memH1Loc_comp_projInit (k := k) hψ).mul_smooth isOpen_univ hηc)
  set V : E (k + 1) → ℝ := fun x ↦ v (projInit k x) +
    η (x (Fin.last k)) * ψ (projInit k x) with hV_def
  set GV : E (k + 1) → E (k + 1) := fun x ↦ (projInit k).adjoint (Gv (projInit k x)) +
    (η (x (Fin.last k)) • (projInit k).adjoint (Gψ (projInit k x)) +
      ψ (projInit k x) • ∇ (fun x : E (k + 1) ↦ η (x (Fin.last k))) x) with hGV_def
  have hV' : MemH1Loc univ V GV := hV
  -- the large ball
  set c : E (k + 1) := joinLast yc 0
  set R : ℝ := r + L + 2
  have hR : 0 < R := by positivity
  have hcyl : ∀ y ∈ B, ∀ s : ℝ, |s| < L + 1 + 1 → joinLast y s ∈ ball c R := by
    intro y hy s hs
    rw [joinLast_mem_ball_iff hR, projInit_joinLast, joinLast_last, sub_zero, mem_ball,
      Real.lt_sqrt dist_nonneg]
    have h1 : dist y yc < r := hy
    have h2 : s ^ 2 < (L + 2) ^ 2 := by
      rw [← sq_abs]; exact pow_lt_pow_left₀ hs (abs_nonneg _) two_ne_zero |>.trans_eq (by ring)
    nlinarith [dist_nonneg (x := y) (y := yc)]
  -- `V = U` a.e. off the large ball
  have hoff : ∀ᵐ x ∂(volume.restrict (univ \ ball c R)), V x = v (projInit k x) := by
    rw [ae_restrict_iff' (MeasurableSet.univ.diff measurableSet_ball)]
    filter_upwards [ae_comp_projInit hgood] with x hx hxB
    simp only [hV_def]
    by_cases hπ : projInit k x ∈ B
    · have hs : L + 1 ≤ |x (Fin.last k)| := by
        by_contra hs
        push Not at hs
        refine hxB.2 ?_
        have := hcyl _ hπ (x (Fin.last k)) (by linarith)
        rwa [joinLast_projInit] at this
      rw [show η (x (Fin.last k)) = 0 from plateau_eq_zero hs, zero_mul, add_zero]
    · rw [(hx hπ).1, mul_zero, add_zero]
  -- minimality of `U` on the large ball
  have hJ : energyJ (ball c R) (fun _ ↦ 1) (fun x ↦ v (projInit k x))
      (fun x ↦ (projInit k).adjoint (Gv (projInit k x))) ≤
      energyJ (ball c R) (fun _ ↦ 1) V GV := by
    have hle := (hm c R hR (subset_univ _)).2.2.2 V GV hV' hoff
      (Eventually.of_forall fun _ ↦ mem_univ _)
    have hG : ∀ᵐ x ∂(volume.restrict (ball c R)),
        GU' x = (projInit k).adjoint (Gv (projInit k x)) :=
      HasWeakGradient.ae_eq_of_eqOn isOpen_univ isOpen_ball (subset_univ _) hGU'.1 hU.1
        fun _ _ ↦ rfl
    rwa [energyJ_congr (fun _ _ ↦ rfl) hG] at hle
  -- slice integrands
  set FU : E (k + 1) → ℝ≥0∞ := (ball c R).indicator fun x ↦ ENNReal.ofReal
    (‖(projInit k).adjoint (Gv (projInit k x))‖ ^ 2 +
      (Ioi (0 : ℝ)).indicator 1 (v (projInit k x))) with hFU_def
  set FV : E (k + 1) → ℝ≥0∞ := (ball c R).indicator fun x ↦ ENNReal.ofReal
    (‖GV x‖ ^ 2 + (Ioi (0 : ℝ)).indicator 1 (V x)) with hFV_def
  set a : ℝ → ℝ≥0∞ := fun s ↦ ∫⁻ y, FV (joinLast y s)
  set b : ℝ → ℝ≥0∞ := fun s ↦ ∫⁻ y, FU (joinLast y s)
  have hJU : energyJ (ball c R) (fun _ ↦ 1) (fun x ↦ v (projInit k x))
      (fun x ↦ (projInit k).adjoint (Gv (projInit k x))) = ∫⁻ s, b s := by
    rw [energyJ_one_eq_lintegral measurableSet_ball,
      lintegral_eq_lintegral_slices (aemeasurable_energyIntegrand measurableSet_ball hU)]
  have hJV : energyJ (ball c R) (fun _ ↦ 1) V GV = ∫⁻ s, a s := by
    rw [energyJ_one_eq_lintegral measurableSet_ball,
      lintegral_eq_lintegral_slices (aemeasurable_energyIntegrand measurableSet_ball hV')]
  have hJUfin : ∫⁻ s, b s ≠ ⊤ := by
    rw [← hJU]
    exact (energyJ_lt_top hU isBounded_ball.isCompact_closure (subset_univ _) (CQ := 1)
      fun _ _ ↦ by simp).ne
  -- explicit values on the slices
  have hVj : ∀ y s, V (joinLast y s) = v y + η s * ψ y := fun y s ↦ by
    simp [hV_def]
  have hGVj : ∀ y s, ‖GV (joinLast y s)‖ ^ 2 =
      ‖Gv y + η s • Gψ y‖ ^ 2 + (ψ y * deriv η s) ^ 2 := fun y s ↦ by
    have : GV (joinLast y s) = joinLast (Gv y + η s • Gψ y) (ψ y * deriv η s) := by
      simp only [hGV_def, projInit_joinLast, joinLast_last, gradient_comp_last hηd]
      rw [joinLast_eq, map_add, map_smul, smul_smul, add_assoc]
    rw [this, norm_sq_joinLast]
  have hFUj : ∀ y s, joinLast y s ∈ ball c R →
      FU (joinLast y s) = ENNReal.ofReal (‖Gv y‖ ^ 2 + (Ioi (0 : ℝ)).indicator 1 (v y)) :=
    fun y s h ↦ by
      rw [hFU_def, indicator_of_mem h]
      simp [norm_projInit_adjoint]
  have hFVj : ∀ y s, joinLast y s ∈ ball c R → FV (joinLast y s) = ENNReal.ofReal
      (‖Gv y + η s • Gψ y‖ ^ 2 + (ψ y * deriv η s) ^ 2 +
        (Ioi (0 : ℝ)).indicator 1 (v y + η s * ψ y)) := fun y s h ↦ by
    rw [hFV_def, indicator_of_mem h, hGVj, hVj]
  -- where `V` and `U` agree on the slice
  have hagree : ∀ y s, (ψ y = 0 ∧ Gψ y = 0) ∨ (η s = 0 ∧ deriv η s = 0) →
      FV (joinLast y s) = FU (joinLast y s) := by
    intro y s h
    by_cases hm : joinLast y s ∈ ball c R
    · rw [hFVj y s hm, hFUj y s hm]
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
    · rw [hFV_def, hFU_def, indicator_of_notMem hm, indicator_of_notMem hm]
  -- splitting the slice integrals
  have hsplit : ∀ f : E k → ℝ≥0∞, ∫⁻ y, f y = (∫⁻ y in B, f y) + ∫⁻ y in Bᶜ, f y :=
    fun f ↦ (lintegral_add_compl f measurableSet_ball).symm
  have hcompl : ∀ s, ∫⁻ y in Bᶜ, FV (joinLast y s) = ∫⁻ y in Bᶜ, FU (joinLast y s) := by
    intro s
    refine setLIntegral_congr_fun_ae measurableSet_ball.compl ?_
    filter_upwards [hgood] with y hy hyB
    exact hagree y s (Or.inl (hy hyB))
  have hbB : ∀ s, |s| ≤ L + 1 →
      ∫⁻ y in B, FU (joinLast y s) = energyJ B (fun _ ↦ 1) v Gv := by
    intro s hs
    rw [energyJ_one_eq measurableSet_ball]
    refine setLIntegral_congr_fun measurableSet_ball fun y hy ↦ ?_
    exact hFUj y s (hcyl y hy s (by linarith))
  -- the core slices
  have hcore : ∀ s, |s| ≤ L → a s + δ ≤ b s := by
    intro s hs
    have hη1 : η s = 1 := plateau_eq_one hs
    have hηd0 : deriv η s = 0 := deriv_plateau_eq_zero (Or.inl hs)
    have haB : ∫⁻ y in B, FV (joinLast y s) = energyJ B (fun _ ↦ 1) q Gq := by
      rw [energyJ_one_eq measurableSet_ball]
      refine setLIntegral_congr_fun measurableSet_ball fun y hy ↦ ?_
      rw [hFVj y s (hcyl y hy s (by linarith)), hη1, hηd0]
      simp [hψ_def, hGψ_def]
    simp only [a, b]
    rw [hsplit, hsplit (fun y ↦ FU (joinLast y s)), haB, hbB s (by linarith), hcompl s,
      ← hqδ, add_right_comm]
  -- the transition slices
  have htrans : ∀ s, a s ≤ b s + C₁ := by
    intro s
    simp only [a, b]
    rw [hsplit, hcompl s]
    have h1 : ∫⁻ y in B, FV (joinLast y s) ≤ C₁ := by
      refine setLIntegral_mono' measurableSet_ball fun y hy ↦ ?_
      by_cases hm : joinLast y s ∈ ball c R
      · rw [hFVj y s hm]
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : Gv y + η s • Gψ y = Gv y + η s • (Gq y - Gv y) := rfl
        have b1 := sq_norm_convex_le (Gv y) (Gq y) (plateau_nonneg L s) (plateau_le_one L s)
        have b2 : (ψ y * deriv η s) ^ 2 ≤ C₀ ^ 2 * ψ y ^ 2 := by
          have hd : (deriv η s) ^ 2 ≤ C₀ ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (abs_deriv_plateau_le hM L s) 2
          calc (ψ y * deriv η s) ^ 2 = ψ y ^ 2 * (deriv η s) ^ 2 := by ring
            _ ≤ ψ y ^ 2 * C₀ ^ 2 := mul_le_mul_of_nonneg_left hd (sq_nonneg _)
            _ = C₀ ^ 2 * ψ y ^ 2 := by ring
        have b3 : (Ioi (0 : ℝ)).indicator 1 (v y + η s * ψ y) ≤ (1 : ℝ) := by
          by_cases h : v y + η s * ψ y ∈ Ioi (0 : ℝ)
          · rw [indicator_of_mem h]; rfl
          · rw [indicator_of_notMem h]; norm_num
        rw [e1]
        simp only [hg_def]
        linarith
      · rw [hFV_def, indicator_of_notMem hm]
        exact bot_le
    have h2 : ∫⁻ y in Bᶜ, FU (joinLast y s) ≤ ∫⁻ y, FU (joinLast y s) :=
      setLIntegral_le_lintegral _ _
    calc _ ≤ C₁ + ∫⁻ y, FU (joinLast y s) := add_le_add h1 h2
      _ = _ := add_comm _ _
  -- the outer slices
  have hout : ∀ s, L + 1 ≤ |s| → a s = b s := by
    intro s hs
    simp only [a, b]
    refine lintegral_congr fun y ↦ hagree y s (Or.inr ⟨plateau_eq_zero hs,
      deriv_plateau_eq_zero (Or.inr hs)⟩)
  -- integrating over `s`
  set core : Set ℝ := Icc (-L) L
  set T : Set ℝ := Icc (-(L + 1)) (L + 1) \ core
  have hpt : ∀ s, a s + δ * core.indicator 1 s ≤ b s + C₁ * T.indicator 1 s := by
    intro s
    by_cases hc : s ∈ core
    · have hT : s ∉ T := fun h ↦ h.2 hc
      rw [indicator_of_mem hc, indicator_of_notMem hT, Pi.one_apply, mul_one, mul_zero, add_zero]
      exact hcore s (abs_le.2 hc)
    · rw [indicator_of_notMem hc, mul_zero, add_zero]
      by_cases hT : s ∈ T
      · rw [indicator_of_mem hT, Pi.one_apply, mul_one]
        exact htrans s
      · have hs : L + 1 ≤ |s| := by
          by_contra h
          push Not at h
          exact hT ⟨abs_le.1 h.le, hc⟩
        rw [hout s hs]
        exact le_self_add
  have hint := lintegral_mono (μ := (volume : Measure ℝ)) hpt
  have hcm : MeasurableSet core := measurableSet_Icc
  have hTm : MeasurableSet T := measurableSet_Icc.diff measurableSet_Icc
  have e1 : ∫⁻ s, (a s + δ * core.indicator 1 s) = (∫⁻ s, a s) + δ * volume core := by
    rw [lintegral_add_right _ ((measurable_one.indicator hcm).const_mul δ),
      lintegral_const_mul _ (measurable_one.indicator hcm), lintegral_indicator_one hcm]
  have e2 : ∫⁻ s, (b s + C₁ * T.indicator 1 s) = (∫⁻ s, b s) + C₁ * volume T := by
    rw [lintegral_add_right _ ((measurable_one.indicator hTm).const_mul C₁),
      lintegral_const_mul _ (measurable_one.indicator hTm), lintegral_indicator_one hTm]
  rw [e1, e2] at hint
  have hvolc : volume core = ENNReal.ofReal (2 * L) := by
    rw [Real.volume_Icc]; ring_nf
  have hvolT : volume T ≤ 2 := by
    calc volume T ≤ volume (Icc (-(L + 1)) (-L) ∪ Icc L (L + 1)) := by
          refine measure_mono fun s hs ↦ ?_
          simp only [T, core, Set.mem_sdiff, mem_Icc, not_and_or, not_le] at hs
          rcases hs.2 with h | h
          · exact Or.inl ⟨hs.1.1, h.le⟩
          · exact Or.inr ⟨h.le, hs.1.2⟩
      _ ≤ volume (Icc (-(L + 1)) (-L)) + volume (Icc L (L + 1)) := measure_union_le _ _
      _ = 2 := by
          rw [Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_add (by linarith) (by linarith)]
          norm_num
  -- the contradiction
  have hfinal : (∫⁻ s, b s) + δ * ENNReal.ofReal (2 * L) ≤ (∫⁻ s, b s) + C₁ * 2 := by
    calc (∫⁻ s, b s) + δ * ENNReal.ofReal (2 * L) ≤ (∫⁻ s, a s) + δ * volume core := by
          rw [hvolc, ← hJU, ← hJV]; gcongr
      _ ≤ (∫⁻ s, b s) + C₁ * volume T := hint
      _ ≤ (∫⁻ s, b s) + C₁ * 2 := by gcongr
  have hle2 : δ * ENNReal.ofReal (2 * L) ≤ C₁ * 2 :=
    (ENNReal.add_le_add_iff_left hJUfin).1 hfinal
  have hlt2 : C₁ * 2 < δ * ENNReal.ofReal (2 * L) := by
    have h1 : C₁ < δ * N := by
      rw [ENNReal.div_lt_iff (Or.inl hδ0) (Or.inl hδtop)] at hN
      rwa [mul_comm]
    have h2 : ENNReal.ofReal (2 * L) = N * 2 := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast, mul_comm]
      norm_num
    rw [h2, ← mul_assoc]
    gcongr
    norm_num
  exact absurd hle2 (not_le.2 hlt2)

/-- Factor minimality in the form used by the regularity argument. -/
theorem factorMinimality_holds : FactorMinimality :=
  fun _ _ _ _ hmin ↦ isLocalEnergyMinimizer_of_prod_invariant hmin

end OnePhaseDimension
