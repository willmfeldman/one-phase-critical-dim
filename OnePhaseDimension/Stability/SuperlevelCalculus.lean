/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Stability.HadamardField
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Second variation of superlevel integrals

For `F_s = F + s φ` and a smooth compactly supported density family `K_s`, the Hadamard rate
`R(s) = ∫_{F_s > 0} ∂_s K_s + Flux_{F_s > 0}(V_s)` is itself a superlevel integral, of the density
`L_s = ∂_s K_s - div V_s`. Applying the Hadamard formula to `L` (and once more, for the continuity
of the resulting rate) shows that `Λ(s) = ∫_{F_s > 0} K_s` is differentiable near `0` with a
derivative that is differentiable at `0`. If `Λ` has a local minimum at `0`, the second derivative
`Λ''(0)`, the Hadamard rate of `L` at `0`, is nonnegative.

## Main results

* `paramDeriv`: the partial derivative `∂_s` of a two-variable family.
* `hasDerivAt_divergence_param`: `∂_s div V_s = div ∂_s V_s` (symmetry of mixed partials).
* `rateDensity`: the density `L_s = ∂_s K_s - div V_s` with `V_s` the Hadamard field.
* `nonneg_of_isLocalMin_of_hasDerivAt`: a second-derivative test needing only
  `f' = g` near `0` and `g` differentiable at `0`.
* `nonneg_secondVariation`: if `Λ` has a local minimum at `0`, the Hadamard rate of `L` at `0`
  is nonnegative.
-/

open Set Filter Topology MeasureTheory Metric InnerProductSpace Function
open scoped ContDiff Gradient NNReal RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

variable {n : ℕ}

theorem infty_add_one_le : (∞ : ℕ∞ω) + 1 ≤ ∞ := by
  exact_mod_cast le_top

/-! ### Partial derivatives in the parameter -/

section ParamDeriv

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The partial derivative `∂_s K(s, x)` of a two-variable family. -/
def paramDeriv (K : ℝ → E n → G) (s : ℝ) (x : E n) : G := fderiv ℝ (uncurry K) (s, x) (1, 0)

theorem hasDerivAt_paramDeriv {K : ℝ → E n → G} {s : ℝ} {x : E n}
    (hK : DifferentiableAt ℝ (uncurry K) (s, x)) :
    HasDerivAt (fun t ↦ K t x) (paramDeriv K s x) s := by
  have h1 : HasDerivAt (fun t : ℝ ↦ (t, x)) ((1 : ℝ), (0 : E n)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  exact hK.hasFDerivAt.comp_hasDerivAt s h1

theorem continuous_paramDeriv {K : ℝ → E n → G} (hK : ContDiff ℝ 1 (uncurry K)) :
    Continuous (uncurry (paramDeriv K)) :=
  (hK.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem contDiff_paramDeriv {K : ℝ → E n → G} (hK : ContDiff ℝ ∞ (uncurry K)) :
    ContDiff ℝ ∞ (uncurry (paramDeriv K)) :=
  (hK.fderiv_right infty_add_one_le).clm_apply contDiff_const

theorem contDiffOn_paramDeriv {K : ℝ → E n → G} {O : Set (ℝ × E n)} (hO : IsOpen O)
    (hK : ContDiffOn ℝ ∞ (uncurry K) O) : ContDiffOn ℝ ∞ (uncurry (paramDeriv K)) O :=
  (hK.fderiv_of_isOpen hO infty_add_one_le).clm_apply contDiffOn_const

theorem paramDeriv_eq_of_hasDerivAt {K : ℝ → E n → G} {s : ℝ} {x : E n} {v : G}
    (hK : DifferentiableAt ℝ (uncurry K) (s, x)) (h : HasDerivAt (fun t ↦ K t x) v s) :
    paramDeriv K s x = v :=
  (hasDerivAt_paramDeriv hK).unique h

theorem paramDeriv_eq_zero_of_forall {K : ℝ → E n → G} {s : ℝ} {x : E n}
    (hK : DifferentiableAt ℝ (uncurry K) (s, x)) (h0 : ∀ t, K t x = 0) : paramDeriv K s x = 0 := by
  refine paramDeriv_eq_of_hasDerivAt hK ?_
  have : (fun t ↦ K t x) = fun _ ↦ (0 : G) := funext h0
  rw [this]
  exact hasDerivAt_const s 0

theorem paramDeriv_eq_zero {K : ℝ → E n → G} {M : Set (E n)}
    (hK : Differentiable ℝ (uncurry K)) (hKM : ∀ s, ∀ x ∉ M, K s x = 0) (s : ℝ) {x : E n}
    (hx : x ∉ M) : paramDeriv K s x = 0 :=
  paramDeriv_eq_zero_of_forall (hK _) fun t ↦ hKM t x hx

end ParamDeriv

/-! ### Mixed partial derivatives -/

/-- **Symmetry of mixed partials for the divergence.** If `(s, x) ↦ V_s(x)` is `C²` near
`(s, x)`, then `∂_s div V_s(x) = div (∂_s V)_s(x)`. -/
theorem hasDerivAt_divergence_param {V : ℝ → E n → E n} {s : ℝ} {x : E n}
    (hV : ContDiffAt ℝ 2 (uncurry V) (s, x)) :
    HasDerivAt (fun t ↦ divergence (V t) x) (divergence (paramDeriv V s) x) s := by
  set Ψ := uncurry V with hΨ_def
  set p : ℝ × E n := (s, x)
  have hev : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 Ψ q := hV.eventually (by simp)
  have hd2 : HasFDerivAt (fderiv ℝ Ψ) (fderiv ℝ (fderiv ℝ Ψ) p) p :=
    ((hV.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero).hasFDerivAt
  have hsymm : IsSymmSndFDerivAt ℝ Ψ p := hV.isSymmSndFDerivAt (by simp)
  set L : E n →L[ℝ] ℝ × E n := (0 : E n →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (E n))
  have hL : ∀ v : E n, L v = (0, v) := fun v ↦ rfl
  -- `fderiv (V t) x = fderiv Ψ (t, x) ∘ L` for `t` near `s`
  have hcomp : ∀ t, DifferentiableAt ℝ Ψ (t, x) →
      fderiv ℝ (V t) x = (fderiv ℝ Ψ (t, x)).comp L := by
    intro t ht
    have h1 : HasFDerivAt (fun y : E n ↦ (t, y)) L x :=
      (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
    exact (ht.hasFDerivAt.comp x h1).fderiv
  have hevt : ∀ᶠ t in 𝓝 s, DifferentiableAt ℝ Ψ (t, x) := by
    have hc : Tendsto (fun t : ℝ ↦ (t, x)) (𝓝 s) (𝓝 p) :=
      (continuous_id.prodMk continuous_const).continuousAt
    filter_upwards [hc.eventually hev] with t ht
    exact ht.differentiableAt (by norm_num)
  -- derivative of `t ↦ fderiv Ψ (t, x)`
  have h2 : HasDerivAt (fun t ↦ fderiv ℝ Ψ (t, x)) (fderiv ℝ (fderiv ℝ Ψ) p (1, 0)) s := by
    have h1 : HasDerivAt (fun t : ℝ ↦ (t, x)) ((1 : ℝ), (0 : E n)) s :=
      (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
    exact hd2.comp_hasDerivAt s h1
  set P : (ℝ × E n →L[ℝ] E n) →L[ℝ] (E n →L[ℝ] E n) :=
    (ContinuousLinearMap.compL ℝ (E n) (ℝ × E n) (E n)).flip L
  have h3 : HasDerivAt (fun t ↦ traceCLM (P (fderiv ℝ Ψ (t, x))))
      (traceCLM (P (fderiv ℝ (fderiv ℝ Ψ) p (1, 0)))) s :=
    (traceCLM.comp P).hasFDerivAt.comp_hasDerivAt s h2
  have h4 : traceCLM (P (fderiv ℝ (fderiv ℝ Ψ) p (1, 0))) =
      divergence (paramDeriv V s) x := by
    rw [divergence_eq_traceCLM]
    congr 1
    have h5 : HasFDerivAt (fun q ↦ fderiv ℝ Ψ q ((1 : ℝ), (0 : E n)))
        ((fderiv ℝ Ψ p).comp (0 : ℝ × E n →L[ℝ] ℝ × E n) +
          (fderiv ℝ (fderiv ℝ Ψ) p).flip ((1 : ℝ), (0 : E n))) p :=
      hd2.clm_apply (hasFDerivAt_const _ p)
    have h6 : HasFDerivAt (fun y : E n ↦ (s, y)) L x :=
      (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x)
    have h7 : fderiv ℝ (paramDeriv V s) x =
        ((fderiv ℝ Ψ p).comp (0 : ℝ × E n →L[ℝ] ℝ × E n) +
          (fderiv ℝ (fderiv ℝ Ψ) p).flip ((1 : ℝ), (0 : E n))).comp L :=
      (h5.comp x h6).fderiv
    rw [h7]
    ext1 v
    have h0 : (fderiv ℝ Ψ p) ((0 : ℝ × E n →L[ℝ] ℝ × E n) (L v)) = 0 := by simp
    simp only [P, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, FunLike.coe_add, Pi.add_apply, h0, zero_add]
    exact hsymm _ _
  refine h3.congr_of_eventuallyEq ?_ |>.congr_deriv h4
  filter_upwards [hevt] with t ht
  rw [divergence_eq_traceCLM, hcomp t ht]
  rfl

/-! ### Smoothness of the Hadamard field and of the rate density -/

section Smooth

variable {F φ χ : E n → ℝ} {K : ℝ → E n → ℝ} {M : Set (E n)}

theorem contDiff_gradient_of_contDiff {G : E n → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (∇ G) :=
  (toDual ℝ (E n)).symm.contDiff.comp (hG.fderiv_right infty_add_one_le)

theorem contDiff_gradParam_infty (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) :
    ContDiff ℝ ∞ fun p : ℝ × E n ↦ gradParam F φ p.1 p.2 :=
  ((contDiff_gradient_of_contDiff hF).comp contDiff_snd).add
    (contDiff_fst.smul ((contDiff_gradient_of_contDiff hφ).comp contDiff_snd))

/-- The Hadamard field is jointly smooth for `|s| < s₀` when `N_s ≠ 0` on the support of the
cut-off. -/
theorem contDiffOn_hadamardField (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ)
    (hK : ContDiff ℝ ∞ (uncurry K)) (hχ : ContDiff ℝ ∞ χ) {s₀ : ℝ}
    (hN : ∀ s ∈ Icc (-s₀) s₀, ∀ x ∈ tsupport χ, gradParam F φ s x ≠ 0) :
    ContDiffOn ℝ ∞ (uncurry (hadamardField F φ K χ)) (Ioo (-s₀) s₀ ×ˢ univ) := by
  intro p hp
  refine ContDiffAt.contDiffWithinAt ?_
  have hNc := contDiff_gradParam_infty hF hφ
  by_cases hx : p.2 ∈ tsupport χ
  · have hNp : gradParam F φ p.1 p.2 ≠ 0 := hN p.1 (Ioo_subset_Icc_self hp.1) p.2 hx
    have hnum : ContDiffAt ℝ ∞ (fun p : ℝ × E n ↦ K p.1 p.2 * φ p.2) p :=
      hK.contDiffAt.mul (hφ.comp contDiff_snd).contDiffAt
    have hden : ContDiffAt ℝ ∞ (fun p : ℝ × E n ↦ ‖gradParam F φ p.1 p.2‖ ^ 2) p :=
      ((contDiff_norm_sq ℝ).comp hNc).contDiffAt
    have hg := (hnum.div hden (pow_ne_zero 2 (norm_ne_zero_iff.2 hNp))).smul hNc.contDiffAt
    exact (hχ.comp contDiff_snd).contDiffAt.smul hg
  · refine (contDiffAt_const (c := (0 : E n))).congr_of_eventuallyEq ?_
    have h0 := notMem_tsupport_iff_eventuallyEq.1 hx
    filter_upwards [continuous_snd.continuousAt.tendsto.eventually h0] with q hq
    change hadamardField F φ K χ q.1 q.2 = 0
    simp only [Pi.zero_apply] at hq
    simp [hadamardField, hq]

theorem hadamardField_eq_zero (hKM : ∀ s, ∀ x ∉ M, K s x = 0) (s : ℝ) {x : E n}
    (hx : x ∉ M) : hadamardField F φ K χ s x = 0 := by
  simp [hadamardField, hKM s x hx]

theorem tsupport_hadamardField_subset (hM : IsClosed M) (hKM : ∀ s, ∀ x ∉ M, K s x = 0)
    (s : ℝ) : tsupport (hadamardField F φ K χ s) ⊆ M :=
  closure_minimal (fun _x hx ↦ by_contra fun h ↦ hx (hadamardField_eq_zero hKM s h)) hM

/-- The density `L_s = ∂_s K_s - div V_s` whose superlevel integral is the Hadamard rate. -/
def rateDensity (F φ : E n → ℝ) (K : ℝ → E n → ℝ) (χ : E n → ℝ) (s : ℝ) (x : E n) : ℝ :=
  paramDeriv K s x - divergence (hadamardField F φ K χ s) x

theorem contDiffOn_rateDensity (hK : ContDiff ℝ ∞ (uncurry K)) {s₀ : ℝ}
    (hV : ContDiffOn ℝ ∞ (uncurry (hadamardField F φ K χ)) (Ioo (-s₀) s₀ ×ˢ univ)) :
    ContDiffOn ℝ ∞ (uncurry (rateDensity F φ K χ)) (Ioo (-s₀) s₀ ×ˢ univ) := by
  have hO : IsOpen (Ioo (-s₀) s₀ ×ˢ (univ : Set (E n))) := isOpen_Ioo.prod isOpen_univ
  refine (contDiff_paramDeriv hK).contDiffOn.sub fun p hp ↦ ContDiffAt.contDiffWithinAt ?_
  have hc : ContDiff ℝ ∞ fun r : (ℝ × E n) × E n ↦ (r.1.1, r.2) :=
    (contDiff_fst.comp contDiff_fst).prodMk contDiff_snd
  have h0 : ContDiffAt ℝ ∞ (uncurry (hadamardField F φ K χ) ∘
      fun r : (ℝ × E n) × E n ↦ (r.1.1, r.2)) (p, p.2) :=
    ContDiffAt.comp (p, p.2) (hV.contDiffAt (hO.mem_nhds hp)) hc.contDiffAt
  have h1 : ContDiffAt ℝ ∞ (uncurry fun (q : ℝ × E n) (y : E n) ↦ hadamardField F φ K χ q.1 y)
      (p, p.2) := h0
  have h2 := h1.fderiv (g := Prod.snd) contDiff_snd.contDiffAt infty_add_one_le
  exact traceCLM.contDiff.contDiffAt.comp p h2

theorem rateDensity_eq_zero (hK : ContDiff ℝ 1 (uncurry K)) (hM : IsClosed M)
    (hKM : ∀ s, ∀ x ∉ M, K s x = 0) (s : ℝ) {x : E n} (hx : x ∉ M) :
    rateDensity F φ K χ s x = 0 := by
  rw [rateDensity, paramDeriv_eq_zero (hK.differentiable one_ne_zero) hKM s hx,
    divergence_of_notMem_tsupport fun h ↦ hx (tsupport_hadamardField_subset hM hKM s h),
    sub_zero]

end Smooth

/-! ### Smooth clamping of the parameter -/

/-- A smooth map `σ : ℝ → (-a, a)` equal to the identity on `[-a/2, a/2]`. -/
theorem exists_smooth_clamp {a : ℝ} (ha : 0 < a) :
    ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ (∀ s, σ s ∈ Ioo (-a) a) ∧
      ∀ s ∈ Icc (-(a / 2)) (a / 2), σ s = s := by
  obtain ⟨ψ, hψ, -, hψU, hψ01, hψ1⟩ := exists_smooth_cutoff
    (isCompact_Icc (a := -(a / 2)) (b := a / 2)) isOpen_Ioo
    (Icc_subset_Ioo (by linarith) (by linarith) : Icc (-(a / 2)) (a / 2) ⊆ Ioo (-a) a)
  refine ⟨fun s ↦ ψ s * s, hψ.mul contDiff_id, fun s ↦ ?_, fun s hs ↦ by simp [hψ1 s hs]⟩
  by_cases h : ψ s = 0
  · simp only [h, zero_mul, mem_Ioo]
    constructor <;> linarith
  · have hs : s ∈ Ioo (-a) a := hψU (subset_tsupport _ h)
    have h1 : |ψ s * s| < a := by
      rw [abs_mul, abs_of_nonneg (hψ01 s).1]
      calc ψ s * |s| ≤ 1 * |s| := mul_le_mul_of_nonneg_right (hψ01 s).2 (abs_nonneg _)
        _ < a := by rw [one_mul]; exact abs_lt.2 hs
    exact abs_lt.1 h1

/-- Clamping a density that is smooth on `(-a, a) × E` gives a globally smooth density. -/
theorem contDiff_clamp {L : ℝ → E n → ℝ} {a : ℝ} {σ : ℝ → ℝ}
    (hL : ContDiffOn ℝ ∞ (uncurry L) (Ioo (-a) a ×ˢ univ)) (hσ : ContDiff ℝ ∞ σ)
    (hσa : ∀ s, σ s ∈ Ioo (-a) a) :
    ContDiff ℝ ∞ (uncurry fun s x ↦ L (σ s) x) :=
  hL.comp_contDiff ((hσ.comp contDiff_fst).prodMk contDiff_snd) fun p ↦ ⟨hσa p.1, mem_univ _⟩

/-! ### The Hadamard rate as a superlevel integral -/

theorem hadamardRate_eq_superlevelIntegral {F φ : E n → ℝ} {K K' L : ℝ → E n → ℝ}
    {V : ℝ → E n → E n} {M : Set (E n)} {a b δ : ℝ} (h : HadamardHyp F φ K K' V M a b δ)
    {s : ℝ} (hs : s ∈ Icc a b) (hL : ∀ x, L s x = K' s x - divergence (V s) x) :
    hadamardRate F φ K' V s = superlevelIntegral F φ L s := by
  have hK'M := deriv_eq_zero_of_notMem h.hasDerivAt_K h.K_eq_zero
  have hi1 : Integrable (K' s) :=
    integrable_of_eq_zero_off (h.continuous_K'.comp (continuous_const.prodMk continuous_id))
      h.isCompact fun x hx ↦ hK'M s hx
  have hi2 := integrable_divergence (h.contDiff_V s hs)
    (h.isCompact.of_isClosed_subset (isClosed_tsupport _) (h.tsupport_V s hs))
  simp only [hadamardRate, superlevelIntegral, fluxFunctional, hL]
  rw [integral_sub hi1.integrableOn hi2.integrableOn]
  ring

/-! ### A second-derivative test -/

/-- If `f` has a local minimum at `0`, `f' = g` near `0`, and `g` is differentiable at `0`
with derivative `c`, then `c ≥ 0`. -/
theorem nonneg_of_isLocalMin_of_hasDerivAt {f g : ℝ → ℝ} {c : ℝ} (hmin : IsLocalMin f 0)
    (hf : ∀ᶠ s in 𝓝 0, HasDerivAt f (g s) s) (hg : HasDerivAt g c 0) : 0 ≤ c := by
  have hg0 : g 0 = 0 := hmin.hasDerivAt_eq_zero hf.self_of_nhds
  by_contra hc
  push Not at hc
  have hsl := hg.tendsto_slope_zero_right
  have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (g (0 + t) - g 0) < 0 :=
    hsl.eventually (gt_mem_nhds hc)
  have hP : ∀ᶠ t in 𝓝[>] (0 : ℝ), (0 < t → g t < 0) ∧ HasDerivAt f (g t) t ∧ f 0 ≤ f t := by
    filter_upwards [hneg, nhdsWithin_le_nhds hf, nhdsWithin_le_nhds hmin] with t h1 h2 h3
    refine ⟨fun ht ↦ ?_, h2, h3⟩
    rw [zero_add, hg0, sub_zero, smul_eq_mul] at h1
    by_contra hge
    push Not at hge
    exact (not_lt.2 (mul_nonneg (inv_nonneg.2 ht.le) hge)) h1
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hP
  have hu0 : (0 : ℝ) < u := hu
  set t := u / 2
  have ht : 0 < t := half_pos hu0
  have htu : t < u := half_lt_self hu0
  have hcont : ContinuousOn f (Icc 0 t) := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h]; exact hf.self_of_nhds.continuousAt.continuousWithinAt
    · exact (hsub ⟨h, hy.2.trans_lt htu⟩).2.1.continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope f g ht hcont
    fun y hy ↦ (hsub ⟨hy.1, hy.2.trans htu⟩).2.1
  have h1 : g ξ < 0 := (hsub ⟨hξ.1, hξ.2.trans htu⟩).1 hξ.1
  have h2 : f 0 ≤ f t := (hsub ⟨ht, htu⟩).2.2
  rw [hξeq, sub_zero] at h1
  exact absurd h1 (not_lt.2 (div_nonneg (sub_nonneg.2 h2) ht.le))

/-! ### The second variation -/

section SecondVariation

variable {F φ : E n → ℝ} {M : Set (E n)}

theorem one_le_infty : (1 : ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.2 le_top

/-- One Hadamard step: the hypotheses of the Hadamard formula for a smooth density family `K`,
and a globally smooth density `L` equal to the rate density `∂_s K_s - div V_s` for small `|s|`. -/
theorem exists_hadamardStep (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (hM : IsCompact M)
    (hreg : ∀ x ∈ M, F x = 0 → ∇ F x ≠ 0) {K : ℝ → E n → ℝ} (hK : ContDiff ℝ ∞ (uncurry K))
    (hKM : ∀ s, ∀ x ∉ M, K s x = 0) :
    ∃ (χ : E n → ℝ) (s₀ δ : ℝ), 0 < s₀ ∧ ContDiff ℝ ∞ χ ∧
      HadamardHyp F φ K (paramDeriv K) (hadamardField F φ K χ) M (-s₀) s₀ δ ∧
      (∀ x ∈ M, |F x| < δ → χ x = 1) ∧
      ContDiffOn ℝ ∞ (uncurry (hadamardField F φ K χ)) (Ioo (-s₀) s₀ ×ˢ univ) ∧
      ∃ L : ℝ → E n → ℝ, ContDiff ℝ ∞ (uncurry L) ∧ (∀ s, ∀ x ∉ M, L s x = 0) ∧
        ∀ s ∈ Icc (-(s₀ / 2)) (s₀ / 2), ∀ x, L s x = rateDensity F φ K χ s x := by
  have hK1 : ContDiff ℝ 1 (uncurry K) := hK.of_le one_le_infty
  obtain ⟨χ, s₀, δ, hs₀, hχ, hyp, hN, hstrip⟩ := exists_hadamardHyp
    (hF.of_le ConeData.two_le_infty) (hφ.of_le ConeData.two_le_infty) hK1
    (continuous_paramDeriv hK1)
    (fun s x ↦ hasDerivAt_paramDeriv ((hK1.differentiable one_ne_zero) _)) hM hKM hreg
  have hV := contDiffOn_hadamardField hF hφ hK hχ hN
  obtain ⟨σ, hσ, hσa, hσid⟩ := exists_smooth_clamp hs₀
  refine ⟨χ, s₀, δ, hs₀, hχ, hyp,
    fun x hx h ↦ hstrip 0 ⟨by linarith, hs₀.le⟩ x hx (by simpa using h), hV,
    fun s x ↦ rateDensity F φ K χ (σ s) x, contDiff_clamp (contDiffOn_rateDensity hK hV) hσ hσa,
    fun s x hx ↦ rateDensity_eq_zero hK1 hM.isClosed hKM _ hx,
    fun s hs x ↦ by simp only [hσid s hs]⟩

/-- **Nonnegativity of the second variation.** If `Λ(s) = ∫_{F_s > 0} K_s` has a local minimum
at `s = 0`, then `Λ''(0) ≥ 0`, where `Λ''(0)` is the Hadamard rate at `0` of the rate density
`L_s = ∂_s K_s - div V_s` (with a second Hadamard field built from `L`). The data needed to
evaluate both rates at `0` are returned. -/
theorem nonneg_secondVariation (hF : ContDiff ℝ ∞ F) (hφ : ContDiff ℝ ∞ φ) (hM : IsCompact M)
    (hreg : ∀ x ∈ M, F x = 0 → ∇ F x ≠ 0) {K : ℝ → E n → ℝ} (hK : ContDiff ℝ ∞ (uncurry K))
    (hKM : ∀ s, ∀ x ∉ M, K s x = 0) (hmin : IsLocalMin (superlevelIntegral F φ K) 0) :
    ∃ (χ₁ χ₂ : E n → ℝ) (L : ℝ → E n → ℝ) (s₀ δ₁ δ₂ : ℝ), 0 < s₀ ∧ 0 < δ₁ ∧ 0 < δ₂ ∧
      ContDiff ℝ ∞ χ₁ ∧ ContDiff ℝ ∞ (uncurry L) ∧ (∀ s, ∀ x ∉ M, L s x = 0) ∧
      (∀ x ∈ M, |F x| < δ₁ → χ₁ x = 1) ∧ (∀ x ∈ M, |F x| < δ₂ → χ₂ x = 1) ∧
      (∀ s ∈ Ioo (-s₀) s₀, ∀ x, L s x = rateDensity F φ K χ₁ s x) ∧
      ContDiffOn ℝ ∞ (uncurry (hadamardField F φ K χ₁)) (Ioo (-s₀) s₀ ×ˢ univ) ∧
      ContDiff ℝ 1 (hadamardField F φ L χ₂ 0) ∧
      0 ≤ hadamardRate F φ (paramDeriv L) (hadamardField F φ L χ₂) 0 := by
  obtain ⟨χ₁, s₁, δ₁, hs₁, hχ₁, hyp1, hχ₁1, hV1, L, hL, hLM, hLeq⟩ :=
    exists_hadamardStep hF hφ hM hreg hK hKM
  obtain ⟨χ₂, s₂, δ₂, hs₂, -, hyp2, hχ₂1, -, L₂, hL₂, hL₂M, hL₂eq⟩ :=
    exists_hadamardStep hF hφ hM hreg hL hLM
  obtain ⟨χ₃, s₃, δ₃, hs₃, -, hyp3, -⟩ := exists_hadamardStep hF hφ hM hreg hL₂ hL₂M
  set R := hadamardRate F φ (paramDeriv K) (hadamardField F φ K χ₁) with hR_def
  set R₂ := hadamardRate F φ (paramDeriv L) (hadamardField F φ L χ₂) with hR₂_def
  have hR : ∀ s ∈ Icc (-(s₁ / 2)) (s₁ / 2), R s = superlevelIntegral F φ L s := fun s hs ↦
    hadamardRate_eq_superlevelIntegral hyp1 ⟨by linarith [hs.1], by linarith [hs.2]⟩
      (hLeq s hs)
  have hR₂ : ∀ s ∈ Icc (-(s₂ / 2)) (s₂ / 2), R₂ s = superlevelIntegral F φ L₂ s := fun s hs ↦
    hadamardRate_eq_superlevelIntegral hyp2 ⟨by linarith [hs.1], by linarith [hs.2]⟩
      (hL₂eq s hs)
  have hRev : ∀ s ∈ Ioo (-(s₁ / 2)) (s₁ / 2), R =ᶠ[𝓝 s] superlevelIntegral F φ L := by
    intro s hs
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with t ht
    exact hR t (Ioo_subset_Icc_self ht)
  -- continuity of `R₂` at `0`
  have hc3 : ContinuousAt (superlevelIntegral F φ L₂) 0 :=
    (HadamardHyp.continuousOn hyp3).continuousAt (Icc_mem_nhds (by linarith) hs₃)
  have hc2 : ContinuousAt R₂ 0 := by
    refine hc3.congr ?_
    filter_upwards [Icc_mem_nhds (by linarith : -(s₂ / 2) < 0) (by linarith : (0 : ℝ) < s₂ / 2)]
      with t ht
    exact (hR₂ t ht).symm
  -- `R'(0) = R₂(0)`
  have hd2 : HasDerivAt R (R₂ 0) 0 :=
    (hyp2.hasDerivAt ⟨by linarith, hs₂⟩ hc2).congr_of_eventuallyEq
      (hRev 0 ⟨by linarith, by linarith⟩)
  -- `Λ' = R` near `0`
  have hd1 : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt (superlevelIntegral F φ K) (R s) s := by
    have hr : 0 < min (s₁ / 2) s₂ := lt_min (by linarith) hs₂
    filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hr) hr] with s hs
    have hs1 : s ∈ Ioo (-(s₁ / 2)) (s₁ / 2) :=
      ⟨by linarith [hs.1, min_le_left (s₁ / 2) s₂], by linarith [hs.2, min_le_left (s₁ / 2) s₂]⟩
    have hs2 : s ∈ Ioo (-s₂) s₂ :=
      ⟨by linarith [hs.1, min_le_right (s₁ / 2) s₂], by linarith [hs.2, min_le_right (s₁ / 2) s₂]⟩
    have hcL : ContinuousAt (superlevelIntegral F φ L) s :=
      (HadamardHyp.continuousOn hyp2).continuousAt (Icc_mem_nhds hs2.1 hs2.2)
    exact hyp1.hasDerivAt ⟨by linarith [hs1.1], by linarith [hs1.2]⟩
      (hcL.congr (hRev s hs1).symm)
  refine ⟨χ₁, χ₂, L, s₁ / 2, δ₁, δ₂, by linarith, hyp1.pos, hyp2.pos, hχ₁, hL, hLM, hχ₁1, hχ₂1,
    fun s hs ↦ hLeq s (Ioo_subset_Icc_self hs), hV1.mono (prod_mono (Ioo_subset_Ioo
      (by linarith) (by linarith)) subset_rfl), hyp2.contDiff_V 0 ⟨by linarith, hs₂.le⟩,
    nonneg_of_isLocalMin_of_hasDerivAt hmin hd1 hd2⟩

end SecondVariation

end OnePhaseDimension
