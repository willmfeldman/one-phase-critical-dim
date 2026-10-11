/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Sanity.Textbook.Encoding
public import EllipticBernoulli.Sobolev.L2Inner
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Zero extension of `H¹₀` functions on a ball

If `f ∈ H¹₀(B)` on a ball `B` with weak gradient `g`, then the zero extension of `f` has the zero
extension of `g` as a weak gradient on all of `ℝᵈ` (`hasWeakGradient_univ_indicator_of_h10`).

Proof: for a test function `ψ` on `ℝᵈ` and `φ ∈ C_c^∞(B)`, integration by parts on `ℝᵈ` gives
`∫_B φ ∂ᵢψ = -∫_B ∂ᵢφ ψ`. Hence
`∫_B f ∂ᵢψ + ∫_B gᵢ ψ = ∫_B (f - φ) ∂ᵢψ + ∫_B (gᵢ - ∂ᵢφ) ψ`,
which the Cauchy–Schwarz inequality bounds by a multiple of the `H¹(B)` distance from `(f, g)`
to `(φ, ∇φ)`. That distance can be made arbitrarily small.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension.Textbook

open EllipticBernoulli

variable {d : ℕ}

/-- A real number bounded by every positive multiple of a fixed constant vanishes. -/
theorem eq_zero_of_forall_abs_le_mul {a K : ℝ} (hK : 0 ≤ K) (h : ∀ ε : ℝ, 0 < ε → |a| ≤ ε * K) :
    a = 0 := by
  by_contra ha
  have hpos : 0 < |a| := abs_pos.2 ha
  have h1 := h (|a| / (2 * (K + 1))) (by positivity)
  have h2 : |a| / (2 * (K + 1)) * K < |a| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- Integration by parts on `ℝᵈ` for two smooth functions with compact support, written on a set
`B` containing the support of the first. -/
theorem setIntegral_mul_partialDeriv_eq_neg {B : Set (E d)} {φ ψ : E d → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφB : tsupport φ ⊆ B)
    (hψ : ContDiff ℝ ∞ ψ) (i : Fin d) :
    ∫ x in B, φ x * partialDeriv i ψ x = -∫ x in B, partialDeriv i φ x * ψ x := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := φ) (g := ψ) (v := EuclideanSpace.single i 1)
    (((continuous_partialDeriv hφ i).mul hψ.continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_partialDeriv hφc i).mul_right))
    ((hφ.continuous.mul (continuous_partialDeriv hψ i)).integrable_of_hasCompactSupport
      hφc.mul_right)
    ((hφ.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hφc.mul_right)
    (fun x _ ↦ hφd x) (fun x _ ↦ hψd x)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφB h)), zero_mul],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [partialDeriv_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφB h)), zero_mul]]
  exact h

theorem memLp_restrict_of_contDiff {B : Set (E d)} {ψ : E d → ℝ} (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) : MemLp ψ 2 (volume.restrict B) :=
  (hψ.memLp_of_hasCompactSupport hψc).restrict B

/-- The `H¹₀` identity against a test function on `ℝᵈ`: `∫_B f ∂ᵢψ = -∫_B gᵢ ψ`. -/
theorem setIntegral_mul_partialDeriv_of_h10 {c : E d} {r : ℝ} {f : E d → ℝ} {g : E d → E d}
    (h : H10 (ball c r) f g) {ψ : E d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (i : Fin d) :
    ∫ x in ball c r, f x * partialDeriv i ψ x = -∫ x in ball c r, g x i * ψ x := by
  set B := ball c r
  obtain ⟨⟨hf, hg, -⟩, happrox⟩ := h
  have hgi : MemLp (fun x ↦ g x i) 2 (volume.restrict B) :=
    (EuclideanSpace.proj i : E d →L[ℝ] ℝ).comp_memLp' hg
  have hψ2 := memLp_restrict_of_contDiff (B := B) hψ.continuous hψc
  have hdψ2 := memLp_restrict_of_contDiff (B := B) (continuous_partialDeriv hψ i)
    (hasCompactSupport_partialDeriv hψc i)
  set K := (eLpNorm (partialDeriv i ψ) 2 (volume.restrict B)).toReal +
    (eLpNorm ψ 2 (volume.restrict B)).toReal
  have hK : 0 ≤ K := by positivity
  rw [← sub_eq_zero, sub_neg_eq_add]
  refine eq_zero_of_forall_abs_le_mul hK fun ε hε ↦ ?_
  obtain ⟨φ, hφ, hφc, hφB, hφf, hφg⟩ := happrox ε hε
  have hφ2 := memLp_restrict_of_contDiff (B := B) hφ.continuous hφc
  have hdφ2 := memLp_restrict_of_contDiff (B := B) (continuous_partialDeriv hφ i)
    (hasCompactSupport_partialDeriv hφc i)
  have hibp := setIntegral_mul_partialDeriv_eq_neg hφ hφc hφB hψ i
  have e : (∫ x in B, f x * partialDeriv i ψ x) + ∫ x in B, g x i * ψ x =
      (∫ x in B, (f x - φ x) * partialDeriv i ψ x) +
        ∫ x in B, (g x i - partialDeriv i φ x) * ψ x := by
    have i1 : Integrable (fun x ↦ f x * partialDeriv i ψ x) (volume.restrict B) :=
      hf.integrable_mul hdψ2
    have i2 : Integrable (fun x ↦ φ x * partialDeriv i ψ x) (volume.restrict B) :=
      hφ2.integrable_mul hdψ2
    have i3 : Integrable (fun x ↦ g x i * ψ x) (volume.restrict B) := hgi.integrable_mul hψ2
    have i4 : Integrable (fun x ↦ partialDeriv i φ x * ψ x) (volume.restrict B) :=
      hdφ2.integrable_mul hψ2
    simp only [sub_mul]
    rw [integral_sub i1 i2, integral_sub i3 i4, hibp]
    ring
  rw [e]
  have h1 := abs_integral_mul_le_L2 (hf.sub hφ2) hdψ2
  have h2 := abs_integral_mul_le_L2 (hgi.sub hdφ2) hψ2
  have h1' : (eLpNorm (fun x ↦ f x - φ x) 2 (volume.restrict B)).toReal ≤ ε :=
    ENNReal.toReal_le_of_le_ofReal hε.le hφf.le
  have h2' : (eLpNorm (fun x ↦ g x i - partialDeriv i φ x) 2 (volume.restrict B)).toReal ≤ ε :=
    ENNReal.toReal_le_of_le_ofReal hε.le (hφg i).le
  have n1 : 0 ≤ (eLpNorm (partialDeriv i ψ) 2 (volume.restrict B)).toReal := ENNReal.toReal_nonneg
  have n2 : 0 ≤ (eLpNorm ψ 2 (volume.restrict B)).toReal := ENNReal.toReal_nonneg
  calc |(∫ x in B, (f x - φ x) * partialDeriv i ψ x) +
        ∫ x in B, (g x i - partialDeriv i φ x) * ψ x|
      ≤ |∫ x in B, (f x - φ x) * partialDeriv i ψ x| +
        |∫ x in B, (g x i - partialDeriv i φ x) * ψ x| := abs_add_le _ _
    _ ≤ ε * (eLpNorm (partialDeriv i ψ) 2 (volume.restrict B)).toReal +
        ε * (eLpNorm ψ 2 (volume.restrict B)).toReal := by
        refine add_le_add (h1.trans ?_) (h2.trans ?_)
        · exact mul_le_mul_of_nonneg_right h1' n1
        · exact mul_le_mul_of_nonneg_right h2' n2
    _ = ε * K := by ring

/-- **Zero extension.** If `f ∈ H¹₀(B)` on a ball `B` with weak gradient `g`, then the zero
extension of `g` is a weak gradient of the zero extension of `f` on `ℝᵈ`. -/
theorem hasWeakGradient_univ_indicator_of_h10 {c : E d} {r : ℝ} {f : E d → ℝ}
    {g : E d → E d} (h : H10 (ball c r) f g) :
    HasWeakGradient univ ((ball c r).indicator f) ((ball c r).indicator g) := by
  have hfi : Integrable ((ball c r).indicator f) :=
    (integrableOn_of_memLp_ball h.1.1).integrable_indicator measurableSet_ball
  have hgi : Integrable ((ball c r).indicator g) :=
    (show IntegrableOn g (ball c r) volume from h.1.2.1.integrable one_le_two).integrable_indicator
      measurableSet_ball
  refine hasWeakGradient_of_weakGrad isOpen_univ (hfi.locallyIntegrable.locallyIntegrableOn _)
    (hgi.locallyIntegrable.locallyIntegrableOn _) fun i ψ hψ hψc _ ↦ ?_
  have e1 : (fun x ↦ (ball c r).indicator f x * partialDeriv i ψ x) =
      (ball c r).indicator (fun x ↦ f x * partialDeriv i ψ x) := by
    funext x; by_cases hx : x ∈ ball c r <;> simp [hx]
  have e2 : (fun x ↦ (ball c r).indicator g x i * ψ x) =
      (ball c r).indicator (fun x ↦ g x i * ψ x) := by
    funext x; by_cases hx : x ∈ ball c r <;> simp [hx]
  simp only [Measure.restrict_univ]
  rw [e1, e2, integral_indicator measurableSet_ball, integral_indicator measurableSet_ball]
  exact setIntegral_mul_partialDeriv_of_h10 h hψ hψc i

end OnePhaseDimension.Textbook
