/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Interface
public import OnePhaseDimension.Reduction.OneDim
public import OnePhaseDimension.Cutoff.WeightedBochner

/-!
# Flatness in dimension two

Every nonzero, nonnegative, one-homogeneous global minimizer of the one-phase energy in `ℝ²` is
flat.

The argument is the reduction to a cone with an isolated singularity, followed by a pointwise
contradiction. If `u` is not flat, then, since minimizers in `ℝ¹` are flat, `u` gives a cone
`C` in `ℝ²` with `C.Sing = {0}` and a point `x` of the selected component `D` with
`D²u(x) ≠ 0`. At `x̂ = x/|x|` the spherical Hessian `T_{ij} = D²u(x̂)[τᵢ, τⱼ]` is a symmetric,
trace-free `1 × 1` matrix, hence `T = 0`; but `w² = |T|²` equals `|D²u(x̂)|²`, which is positive
because `D²u(x) ≠ 0` and `D²u` is homogeneous of degree `-1`.

## Main statements

* `ConeData.false_of_two`: there is no cone in `ℝ²` with singular set `{0}`.
* `flatInDim_succ_of_exclusion`: if minimizers in `ℝᵏ` are flat and there is no cone in
  `ℝ^{k+1}` with singular set `{0}`, then minimizers in `ℝ^{k+1}` are flat.
* `flatInDim_two`: minimizers in `ℝ²` are flat.

## Differences from the source

* The 2026-09-24 version cites the classification of one-homogeneous minimizers in dimensions at
  most four. For dimension two we use the reduction of the source to a cone with an isolated
  singularity, together with the fact that a symmetric trace-free `1 × 1` matrix vanishes.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set MeasureTheory

@[expose] public section

namespace OnePhaseDimension

open EllipticBernoulli

/-- **No cone in `ℝ²`.** There is no cone `C` in `ℝ²` with singular set `{0}`: the Hessian of
a one-homogeneous harmonic function on a planar cone vanishes, since its spherical part is a
symmetric trace-free `1 × 1` matrix. -/
theorem ConeData.false_of_two (C : ConeData 2) (hS : C.Sing = {0}) : False := by
  obtain ⟨x, hxD, hx2⟩ := C.nonflat
  have hx0 := C.ne_zero_of_mem_D hxD
  set y := radialProj x
  have hyD : y ∈ C.D := C.radialProj_mem_D hxD
  have hy1 : ‖y‖ = 1 := norm_radialProj hx0
  -- `w² > 0` at `x`
  have hJx : 0 < jetNormSq (stdOrthonormalBasis ℝ (E 2)) 2 C.u x :=
    lt_of_le_of_ne (jetNormSq_nonneg _ _ _ _)
      fun h ↦ hx2 (iteratedFDeriv_two_eq_zero_of_jetNormSq_eq_zero _ h.symm)
  have hrel := C.jetNormSq_radialProj hS (stdOrthonormalBasis ℝ (E 2)) 2 hxD
  have hwx : 0 < C.wSq x := by
    have h4 : 0 < ‖x‖ ^ 2 * C.wSq x := by
      change 0 < ‖x‖ ^ 2 * jetNormSq (stdOrthonormalBasis ℝ (E 2)) 2 C.u (radialProj x)
      rw [← hrel]
      have : 0 < ‖x‖ := norm_pos_iff.2 hx0
      positivity
    exact pos_of_mul_pos_right h4 (by positivity)
  -- `w² = T₀₀² = 0` at `x̂`
  have hJ := C.isConeJet_of_mem_D hS hyD hy1
  have hT : (ConeJets.ofHarmonicHomogeneous C.u y hy1).T 0 0 = 0 := by
    simpa using hJ.T_trace
  have hw : C.wSq y = 0 := by
    have h := C.wSq_eq hJ
    change C.wSq y = _ at h
    rw [h]
    simp [hT]
  have hyx : C.wSq y = C.wSq x := by
    change C.wSq y = jetNormSq (stdOrthonormalBasis ℝ (E 2)) 2 C.u y
    exact C.wSq_of_norm_eq_one hy1
  linarith

/-- **Inductive step from the exclusion of cones.** Let `k ≥ 1`. If every nonzero, nonnegative,
one-homogeneous global minimizer in `ℝᵏ` is flat, and there is no cone in `ℝ^{k+1}` with
singular set `{0}`, then every nonzero, nonnegative, one-homogeneous global minimizer in
`ℝ^{k+1}` is flat. -/
theorem flatInDim_succ_of_exclusion {k : ℕ} (hk : 1 ≤ k) (hlow : FlatInDim k)
    (hexcl : ∀ C : ConeData (k + 1), C.Sing = {0} → False) : FlatInDim (k + 1) := by
  intro u hnn hmin hhom hne
  obtain ⟨v, hvu, -, hc, hnn', hhom', hmin', -, -, hpos⟩ :=
    exists_headline_representative (by omega) hnn hmin hhom hne
  by_cases hflat : FlatAE v
  · exact flatAE_congr hvu hflat
  · exact (hexcl (ConeData.ofFirstNonflat reductionInputs hk hlow v hc hnn' hmin' hhom' hpos
      hflat) rfl).elim

/-- **Flatness in dimension two.** Every nonzero, nonnegative, one-homogeneous global minimizer
of the one-phase energy in `ℝ²` is flat. -/
theorem flatInDim_two : FlatInDim 2 :=
  flatInDim_succ_of_exclusion (k := 1) le_rfl flatInDim_one ConeData.false_of_two

end OnePhaseDimension
