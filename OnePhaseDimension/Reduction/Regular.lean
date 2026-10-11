/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Bridges
public import OnePhaseDimension.Registry.Blowup
public import OnePhaseDimension.Registry.Chart
public import OnePhaseDimension.Statements.Cone
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# Regularity of a first nonflat cone away from the vertex

Let `u` be a continuous, nonnegative, one-homogeneous global minimizer in `ℝ^{k+1}`, and assume
that every nonzero, nonnegative, one-homogeneous global minimizer in `ℝ^k` is flat. Then every
blowup of `u` at a free boundary point `x₀ ≠ 0` is a half-space solution
(`exists_flat_blowup`), so the cited smooth chart applies at `x₀` (`exists_chart_of_freeBoundary`).
In the positive phase, `u` is smooth and harmonic (`contDiffOn_pos`, `laplacian_pos`).

The argument uses four inputs from the dimension reduction, recorded as propositions:

* `BlowupTranslationInvariance`: a blowup at `x₀` of a one-homogeneous minimizer is invariant
  under translations along `x₀`;
* `FactorMinimality`: if `v ∘ π` is a global minimizer in `ℝ^{k+1}`, where `π` drops the last
  coordinate, then `v` is a global minimizer in `ℝ^k`;
* `SuspensionMinimality`: conversely, if `v ≥ 0` is a global minimizer in `ℝ^k`, then so is
  `v ∘ π` in `ℝ^{k+1}`;
* `IsometryMinimality`: global minimality is invariant under linear isometries.

## Differences from the source

The 2026-09-24 version writes the blowup in orthogonal coordinates `ℝ^d = x₀^⊥ × ℝ`. We map
`x₀ / |x₀|` to the last basis vector by the reflection in the hyperplane orthogonal to
`x₀ / |x₀| - e_last`, and then drop the last coordinate.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient Laplacian RealInnerProductSpace

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### Dropping the last coordinate -/

section Coordinates

variable {k : ℕ}

/-- Drop the last coordinate, `ℝ^{k+1} → ℝ^k`. For `k = 5` this is `dropLast`. -/
def projInit (k : ℕ) : E (k + 1) →L[ℝ] E k :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin k → ℝ)).symm.toLinearMap ∘ₗ
      LinearMap.funLeft ℝ ℝ (Fin.castSucc : Fin k → Fin (k + 1)) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin (k + 1) → ℝ)).toLinearMap)

theorem projInit_five : projInit 5 = dropLast := rfl

@[simp] theorem projInit_apply (x : E (k + 1)) (i : Fin k) :
    projInit k x i = x (Fin.castSucc i) := rfl

/-- The last basis vector of `ℝ^{k+1}`. -/
def lastVec (k : ℕ) : E (k + 1) := EuclideanSpace.single (Fin.last k) 1

theorem norm_lastVec : ‖lastVec k‖ = 1 := by
  simp [lastVec]

theorem projInit_single_castSucc (i : Fin k) :
    projInit k (EuclideanSpace.single (Fin.castSucc i) (1 : ℝ)) = EuclideanSpace.single i 1 := by
  ext j
  simp [PiLp.single_apply]

theorem projInit_lastVec : projInit k (lastVec k) = 0 := by
  ext j
  simp only [projInit_apply, lastVec, PiLp.single_apply, PiLp.zero_apply]
  exact ite_eq_right (Fin.castSucc_ne_last j)

/-- The adjoint `π†` of `π = projInit k` is the embedding `v ↦ (v, 0)`. -/
theorem projInit_adjoint_apply (v : E k) : projInit k ((projInit k).adjoint v) = v := by
  ext i
  have h := (projInit k).adjoint_inner_left (EuclideanSpace.single (Fin.castSucc i) (1 : ℝ)) v
  rw [projInit_single_castSucc, EuclideanSpace.inner_single_right,
    EuclideanSpace.inner_single_right] at h
  simpa using h

theorem projInit_adjoint_apply_last (v : E k) : (projInit k).adjoint v (Fin.last k) = 0 := by
  have h := (projInit k).adjoint_inner_left (lastVec k) v
  rw [projInit_lastVec, inner_zero_right, lastVec, EuclideanSpace.inner_single_right] at h
  simpa using h

theorem norm_projInit_adjoint (v : E k) : ‖(projInit k).adjoint v‖ = ‖v‖ := by
  have h : ‖(projInit k).adjoint v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      ContinuousLinearMap.adjoint_inner_left, projInit_adjoint_apply]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- `x = π†(π x) + x_last e_last`. -/
theorem adjoint_projInit_add_smul_lastVec (x : E (k + 1)) :
    (projInit k).adjoint (projInit k x) + x (Fin.last k) • lastVec k = x := by
  ext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [projInit_adjoint_apply_last, lastVec]
  · have h := congrArg (fun y : E k ↦ y j) (projInit_adjoint_apply (projInit k x))
    simp only [projInit_apply] at h
    simp [h, lastVec, Fin.castSucc_ne_last]

end Coordinates

/-! ### Inputs from the dimension reduction -/

/-- Every nonzero, nonnegative, one-homogeneous global minimizer in `ℝᵏ` is flat (the hypotheses
of the headline statement in dimension `k`). -/
def FlatInDim (k : ℕ) : Prop :=
  ∀ v : E k → ℝ, (∀ᵐ x ∂(volume : Measure (E k)), 0 ≤ v x) →
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) v → OneHomogeneousAE v → ¬ v =ᵐ[volume] 0 →
      FlatAE v

/-- A blowup at a free boundary point `x₀` of a continuous, nonnegative, one-homogeneous global
minimizer is invariant under translations along `x₀`. -/
def BlowupTranslationInvariance : Prop :=
  ∀ ⦃n : ℕ⦄, 2 ≤ n → ∀ ⦃u : E n → ℝ⦄, Continuous u → (∀ x, 0 ≤ u x) →
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) u → (∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x) →
    ∀ ⦃x₀ : E n⦄, x₀ ∈ freeBoundary u univ → ∀ ⦃U₀ : E n → ℝ⦄, IsBlowupLimit u x₀ U₀ →
      ∀ (y : E n) (t : ℝ), U₀ (y + t • x₀) = U₀ y

/-- If `v` is continuous and nonnegative and `v ∘ π` is a global minimizer in `ℝ^{k+1}`, where
`π` drops the last coordinate, then `v` is a global minimizer in `ℝᵏ`. -/
def FactorMinimality : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃v : E k → ℝ⦄, Continuous v → (∀ x, 0 ≤ v x) →
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) (v ∘ projInit k) →
      IsLocalEnergyMinimizer univ (fun _ ↦ 1) v

/-- If `v ≥ 0` is a global minimizer in `ℝᵏ`, then its suspension `v ∘ π` is a global minimizer in
`ℝ^{k+1}`. -/
def SuspensionMinimality : Prop :=
  ∀ ⦃k : ℕ⦄ ⦃v : E k → ℝ⦄, (∀ x, 0 ≤ v x) → IsLocalEnergyMinimizer univ (fun _ ↦ 1) v →
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) (v ∘ projInit k)

/-- Global minimality is invariant under linear isometries. -/
def IsometryMinimality : Prop :=
  ∀ ⦃n : ℕ⦄ (L : E n ≃ₗᵢ[ℝ] E n) ⦃v : E n → ℝ⦄, IsLocalEnergyMinimizer univ (fun _ ↦ 1) v →
    IsLocalEnergyMinimizer univ (fun _ ↦ 1) (v ∘ L)

/-! ### Flatness of translation-invariant minimizers -/

/-- A continuous, nonnegative, nonzero, one-homogeneous global minimizer in `ℝ^{k+1}` that is
invariant along a direction `a ≠ 0` is flat, provided minimizers in `ℝᵏ` are. -/
theorem flat_of_translation_invariant (hiso : IsometryMinimality) (hfac : FactorMinimality)
    {k : ℕ} (hlow : FlatInDim k) {U : E (k + 1) → ℝ} (hc : Continuous U) (hnn : ∀ x, 0 ≤ U x)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, U (r • x) = r * U x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) U) (hpos : ∃ y, 0 < U y)
    {a : E (k + 1)} (ha : a ≠ 0) (hinv : ∀ (y : E (k + 1)) (t : ℝ), U (y + t • a) = U y) :
    ∃ e : E (k + 1), ‖e‖ = 1 ∧ ∀ x, U x = max ⟪x, e⟫ 0 := by
  set â : E (k + 1) := ‖a‖⁻¹ • a with hâdef
  have hâ : ‖â‖ = 1 := norm_smul_inv_norm ha
  set R := (ℝ ∙ (â - lastVec k))ᗮ.reflection with hRdef
  have hRa : R â = lastVec k := Submodule.reflection_sub (by rw [hâ, norm_lastVec])
  have hRl : R (lastVec k) = â := by rw [← hRa, Submodule.reflection_reflection]
  have hRR : ∀ y, R (R y) = y := fun y ↦ Submodule.reflection_reflection _ y
  set W : E (k + 1) → ℝ := U ∘ R with hWdef
  have hWinv : ∀ y (t : ℝ), W (y + t • lastVec k) = W y := by
    intro y t
    simp only [hWdef, Function.comp_apply, map_add, map_smul, hRl, hâdef, smul_smul]
    exact hinv _ _
  set v : E k → ℝ := W ∘ (projInit k).adjoint with hvdef
  have hWv : ∀ y, W y = v (projInit k y) := by
    intro y
    conv_lhs => rw [← adjoint_projInit_add_smul_lastVec y]
    exact hWinv _ _
  have hWeq : W = v ∘ projInit k := funext hWv
  have hvc : Continuous v := (hc.comp R.continuous).comp (projInit k).adjoint.continuous
  have hvmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) v :=
    hfac hvc (fun x ↦ hnn _) (hWeq ▸ hiso R hmin)
  have hvhom : ∀ r : ℝ, 0 < r → ∀ x, v (r • x) = r * v x := by
    intro r hr x
    simp only [hvdef, hWdef, Function.comp_apply, map_smul, hhom r hr]
  have hvne : ¬ v =ᵐ[volume] 0 := by
    intro h
    have h0 := congrFun ((Continuous.ae_eq_iff_eq volume hvc continuous_const).1 h)
      (projInit k (R hpos.choose))
    rw [← hWv] at h0
    simp only [hWdef, Function.comp_apply, hRR] at h0
    exact (ne_of_gt hpos.choose_spec) h0
  obtain ⟨e', he', hflat⟩ := flat_of_flatAE_of_continuous hvc
    (hlow v (Filter.Eventually.of_forall fun x ↦ hnn _) hvmin (oneHomogeneousAE_of_forall hvhom)
      hvne)
  refine ⟨R ((projInit k).adjoint e'), by rw [LinearIsometryEquiv.norm_map, norm_projInit_adjoint,
    he'], fun x ↦ ?_⟩
  have hx : U x = W (R x) := by simp only [hWdef, Function.comp_apply, hRR]
  rw [hx, hWv, hflat, ← ContinuousLinearMap.adjoint_inner_right,
    ← LinearIsometryEquiv.inner_map_map R x, hRR]

/-! ### Flat blowups at nonzero free boundary points -/

section Blowup

variable {k : ℕ} {u : E (k + 1) → ℝ}

/-- **Every blowup off the vertex is flat.** If minimizers in `ℝᵏ` are flat, then at a free
boundary point `x₀ ≠ 0` of a continuous, nonnegative, one-homogeneous global minimizer in
`ℝ^{k+1}`, `k ≥ 1`, some half-space solution is a blowup limit. -/
theorem exists_flat_blowup (htr : BlowupTranslationInvariance) (hiso : IsometryMinimality)
    (hfac : FactorMinimality) (hk : 1 ≤ k) (hlow : FlatInDim k) (hc : Continuous u)
    (hnn : ∀ x, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x) {x₀ : E (k + 1)}
    (hx₀ : x₀ ∈ freeBoundary u univ) (h0 : x₀ ≠ 0) :
    ∃ e : E (k + 1), ‖e‖ = 1 ∧ IsBlowupLimit u x₀ (fun y ↦ max ⟪y, e⟫ 0) := by
  have hd : 2 ≤ k + 1 := by omega
  set r : ℕ → ℝ := fun j ↦ 1 / ((j : ℝ) + 1) with hrdef
  have hr : ∀ j, 0 < r j := fun j ↦ Nat.one_div_pos_of_nat
  have hr₀ : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨φ, hφ, U₀, hconv, hU₀c, hU₀nn, hU₀min, hU₀pos, -⟩ :=
    Registry.exists_blowup_limit hd hc hnn hmin hx₀ hr hr₀
  have hbl : IsBlowupLimit u x₀ U₀ :=
    ⟨r ∘ φ, fun j ↦ hr _, hr₀.comp hφ.tendsto_atTop, hconv⟩
  have hU₀hom := Registry.blowup_limit_oneHomogeneous hd hc hnn hmin hx₀ hbl
  obtain ⟨e, he, hU₀⟩ := flat_of_translation_invariant hiso hfac hlow hU₀c hU₀nn hU₀hom hU₀min
    hU₀pos h0 (htr hd hc hnn hmin hhom hx₀ hbl)
  refine ⟨e, he, ?_⟩
  have hfun : U₀ = fun y ↦ max ⟪y, e⟫ 0 := funext hU₀
  exact hfun ▸ hbl

/-- **The chart at a nonzero free boundary point**: the cited smooth one-sided chart applies at
every free boundary point `x₀ ≠ 0`. -/
theorem exists_chart_of_freeBoundary (htr : BlowupTranslationInvariance)
    (hiso : IsometryMinimality) (hfac : FactorMinimality) (hk : 1 ≤ k) (hlow : FlatInDim k)
    (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u)
    (hhom : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x) {x₀ : E (k + 1)}
    (hx₀ : x₀ ∈ freeBoundary u univ) (h0 : x₀ ≠ 0) :
    ∃ ρ > 0, ∃ F : E (k + 1) → ℝ, ContDiffOn ℝ ∞ F (ball x₀ ρ) ∧
      (∀ x ∈ ball x₀ ρ, u x = max (F x) 0) ∧
      (∀ x ∈ ball x₀ ρ, ∇ F x ≠ 0) ∧
      (∀ x ∈ ball x₀ ρ, F x = 0 → ‖∇ F x‖ = 1) ∧
      (∀ x ∈ ball x₀ ρ, 0 < F x → Δ F x = 0) ∧
      IsPreconnected {x ∈ ball x₀ ρ | 0 < F x} := by
  obtain ⟨e, he, hbl⟩ := exists_flat_blowup htr hiso hfac hk hlow hc hnn hmin hhom hx₀ h0
  exact Registry.chart_of_flat_blowup (by omega) hc hnn hmin hx₀ he hbl

end Blowup

/-! ### The positive phase -/

section Positive

variable {n : ℕ} {u : E n → ℝ}

/-- A continuous, nonnegative global minimizer in `ℝⁿ`, `n ≥ 2`, is smooth and harmonic in its
positivity set. -/
theorem contDiffOn_pos_and_laplacian (hd : 2 ≤ n) (hc : Continuous u) (hnn : ∀ x, 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) :
    ContDiffOn ℝ ∞ u {x | 0 < u x} ∧ ∀ x, 0 < u x → Δ u x = 0 := by
  obtain ⟨v, hvu, -, hvc, -, hsmooth, hharm, -⟩ :=
    exists_continuous_minimizer_representative hd (Filter.Eventually.of_forall hnn) hmin
  obtain rfl : v = u := (Continuous.ae_eq_iff_eq volume hvc hc).1 hvu
  exact ⟨hsmooth, hharm⟩

end Positive

end OnePhaseDimension
