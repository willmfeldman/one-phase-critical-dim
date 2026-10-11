/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Sanity.Textbook.Defs
public import OnePhaseDimension.Basic
public import EllipticBernoulli.Sobolev.Uniqueness

/-!
# Encoding lemmas between the textbook and the project vocabulary

The textbook vocabulary of `OnePhaseDimension.Sanity.Textbook.Defs` and the Sobolev vocabulary
of `EllipticBernoulli` differ in a few encoding choices, each closed here by a short lemma.

* Coordinate partials versus all directions: `hasWeakGradient_of_weakGrad` and
  `weakGrad_of_hasWeakGradient_univ`, by linearity of the derivative.
* Balls versus compact sets: `h1_ball_of_memH1Loc` and `memH1Loc_univ_of_h1_ball`.
* The `ℝ≥0∞`-valued energy with the indicator of the positivity set versus the real energy with
  `if 0 < f x`: `energyJ_ball_eq_ofReal_J`, using that `|g|²` is integrable on a ball.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension.Textbook

open EllipticBernoulli

variable {d : ℕ}

/-! ### Coordinates -/

/-- A directional derivative is the combination of the partial derivatives. -/
theorem fderiv_apply_eq_sum (φ : E d → ℝ) (x v : E d) :
    fderiv ℝ φ x v = ∑ i, v i * partialDeriv i φ x := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp [partialDeriv, map_sum, map_smul]

theorem inner_eq_sum (z v : E d) : inner ℝ z v = ∑ i, z i * v i := by
  simp [PiLp.inner_apply, mul_comm]

theorem inner_single_one (z : E d) (i : Fin d) :
    inner ℝ z (EuclideanSpace.single i (1 : ℝ)) = z i := by
  simp [EuclideanSpace.inner_single_right]

theorem continuous_partialDeriv {φ : E d → ℝ} (hφ : ContDiff ℝ ∞ φ) (i : Fin d) :
    Continuous (partialDeriv i φ) :=
  (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem hasCompactSupport_partialDeriv {φ : E d → ℝ} (hφc : HasCompactSupport φ) (i : Fin d) :
    HasCompactSupport (partialDeriv i φ) :=
  hφc.fderiv_apply (𝕜 := ℝ) _

theorem tsupport_partialDeriv_subset (φ : E d → ℝ) (i : Fin d) :
    tsupport (partialDeriv i φ) ⊆ tsupport φ :=
  tsupport_fderiv_apply_subset ℝ _

theorem partialDeriv_eq_zero_of_notMem_tsupport {φ : E d → ℝ} {x : E d} (hx : x ∉ tsupport φ)
    (i : Fin d) : partialDeriv i φ x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_partialDeriv_subset φ i h)

theorem locallyIntegrableOn_apply {U : Set (E d)} {g : E d → E d}
    (hg : LocallyIntegrableOn g U) (i : Fin d) : LocallyIntegrableOn (fun x ↦ g x i) U := by
  simpa only [inner_single_one] using locallyIntegrableOn_inner_const hg (EuclideanSpace.single i 1)

/-- On an open set, a coordinate weak gradient of locally integrable functions is a weak gradient
in every direction. -/
theorem hasWeakGradient_of_weakGrad {U : Set (E d)} (hU : IsOpen U) {f : E d → ℝ}
    {g : E d → E d} (hf : LocallyIntegrableOn f U) (hg : LocallyIntegrableOn g U)
    (hw : WeakGrad U f g) : HasWeakGradient U f g := by
  refine ⟨hf, hg, fun φ hφ hφc hφU v ↦ ?_⟩
  have hi1 : ∀ i, IntegrableOn (fun x ↦ f x * partialDeriv i φ x) U := fun i ↦
    integrableOn_mul_of_tsupport_subset hU hf (continuous_partialDeriv hφ i)
      (hasCompactSupport_partialDeriv hφc i) ((tsupport_partialDeriv_subset φ i).trans hφU)
  have hi2 : ∀ i, IntegrableOn (fun x ↦ g x i * φ x) U := fun i ↦
    integrableOn_mul_of_tsupport_subset hU (locallyIntegrableOn_apply hg i) hφ.continuous hφc hφU
  calc ∫ x in U, f x * fderiv ℝ φ x v
      = ∫ x in U, ∑ i, v i * (f x * partialDeriv i φ x) := by
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [fderiv_apply_eq_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
    _ = ∑ i, v i * ∫ x in U, f x * partialDeriv i φ x := by
        rw [integral_finsetSum _ fun i _ ↦ (hi1 i).const_mul (v i)]
        simp only [integral_const_mul]
    _ = ∑ i, v i * -∫ x in U, g x i * φ x := by
        simp only [hw _ φ hφ hφc hφU]
    _ = -∫ x in U, ∑ i, v i * (g x i * φ x) := by
        rw [integral_finsetSum _ fun i _ ↦ (hi2 i).const_mul (v i)]
        simp only [integral_const_mul, Finset.sum_neg_distrib, mul_neg]
    _ = -∫ x in U, inner ℝ (g x) v * φ x := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
        simp only [inner_eq_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- The coordinate identities of a weak gradient. -/
theorem weakGrad_of_hasWeakGradient {U : Set (E d)} {f : E d → ℝ} {g : E d → E d}
    (hw : HasWeakGradient U f g) : WeakGrad U f g := by
  intro i φ hφ hφc hφU
  simpa only [partialDeriv, inner_single_one] using
    hw.2.2 φ hφ hφc hφU (EuclideanSpace.single i 1)

/-- A whole-space weak gradient restricts to a weak gradient on any measurable set `B`. -/
theorem weakGrad_of_hasWeakGradient_univ {B : Set (E d)} {f : E d → ℝ} {g : E d → E d}
    (hw : HasWeakGradient univ f g) : WeakGrad B f g := by
  intro i φ hφ hφc hφB
  have h := weakGrad_of_hasWeakGradient hw i φ hφ hφc (subset_univ _)
  simp only [Measure.restrict_univ] at h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [partialDeriv_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφB h)), mul_zero],
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφB h)), mul_zero]]
  exact h

/-! ### Balls and compact sets -/

instance isFiniteMeasure_restrict_ball (c : E d) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (ball c r)) :=
  isFiniteMeasure_restrict.2 measure_ball_lt_top.ne

theorem integrableOn_of_memLp_ball {f : E d → ℝ} {c : E d} {r : ℝ}
    (hf : MemLp f 2 (volume.restrict (ball c r))) : IntegrableOn f (ball c r) :=
  hf.integrable one_le_two

/-- An `H¹_loc(ℝᵈ)` function is in `H¹(B)` on every ball. -/
theorem h1_ball_of_memH1Loc {u : E d → ℝ} {G : E d → E d} (hu : MemH1Loc univ u G)
    (c : E d) (r : ℝ) : H1 (ball c r) u G := by
  obtain ⟨h1, h2⟩ := hu.2 (closedBall c r) (subset_univ _) (isCompact_closedBall c r)
  exact ⟨h1.mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl),
    h2.mono_measure (Measure.restrict_mono ball_subset_closedBall le_rfl),
    weakGrad_of_hasWeakGradient_univ hu.1⟩

/-- A function in `H¹(B)` on every ball, with a common weak gradient, is in `H¹_loc(ℝᵈ)`. -/
theorem memH1Loc_univ_of_h1_ball {u : E d → ℝ} {G : E d → E d}
    (hu : ∀ (c : E d) (r : ℝ), 0 < r → H1 (ball c r) u G) : MemH1Loc univ u G := by
  have hball : ∀ K : Set (E d), IsCompact K → ∃ R, 0 < R ∧ K ⊆ ball 0 R := by
    intro K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : E d)
    exact ⟨max R 1, by positivity, hR.trans (ball_subset_ball (le_max_left _ _))⟩
  have hloc : ∀ c : E d, ∀ r, 0 < r → LocallyIntegrableOn u (ball c r) ∧
      LocallyIntegrableOn G (ball c r) := fun c r hr ↦
    ⟨(integrableOn_of_memLp_ball (hu c r hr).1).locallyIntegrableOn,
      (show IntegrableOn G (ball c r) volume from
        (hu c r hr).2.1.integrable one_le_two).locallyIntegrableOn⟩
  have hLu : LocallyIntegrable u := fun x ↦
    ⟨ball x 1, ball_mem_nhds x one_pos, integrableOn_of_memLp_ball (hu x 1 one_pos).1⟩
  have hLG : LocallyIntegrable G := fun x ↦
    ⟨ball x 1, ball_mem_nhds x one_pos, (hu x 1 one_pos).2.1.integrable one_le_two⟩
  refine ⟨⟨hLu.locallyIntegrableOn _, hLG.locallyIntegrableOn _, fun φ hφ hφc _ v ↦ ?_⟩,
    fun K _ hK ↦ ?_⟩
  · obtain ⟨R, hR, hφR⟩ := hball _ hφc
    have h := (hasWeakGradient_of_weakGrad isOpen_ball (hloc 0 R hR).1 (hloc 0 R hR).2
      (hu 0 R hR).2.2).2.2 φ hφ hφc hφR v
    simp only [Measure.restrict_univ]
    rwa [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [fderiv_apply_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφR h)) v, mul_zero],
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
        rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hφR h)), mul_zero]] at h
  · obtain ⟨R, hR, hKR⟩ := hball K hK
    exact ⟨(hu 0 R hR).1.mono_measure (Measure.restrict_mono hKR le_rfl),
      (hu 0 R hR).2.1.mono_measure (Measure.restrict_mono hKR le_rfl)⟩

/-! ### Energies -/

theorem J_nonneg (B : Set (E d)) (f : E d → ℝ) (g : E d → E d) : 0 ≤ J B f g :=
  integral_nonneg fun x ↦ add_nonneg (sq_nonneg _) (by split_ifs <;> norm_num)

/-- On a ball, the `ℝ≥0∞`-valued energy is the real energy, provided `f` is measurable and `g` is
square integrable there. -/
theorem energyJ_ball_eq_ofReal_J {c : E d} {r : ℝ} {f : E d → ℝ} {g : E d → E d}
    (hf : AEStronglyMeasurable f (volume.restrict (ball c r)))
    (hg : MemLp g 2 (volume.restrict (ball c r))) :
    energyJ (ball c r) (fun _ ↦ 1) f g = ENNReal.ofReal (J (ball c r) f g) := by
  have hstep : Measurable fun t : ℝ ↦ if 0 < t then (1 : ℝ) else 0 :=
    Measurable.ite measurableSet_Ioi measurable_const measurable_const
  have hint : Integrable (fun x ↦ ‖g x‖ ^ 2 + (if 0 < f x then (1 : ℝ) else 0))
      (volume.restrict (ball c r)) := by
    refine (hg.integrable_norm_pow two_ne_zero).add ?_
    refine Integrable.of_bound (hstep.comp_aemeasurable hf.aemeasurable).aestronglyMeasurable 1
      (Eventually.of_forall fun x ↦ ?_)
    split_ifs <;> norm_num
  rw [J, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x ↦ add_nonneg (sq_nonneg _) (by split_ifs <;> norm_num)), energyJ]
  refine setLIntegral_congr_fun measurableSet_ball fun x hx ↦ ?_
  have hx' : dist x c < r := hx
  by_cases h : 0 < f x
  · simp [posSet, Set.indicator, hx', h]
  · simp [posSet, Set.indicator, hx', h]

end OnePhaseDimension.Textbook
