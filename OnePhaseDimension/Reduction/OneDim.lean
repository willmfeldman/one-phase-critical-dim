/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Homogeneity
public import OnePhaseDimension.Reduction.Bridges
public import OnePhaseDimension.Reduction.Regular
public import EllipticBernoulli.Sobolev.Energy
public import EllipticBernoulli.Sobolev.Lattice
public import EllipticBernoulli.Sobolev.Lipschitz
public import EllipticBernoulli.Sobolev.Uniqueness
public import EllipticBernoulli.Flatness.TestCalculus

/-!
# The classification in dimension one

Every nonzero, nonnegative, one-homogeneous global minimizer of the one-phase energy on the line
is flat: `u(x) = x₊` or `u(x) = (-x)₊` almost everywhere.

## Proof

* A measurable function on the line that is one-homogeneous almost everywhere, for each dilation
  factor, is a.e. equal to `a x₊ + b (-x)₊`, `a, b ≥ 0`: by Fubini, almost every `t` satisfies
  `u(r t) = r u(t)` for almost every `r > 0`, and one such `t` on each side of the origin fixes
  the slopes.
* If `a, b > 0`, the competitor `max(u, m)`, `0 < m < min(a, b)`, has the same positivity set in
  `(-1, 1)` and a strictly smaller Dirichlet energy.
* If exactly one slope `a` is positive, the competitors equal to `a (x - t)₊ / (1 - t)` on
  `(-1, 1)` and to `u` outside have energy `a² / (1 - t) + 1 - t`, while `u` has energy `a² + 1`.
  Minimality for all `t ∈ (-1, 1)` forces `a = 1`.

## Main results

* `exists_ae_eq_slopes`: a.e. one-homogeneous nonnegative functions on `ℝ¹` are piecewise linear.
* `energyJ_le_of_eqOn_compl`: the minimality inequality for a competitor that agrees with the
  minimizer off a ball, for any weak gradient of the minimizer.
* `flat_of_dim_one`, `flatInDim_one`: the classification.

## Differences from the source

The 2026-09-24 version uses a smooth bump `φ` with `φ(0) > 0` and the expansion
`J(u + τφ) - J(u) = -2τ(b₊ + b₋)φ(0) + O(τ²)` to exclude two positive slopes; we use the
competitor `max(u, m)`, whose energy density is pointwise no larger and strictly smaller near the
origin. The source writes the translated competitors on `(-R, R)` and differentiates the energy
`b²R²/(R - t) + (R - t)` at `t = 0`; we take `R = 1`, write the competitors with `min` and `max`
of two affine functions, and compare energies for all small `t` of both signs instead of
differentiating. The source also states that one-homogeneous Sobolev functions on the line are
piecewise linear; we prove this for a.e. one-homogeneity by Fubini.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Gradient RealInnerProductSpace ENNReal

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-! ### Homogeneous functions on the line -/

/-- A measurable nonnegative function on `ℝ` that is one-homogeneous almost everywhere for each
dilation factor is a.e. equal to `a t₊ + b (-t)₊` with `a, b ≥ 0`. -/
theorem exists_ae_eq_slopes_real {f : ℝ → ℝ} (hf : Measurable f) (hnn : ∀ᵐ t, 0 ≤ f t)
    (h : ∀ r : ℝ, 0 < r → ∀ᵐ t, f (r * t) = r * f t) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ ∀ᵐ t, f t = a * max t 0 + b * max (-t) 0 := by
  set P : ℝ → ℝ → Prop := fun r t ↦ 0 < r → f (r * t) = r * f t with hP
  have hmeas : MeasurableSet {p : ℝ × ℝ | P p.1 p.2} := by
    have : {p : ℝ × ℝ | P p.1 p.2} = {p | p.1 ≤ 0} ∪ {p | f (p.1 * p.2) = p.1 * f p.2} := by
      ext p
      simp only [hP, mem_ofPred_eq, mem_union]
      by_cases hp : 0 < p.1
      · simp [hp, not_le.2 hp]
      · simp [hp, not_lt.1 hp]
    rw [this]
    exact (measurableSet_le measurable_fst measurable_const).union
      (measurableSet_eq_fun (hf.comp (measurable_fst.mul measurable_snd))
        (measurable_fst.mul (hf.comp measurable_snd)))
  have hall : ∀ᵐ r : ℝ, ∀ᵐ t : ℝ, P r t := Eventually.of_forall fun r ↦ by
    by_cases hr : 0 < r
    · filter_upwards [h r hr] with t ht _ using ht
    · exact Eventually.of_forall fun t h' ↦ absurd h' hr
  have hgood : ∀ᵐ t : ℝ, ∀ᵐ r : ℝ, P r t := (Measure.ae_ae_comm hmeas).1 hall
  have hex : ∀ s : Set ℝ, MeasurableSet s → volume s ≠ 0 →
      ∃ t ∈ s, 0 ≤ f t ∧ ∀ᵐ r : ℝ, P r t := by
    intro s hs hs0
    have hae : ∀ᵐ t ∂(volume.restrict s), t ∈ s ∧ 0 ≤ f t ∧ ∀ᵐ r : ℝ, P r t := by
      filter_upwards [ae_restrict_mem hs, ae_restrict_of_ae hnn, ae_restrict_of_ae hgood]
        with t h1 h2 h3
      exact ⟨h1, h2, h3⟩
    have : (ae (volume.restrict s)).NeBot := ae_neBot.2 (by
      rwa [Ne, Measure.restrict_eq_zero])
    obtain ⟨t, ht⟩ := hae.exists
    exact ⟨t, ht.1, ht.2⟩
  obtain ⟨t₁, ht₁, hf₁, hP₁⟩ := hex (Ioi 0) measurableSet_Ioi (by simp)
  obtain ⟨t₂, ht₂, hf₂, hP₂⟩ := hex (Iio 0) measurableSet_Iio (by simp)
  have ht₁' : 0 < t₁ := ht₁
  have ht₂' : t₂ < 0 := ht₂
  have htrans : ∀ t : ℝ, t ≠ 0 → (∀ᵐ r : ℝ, P r t) →
      ∀ᵐ s : ℝ, 0 < t⁻¹ * s → f s = t⁻¹ * s * f t := by
    intro t ht hPt
    have hq := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) (inv_ne_zero ht)
    filter_upwards [hq.ae hPt] with s hs hpos
    have hst : t⁻¹ * s * t = s := by field_simp
    have := hs (by simpa [smul_eq_mul] using hpos)
    simp only [smul_eq_mul] at this
    rwa [hst] at this
  have h0 : ∀ᵐ s : ℝ, s ≠ 0 := by
    rw [ae_iff]
    simp
  refine ⟨t₁⁻¹ * f t₁, -(t₂⁻¹ * f t₂), mul_nonneg (inv_nonneg.2 ht₁'.le) hf₁,
    neg_nonneg.2 (mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 ht₂'.le) hf₂), ?_⟩
  filter_upwards [htrans t₁ ht₁'.ne' hP₁, htrans t₂ ht₂'.ne hP₂, h0] with s h1 h2 hs0
  rcases hs0.lt_or_gt with hs | hs
  · have hpos : 0 < t₂⁻¹ * s := mul_pos_of_neg_of_neg (inv_lt_zero.2 ht₂') hs
    rw [h2 hpos, max_eq_right hs.le, max_eq_left (neg_nonneg.2 hs.le)]
    ring
  · have hpos : 0 < t₁⁻¹ * s := mul_pos (inv_pos.2 ht₁') hs
    rw [h1 hpos, max_eq_left hs.le, max_eq_right (neg_nonpos.2 hs.le)]
    ring

/-! ### The line as `E 1` -/

/-- The coordinate `E 1 ≃ ℝ`, as a measurable equivalence. -/
def coordOne : E 1 ≃ᵐ ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).symm.trans (MeasurableEquiv.funUnique (Fin 1) ℝ)

@[simp]
theorem coordOne_apply (x : E 1) : coordOne x = x 0 := rfl

theorem coordOne_symm_mul (r t : ℝ) : coordOne.symm (r * t) = r • coordOne.symm t := by
  apply coordOne.injective
  simp only [MeasurableEquiv.apply_symm_apply, coordOne_apply, PiLp.smul_apply, smul_eq_mul]
  rw [← coordOne_apply (coordOne.symm t), MeasurableEquiv.apply_symm_apply]

theorem measurePreserving_coordOne : MeasurePreserving coordOne volume volume :=
  (volume_preserving_funUnique (Fin 1) ℝ).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 1))

/-- The unit vector of `E 1`. -/
def basisOne : E 1 := EuclideanSpace.single 0 1

theorem inner_basisOne (x : E 1) : ⟪x, basisOne⟫ = x 0 := by
  simp [basisOne, EuclideanSpace.inner_single_right]

theorem norm_basisOne : ‖basisOne‖ = 1 := by
  simp [basisOne]

theorem norm_eq_abs_one (x : E 1) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq]
  simp [Real.sqrt_sq_eq_abs]

/-- `e` is one of the two unit vectors of `E 1`. -/
def IsAxisOne (e : E 1) : Prop := e = basisOne ∨ e = -basisOne

theorem IsAxisOne.norm_eq {e : E 1} (he : IsAxisOne e) : ‖e‖ = 1 := by
  rcases he with rfl | rfl <;> simp [norm_basisOne]

theorem IsAxisOne.abs_inner {e : E 1} (he : IsAxisOne e) (x : E 1) : |⟪x, e⟫| = ‖x‖ := by
  rcases he with rfl | rfl <;> simp [inner_basisOne, norm_eq_abs_one]

theorem IsAxisOne.measurePreserving {e : E 1} (he : IsAxisOne e) :
    MeasurePreserving (fun x : E 1 ↦ ⟪x, e⟫) volume volume := by
  rcases he with rfl | rfl
  · convert measurePreserving_coordOne using 1
    funext x
    simp [inner_basisOne]
  · convert (Measure.measurePreserving_neg (volume : Measure ℝ)).comp measurePreserving_coordOne
      using 1
    funext x
    simp [inner_basisOne]

/-- A nonnegative function on `E 1` that is one-homogeneous almost everywhere is a.e. equal to
`a x₊ + b (-x)₊` with `a, b ≥ 0`. -/
theorem exists_ae_eq_slopes {u : E 1 → ℝ} (hmeas : AEStronglyMeasurable u volume)
    (hnn : ∀ᵐ x ∂(volume : Measure (E 1)), 0 ≤ u x) (hhom : OneHomogeneousAE u) :
    ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ u =ᵐ[volume] fun x ↦ a * max (x 0) 0 + b * max (-x 0) 0 := by
  set u' := hmeas.mk u
  have huu' : u =ᵐ[volume] u' := hmeas.ae_eq_mk
  have hu'm : Measurable u' := hmeas.stronglyMeasurable_mk.measurable
  have hhom' := oneHomogeneousAE_congr huu' hhom
  have hsymm := (MeasurePreserving.symm coordOne measurePreserving_coordOne).quasiMeasurePreserving
  obtain ⟨a, b, ha, hb, hab⟩ := exists_ae_eq_slopes_real (f := fun t ↦ u' (coordOne.symm t))
    (hu'm.comp coordOne.symm.measurable)
    (hsymm.ae (show ∀ᵐ x ∂(volume : Measure (E 1)), 0 ≤ u' x by
      filter_upwards [hnn, huu'] with x h1 h2; rwa [← h2]))
    (fun r hr ↦ by
      filter_upwards [hsymm.ae (hhom' r hr)] with t ht
      rw [coordOne_symm_mul, ht])
  refine ⟨a, b, ha, hb, ?_⟩
  filter_upwards [huu', measurePreserving_coordOne.quasiMeasurePreserving.ae hab] with x h1 h2
  simp only [coordOne_apply] at h2
  rw [show coordOne.symm (x 0) = x from coordOne.symm_apply_apply x] at h2
  rw [h1, h2]

/-! ### Slope profiles -/

variable {d : ℕ}

/-- The profile `x ↦ (s (⟪x, e⟫ - t₀))₊`. -/
def slopeProfile (e : E d) (s t₀ : ℝ) (x : E d) : ℝ := max (s * (⟪x, e⟫ - t₀)) 0

/-- The weak gradient `1_{⟪x, e⟫ > t₀} s e` of the slope profile. -/
def slopeGrad (e : E d) (s t₀ : ℝ) : E d → E d := {x | t₀ < ⟪x, e⟫}.indicator fun _ ↦ s • e

/-- An affine function `x ↦ s (⟪x, e⟫ - t₀)` is in `H¹_loc` with gradient `s e`. -/
theorem memH1Loc_affine (e : E d) (s t₀ : ℝ) :
    MemH1Loc univ (fun x ↦ s * (⟪x, e⟫ - t₀)) (fun _ ↦ s • e) := by
  have h1 := memH1Loc_gradient_of_contDiff (u := fun y : E d ↦ ⟪y, s • e⟫) isOpen_univ
    (contDiff_id.inner ℝ contDiff_const)
  rw [show ∇ (fun y : E d ↦ ⟪y, s • e⟫) = fun _ ↦ s • e from
    funext (gradient_inner_const (s • e))] at h1
  convert h1.sub_const (s * t₀) using 1
  funext x
  rw [real_inner_smul_right]
  ring

theorem memH1Loc_slopeProfile (e : E d) {s : ℝ} (hs : 0 < s) (t₀ : ℝ) :
    MemH1Loc univ (slopeProfile e s t₀) (slopeGrad e s t₀) := by
  convert memH1Loc_posPart isOpen_univ (memH1Loc_affine e s t₀) using 1
  · rfl
  unfold slopeGrad
  congr 1
  ext x
  simp only [mem_ofPred_eq]
  rw [mul_pos_iff_of_pos_left hs, sub_pos]

theorem measurable_slopeGrad (e : E d) (s t₀ : ℝ) : Measurable (slopeGrad e s t₀) :=
  measurable_const.indicator
    (measurableSet_lt measurable_const (continuous_id.inner continuous_const).measurable)

theorem continuous_slopeProfile (e : E d) (s t₀ : ℝ) : Continuous (slopeProfile e s t₀) :=
  (continuous_const.mul ((continuous_id.inner continuous_const).sub continuous_const)).max
    continuous_const

/-- **The energy of a slope profile** on `(-1, 1)`: `(s² + 1)(1 - t₀)`. -/
theorem energyJ_slopeProfile {e : E 1} (he : IsAxisOne e) {s t₀ : ℝ} (hs : 0 < s)
    (ht₀ : -1 ≤ t₀) :
    energyJ (ball 0 1) (fun _ ↦ 1) (slopeProfile e s t₀) (slopeGrad e s t₀) =
      ENNReal.ofReal ((s ^ 2 + 1) * (1 - t₀)) := by
  have hS : MeasurableSet {x : E 1 | t₀ < ⟪x, e⟫} :=
    measurableSet_lt measurable_const (continuous_id.inner continuous_const).measurable
  have hpt : ∀ x ∈ ball (0 : E 1) 1,
      ENNReal.ofReal (‖slopeGrad e s t₀ x‖ ^ 2 +
        (fun _ ↦ (1 : ℝ)) x ^ 2 * (posSet (slopeProfile e s t₀) (ball 0 1)).indicator 1 x) =
      {x : E 1 | t₀ < ⟪x, e⟫}.indicator (fun _ ↦ ENNReal.ofReal (s ^ 2 + 1)) x := by
    intro x hx
    by_cases h : t₀ < ⟪x, e⟫
    · have hpos : x ∈ posSet (slopeProfile e s t₀) (ball 0 1) :=
        ⟨hx, lt_max_of_lt_left (mul_pos hs (sub_pos.2 h))⟩
      rw [indicator_of_mem hpos, indicator_of_mem (show x ∈ {x : E 1 | t₀ < ⟪x, e⟫} from h)]
      simp [slopeGrad, h, norm_smul, he.norm_eq, abs_of_pos hs]
    · have hpos : x ∉ posSet (slopeProfile e s t₀) (ball 0 1) := by
        rintro ⟨-, hp⟩
        refine (lt_irrefl (0 : ℝ)) (lt_of_lt_of_le hp (max_le ?_ le_rfl))
        exact mul_nonpos_of_nonneg_of_nonpos hs.le (sub_nonpos.2 (not_lt.1 h))
      rw [indicator_of_notMem hpos,
        indicator_of_notMem (show x ∉ {x : E 1 | t₀ < ⟪x, e⟫} from h)]
      simp [slopeGrad, h]
  have hset : {x : E 1 | t₀ < ⟪x, e⟫} ∩ ball 0 1 = (fun x : E 1 ↦ ⟪x, e⟫) ⁻¹' Ioo t₀ 1 := by
    ext x
    simp only [mem_inter_iff, mem_ofPred_eq, mem_ball, dist_zero_right, mem_preimage, mem_Ioo]
    rw [← he.abs_inner x, abs_lt]
    constructor
    · rintro ⟨h1, -, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by linarith, h2⟩
  unfold energyJ
  rw [setLIntegral_congr_fun measurableSet_ball hpt, lintegral_indicator_const hS,
    Measure.restrict_apply hS, hset,
    he.measurePreserving.measure_preimage measurableSet_Ioo.nullMeasurableSet, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (by positivity)]

/-! ### Comparison with competitors -/

/-- The minimality inequality on `ball x r` for a competitor `v` agreeing with the minimizer `u`
off the ball, stated for an arbitrary weak gradient `Gu` of `u` (weak gradients are unique). -/
theorem energyJ_le_of_eqOn_compl {Q u v : E d → ℝ} {Gu Gv : E d → E d}
    (hmin : IsLocalEnergyMinimizer univ Q u) (hu : MemH1Loc univ u Gu) (hv : MemH1Loc univ v Gv)
    {x : E d} {r : ℝ} (hr : 0 < r) (hoff : ∀ y ∉ ball x r, v y = u y) :
    energyJ (ball x r) Q u Gu ≤ energyJ (ball x r) Q v Gv := by
  obtain ⟨Gu', hGu', hm⟩ := hmin
  have hle := (hm x r hr (subset_univ _)).2.2.2 v Gv hv
    (ae_restrict_of_forall_mem (MeasurableSet.univ.diff measurableSet_ball)
      fun y hy ↦ hoff y hy.2)
    (Eventually.of_forall fun _ ↦ mem_univ _)
  have hG : ∀ᵐ y ∂(volume.restrict (ball x r)), Gu' y = Gu y :=
    HasWeakGradient.ae_eq_of_eqOn isOpen_univ isOpen_ball (subset_univ _) hGu'.1 hu.1
      fun _ _ ↦ rfl
  rwa [energyJ_congr (fun _ _ ↦ rfl) hG] at hle

/-- Two `H¹_loc` functions that agree on a ball have the same energy on it. -/
theorem energyJ_eq_of_eqOn_ball {Q v w : E d → ℝ} {Gv Gw : E d → E d}
    (hv : MemH1Loc univ v Gv) (hw : MemH1Loc univ w Gw) {x : E d} {r : ℝ}
    (h : EqOn v w (ball x r)) : energyJ (ball x r) Q v Gv = energyJ (ball x r) Q w Gw :=
  energyJ_congr h
    (HasWeakGradient.ae_eq_of_eqOn isOpen_univ isOpen_ball (subset_univ _) hv.1 hw.1 h)

/-- The translated competitors: for `|t| < 1` there is an `H¹_loc` function equal to
`a (⟪x, e⟫ - t)₊ / (1 - t)` on `(-1, 1)` and to `a ⟪x, e⟫₊` outside. -/
theorem exists_slope_competitor {e : E 1} (he : IsAxisOne e) {a t : ℝ} (ha : 0 < a)
    (ht₁ : -1 < t) (ht₂ : t < 1) :
    ∃ v Gv, MemH1Loc univ v Gv ∧ (∀ y ∉ ball (0 : E 1) 1, v y = slopeProfile e a 0 y) ∧
      EqOn v (slopeProfile e (a / (1 - t)) t) (ball 0 1) := by
  have h1t : 0 < 1 - t := by linarith
  set s := a / (1 - t) with hs_def
  have hs : 0 < s := div_pos ha h1t
  -- `ℓ - m = a t (p - 1) / (1 - t)`
  have hdiff : ∀ p : ℝ, s * (p - t) - a * (p - 0) = a * t * (p - 1) / (1 - t) := by
    intro p
    rw [hs_def]
    field_simp
    ring
  have hℓ := memH1Loc_affine e s t
  have hm := memH1Loc_affine e a 0
  have hin : ∀ y ∈ ball (0 : E 1) 1, ⟪y, e⟫ < 1 := fun y hy ↦
    lt_of_le_of_lt (le_abs_self _) (by rw [he.abs_inner]; simpa using hy)
  have hout : ∀ y ∉ ball (0 : E 1) 1, 1 ≤ ⟪y, e⟫ ∨ ⟪y, e⟫ ≤ -1 := by
    intro y hy
    have : 1 ≤ |⟪y, e⟫| := by rw [he.abs_inner]; simpa using hy
    rcases le_abs'.1 this with h | h
    · exact Or.inr h
    · exact Or.inl h
  rcases le_or_gt 0 t with ht | ht
  · -- `t ≥ 0`: `v = (min ℓ m)₊`
    refine ⟨_, _, memH1Loc_posPart isOpen_univ (MemH1Loc.min isOpen_univ hℓ hm), ?_, ?_⟩
    · intro y hy
      simp only [slopeProfile]
      rcases hout y hy with hp | hp
      · have : a * (⟪y, e⟫ - 0) ≤ s * (⟪y, e⟫ - t) := by
          have := hdiff ⟪y, e⟫
          have : 0 ≤ a * t * (⟪y, e⟫ - 1) / (1 - t) :=
            div_nonneg (mul_nonneg (mul_nonneg ha.le ht) (by linarith)) h1t.le
          linarith
        rw [min_eq_right this]
      · have h1 : a * (⟪y, e⟫ - 0) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
        rw [max_eq_right (le_trans (min_le_right _ _) h1.le), max_eq_right h1.le]
    · intro y hy
      simp only [slopeProfile]
      have : s * (⟪y, e⟫ - t) ≤ a * (⟪y, e⟫ - 0) := by
        have := hdiff ⟪y, e⟫
        have : a * t * (⟪y, e⟫ - 1) / (1 - t) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ha.le ht) (by linarith [hin y hy]))
            h1t.le
        linarith
      rw [min_eq_left this]
  · -- `t < 0`: `v = (max ℓ m)₊`
    refine ⟨_, _, memH1Loc_posPart isOpen_univ (MemH1Loc.max isOpen_univ hℓ hm), ?_, ?_⟩
    · intro y hy
      simp only [slopeProfile]
      rcases hout y hy with hp | hp
      · have : s * (⟪y, e⟫ - t) ≤ a * (⟪y, e⟫ - 0) := by
          have := hdiff ⟪y, e⟫
          have : a * t * (⟪y, e⟫ - 1) / (1 - t) ≤ 0 :=
            div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos ha.le ht.le)
                (by linarith)) h1t.le
          linarith
        rw [max_eq_right this]
      · have h1 : a * (⟪y, e⟫ - 0) < 0 := mul_neg_of_pos_of_neg ha (by linarith)
        have h2 : s * (⟪y, e⟫ - t) < 0 := mul_neg_of_pos_of_neg hs (by linarith)
        rw [max_eq_right (max_le h2.le h1.le), max_eq_right h1.le]
    · intro y hy
      simp only [slopeProfile]
      have : a * (⟪y, e⟫ - 0) ≤ s * (⟪y, e⟫ - t) := by
        have := hdiff ⟪y, e⟫
        have : 0 ≤ a * t * (⟪y, e⟫ - 1) / (1 - t) :=
          div_nonneg (mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha.le ht.le)
            (by linarith [hin y hy])) h1t.le
        linarith
      rw [max_eq_left this]

/-- **A single positive slope is one.** If `x ↦ a ⟪x, e⟫₊`, `a > 0`, is a global minimizer on
the line, then `a = 1`. -/
theorem slope_eq_one {e : E 1} (he : IsAxisOne e) {a : ℝ} (ha : 0 < a)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) (slopeProfile e a 0)) : a = 1 := by
  have key : ∀ t : ℝ, -1 < t → t < 1 → t * (1 - a ^ 2) ≤ t ^ 2 := by
    intro t ht₁ ht₂
    have h1t : 0 < 1 - t := by linarith
    obtain ⟨v, Gv, hv, hoff, hon⟩ := exists_slope_competitor he ha ht₁ ht₂
    have hle := energyJ_le_of_eqOn_compl hmin (memH1Loc_slopeProfile e ha 0) hv one_pos hoff
    rw [energyJ_slopeProfile he ha (by norm_num),
      energyJ_eq_of_eqOn_ball hv (memH1Loc_slopeProfile e (div_pos ha h1t) t) hon,
      energyJ_slopeProfile he (div_pos ha h1t) ht₁.le,
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hle
    have hs : (a / (1 - t)) ^ 2 * (1 - t) = a ^ 2 / (1 - t) := by
      field_simp
    have h2 : a ^ 2 + t ≤ a ^ 2 / (1 - t) := by nlinarith
    rw [le_div_iff₀ h1t] at h2
    nlinarith
  have hpos : ∀ t : ℝ, 0 < t → t < 1 → 1 - a ^ 2 ≤ t := fun t h0 h1 ↦ by
    have := key t (by linarith) h1
    nlinarith
  have hneg : ∀ t : ℝ, -1 < t → t < 0 → t ≤ 1 - a ^ 2 := fun t h0 h1 ↦ by
    have := key t h0 (by linarith)
    nlinarith
  have hle : 1 - a ^ 2 ≤ 0 := by
    by_contra h
    push Not at h
    have := hpos (min ((1 - a ^ 2) / 2) (1 / 2)) (lt_min (by linarith) (by norm_num))
      (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    have := min_le_left ((1 - a ^ 2) / 2) (1 / 2)
    linarith
  have hge : 0 ≤ 1 - a ^ 2 := by
    by_contra h
    push Not at h
    have := hneg (max ((1 - a ^ 2) / 2) (-1 / 2))
      (lt_of_lt_of_le (by norm_num) (le_max_right _ _)) (max_lt (by linarith) (by norm_num))
    have := le_max_left ((1 - a ^ 2) / 2) (-1 / 2)
    linarith
  nlinarith

/-- **Two positive slopes are excluded.** -/
theorem not_isLocalEnergyMinimizer_two_slopes {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ¬ IsLocalEnergyMinimizer univ (fun _ ↦ 1)
      (fun x ↦ slopeProfile basisOne a 0 x + slopeProfile (-basisOne) b 0 x) := by
  intro hmin
  set u₀ : E 1 → ℝ := fun x ↦ slopeProfile basisOne a 0 x + slopeProfile (-basisOne) b 0 x
    with hu₀_def
  set G₀ : E 1 → E 1 := fun x ↦ slopeGrad basisOne a 0 x + slopeGrad (-basisOne) b 0 x
    with hG₀_def
  have hu₀ : MemH1Loc univ u₀ G₀ :=
    (memH1Loc_slopeProfile basisOne ha 0).add (memH1Loc_slopeProfile (-basisOne) hb 0)
  set m : ℝ := min a b / 2 with hm_def
  have hm : 0 < m := by positivity
  have hma : m < a := by have := min_le_left a b; linarith
  have hmb : m < b := by have := min_le_right a b; linarith
  have hv := MemH1Loc.max isOpen_univ hu₀ (memH1Loc_const (U := univ) m)
  set v : E 1 → ℝ := fun y ↦ max (u₀ y) m with hv_def
  set Gv : E 1 → E 1 := fun y ↦ if u₀ y < m then 0 else G₀ y with hGv_def
  -- explicit formulas
  have hu₀x : ∀ x : E 1, u₀ x = max (a * x 0) 0 + max (-(b * x 0)) 0 := fun x ↦ by
    simp [hu₀_def, slopeProfile, inner_basisOne]
  have hG₀pos : ∀ x : E 1, 0 < x 0 → G₀ x = a • basisOne := fun x hx ↦ by
    simp [hG₀_def, slopeGrad, inner_basisOne, hx, not_lt.2 hx.le]
  have hG₀neg : ∀ x : E 1, x 0 < 0 → G₀ x = b • -basisOne := fun x hx ↦ by
    simp [hG₀_def, slopeGrad, inner_basisOne, hx, not_lt.2 hx.le]
  have hoff : ∀ y ∉ ball (0 : E 1) 1, v y = u₀ y := by
    intro y hy
    have : 1 ≤ |y 0| := by rw [← norm_eq_abs_one]; simpa using hy
    refine max_eq_left ?_
    rw [hu₀x]
    rcases le_abs'.1 this with h | h
    · have : b ≤ -(b * y 0) := by nlinarith
      have := le_max_left (-(b * y 0)) 0
      have := le_max_right (a * y 0) 0
      linarith
    · have : a ≤ a * y 0 := by nlinarith
      have := le_max_left (a * y 0) 0
      have := le_max_right (-(b * y 0)) 0
      linarith
  have hle := energyJ_le_of_eqOn_compl hmin hu₀ hv one_pos hoff
  -- the strict inequality
  have hne0 : ∀ᵐ x : E 1, x 0 ≠ 0 := by
    have h0 : ∀ᵐ s : ℝ, s ≠ 0 := by rw [ae_iff]; simp
    simpa using measurePreserving_coordOne.quasiMeasurePreserving.ae h0
  have hmeasG₀ : Measurable G₀ :=
    (measurable_slopeGrad basisOne a 0).add (measurable_slopeGrad (-basisOne) b 0)
  have hcont₀ : Continuous u₀ :=
    (continuous_slopeProfile basisOne a 0).add (continuous_slopeProfile (-basisOne) b 0)
  have hpos₀ : MeasurableSet (posSet u₀ (ball 0 1)) :=
    measurableSet_ball.inter (measurableSet_lt measurable_const hcont₀.measurable)
  have hlt : energyJ (ball 0 1) (fun _ ↦ 1) v Gv < energyJ (ball 0 1) (fun _ ↦ 1) u₀ G₀ := by
    unfold energyJ
    refine lintegral_strict_mono_of_ae_le_of_ae_lt_on
      (s := (fun x : E 1 ↦ x 0) ⁻¹' Ioo 0 (m / a)) ?_ ?_ ?_ ?_ ?_
    · exact (((hmeasG₀.norm.pow_const 2).add (measurable_const.mul
        (measurable_const.indicator hpos₀))).ennreal_ofReal).aemeasurable
    · exact (energyJ_lt_top hv isBounded_ball.isCompact_closure (subset_univ _)
        (CQ := 1) (fun _ _ ↦ by simp)).ne
    · filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne0] with x hx hx0
      refine ENNReal.ofReal_le_ofReal ?_
      have hu₀p : 0 < u₀ x := by
        rw [hu₀x]
        have h1 := le_max_right (a * x 0) 0
        have h2 := le_max_left (a * x 0) 0
        have h3 := le_max_right (-(b * x 0)) 0
        have h4 := le_max_left (-(b * x 0)) 0
        rcases hx0.lt_or_gt with h | h
        · nlinarith
        · nlinarith
      have hvp : 0 < v x := lt_of_lt_of_le hm (le_max_right _ _)
      rw [indicator_of_mem (show x ∈ posSet v (ball 0 1) from ⟨hx, hvp⟩),
        indicator_of_mem (show x ∈ posSet u₀ (ball 0 1) from ⟨hx, hu₀p⟩)]
      gcongr
      simp only [hGv_def]
      split_ifs <;> simp
    · rw [Measure.restrict_apply' measurableSet_ball]
      have hsub : (fun x : E 1 ↦ x 0) ⁻¹' Ioo 0 (m / a) ⊆ ball 0 1 := by
        intro x hx
        have hma' : m / a < 1 := (div_lt_one ha).2 hma
        simp only [mem_preimage, mem_Ioo] at hx
        rw [mem_ball, dist_zero_right, norm_eq_abs_one, abs_lt]
        constructor <;> linarith
      rw [inter_eq_left.2 hsub]
      have hmp : MeasurePreserving (fun x : E 1 ↦ x 0) volume volume := measurePreserving_coordOne
      rw [hmp.measure_preimage measurableSet_Ioo.nullMeasurableSet, Real.volume_Ioo]
      simpa using div_pos hm ha
    · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx hxs
      simp only [mem_preimage, mem_Ioo] at hxs
      have hux : u₀ x = a * x 0 := by
        rw [hu₀x, max_eq_left (by nlinarith), max_eq_right (by nlinarith), add_zero]
      have hlt' : u₀ x < m := by
        rw [hux]
        have := (lt_div_iff₀ ha).1 hxs.2
        linarith
      have hvp : 0 < v x := lt_of_lt_of_le hm (le_max_right _ _)
      have hu₀p : 0 < u₀ x := by rw [hux]; exact mul_pos ha hxs.1
      rw [indicator_of_mem (show x ∈ posSet v (ball 0 1) from ⟨hx, hvp⟩),
        indicator_of_mem (show x ∈ posSet u₀ (ball 0 1) from ⟨hx, hu₀p⟩)]
      simp only [hGv_def, hlt', ite_true, hG₀pos x hxs.1, norm_zero, norm_smul, norm_basisOne,
        Real.norm_eq_abs, abs_of_pos ha]
      rw [ENNReal.ofReal_lt_ofReal_iff']
      constructor <;> norm_num <;> nlinarith
  exact absurd hle (not_le.2 hlt)

/-- **The classification in dimension one.** Every nonzero, nonnegative, one-homogeneous global
minimizer of the one-phase energy on the line is flat. -/
theorem flat_of_dim_one (u : E 1 → ℝ) (hnn : ∀ᵐ x ∂(volume : Measure (E 1)), 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) (hhom : OneHomogeneousAE u)
    (hne : ¬ u =ᵐ[volume] 0) : FlatAE u := by
  obtain ⟨Gu, hGu, -⟩ := id hmin
  have hmeas : AEStronglyMeasurable u volume :=
    (locallyIntegrableOn_univ.1 hGu.1.1).aestronglyMeasurable
  obtain ⟨a, b, ha, hb, hu⟩ := exists_ae_eq_slopes hmeas hnn hhom
  set u₀ : E 1 → ℝ := fun x ↦ slopeProfile basisOne a 0 x + slopeProfile (-basisOne) b 0 x
    with hu₀_def
  have hu₀ : u =ᵐ[volume] u₀ := by
    filter_upwards [hu] with x hx
    rw [hx, hu₀_def]
    simp only [slopeProfile, inner_basisOne, inner_neg_right, sub_zero]
    rw [mul_max_of_nonneg _ _ ha, mul_max_of_nonneg _ _ hb, mul_zero, mul_zero]
  have hmin₀ := (isLocalEnergyMinimizer_congr_ae hu₀).1 hmin
  have hzero : ∀ (e : E 1) (x : E 1), slopeProfile e 0 0 x = 0 := fun e x ↦ by
    simp [slopeProfile]
  rcases ha.eq_or_lt with rfl | ha' <;> rcases hb.eq_or_lt with rfl | hb'
  · exact absurd (hu₀.trans (Eventually.of_forall fun x ↦ by simp [hu₀_def, hzero])) hne
  · have h : u₀ = slopeProfile (-basisOne) b 0 := funext fun x ↦ by simp [hu₀_def, hzero]
    rw [h] at hmin₀ hu₀
    obtain rfl := slope_eq_one (Or.inr rfl) hb' hmin₀
    refine ⟨-basisOne, by simp [norm_basisOne], ?_⟩
    filter_upwards [hu₀] with x hx
    simp [hx, slopeProfile]
  · have h : u₀ = slopeProfile basisOne a 0 := funext fun x ↦ by simp [hu₀_def, hzero]
    rw [h] at hmin₀ hu₀
    obtain rfl := slope_eq_one (Or.inl rfl) ha' hmin₀
    refine ⟨basisOne, norm_basisOne, ?_⟩
    filter_upwards [hu₀] with x hx
    simp [hx, slopeProfile]
  · exact absurd hmin₀ (not_isLocalEnergyMinimizer_two_slopes ha' hb')

/-- The one-dimensional classification in the form used by the induction on the dimension. -/
theorem flatInDim_one : FlatInDim 1 := flat_of_dim_one

end OnePhaseDimension
