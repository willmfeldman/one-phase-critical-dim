/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Flux.Interior
public import OnePhaseDimension.Geometry.GradientBoundSuspension

/-!
# Uniform bounds for the flux fields

The certificate data are generic (`Gen.Coeffs m`, `m = n - 1`, with constants `ε > 0`, `δ`); the
declarations at the end of the file are the case `n = 6`.

The coefficient domain `{(A, p, g) : A symmetric trace-free, |A| = 1, g² + |p|² ≤ 1}` is compact
(`isCompact_certDomain`), so the certificate coefficients and the derivative of `f` are bounded
there (`exists_coeff_bound`). With `|q| ≤ C|X|` this gives a constant `C_F ≥ 1`, depending only on
the certificate coefficients, such that at every unit point `x₀` where `u` is one-homogeneous,
smooth and harmonic, with `w > 0` and `|∇u|² ≤ 1`,

  `|h| ≤ C_F w^a`, `|∇h| ≤ C_F w^a (1 + w + |X|)`, `|Z| ≤ C_F w^{2a} (1 + w + |X|)`,

where `|X| = |B|/w` (`exists_fieldBound_const`). The constant is chosen before the function `u`,
so it is uniform over all cones (`ConeData.exists_fieldBound_const`,
`IsSuspension.exists_fieldBound_const`).

## Differences from the source

The 2026-09-24 version bounds `|q| ≤ |X|` by Cauchy–Schwarz and works with Euclidean norms of the
coefficient tensors. We bound entries one at a time (`|q_l| ≤ m² |X|`, sup norms of the
coefficients) and absorb the resulting dimensional factors into the constant.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Finset Filter Topology Metric EllipticBernoulli
open scoped RealInnerProductSpace ContDiff Gradient Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

/-! ### Regular points of a cone -/

namespace ConeData

variable {n : ℕ} {C : ConeData n} {x : E n}

private theorem isOpen_D' (C : ConeData n) : IsOpen C.D := by
  rw [C.D_eq]
  exact (isOpen_lt continuous_const C.continuous).connectedComponentIn

/-- `u` is smooth and harmonic near every regular point of `D`. -/
theorem contDiffAt_u_and_eventually_laplacian (hx : x ∈ C.D) (hxS : x ∉ C.Sing) :
    ContDiffAt ℝ ∞ C.u x ∧ ∀ᶠ y in 𝓝 x, Δ C.u y = 0 := by
  obtain ⟨U, hU, hxU, F, hF, hu, -, -, hΔ⟩ := C.chart x ⟨subset_closure hx, hxS⟩
  refine ⟨(hF.contDiffAt (hU.mem_nhds hxU)).congr_of_eventuallyEq
    (chart_eventuallyEq hU hu hxU hx), ?_⟩
  filter_upwards [hU.mem_nhds hxU, (isOpen_D' C).mem_nhds hx] with y hyU hyD
  rw [(InnerProductSpace.laplacian_congr_nhds (chart_eventuallyEq hU hu hyU hyD)).self_of_nhds]
  exact hΔ y hyU (chart_pos_of_mem_D hu hyU hyD)

end ConeData

theorem norm_frameVec {n : ℕ} (ι : E (n - 1) →ₗᵢ[ℝ] E n) (i : Fin (n - 1)) :
    ‖frameVec ι i‖ = 1 :=
  (orthonormal_frameVec ι).1 i

namespace Gen

section Tensor

variable {m : ℕ}

/-! ### The coefficient domain -/

/-- The normalized coefficient domain `{(A, p, g) : A ∈ STF², |A| = 1, g² + |p|² ≤ 1}`. -/
def certDomain : Set (Ten2 m × Ten1 m × ℝ) :=
  {x | IsSTF2 x.1 ∧ sq2 x.1 = 1 ∧ x.2.2 ^ 2 + sq1 x.2.1 ≤ 1}

theorem continuous_sq1 : Continuous (sq1 : Ten1 m → ℝ) := by
  unfold sq1
  fun_prop

theorem isClosed_certDomain : IsClosed (certDomain (m := m)) := by
  have h1 : IsClosed {x : Ten2 m × Ten1 m × ℝ | ∀ i j, x.1 i j = x.1 j i} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_iInter fun j ↦ isClosed_eq (by fun_prop) (by fun_prop)
  have h2 : IsClosed {x : Ten2 m × Ten1 m × ℝ | ∑ i, x.1 i i = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have h3 : IsClosed {x : Ten2 m × Ten1 m × ℝ | sq2 x.1 = 1} :=
    isClosed_eq (contDiff_sq2.continuous.comp continuous_fst) continuous_const
  have h4 : IsClosed {x : Ten2 m × Ten1 m × ℝ | x.2.2 ^ 2 + sq1 x.2.1 ≤ 1} :=
    isClosed_le ((by fun_prop : Continuous fun x : Ten2 m × Ten1 m × ℝ ↦ x.2.2 ^ 2).add
      (continuous_sq1.comp (by fun_prop))) continuous_const
  have : certDomain (m := m) = (({x | ∀ i j, x.1 i j = x.1 j i} ∩ {x | ∑ i, x.1 i i = 0}) ∩
      {x | sq2 x.1 = 1}) ∩ {x | x.2.2 ^ 2 + sq1 x.2.1 ≤ 1} := by
    ext x
    simp only [certDomain, IsSTF2, IsSymm2, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  rw [this]
  exact ((h1.inter h2).inter h3).inter h4

theorem sq_le_sq2 (A : Ten2 m) (i j : Fin m) : A i j ^ 2 ≤ sq2 A := by
  unfold sq2
  calc A i j ^ 2 ≤ ∑ j', A i j' ^ 2 :=
        single_le_sum (f := fun j' ↦ A i j' ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ j)
    _ ≤ ∑ i', ∑ j', A i' j' ^ 2 :=
        single_le_sum (f := fun i' ↦ ∑ j', A i' j' ^ 2)
          (fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (mem_univ i)

theorem sq_le_sq1 (p : Ten1 m) (i : Fin m) : p i ^ 2 ≤ sq1 p :=
  single_le_sum (f := fun i ↦ p i ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ i)

theorem sq1_nonneg (p : Ten1 m) : 0 ≤ sq1 p := sum_nonneg fun _ _ ↦ sq_nonneg _

theorem abs_le_one_of_sq_le_one {t : ℝ} (h : t ^ 2 ≤ 1) : |t| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  exact h

theorem certDomain_bounds {x : Ten2 m × Ten1 m × ℝ} (hx : x ∈ certDomain) :
    (∀ i j, |x.1 i j| ≤ 1) ∧ (∀ i, |x.2.1 i| ≤ 1) ∧ |x.2.2| ≤ 1 := by
  obtain ⟨-, hA, hpg⟩ := hx
  refine ⟨fun i j ↦ abs_le_one_of_sq_le_one ((sq_le_sq2 _ i j).trans hA.le),
    fun i ↦ abs_le_one_of_sq_le_one ?_, abs_le_one_of_sq_le_one ?_⟩
  · nlinarith [sq_le_sq1 x.2.1 i, sq_nonneg x.2.2]
  · nlinarith [sq1_nonneg x.2.1]

theorem isBounded_certDomain : Bornology.IsBounded (certDomain (m := m)) := by
  refine (isBounded_closedBall (x := (0 : Ten2 m × Ten1 m × ℝ)) (r := 1)).subset fun x hx ↦ ?_
  obtain ⟨hA, hp, hg⟩ := certDomain_bounds hx
  rw [mem_closedBall, dist_zero_right, norm_prod_le_iff, norm_prod_le_iff,
    pi_norm_le_iff_of_nonneg zero_le_one, pi_norm_le_iff_of_nonneg zero_le_one, Real.norm_eq_abs]
  exact ⟨fun i ↦ (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j ↦ by
    rw [Real.norm_eq_abs]; exact hA i j, fun i ↦ by rw [Real.norm_eq_abs]; exact hp i, hg⟩

/-- **The coefficient domain is compact.** -/
theorem isCompact_certDomain : IsCompact (certDomain (m := m)) :=
  isCompact_of_isClosed_isBounded isClosed_certDomain isBounded_certDomain

/-! ### Bounds on the coefficients -/

section Coeff

variable {c : Coeffs m} {ε δ : ℝ} (hc : CertificateHolds m ε δ c)
include hc

/-- The coefficients and the derivative of `f` are bounded on the coefficient domain. -/
theorem exists_coeff_bound : ∃ K, 0 ≤ K ∧ ∀ x ∈ certDomain,
    ‖c.f x‖ ≤ K ∧ ‖c.U x‖ ≤ K ∧ ‖c.K x‖ ≤ K ∧ ‖c.M x‖ ≤ K ∧ ‖c.P x‖ ≤ K ∧
      ‖fderiv ℝ c.f x‖ ≤ K := by
  have hK := isCompact_certDomain (m := m)
  obtain ⟨K1, h1⟩ := hK.exists_bound_of_continuousOn hc.smooth_f.continuous.continuousOn
  obtain ⟨K2, h2⟩ := hK.exists_bound_of_continuousOn hc.smooth_U.continuous.continuousOn
  obtain ⟨K3, h3⟩ := hK.exists_bound_of_continuousOn hc.smooth_K.continuous.continuousOn
  obtain ⟨K4, h4⟩ := hK.exists_bound_of_continuousOn hc.smooth_M.continuous.continuousOn
  obtain ⟨K5, h5⟩ := hK.exists_bound_of_continuousOn hc.smooth_P.continuous.continuousOn
  obtain ⟨K6, h6⟩ := hK.exists_bound_of_continuousOn
    (hc.smooth_f.continuous_fderiv (by simp)).continuousOn
  refine ⟨|K1| + |K2| + |K3| + |K4| + |K5| + |K6|, by positivity, fun x hx ↦ ?_⟩
  have := h1 x hx; have := h2 x hx; have := h3 x hx; have := h4 x hx; have := h5 x hx
  have := h6 x hx
  have := le_abs_self K1; have := le_abs_self K2; have := le_abs_self K3
  have := le_abs_self K4; have := le_abs_self K5; have := le_abs_self K6
  have := abs_nonneg K1; have := abs_nonneg K2; have := abs_nonneg K3
  have := abs_nonneg K4; have := abs_nonneg K5; have := abs_nonneg K6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Coeff

/-! ### Elementary tensor estimates -/

/-- Squared norm of a three-tensor, `|X|² = ∑ X_{ijk}²`. -/
def sq3 (X : Ten3 m) : ℝ := ∑ i, ∑ j, ∑ k, X i j k ^ 2

theorem sq3_nonneg (X : Ten3 m) : 0 ≤ sq3 X := by
  unfold sq3
  positivity

theorem abs_le_sqrt_sq3 (X : Ten3 m) (i j k : Fin m) : |X i j k| ≤ √(sq3 X) := by
  refine Real.abs_le_sqrt ?_
  unfold sq3
  calc X i j k ^ 2 ≤ ∑ k', X i j k' ^ 2 :=
        single_le_sum (f := fun k' ↦ X i j k' ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ k)
    _ ≤ ∑ j', ∑ k', X i j' k' ^ 2 :=
        single_le_sum (f := fun j' ↦ ∑ k', X i j' k' ^ 2)
          (fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (mem_univ j)
    _ ≤ ∑ i', ∑ j', ∑ k', X i' j' k' ^ 2 :=
        single_le_sum (f := fun i' ↦ ∑ j', ∑ k', X i' j' k' ^ 2)
          (fun _ _ ↦ sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (mem_univ i)

theorem sq3_act3 {O : Ten2 m} (hO : IsOrth O) (X : Ten3 m) : sq3 (act3 O X) = sq3 X := by
  simp only [sq3, sq]
  exact sum_act3_mul_act3 hO X X

/-- `|B/w| = |B|/w`. -/
theorem sqrt_sq3_normalizedX (T : Ten2 m) (B : Ten3 m) :
    √(sq3 (normalizedX T B)) = √(sq3 B) / normW T := by
  have h : sq3 (normalizedX T B) = sq3 B / normW T ^ 2 := by
    simp only [sq3, normalizedX, div_pow, sum_div]
  rw [h, Real.sqrt_div' _ (sq_nonneg _), Real.sqrt_sq (show 0 ≤ normW T from Real.sqrt_nonneg _)]

theorem sum_three_le {f : Fin m → Fin m → Fin m → ℝ} {b : ℝ} (h : ∀ i j k, |f i j k| ≤ b) :
    |∑ i, ∑ j, ∑ k, f i j k| ≤ (m : ℝ) ^ 3 * b := by
  calc |∑ i, ∑ j, ∑ k, f i j k| ≤ ∑ i, ∑ j, ∑ k, |f i j k| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ (abs_sum_le_sum_abs _ _).trans
          (sum_le_sum fun j _ ↦ abs_sum_le_sum_abs _ _))
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, ∑ _k : Fin m, b :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ sum_le_sum fun k _ ↦ h i j k
    _ = (m : ℝ) ^ 3 * b := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem sum_two_le {f : Fin m → Fin m → ℝ} {b : ℝ} (h : ∀ i j, |f i j| ≤ b) :
    |∑ i, ∑ j, f i j| ≤ (m : ℝ) ^ 2 * b := by
  calc |∑ i, ∑ j, f i j| ≤ ∑ i, ∑ j, |f i j| :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ ↦ abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, b := sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ h i j
    _ = (m : ℝ) ^ 2 * b := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem sum_one_le {f : Fin m → ℝ} {b : ℝ} (h : ∀ i, |f i| ≤ b) : |∑ i, f i| ≤ (m : ℝ) * b := by
  calc |∑ i, f i| ≤ ∑ i, |f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin m, b := sum_le_sum fun i _ ↦ h i
    _ = (m : ℝ) * b := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem abs_kron_le (i j : Fin m) : |kron i j| ≤ 1 := by
  unfold kron
  split_ifs <;> simp

/-- `|q_l| ≤ m² |X|` on the coefficient domain. -/
theorem abs_qVec_le {A : Ten2 m} (hA : ∀ i j, |A i j| ≤ 1) (X : Ten3 m) (l : Fin m) :
    |qVec X A l| ≤ (m : ℝ) ^ 2 * √(sq3 X) :=
  sum_two_le fun i j ↦ by
    rw [abs_mul]
    nlinarith [abs_le_sqrt_sq3 X l i j, hA i j, abs_nonneg (X l i j), abs_nonneg (A i j)]

/-! ### Bounds on the frame components -/

section Comp

variable {c : Coeffs m} {ε δ : ℝ} {K : ℝ} (hK0 : 0 ≤ K) (hK : ∀ x ∈ certDomain,
    ‖c.f x‖ ≤ K ∧ ‖c.U x‖ ≤ K ∧ ‖c.K x‖ ≤ K ∧ ‖c.M x‖ ≤ K ∧ ‖c.P x‖ ≤ K ∧
      ‖fderiv ℝ c.f x‖ ≤ K)
  {x : Ten2 m × Ten1 m × ℝ} (hx : x ∈ certDomain)
include hK0 hK hx

omit hK0 in
theorem abs_G_le (l i j k : Fin m) : |c.G x l i j k| ≤ 3 * K := by
  obtain ⟨-, hU, hKx, -⟩ := hK x hx
  have hu : |c.U x j k| ≤ K :=
    (norm_le_pi_norm (c.U x j) k).trans ((norm_le_pi_norm (c.U x) j).trans hU)
  have hk : ∀ a b d e, |c.K x a b d e| ≤ K := fun a b d e ↦
    (norm_le_pi_norm (c.K x a b d) e).trans ((norm_le_pi_norm (c.K x a b) d).trans
      ((norm_le_pi_norm (c.K x a) b).trans ((norm_le_pi_norm (c.K x) a).trans hKx)))
  simp only [Coeffs.G, Coeffs.C]
  calc |kron l i * c.U x j k + (c.K x l i j k - c.K x i l j k)|
      ≤ |kron l i| * |c.U x j k| + (|c.K x l i j k| + |c.K x i l j k|) := by
        rw [← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add le_rfl (abs_sub _ _))
    _ ≤ 1 * K + (K + K) := by
        gcongr
        · exact abs_kron_le l i
        · exact hk _ _ _ _
        · exact hk _ _ _ _
    _ = 3 * K := by ring

theorem abs_contractG_le (X : Ten3 m) (l : Fin m) :
    |c.contractG x X l| ≤ 3 * (m : ℝ) ^ 3 * K * √(sq3 X) := by
  have := sum_three_le (f := fun i j k ↦ c.G x l i j k * X i j k) (b := 3 * K * √(sq3 X))
    fun i j k ↦ by
      rw [abs_mul]
      exact mul_le_mul (abs_G_le hK hx l i j k) (abs_le_sqrt_sq3 X i j k) (abs_nonneg _)
        (by positivity)
  unfold Coeffs.contractG
  linarith

/-- `|D_l f| ≤ (m² + 1) K (1 + w + |X|)` at `z = 1`. -/
theorem abs_Dl_f_le {w : ℝ} (hw : 0 ≤ w) (X : Ten3 m) (l : Fin m) :
    |Dl c.f x.1 X x.2.1 x.2.2 w 1 l| ≤ ((m : ℝ) ^ 2 + 1) * K * (1 + w + √(sq3 X)) := by
  obtain ⟨hA, hp, hg⟩ := certDomain_bounds hx
  have hs := Real.sqrt_nonneg (sq3 X)
  have hm := sq_nonneg (m : ℝ)
  have hN : 0 ≤ (m : ℝ) ^ 2 * (1 + w + √(sq3 X)) := by positivity
  have hgen : ‖gen x.1 X x.2.1 x.2.2 w 1 l‖ ≤ ((m : ℝ) ^ 2 + 1) * (1 + w + √(sq3 X)) := by
    have hr : 0 ≤ ((m : ℝ) ^ 2 + 1) * (1 + w + √(sq3 X)) := by positivity
    rw [gen, norm_prod_le_iff, norm_prod_le_iff, pi_norm_le_iff_of_nonneg hr,
      pi_norm_le_iff_of_nonneg hr]
    refine ⟨fun i ↦ (pi_norm_le_iff_of_nonneg hr).2 fun j ↦ ?_, fun i ↦ ?_, ?_⟩
    · rw [Real.norm_eq_abs]
      have hq := abs_qVec_le hA X l
      calc |X l i j - qVec X x.1 l * x.1 i j| ≤ |X l i j| + |qVec X x.1 l| * |x.1 i j| := by
            rw [← abs_mul]; exact abs_sub _ _
        _ ≤ √(sq3 X) + (m : ℝ) ^ 2 * √(sq3 X) * 1 := by
            gcongr
            · exact abs_le_sqrt_sq3 X l i j
            · exact hA i j
        _ ≤ _ := by nlinarith [mul_nonneg hm (add_nonneg zero_le_one hw)]
    · rw [Real.norm_eq_abs]
      calc |w * x.1 l i - x.2.2 * 1 * kron l i| ≤ |w * x.1 l i| + |x.2.2 * 1 * kron l i| :=
            abs_sub _ _
        _ = w * |x.1 l i| + |x.2.2| * 1 * |kron l i| := by
            rw [abs_mul, abs_mul, abs_mul, abs_one, abs_of_nonneg hw]
        _ ≤ w * 1 + 1 * 1 * 1 := by
            gcongr
            · exact hA l i
            · exact abs_kron_le l i
        _ ≤ _ := by nlinarith
    · rw [Real.norm_eq_abs, one_mul]
      nlinarith [hp l]
  obtain ⟨-, -, -, -, -, hdf⟩ := hK x hx
  calc |Dl c.f x.1 X x.2.1 x.2.2 w 1 l| = ‖fderiv ℝ c.f x (gen x.1 X x.2.1 x.2.2 w 1 l)‖ := by
        rw [Real.norm_eq_abs]; rfl
    _ ≤ ‖fderiv ℝ c.f x‖ * ‖gen x.1 X x.2.1 x.2.2 w 1 l‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ K * (((m : ℝ) ^ 2 + 1) * (1 + w + √(sq3 X))) := mul_le_mul hdf hgen (norm_nonneg _) hK0
    _ = _ := by ring

/-- `|𝓕_l| ≤ (3m² + 1) K (1 + w + |X|)`. -/
theorem abs_calF_le {w : ℝ} (hw : 0 ≤ w) (X : Ten3 m) (l : Fin m) :
    |c.calF x.1 X x.2.1 x.2.2 w l| ≤ (3 * (m : ℝ) ^ 2 + 1) * K * (1 + w + √(sq3 X)) := by
  obtain ⟨hA, -, -⟩ := certDomain_bounds hx
  obtain ⟨hf, -⟩ := hK x hx
  rw [Real.norm_eq_abs] at hf
  have hD := abs_Dl_f_le hK0 hK hx hw X l
  have hq := abs_qVec_le hA X l
  have hs := Real.sqrt_nonneg (sq3 X)
  have hm := sq_nonneg (m : ℝ)
  have ha : 0 ≤ 2 * aExp ∧ 2 * aExp ≤ 2 := by norm_num [aExp]
  unfold Coeffs.calF
  calc |Dl c.f x.1 X x.2.1 x.2.2 w 1 l + 2 * aExp * qVec X x.1 l * c.f x|
      ≤ |Dl c.f x.1 X x.2.1 x.2.2 w 1 l| + 2 * aExp * |qVec X x.1 l| * |c.f x| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg ha.1]
    _ ≤ ((m : ℝ) ^ 2 + 1) * K * (1 + w + √(sq3 X)) + 2 * ((m : ℝ) ^ 2 * √(sq3 X)) * K := by
        gcongr
        exact ha.2
    _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hm hK0) (add_nonneg zero_le_one hw)]

/-- `|Z_l| ≤ (3m³ + 1) K w^{2a} (1 + w + |X|)` for the frame components. -/
theorem abs_fluxZComp_le {T : Ten2 m} (hT : (normalizedA T, x.2.1, x.2.2) = x) (B : Ten3 m)
    (l : Fin m) :
    |c.fluxZComp T B x.2.1 x.2.2 l| ≤
      (3 * (m : ℝ) ^ 3 + 1) * K * normW T ^ (2 * aExp) *
        (1 + normW T + √(sq3 (normalizedX T B))) := by
  obtain ⟨-, -, -, hM, hP, -⟩ := hK x hx
  have hm : |c.M x l| ≤ K := (norm_le_pi_norm (c.M x) l).trans hM
  have hp : |c.P x l| ≤ K := (norm_le_pi_norm (c.P x) l).trans hP
  have hG := abs_contractG_le hK0 hK hx (normalizedX T B) l
  have hw : 0 ≤ normW T := Real.sqrt_nonneg _
  have hs := Real.sqrt_nonneg (sq3 (normalizedX T B))
  have hW : 0 ≤ normW T ^ (2 * aExp) := Real.rpow_nonneg hw _
  have hm3 : 0 ≤ (m : ℝ) ^ 3 := by positivity
  unfold Coeffs.fluxZComp
  rw [hT, abs_mul, abs_of_nonneg hW]
  have hin : |c.contractG x (normalizedX T B) l + normW T * c.M x l + c.P x l| ≤
      (3 * (m : ℝ) ^ 3 + 1) * K * (1 + normW T + √(sq3 (normalizedX T B))) := by
    calc _ ≤ |c.contractG x (normalizedX T B) l| + normW T * |c.M x l| + |c.P x l| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans ?_) le_rfl)
          rw [abs_mul, abs_of_nonneg hw]
      _ ≤ 3 * (m : ℝ) ^ 3 * K * √(sq3 (normalizedX T B)) + normW T * K + K := by gcongr
      _ ≤ _ := by
          nlinarith [mul_nonneg (mul_nonneg hm3 hK0) (add_nonneg zero_le_one hw),
            mul_nonneg hK0 hs]
  calc normW T ^ (2 * aExp) * |c.contractG x (normalizedX T B) l + normW T * c.M x l + c.P x l|
      ≤ normW T ^ (2 * aExp) * ((3 * (m : ℝ) ^ 3 + 1) * K *
          (1 + normW T + √(sq3 (normalizedX T B)))) :=
        mul_le_mul_of_nonneg_left hin hW
    _ = _ := by ring

end Comp

end Tensor

/-! ### The norm of the third derivative -/

variable {n : ℕ}

/-- `|B|` at `x/|x|`: the norm of the third derivative of `u` on the tangent space of the sphere
(zero at the origin). -/
def fluxBNorm (u : E n → ℝ) (x : E n) : ℝ :=
  if x = 0 then 0 else √(sq3 (frameB u (sphereFrame (radialProj x)) (radialProj x)))

theorem isZeroHomogeneous_fluxBNorm (u : E n → ℝ) : IsZeroHomogeneous (fluxBNorm u) := by
  intro r hr x
  simp only [fluxBNorm, smul_eq_zero, hr.ne', false_or, radialProj_smul hr]

theorem fluxBNorm_nonneg (u : E n → ℝ) (x : E n) : 0 ≤ fluxBNorm u x := by
  unfold fluxBNorm
  split_ifs
  · exact le_rfl
  · exact Real.sqrt_nonneg _

/-- `|B|` may be computed in any orthonormal frame. -/
theorem fluxBNorm_eq_of_frame {u : E n → ℝ} {x : E n} {ι : E (n - 1) →ₗᵢ[ℝ] E n} (hx : x ≠ 0)
    (hι : ∀ v, ⟪ι v, radialProj x⟫ = 0) :
    fluxBNorm u x = √(sq3 (frameB u ι (radialProj x))) := by
  have hy := norm_radialProj hx
  rw [fluxBNorm, ite_eq_right hx, frameB_frameChange hy (inner_sphereFrame hy) hι,
    sq3_act3 (isOrth_frameChange hy (inner_sphereFrame hy) hι)]

/-! ### The field bounds -/

/-- **Uniform field bounds.** For certificate data in `ℝ^{n-1}` with constants `ε > 0`, `δ`,
there is a constant `C_F ≥ 1`, depending only on the certificate, such that at every unit vector
`x₀` near which `u` is one-homogeneous, smooth and harmonic, with `w(x₀) > 0` and
`|∇u(x₀)|² ≤ 1`, `|h| ≤ C_F w^a`, `|∇h| ≤ C_F w^a(1 + w + |B|/w)` and
`|Z| ≤ C_F w^{2a}(1 + w + |B|/w)`. -/
theorem exists_fieldBound_const {c : Coeffs (n - 1)} {ε δ : ℝ}
    (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) :
    ∃ Cf ≥ (1 : ℝ), ∀ (u : E n → ℝ) (x₀ : E n), IsOneHomogeneous u → ‖x₀‖ = 1 →
      ContDiffAt ℝ ∞ u x₀ → (∀ᶠ y in 𝓝 x₀, Δ u y = 0) → 0 < fluxW u x₀ →
      ‖∇ u x₀‖ ^ 2 ≤ 1 →
      |fluxH c u x₀| ≤ Cf * fluxW u x₀ ^ aExp ∧
      ‖∇ (fluxH c u) x₀‖ ≤
        Cf * fluxW u x₀ ^ aExp * (1 + fluxW u x₀ + fluxBNorm u x₀ / fluxW u x₀) ∧
      ‖fluxZ c u x₀‖ ≤
        Cf * fluxW u x₀ ^ (2 * aExp) * (1 + fluxW u x₀ + fluxBNorm u x₀ / fluxW u x₀) := by
  obtain ⟨K, hK0, hK⟩ := exists_coeff_bound hc
  set m : ℝ := ((n - 1 : ℕ) : ℝ) with hmdef
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  set CF := 3 * m ^ 2 + 1 with hCF
  set CZ := 3 * m ^ 3 + 1 with hCZ
  set G := CF * (m + 1 / ε) with hG
  have hCF0 : 0 ≤ CF := by positivity
  have hCZ0 : 0 ≤ CZ := by positivity
  have hε1 : 0 ≤ 1 / ε := by positivity
  have hG0 : 0 ≤ G := by positivity
  -- `m CF² / (4ε) ≤ G²`
  have hGsq : m * CF ^ 2 / (4 * ε) ≤ G ^ 2 := by
    rw [div_le_iff₀ (by positivity), hG]
    have hεinv : ε * (1 / ε) = 1 := by field_simp
    have h1 : m * CF ^ 2 ≤ 4 * ε * (CF ^ 2 * (m * (1 / ε))) := by
      have : 4 * ε * (CF ^ 2 * (m * (1 / ε))) = 4 * (m * CF ^ 2) * (ε * (1 / ε)) := by ring
      rw [this, hεinv]
      nlinarith [mul_nonneg hm0 (sq_nonneg CF)]
    have h2 : CF ^ 2 * (m * (1 / ε)) ≤ (CF * (m + 1 / ε)) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg CF) (sq_nonneg m), mul_nonneg (sq_nonneg CF)
        (sq_nonneg (1 / ε)), mul_nonneg (sq_nonneg CF) (mul_nonneg hm0 hε1)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * ε)]
  refine ⟨1 + (1 + K) + m * CZ * K + G * K,
    (by linarith [mul_nonneg (mul_nonneg hm0 hCZ0) hK0, mul_nonneg hG0 hK0]), ?_⟩
  intro u x₀ hhom hx₀ hu hΔ hw hs
  have hu4 : ∀ᶠ y in 𝓝 x₀, ContDiffAt ℝ 4 u y :=
    (hu.of_le (by simp)).eventually (by simp)
  have hJ := ConeJets.isConeJet_ofHarmonicHomogeneous hx₀ hhom hu4 hΔ
  set J := ConeJets.ofHarmonicHomogeneous u x₀ hx₀ with hJdef
  have hu' : ContDiffAt ℝ ∞ u J.x₀ := hu
  have hs' := hJ.admissible_of_normSq_gradient_le hs
  have hwJ : fluxW u x₀ = normW J.T := hJ.fluxW_self
  have hw' : sq2 J.T ≠ 0 := by
    rw [hwJ] at hw
    exact normW_pos_iff.1 hw
  have hx : (normalizedA J.T, J.p, J.g) ∈ certDomain :=
    ⟨hJ.isSTF2_normalizedA, sq2_normalizedA hw', hs'⟩
  have hfε : ε ≤ c.f (normalizedA J.T, J.p, J.g) :=
    hc.f_ge _ _ _ hJ.isSTF2_normalizedA (sq2_normalizedA hw') hs'
  have hf : 0 < c.f (normalizedA J.T, J.p, J.g) := lt_of_lt_of_le hε hfε
  have hfK : c.f (normalizedA J.T, J.p, J.g) ≤ K := by
    have := (hK _ hx).1
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have hx0 : x₀ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hx₀
    norm_num at hx₀
  have hr : radialProj x₀ = x₀ := radialProj_of_norm_eq_one hx₀
  have hι : ∀ v, ⟪J.ι v, radialProj x₀⟫ = 0 := by
    rw [hr]
    exact hJ.inner_ι
  have hBn : fluxBNorm u x₀ / fluxW u x₀ = √(sq3 (normalizedX J.T J.B)) := by
    rw [fluxBNorm_eq_of_frame hx0 hι, hr, hwJ, sqrt_sq3_normalizedX]
    rfl
  rw [hBn, hwJ]
  set w := normW J.T with hwdef
  set N := 1 + w + √(sq3 (normalizedX J.T J.B)) with hN
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hN0 : 0 ≤ N := by positivity
  have hwa : 0 ≤ w ^ aExp := Real.rpow_nonneg hw0 _
  have hw2a : 0 ≤ w ^ (2 * aExp) := Real.rpow_nonneg hw0 _
  have hpow : (w ^ aExp) ^ 2 = w ^ (2 * aExp) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hw0]
    ring_nf
  refine ⟨?_, ?_, ?_⟩
  · -- `|h| ≤ C_F w^a`
    rw [show fluxH c u x₀ = _ from hJ.fluxH_self hc,
      abs_of_nonneg (mul_nonneg hwa (Real.sqrt_nonneg _))]
    have hsq : √(c.f (normalizedA J.T, J.p, J.g)) ≤ 1 + K := by
      calc √(c.f (normalizedA J.T, J.p, J.g)) ≤ √((1 + K) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = 1 + K := Real.sqrt_sq (by linarith)
    calc w ^ aExp * √(c.f (normalizedA J.T, J.p, J.g)) ≤ w ^ aExp * (1 + K) :=
          mul_le_mul_of_nonneg_left hsq hwa
      _ = (1 + K) * w ^ aExp := by ring
      _ ≤ (1 + (1 + K) + m * CZ * K + G * K) * w ^ aExp :=
          mul_le_mul_of_nonneg_right
            (by linarith [mul_nonneg (mul_nonneg hm0 hCZ0) hK0, mul_nonneg hG0 hK0]) hwa
  · -- `|∇h| ≤ C_F w^a N`
    have hF : ∀ l, |c.calF (normalizedA J.T) (normalizedX J.T J.B) J.p J.g w l| ≤ CF * K * N :=
      fun l ↦ abs_calF_le (x := (normalizedA J.T, J.p, J.g)) hK0 hK hx hw0 _ l
    have hsq1 : sq1 (c.calF (normalizedA J.T) (normalizedX J.T J.B) J.p J.g w) ≤
        m * (CF * K * N) ^ 2 := by
      unfold sq1
      calc ∑ l, c.calF (normalizedA J.T) (normalizedX J.T J.B) J.p J.g w l ^ 2
          ≤ ∑ _l : Fin (n - 1), (CF * K * N) ^ 2 := sum_le_sum fun l _ ↦ by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) (hF l) 2
        _ = m * (CF * K * N) ^ 2 := by
            simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
            rfl
    have hgrad := hJ.normSq_gradient_fluxH hc hu' hw' hf
    have hle : ‖∇ (fluxH c u) J.x₀‖ ^ 2 ≤ (G * K * w ^ aExp * N) ^ 2 := by
      rw [hgrad]
      have ht : 0 ≤ w ^ (2 * aExp) * (K * N) ^ 2 := by positivity
      calc w ^ (2 * aExp) * sq1 (c.calF (normalizedA J.T) (normalizedX J.T J.B) J.p J.g w) /
            (4 * c.f (normalizedA J.T, J.p, J.g))
          ≤ w ^ (2 * aExp) * (m * (CF * K * N) ^ 2) / (4 * ε) := by
            gcongr
        _ = m * CF ^ 2 / (4 * ε) * (w ^ (2 * aExp) * (K * N) ^ 2) := by ring
        _ ≤ G ^ 2 * (w ^ (2 * aExp) * (K * N) ^ 2) := mul_le_mul_of_nonneg_right hGsq ht
        _ = (G * K * w ^ aExp * N) ^ 2 := by rw [← hpow]; ring
    have hle' : ‖∇ (fluxH c u) J.x₀‖ ≤ G * K * w ^ aExp * N :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle
    calc ‖∇ (fluxH c u) x₀‖ ≤ G * K * w ^ aExp * N := hle'
      _ = G * K * (w ^ aExp * N) := by ring
      _ ≤ (1 + (1 + K) + m * CZ * K + G * K) * (w ^ aExp * N) :=
          mul_le_mul_of_nonneg_right (by linarith [mul_nonneg (mul_nonneg hm0 hCZ0) hK0])
            (by positivity)
      _ = _ := by ring
  · -- `|Z| ≤ C_F w^{2a} N`
    have hZ : fluxZ c u x₀ = ∑ l, c.fluxZComp J.T J.B J.p J.g l • frameVec J.ι l := by
      rw [fluxZ_eq_of_frame hc hx0 hι, hr]
      rfl
    have hl : ∀ l, |c.fluxZComp J.T J.B J.p J.g l| ≤ CZ * K * w ^ (2 * aExp) * N :=
      fun l ↦ abs_fluxZComp_le (x := (normalizedA J.T, J.p, J.g)) hK0 hK hx rfl J.B l
    rw [hZ]
    calc ‖∑ l, c.fluxZComp J.T J.B J.p J.g l • frameVec J.ι l‖
        ≤ ∑ l, ‖c.fluxZComp J.T J.B J.p J.g l • frameVec J.ι l‖ := norm_sum_le _ _
      _ = ∑ l, |c.fluxZComp J.T J.B J.p J.g l| := by
          simp only [norm_smul, norm_frameVec, mul_one, Real.norm_eq_abs]
      _ ≤ ∑ _l : Fin (n - 1), CZ * K * w ^ (2 * aExp) * N := sum_le_sum fun l _ ↦ hl l
      _ = m * CZ * K * (w ^ (2 * aExp) * N) := by
          simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← hmdef]; ring
      _ ≤ (1 + (1 + K) + m * CZ * K + G * K) * (w ^ (2 * aExp) * N) :=
          mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hG0 hK0]) (by positivity)
      _ = _ := by ring

/-! ### The field bounds on the working cones -/

namespace ConeData

/-- **Uniform field bounds on a cone**, at unit regular points of `D` with `w > 0` and
`|∇u|² ≤ 1`, with a constant independent of the cone. -/
theorem exists_fieldBound_const {c : Coeffs (n - 1)} {ε δ : ℝ}
    (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) :
    ∃ Cf ≥ (1 : ℝ), ∀ (C : ConeData n) (x : E n), x ∈ C.D → x ∉ C.Sing → ‖x‖ = 1 →
      ‖∇ C.u x‖ ^ 2 ≤ 1 → 0 < fluxW C.u x →
      |fluxH c C.u x| ≤ Cf * fluxW C.u x ^ aExp ∧
      ‖∇ (fluxH c C.u) x‖ ≤
        Cf * fluxW C.u x ^ aExp * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x) ∧
      ‖fluxZ c C.u x‖ ≤
        Cf * fluxW C.u x ^ (2 * aExp) * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x) := by
  obtain ⟨Cf, hCf, hb⟩ := Gen.exists_fieldBound_const hc hε
  refine ⟨Cf, hCf, fun C x hx hxS hx₁ hs hw ↦ ?_⟩
  obtain ⟨hu, hΔ⟩ := OnePhaseDimension.ConeData.contDiffAt_u_and_eventually_laplacian hx hxS
  exact hb C.u x C.isOneHomogeneous_u hx₁ hu hΔ hw hs

/-- **Uniform field bounds on original cones** (`Sing = {0}`). -/
theorem exists_fieldBound_const_orig {c : Coeffs (n - 1)} {ε δ : ℝ}
    (hc : CertificateHolds (n - 1) ε δ c) (hε : 0 < ε) :
    ∃ Cf ≥ (1 : ℝ), ∀ (C : ConeData n), C.Sing = {0} → ∀ x ∈ C.D, ‖x‖ = 1 →
      0 < fluxW C.u x →
      |fluxH c C.u x| ≤ Cf * fluxW C.u x ^ aExp ∧
      ‖∇ (fluxH c C.u) x‖ ≤
        Cf * fluxW C.u x ^ aExp * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x) ∧
      ‖fluxZ c C.u x‖ ≤
        Cf * fluxW C.u x ^ (2 * aExp) * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x) := by
  obtain ⟨Cf, hCf, hb⟩ := exists_fieldBound_const hc hε
  refine ⟨Cf, hCf, fun C hS x hx hx₁ hw ↦ hb C x hx ?_ hx₁ (C.sSq_le_one hS hx) hw⟩
  rw [hS]
  exact C.ne_zero_of_mem_D hx

end ConeData

end Gen

/-! ### Dimension six -/

/-- Squared norm of a three-tensor, `|X|² = ∑ X_{ijk}²`. -/
def sq3 (X : Ten3) : ℝ := ∑ i, ∑ j, ∑ k, X i j k ^ 2

theorem sq3_nonneg (X : Ten3) : 0 ≤ sq3 X := Gen.sq3_nonneg X

theorem sq1_nonneg (p : Ten1) : 0 ≤ sq1 p := Gen.sq1_nonneg p

/-- `|B|` at `x/|x|` (zero at the origin). -/
def fluxBNorm (u : E 6 → ℝ) (x : E 6) : ℝ := Gen.fluxBNorm u x

theorem fluxBNorm_nonneg (u : E 6 → ℝ) (x : E 6) : 0 ≤ fluxBNorm u x := Gen.fluxBNorm_nonneg u x

/-- `|B|` may be computed in any orthonormal frame. -/
theorem fluxBNorm_eq_of_frame {u : E 6 → ℝ} {x : E 6} {ι : E (6 - 1) →ₗᵢ[ℝ] E 6} (hx : x ≠ 0)
    (hι : ∀ v, ⟪ι v, radialProj x⟫ = 0) :
    fluxBNorm u x = √(sq3 (frameB u ι (radialProj x))) :=
  Gen.fluxBNorm_eq_of_frame hx hι

/-- **Uniform field bounds in `ℝ⁶`.** There is a constant `C_F ≥ 1`, depending only on the
certificate coefficients, such that at every unit vector `x₀` near which `u` is one-homogeneous,
smooth and harmonic, with `w(x₀) > 0` and `|∇u(x₀)|² ≤ 1`, `|h| ≤ C_F w^a`,
`|∇h| ≤ C_F w^a(1 + w + |B|/w)` and `|Z| ≤ C_F w^{2a}(1 + w + |B|/w)`. -/
theorem exists_fieldBound_const {c : Coeffs} (hc : CertificateHolds c) :
    ∃ Cf ≥ (1 : ℝ), ∀ (u : E 6 → ℝ) (x₀ : E 6), IsOneHomogeneous u → ‖x₀‖ = 1 →
      ContDiffAt ℝ ∞ u x₀ → (∀ᶠ y in 𝓝 x₀, Δ u y = 0) → 0 < fluxW u x₀ →
      ‖∇ u x₀‖ ^ 2 ≤ 1 →
      |fluxH c u x₀| ≤ Cf * fluxW u x₀ ^ aExp ∧
      ‖∇ (fluxH c u) x₀‖ ≤
        Cf * fluxW u x₀ ^ aExp * (1 + fluxW u x₀ + fluxBNorm u x₀ / fluxW u x₀) ∧
      ‖fluxZ c u x₀‖ ≤
        Cf * fluxW u x₀ ^ (2 * aExp) * (1 + fluxW u x₀ + fluxBNorm u x₀ / fluxW u x₀) :=
  Gen.exists_fieldBound_const (n := 6) hc.toGen εStar_pos

namespace ConeData

/-- **Uniform field bounds on a cone in `ℝ⁶`**, at unit regular points of `D` with `w > 0` and
`|∇u|² ≤ 1`, with a constant independent of the cone. -/
theorem exists_fieldBound_const {c : Coeffs} (hc : CertificateHolds c) :
    ∃ Cf ≥ (1 : ℝ), ∀ (C : ConeData 6) (x : E 6), x ∈ C.D → x ∉ C.Sing → ‖x‖ = 1 →
      ‖∇ C.u x‖ ^ 2 ≤ 1 → 0 < fluxW C.u x →
      |fluxH c C.u x| ≤ Cf * fluxW C.u x ^ aExp ∧
      ‖∇ (fluxH c C.u) x‖ ≤
        Cf * fluxW C.u x ^ aExp * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x) ∧
      ‖fluxZ c C.u x‖ ≤
        Cf * fluxW C.u x ^ (2 * aExp) * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x) :=
  Gen.ConeData.exists_fieldBound_const (n := 6) hc.toGen εStar_pos

/-- **Uniform field bounds on original cones in `ℝ⁶`** (`Sing = {0}`). -/
theorem exists_fieldBound_const_orig {c : Coeffs} (hc : CertificateHolds c) :
    ∃ Cf ≥ (1 : ℝ), ∀ (C : ConeData 6), C.Sing = {0} → ∀ x ∈ C.D, ‖x‖ = 1 →
      0 < fluxW C.u x →
      |fluxH c C.u x| ≤ Cf * fluxW C.u x ^ aExp ∧
      ‖∇ (fluxH c C.u) x‖ ≤
        Cf * fluxW C.u x ^ aExp * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x) ∧
      ‖fluxZ c C.u x‖ ≤
        Cf * fluxW C.u x ^ (2 * aExp) * (1 + fluxW C.u x + fluxBNorm C.u x / fluxW C.u x) :=
  Gen.ConeData.exists_fieldBound_const_orig (n := 6) hc.toGen εStar_pos

end ConeData

namespace IsSuspension

/-- **Uniform field bounds on suspensions**, at unit points of the component `D̃`. -/
theorem exists_fieldBound_const {c : Coeffs} (hc : CertificateHolds c) :
    ∃ Cf ≥ (1 : ℝ), ∀ (O : ConeData 5) (W : ConeData 6), IsSuspension W O → O.Sing = {0} →
      ∀ x ∈ W.D, ‖x‖ = 1 → 0 < fluxW W.u x →
      |fluxH c W.u x| ≤ Cf * fluxW W.u x ^ aExp ∧
      ‖∇ (fluxH c W.u) x‖ ≤
        Cf * fluxW W.u x ^ aExp * (1 + fluxW W.u x + fluxBNorm W.u x / fluxW W.u x) ∧
      ‖fluxZ c W.u x‖ ≤
        Cf * fluxW W.u x ^ (2 * aExp) * (1 + fluxW W.u x + fluxBNorm W.u x / fluxW W.u x) := by
  obtain ⟨Cf, hCf, hb⟩ := ConeData.exists_fieldBound_const hc
  refine ⟨Cf, hCf, fun O W hW hO x hx hx₁ hw ↦
    hb W x hx ?_ hx₁ (hW.sSq_lt_one hO hx).le hw⟩
  rw [hW.sing_eq]
  exact O.ne_zero_of_mem_D (hW.mem_D_iff.1 hx)

end IsSuspension

end OnePhaseDimension
