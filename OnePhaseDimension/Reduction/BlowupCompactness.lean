/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Reduction.Bridges
public import OnePhaseDimension.Reduction.Lattice
public import PerronVariational.Stationary.DirectionalStable.Blowup
public import EllipticBernoulli.Nondegeneracy.Minimizer
public import EllipticBernoulli.Classical.BlowupExtraction

/-!
# Compactness of blowups and minimality of the limit

Let `u ≥ 0` be a continuous global minimizer of the one-phase energy (volume coefficient `1`) in
`ℝᵈ`, `d ≥ 2`, and `x₀` a free boundary point. Along a subsequence of every `r_j → 0⁺`, the
rescalings `u_{x₀,r_j}(y) = u(x₀ + r_j y)/r_j` converge locally uniformly to a continuous,
nonnegative global minimizer `U₀` with `U₀(0) = 0` which is positive somewhere.

## Main results

* `regularity_of_isLocalEnergyMinimizer`: a continuous nonnegative global minimizer is locally
  Lipschitz and harmonic in its positivity set.
* `exists_blowup_limit_proof`: compactness, nondegeneracy and minimality of blowup limits.

## Proof

* The rescalings are uniformly Lipschitz on the balls `B_{δ/r_j}` (local Lipschitz continuity of
  `u` near `x₀`) and vanish at the origin (`u(x₀) = 0`), so a subsequence converges locally
  uniformly (Arzelà–Ascoli).
* A global minimizer is a downward and an upward minimizer (`Reduction/Lattice.lean`). Each of
  these one-sided properties passes to blowup limits (Abedin–Feldman–Stinson, Lemma 2.12 and
  Corollary 2.13), and a function which is both a downward and an upward minimizer is a global
  minimizer, by the lattice identity `J(u ∨ v) + J(u ∧ v) = J(u) + J(v)`.
* Nondegeneracy of downward minimizers (Alt–Caffarelli, Lemma 3.4) gives
  `sup_{B̄_r(x₀)} u ≥ c r` at every scale, so `sup_{B̄_1} u_{x₀,r_j} ≥ c` and the limit is positive
  somewhere.

## Differences from the source

The 2026-09-24 version obtains minimality of the limit from strong `H¹_loc` convergence and
`L¹_loc` convergence of the positivity indicators (Velichkov, Proposition 6.2), and
nondegeneracy from Velichkov, Proposition 4.1. We use instead the stability of downward and
upward minimality under locally uniform convergence of uniformly Lipschitz functions, combined
with the lattice identity, and the nondegeneracy of downward minimizers. The strong convergence
statements are not formalized (they are not needed).

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
* F. Abedin, W. M. Feldman, K. Stinson, *Variational properties of Perron's extremal solutions
  in the Bernoulli one-phase problem*, arXiv:2609.14981, Lemma 2.12 and Corollary 2.13.
* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), Lemma 3.4.
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer (2023), Proposition 4.1, Proposition 6.2.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff Laplacian NNReal

@[expose] public section

namespace OnePhaseDimension

open EllipticBernoulli

variable {d : ℕ}

/-- A continuous nonnegative global minimizer in `ℝᵈ`, `d ≥ 2`, is locally Lipschitz, and `C²`
and harmonic in its positivity set (it is its own continuous representative). -/
theorem regularity_of_isLocalEnergyMinimizer (hd : 2 ≤ d) {u : E d → ℝ} (hc : Continuous u)
    (hnn : ∀ x, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer univ (fun _ ↦ 1) u) :
    LocallyLipschitz u ∧ ContDiffOn ℝ 2 u (posSet u univ) ∧
      ∀ x ∈ posSet u univ, Δ u x = 0 := by
  obtain ⟨v, hvu, hlip, hcont, -, hsm, hharm, -⟩ :=
    exists_continuous_minimizer_representative hd (ae_of_all _ hnn) hmin
  obtain rfl : v = u := (Continuous.ae_eq_iff_eq volume hcont hc).1 hvu
  exact ⟨hlip, (hsm.of_le (by simp)).mono fun x hx ↦ hx.2,
    fun x hx ↦ hharm x hx.2⟩

/-- **Blowup limits at free boundary points** (Velichkov 2023, Proposition 4.1 and
Proposition 6.2). Let `u ≥ 0` be a continuous global minimizer in `ℝᵈ`, `d ≥ 2`, and
`x₀ ∈ ∂{u > 0}`. Along a subsequence of any `r_j → 0⁺`, the rescalings `u_{x₀,r_j}` converge
locally uniformly to a continuous, nonnegative global minimizer `U₀` which is positive somewhere,
with `U₀ 0 = 0`. -/
theorem exists_blowup_limit_proof {d : ℕ} (hd : 2 ≤ d) {u : E d → ℝ} (hc : Continuous u)
    (hnn : ∀ x, 0 ≤ u x) (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u)
    {x₀ : E d} (hx₀ : x₀ ∈ freeBoundary u Set.univ) {r : ℕ → ℝ} (hr : ∀ j, 0 < r j)
    (hr₀ : Tendsto r atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ U₀ : E d → ℝ,
      TendstoLocallyUniformly (fun j ↦ blowup u x₀ (r (φ j))) U₀ atTop ∧
      Continuous U₀ ∧ (∀ y, 0 ≤ U₀ y) ∧ IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) U₀ ∧
      (∃ y, 0 < U₀ y) ∧ U₀ 0 = 0 := by
  obtain ⟨hlip, hc2, hΔ⟩ := regularity_of_isLocalEnergyMinimizer hd hc hnn hmin
  have hopen : IsOpen (posSet u univ) :=
    hc.continuousOn.isOpen_inter_preimage isOpen_univ isOpen_Ioi
  -- `u(x₀) = 0`
  have hux₀ : u x₀ = 0 := by
    refine le_antisymm (not_lt.1 fun hpos ↦ hx₀.1.2 ?_) (hnn x₀)
    rw [hopen.interior_eq]
    exact ⟨mem_univ _, hpos⟩
  have hdown := isDownwardMinimizer_of_contDiffOn isOpen_univ hmin hopen hc2 hΔ
  have hup := isUpwardMinimizer_of_contDiffOn isOpen_univ hmin hopen hc2 hΔ
  -- uniform Lipschitz bounds for the rescalings
  obtain ⟨L, t, ht, hLt⟩ := hlip x₀
  obtain ⟨δ, hδ, hδt⟩ := Metric.mem_nhds_iff.1 ht
  have hLip : ∀ k, LipschitzOnWith L (blowup u x₀ (r k)) (ball 0 (δ / r k)) := by
    intro k
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦
      PerronVariational.DirectionalStable.dist_blowup_le (hr k) (hLt.mono hδt) ?_ ?_
    all_goals
      rw [mem_ball_zero_iff, lt_div_iff₀ (hr k)] at *
      rwa [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hr k), mul_comm]
  have hρ : Tendsto (fun k ↦ δ / r k) atTop atTop := by
    simp only [div_eq_mul_inv]
    exact (tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.2 ⟨hr₀, Eventually.of_forall hr⟩)).const_mul_atTop hδ
  have hzero : ∀ k, blowup u x₀ (r k) 0 = 0 := fun k ↦ by simp [blowup, hux₀]
  obtain ⟨φ, hφ, U₀, hU₀L, hconv⟩ := exists_blowup_subseq hρ (fun k ↦ div_pos hδ (hr k)) hLip
    (M := 0) fun k ↦ by rw [hzero, abs_zero]
  have hpt : ∀ y, Tendsto (fun j ↦ blowup u x₀ (r (φ j)) y) atTop (𝓝 (U₀ y)) := fun y ↦
    (tendstoLocallyUniformlyOn_univ.2 hconv).tendsto_at (mem_univ y)
  refine ⟨φ, hφ, U₀, hconv, hU₀L.continuous, fun y ↦ ?_, ?_, ?_, ?_⟩
  · exact ge_of_tendsto' (hpt y) fun j ↦ div_nonneg (hnn _) (hr _).le
  · -- minimality of the limit
    have hbl : PerronVariational.IsBlowupLimit u x₀ U₀ :=
      ⟨fun j ↦ r (φ j), fun j ↦ hr _, hr₀.comp hφ.tendsto_atTop, hconv⟩
    have hD : IsDownwardMinimizer univ (fun _ ↦ 1) U₀ :=
      PerronVariational.DirectionalStable.blowup_isDownwardMinimizer isOpen_univ
        continuousOn_const (Qmax := 1) (fun _ _ ↦ by norm_num) hlip.locallyLipschitzOn
        (mem_univ x₀) hdown hbl
    have hU : IsUpwardMinimizer univ (fun _ ↦ 1) U₀ :=
      PerronVariational.DirectionalStable.blowup_isUpwardMinimizer' isOpen_univ
        continuousOn_const (Qmax := 1) (fun _ _ ↦ by norm_num) hlip.locallyLipschitzOn
        (mem_univ x₀) hup hbl
    exact isLocalEnergyMinimizer_of_isDownwardMinimizer_of_isUpwardMinimizer isOpen_univ
      measurable_const ⟨1, fun _ _ ↦ by norm_num⟩ hD hU
  · -- nondegeneracy
    set c : ℝ := 1 / (8 * d * Real.exp ((d : ℝ) / 2)) with hc_def
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hcpos : 0 < c := by positivity
    have hnd : ∀ j, ∃ y ∈ closedBall (0 : E d) 1, c ≤ blowup u x₀ (r j) y := by
      intro j
      obtain ⟨z, hz, hcz⟩ := IsDownwardMinimizer.exists_le_of_closedBall_subset (by omega)
        isOpen_univ hdown hlip.locallyLipschitzOn (fun y _ ↦ hnn y) one_pos
        (fun _ _ ↦ le_rfl) ⟨1, fun _ _ ↦ le_rfl⟩ measurable_const x₀ hx₀.1.1 (r j) (hr j)
        (subset_univ _)
      refine ⟨(r j)⁻¹ • (z - x₀), ?_, ?_⟩
      · rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hr j),
          inv_mul_le_iff₀ (hr j), mul_one, ← dist_eq_norm]
        exact hz
      · rw [blowup, smul_smul, mul_inv_cancel₀ (hr j).ne', one_smul, add_sub_cancel,
          le_div_iff₀ (hr j)]
        exact hcz
    have hunif := (Metric.tendstoUniformlyOn_iff.1
      ((tendstoLocallyUniformly_iff_forall_isCompact.1 hconv) _ (isCompact_closedBall 0 1)))
      (c / 2) (half_pos hcpos)
    obtain ⟨j, hj⟩ := hunif.exists
    obtain ⟨y, hy, hcy⟩ := hnd (φ j)
    refine ⟨y, ?_⟩
    have := hj y hy
    rw [Real.dist_eq, abs_lt] at this
    linarith
  · exact tendsto_nhds_unique (hpt 0) (tendsto_const_nhds.congr fun j ↦ (hzero _).symm)

end OnePhaseDimension
