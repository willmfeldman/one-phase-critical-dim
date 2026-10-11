/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Boundary.Kernel

/-!
# The boundary inequality at diagonal data

For `x ∈ ℝ⁴` with `R(x) = ∑ xᵢ² + (∑ xᵢ)² = 1` and `∑ xᵢ ≥ 0`, at `A = diag(x, λ)`,
`λ = -∑ xᵢ`, `p = e₅`, we prove `𝓢 ≥ δ*`:

* the boundary Gram term `Λ` (`boundaryGram`) is nonnegative when `∑ xᵢ ≥ 0`;
* on `R = 1`, `Λ + 1/4 - 𝓢 = ∑_β e_β m_β(x)` with the eleven printed coefficients, by the
  kernel identity and the soundness of homogenization;
* `|m_β| ≤ 1` since `|xᵢ| ≤ 1`, so `𝓢 ≥ 1/4 - ∑|e_β| = δ*`.

## Differences from the source

The 2026-09-24 version evaluates `𝓢` with the trace reductions `tr A² = 1` and then
homogenizes; here every trace is kept as its exact value `∑ xᵢ^k + λ^k`, so the polynomial of
`𝓢` is exact for all `x`, and the same eleven coefficients result after homogenization. The
averaging over `S₄` is carried out on the polynomial side: instead of using that `𝓢` is
symmetric, we check that the homogenized remainder equals `∑_β e_β ∑_σ x^{σ·β}` exactly, which
also shows the symmetry. The multiplier `ρ = ∑ xᵢ` of the second boundary block is applied
outside the average (it is symmetric).

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate.Boundary

open Poly4 Data

variable (x : Fin 4 → ℝ)

/-! ### The boundary Gram term -/

/-- `J_c(y) = Q⁻¹ ∑_t c_{tc} y^{β_t}` for column `c` of a boundary block. -/
def jFun (b : Block) (c : ℕ) (y : Fin 4 → ℝ) : ℝ :=
  (b.rows.map fun r => (r.2.2.getD c 0 : ℝ) * (wordMono r.1 r.2.1).eval y).sum / certQ

/-- The multiplier `ρ`: `1` in mode `I`, `∑ xᵢ` in mode `H`. -/
def rhoFun (b : Block) (y : Fin 4 → ℝ) : ℝ := if b.mode = .H then ∑ i, y i else 1

/-- The boundary Gram term `Λ(x) = ∑_blocks ρ(x) Av(∑_c J_c²)(x)`. -/
def boundaryGram : ℝ :=
  (tableIIBoundary.map fun b => rhoFun b x *
    ((perms4.map fun σ => ((List.range 5).map fun c => jFun b c (x ∘ σ) ^ 2).sum).sum / 24)).sum

theorem boundaryGram_nonneg (hx : 0 ≤ ∑ i, x i) : 0 ≤ boundaryGram x := by
  refine List.sum_nonneg fun t ht => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 ht
  refine mul_nonneg ?_ (div_nonneg (List.sum_nonneg fun u hu => ?_) (by norm_num))
  · unfold rhoFun; split_ifs <;> first | exact hx | norm_num
  · obtain ⟨σ, -, rfl⟩ := List.mem_map.1 hu
    exact List.sum_nonneg fun v hv => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hv
      exact sq_nonneg _

theorem eval_jPoly (b : Block) (c : ℕ) (y : Fin 4 → ℝ) :
    eval (jPoly b c) y = certQ * jFun b c y := by
  rw [jPoly, eval_ofList, jFun, mul_div_cancel₀ _ (by norm_num [certQ]), eval, List.map_map]
  rfl

theorem eval_rhoPoly (b : Block) : eval (rhoPoly b) x = rhoFun b x := by
  unfold rhoPoly rhoFun
  split_ifs
  · rw [eval_sum, List.map_map, Fin.sum_univ_def]
    simp [Function.comp_def, eval_var]
  · simp [eval_const]

/-- The contribution of one boundary block. -/
theorem eval_blockGram (b : Block) :
    eval (mul (rhoPoly b) (Poly4.sum (perms4.map fun σ => subst σ (gramPoly b)))) x =
      24 * certQ ^ 2 * (rhoFun b x *
        ((perms4.map fun σ => ((List.range 5).map fun c => jFun b c (x ∘ σ) ^ 2).sum).sum /
          24)) := by
  rw [eval_mul, eval_rhoPoly, eval_sum, List.map_map]
  have h : ∀ σ : Fin 4 → Fin 4, eval (subst σ (gramPoly b)) x =
      certQ ^ 2 * ((List.range 5).map fun c => jFun b c (x ∘ σ) ^ 2).sum := fun σ => by
    rw [eval_subst, gramPoly, eval_sum, List.map_map, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun c _ => ?_
    simp only [Function.comp_apply, eval_pow, eval_jPoly]
    ring
  generalize perms4 = L
  have h2 : (L.map ((fun P => eval P x) ∘ fun σ => subst σ (gramPoly b))) =
      L.map fun σ => certQ ^ 2 * ((List.range 5).map fun c => jFun b c (x ∘ σ) ^ 2).sum :=
    List.map_congr_left fun σ _ => h σ
  rw [h2, List.sum_map_mul_left]
  ring

theorem eval_lamGramPoly : eval lamGramPoly x = 24 * certQ ^ 2 * boundaryGram x := by
  unfold lamGramPoly boundaryGram
  generalize tableIIBoundary = L
  induction L with
  | nil => simp [eval_sum]
  | cons b L ih =>
    rw [List.map_cons, eval_sum, List.map_cons, List.sum_cons, ← eval_sum, ih, eval_blockGram,
      List.map_cons, List.sum_cons]
    ring

/-! ### The orbit sums `m_β` -/

/-- `m_β(x) = 24⁻¹ ∑_{σ ∈ S₄} x^{σ·β}`. -/
def mBeta (β : Mono) : ℝ := (perms4.map fun σ => β.eval (x ∘ σ)).sum / 24

theorem eval_orbitPoly (β : Mono) : eval (orbitPoly β) x = 24 * mBeta x β := by
  rw [orbitPoly, eval_ofList, mBeta, mul_div_cancel₀ _ (by norm_num), eval, List.map_map]
  congr 1
  refine List.map_congr_left fun σ _ => ?_
  simp [Mono.eval_subst]

theorem abs_mono_eval_le (β : Mono) {y : Fin 4 → ℝ} (hy : ∀ i, |y i| ≤ 1) : |β.eval y| ≤ 1 := by
  have h : ∀ i n, |y i ^ n| ≤ 1 := fun i n => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hy i)
  have hm : ∀ a b : ℝ, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 → a * b ≤ 1 :=
    fun a b ha ha1 hb hb1 => by nlinarith
  simp only [Mono.eval, abs_mul]
  exact hm _ _ (by positivity) (hm _ _ (by positivity) (hm _ _ (abs_nonneg _) (h 0 _)
    (abs_nonneg _) (h 1 _)) (abs_nonneg _) (h 2 _)) (abs_nonneg _) (h 3 _)

/-- `|m_β(x)| ≤ 1` when every `|xᵢ| ≤ 1`. -/
theorem abs_mBeta_le (β : Mono) (hx : ∀ i, |x i| ≤ 1) : |mBeta x β| ≤ 1 := by
  rw [mBeta, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 24), div_le_one (by norm_num)]
  refine (abs_list_sum_le _ _ (fun _ => 1) fun σ _ => abs_mono_eval_le β fun i => hx (σ i)).trans ?_
  simp [perms4]
  norm_num

theorem abs_le_one_of_rQuad (hR : rQuad x = 1) (i : Fin 4) : |x i| ≤ 1 := by
  have h : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
    Finset.single_le_sum (f := fun j => x j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have : x i ^ 2 ≤ 1 := by rw [rQuad] at hR; nlinarith [sq_nonneg (∑ j, x j)]
  exact abs_le_one_iff_mul_self_le_one.2 (by rw [← sq]; exact this)

/-! ### The inequality -/

/-- **The boundary remainder identity.** On `R = 1`,
`24 Q² (Λ + 1/4 - 𝓢) = ∑_β (Q² e_β) 24 m_β(x)`. -/
theorem boundary_remainder_eq (hR : rQuad x = 1) :
    24 * certQ ^ 2 * (boundaryGram x + 1 / 4 -
        tableCoeffs.boundaryExpr (diagA x) e5 (dvec x 4)) =
      (elevenCoeffs.map fun t => (t.2 : ℝ) * (24 * mBeta x t.1)).sum := by
  have h := congrArg (fun P => eval P x) eb_eq
  simp only [eval_homog _ x hR] at h
  rw [ebPoly, eval_sum] at h
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, eval_lamGramPoly,
    eval_const, eval_smul, eval_sPoly, elevenPoly, eval_sum, List.map_map] at h
  rw [show (elevenCoeffs.map fun t => (t.2 : ℝ) * (24 * mBeta x t.1)) =
    elevenCoeffs.map ((fun P => eval P x) ∘ fun t => smul t.2 (orbitPoly t.1)) from
    List.map_congr_left fun t _ => by simp [eval_smul, eval_orbitPoly]]
  rw [← h]
  simp only [qInt, certQ]
  push_cast
  ring

/-- **`𝓢 ≥ δ*` at diagonal data** with `R(x) = 1` and `∑ xᵢ ≥ 0`. -/
theorem boundaryExpr_diag_ge (hR : rQuad x = 1) (hx : 0 ≤ ∑ i, x i) :
    δStar ≤ tableCoeffs.boundaryExpr (diagA x) e5 (dvec x 4) := by
  have hE := boundary_remainder_eq x hR
  have hΛ := boundaryGram_nonneg x hx
  have hB : (elevenCoeffs.map fun t => (t.2 : ℝ) * (24 * mBeta x t.1)).sum ≤
      24 * 1656725282 := by
    refine (le_abs_self _).trans ((abs_list_sum_le _ _ (fun t => |(t.2 : ℝ)| * 24) fun t _ => ?_)
      |>.trans (le_of_eq ?_))
    · rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 24)]
      have := abs_mBeta_le x t.1 (abs_le_one_of_rQuad x hR)
      have h0 := abs_nonneg (t.2 : ℝ)
      nlinarith
    · simp only [elevenCoeffs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      norm_num
  rw [δStar]
  simp only [certQ] at hE
  nlinarith

end OnePhaseDimension.Certificate.Boundary
