/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Geometry.BoundaryJets

/-!
# Normalized boundary data

At a regular boundary point with `w = |T| > 0` we normalize:

* `A = T/w` and `λ = T(p, p)/w` (`= -H/w`), so that `Ap = λp`;
* `S₀ = λA - A²`, with `S₀p = 0` and `tr S₀ = -1`;
* `V_{ijk} = pᵢ(S₀)_{jk} + pⱼ(S₀)_{ki} + p_k(S₀)_{ij} + pᵢpⱼp_k`, which is trace-free with
  `pᵢV_{ijk} = (S₀ + p ⊗ p)_{jk}`.

The odd normal components of `B/w²` are those of `V`: `B(p, a, c) = w² S₀(a, c)` for `a, c ⊥ p`
and `B(p, p, p) = w²`.
-/

open Function Filter Topology Set EllipticBernoulli
open scoped RealInnerProductSpace Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension.ConeJets

variable {n : ℕ}

/-- `w = |T|`. -/
def w (J : ConeJets n) : ℝ := √(∑ i, ∑ j, J.T i j ^ 2)

/-- `A = T/w`. -/
def A (J : ConeJets n) (i j : Fin (n - 1)) : ℝ := J.T i j / J.w

/-- `λ = T(p, p)/w`. -/
def lam (J : ConeJets n) : ℝ := J.Tpp / J.w

/-- `S₀ = λA - A²`. -/
def S₀ (J : ConeJets n) (i j : Fin (n - 1)) : ℝ := J.lam * J.A i j - ∑ k, J.A i k * J.A k j

/-- `V_{ijk} = pᵢ(S₀)_{jk} + pⱼ(S₀)_{ki} + p_k(S₀)_{ij} + pᵢpⱼp_k`. -/
def V (J : ConeJets n) (i j k : Fin (n - 1)) : ℝ :=
  J.p i * J.S₀ j k + J.p j * J.S₀ k i + J.p k * J.S₀ i j + J.p i * J.p j * J.p k

theorem w_sq (J : ConeJets n) : J.w ^ 2 = ∑ i, ∑ j, J.T i j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)

theorem w_nonneg (J : ConeJets n) : 0 ≤ J.w := Real.sqrt_nonneg _

/-- `∑ₐ (δ_{ja} - pⱼpₐ) fₐ = fⱼ - pⱼ ∑ₐ pₐ fₐ`. -/
theorem sum_proj_mul (J : ConeJets n) (j : Fin (n - 1)) (f : Fin (n - 1) → ℝ) :
    ∑ a, ((if j = a then 1 else 0) - J.p j * J.p a) * f a = f j - J.p j * ∑ a, J.p a * f a := by
  simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, mul_assoc, ← Finset.mul_sum]

namespace IsBoundaryJet

variable {F : E n → ℝ} {J : ConeJets n} (h : IsBoundaryJet F J)
include h

theorem A_symm (i j : Fin (n - 1)) : J.A i j = J.A j i := by
  simp only [A, h.isConeJet.T_symm i j]

theorem A_trace : ∑ i, J.A i i = 0 := by
  simp only [A, ← Finset.sum_div, h.isConeJet.T_trace, zero_div]

omit h in
theorem sum_A_sq (hw : 0 < J.w) : ∑ i, ∑ j, J.A i j ^ 2 = 1 := by
  simp only [A, div_pow, ← Finset.sum_div, ← w_sq]
  exact div_self (pow_ne_zero 2 hw.ne')

/-- `Ap = λp`. -/
theorem A_mulVec_p (i : Fin (n - 1)) : ∑ j, J.A i j * J.p j = J.lam * J.p i := by
  simp only [A, lam, div_mul_eq_mul_div, ← Finset.sum_div, h.T_mulVec_p]

theorem S₀_symm (i j : Fin (n - 1)) : J.S₀ i j = J.S₀ j i := by
  simp only [S₀, h.A_symm i j]
  congr 1
  exact Finset.sum_congr rfl fun k _ ↦ by rw [h.A_symm i k, h.A_symm k j, mul_comm]

/-- `S₀p = 0`. -/
theorem S₀_mulVec_p (i : Fin (n - 1)) : ∑ j, J.S₀ i j * J.p j = 0 := by
  have h1 : ∑ j, (∑ k, J.A i k * J.A k j) * J.p j = J.lam * ∑ k, J.A i k * J.p k := by
    have : ∑ j, (∑ k, J.A i k * J.A k j) * J.p j = ∑ k, J.A i k * ∑ j, J.A k j * J.p j := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [h.A_mulVec_p]; ring
  simp only [S₀, sub_mul, Finset.sum_sub_distrib, h1, mul_assoc, ← Finset.mul_sum,
    h.A_mulVec_p]
  ring

/-- `tr S₀ = -1`. -/
theorem trace_S₀ (hw : 0 < J.w) : ∑ i, J.S₀ i i = -1 := by
  simp only [S₀, Finset.sum_sub_distrib, ← Finset.mul_sum, h.A_trace, mul_zero, zero_sub]
  rw [← sum_A_sq hw]
  congr 1
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by
    rw [h.A_symm k i, sq]

/-- `V` is trace-free in its last two slots. -/
theorem V_trace (hw : 0 < J.w) (i : Fin (n - 1)) : ∑ j, J.V i j j = 0 := by
  have hS : ∑ j, J.p j * J.S₀ j i = 0 := by
    rw [← h.S₀_mulVec_p i]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [h.S₀_symm j i, mul_comm]
  have hS' : ∑ j, J.p j * J.S₀ i j = 0 := by
    rw [← h.S₀_mulVec_p i]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  simp only [V, Finset.sum_add_distrib, ← Finset.mul_sum, h.trace_S₀ hw, hS, hS']
  have hp : ∑ j, J.p i * J.p j * J.p j = J.p i := by
    simp_rw [mul_assoc, ← Finset.mul_sum, ← sq, h.sum_p_sq, mul_one]
  rw [hp]
  ring

/-- `pᵢV_{ijk} = (S₀ + p ⊗ p)_{jk}`. -/
theorem V_normal (j k : Fin (n - 1)) :
    ∑ i, J.p i * J.V i j k = J.S₀ j k + J.p j * J.p k := by
  have hSk : ∑ i, J.p i * J.S₀ k i = 0 := by
    rw [← h.S₀_mulVec_p k]
    exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
  have hSj : ∑ i, J.p i * J.S₀ i j = 0 := by
    rw [← h.S₀_mulVec_p j]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [h.S₀_symm i j, mul_comm]
  have hpp : ∑ i, J.p i * J.p i = 1 := by simpa [sq] using h.sum_p_sq
  have : ∀ i, J.p i * J.V i j k = J.p i * J.p i * J.S₀ j k +
      J.p j * (J.p i * J.S₀ k i) + J.p k * (J.p i * J.S₀ i j) +
      J.p i * J.p i * (J.p j * J.p k) := fun i ↦ by simp only [V]; ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hSk, hSj, hpp]
  ring

/-- **Normalized odd boundary jets**: `B(p, a, c) = w² S₀(a, c)` for `a, c ⊥ p`. -/
theorem B_odd_eq_S₀ (hw : 0 < J.w) (a c : Fin (n - 1) → ℝ) (ha : ∑ i, a i * J.p i = 0)
    (hc : ∑ i, c i * J.p i = 0) :
    ∑ i, ∑ j, ∑ k, J.p i * a j * c k * J.B i j k =
      J.w ^ 2 * ∑ j, ∑ k, a j * c k * J.S₀ j k := by
  rw [h.B_odd a c ha hc]
  have hT : ∀ i j, J.T i j = J.w * J.A i j := fun i j ↦ by
    rw [ConeJets.A, mul_div_cancel₀ _ hw.ne']
  have hTpp : J.Tpp = J.w * J.lam := by rw [ConeJets.lam, mul_div_cancel₀ _ hw.ne']
  set X := ∑ j, ∑ k, a j * c k * J.A j k
  set Y := ∑ l, (∑ i, a i * J.A i l) * (∑ k, c k * J.A l k)
  have hL1 : ∑ i, ∑ k, a i * c k * J.T i k = J.w * X := by
    simp only [X, hT, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have e1 : ∀ l, ∑ i, a i * J.T i l = J.w * ∑ i, a i * J.A i l := fun l ↦ by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hT]; ring
  have e2 : ∀ l, ∑ k, c k * J.T l k = J.w * ∑ k, c k * J.A l k := fun l ↦ by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [hT]; ring
  have hL2 : ∑ l, (∑ i, a i * J.T i l) * (∑ k, c k * J.T l k) = J.w ^ 2 * Y := by
    simp only [e1, e2, Y]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ ↦ by ring
  have hY : Y = ∑ l, ∑ j, ∑ k, a j * c k * (J.A j l * J.A l k) := by
    simp only [Y]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by ring
  have h2 : ∑ j, ∑ k, a j * c k * ∑ l, J.A j l * J.A l k =
      ∑ l, ∑ j, ∑ k, a j * c k * (J.A j l * J.A l k) := by
    calc _ = ∑ j, ∑ k, ∑ l, a j * c k * (J.A j l * J.A l k) :=
          Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ by rw [Finset.mul_sum]
      _ = ∑ j, ∑ l, ∑ k, a j * c k * (J.A j l * J.A l k) :=
          Finset.sum_congr rfl fun j _ ↦ Finset.sum_comm
      _ = _ := Finset.sum_comm
  have hX : ∑ j, ∑ k, J.lam * (a j * c k * J.A j k) = J.lam * X := by
    simp only [X]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [Finset.mul_sum]
  have hR : ∑ j, ∑ k, a j * c k * J.S₀ j k = J.lam * X - Y := by
    have hpt : ∀ j k, a j * c k * J.S₀ j k =
        J.lam * (a j * c k * J.A j k) - a j * c k * ∑ l, J.A j l * J.A l k := fun j k ↦ by
      simp only [S₀]
      ring
    simp only [hpt, Finset.sum_sub_distrib]
    rw [hX, h2, hY]
  rw [hL1, hL2, hR, hTpp]
  ring

/-- **Normalized `B_{NNN}`**: `B(p, p, p) = w²`. -/
theorem B_NNN_eq : ∑ i, ∑ j, ∑ k, J.p i * J.p j * J.p k * J.B i j k = J.w ^ 2 := by
  rw [h.B_NNN, w_sq]

/-- **Normal derivative of `w`**: `∑ pᵢ T_{jk} B_{ijk} = w³(2λ - tr A³)`, so that
`∂_N w = w⁻¹ ⟨T, B_N⟩ = w²(2λ - tr A³)`. Only the odd normal components of `B` enter. -/
theorem sum_p_T_B (hw : 0 < J.w) :
    ∑ i, ∑ j, ∑ k, J.p i * J.T j k * J.B i j k =
      J.w ^ 3 * (2 * J.lam - ∑ j, ∑ k, ∑ l, J.A j k * J.A k l * J.A l j) := by
  have hJ := h.isConeJet
  set Bp : Fin (n - 1) → Fin (n - 1) → ℝ := fun j k ↦ ∑ i, J.p i * J.B i j k with hBp
  set Q : Fin (n - 1) → ℝ := fun a ↦ ∑ b, J.p b * Bp a b with hQ
  set Pv : Fin (n - 1) → Fin (n - 1) → ℝ := fun j a ↦ (if j = a then 1 else 0) - J.p j * J.p a
  have hPv : ∀ j, ∑ a, Pv j a * J.p a = 0 := fun j ↦ by
    rw [J.sum_proj_mul j J.p]
    simp only [← sq, h.sum_p_sq, mul_one, sub_self]
  have hBp_symm : ∀ j k, Bp j k = Bp k j := fun j k ↦
    Finset.sum_congr rfl fun i _ ↦ by rw [hJ.B_symm₂₃]
  have hSp : ∀ j, ∑ a, J.p a * J.S₀ j a = 0 := fun j ↦ by
    rw [← h.S₀_mulVec_p j]
    exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _
  -- decomposition of `Bp` from the odd components
  have hdec : ∀ j k, Bp j k = J.w ^ 2 * J.S₀ j k + J.p k * Q j + J.p j * Q k -
      J.p j * J.p k * ∑ a, J.p a * Q a := by
    intro j k
    have hodd := h.B_odd_eq_S₀ hw (Pv j) (Pv k) (hPv j) (hPv k)
    have hL : ∑ i, ∑ a, ∑ b, J.p i * Pv j a * Pv k b * J.B i a b =
        ∑ a, Pv j a * ∑ b, Pv k b * Bp a b := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      simp only [hBp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    have hR : ∑ a, ∑ b, Pv j a * Pv k b * J.S₀ a b = J.S₀ j k := by
      have : ∀ a, ∑ b, Pv j a * Pv k b * J.S₀ a b = Pv j a * ∑ b, Pv k b * J.S₀ a b :=
        fun a ↦ by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ ↦ by ring
      simp only [this]
      simp only [Pv, J.sum_proj_mul k, hSp, mul_zero, sub_zero]
      rw [J.sum_proj_mul j (fun a ↦ J.S₀ a k)]
      have : ∑ a, J.p a * J.S₀ a k = 0 := by
        rw [← hSp k]
        exact Finset.sum_congr rfl fun a _ ↦ by rw [h.S₀_symm]
      rw [this, mul_zero, sub_zero]
    rw [hL, hR] at hodd
    simp only [Pv, J.sum_proj_mul k] at hodd
    rw [J.sum_proj_mul j (fun a ↦ Bp a k - J.p k * ∑ b, J.p b * Bp a b)] at hodd
    have hQk : ∑ a, J.p a * Bp a k = Q k := by
      simp only [hQ]
      exact Finset.sum_congr rfl fun a _ ↦ by rw [hBp_symm]
    simp only [mul_sub, Finset.sum_sub_distrib, hQk] at hodd
    have : ∑ a, J.p a * (J.p k * ∑ b, J.p b * Bp a b) = J.p k * ∑ a, J.p a * Q a := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ ↦ by simp only [hQ]; ring
    rw [this] at hodd
    linarith
  have hTp : ∀ j, ∑ k, J.T j k * J.p k = J.Tpp * J.p j := h.T_mulVec_p
  have hpQ : ∑ a, J.p a * Q a = J.w ^ 2 := by
    rw [← h.B_NNN_eq]
    simp only [hQ, hBp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hJ.B_symm₁₂ j k i, hJ.B_symm₁₃ k j i]
    ring
  have hTS : ∑ j, ∑ k, J.T j k * J.S₀ j k =
      J.w * (J.lam - ∑ j, ∑ k, ∑ l, J.A j k * J.A k l * J.A l j) := by
    have hT : ∀ i j, J.T i j = J.w * J.A i j := fun i j ↦ by
      rw [ConeJets.A, mul_div_cancel₀ _ hw.ne']
    have h1 : ∑ j, ∑ k, J.A j k * J.A j k = 1 := by
      rw [← sum_A_sq hw]
      simp only [sq]
    simp only [hT, S₀, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · have : ∑ x, ∑ y, J.w * J.A x y * (J.lam * J.A x y) =
          J.w * J.lam * ∑ j, ∑ k, J.A j k * J.A j k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ ↦ by ring
      rw [this, h1, mul_one]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [h.A_symm l j]
      ring
  -- assemble
  have hsum : ∑ i, ∑ j, ∑ k, J.p i * J.T j k * J.B i j k = ∑ j, ∑ k, J.T j k * Bp j k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [hBp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hterm : ∀ j k, J.T j k * Bp j k = J.w ^ 2 * (J.T j k * J.S₀ j k) +
      Q j * (J.T j k * J.p k) + Q k * (J.T k j * J.p j) -
        J.w ^ 2 * (J.p j * (J.T j k * J.p k)) := fun j k ↦ by
    rw [hdec, hpQ, hJ.T_symm k j]
    ring
  have hS1 : ∑ j, ∑ k, J.w ^ 2 * (J.T j k * J.S₀ j k) =
      J.w ^ 2 * (J.w * (J.lam - ∑ j, ∑ k, ∑ l, J.A j k * J.A k l * J.A l j)) := by
    simp only [← Finset.mul_sum, hTS]
  have hS2 : ∑ j, ∑ k, Q j * (J.T j k * J.p k) = J.Tpp * J.w ^ 2 := by
    simp only [← Finset.mul_sum, hTp]
    rw [← hpQ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hS3 : ∑ j, ∑ k, Q k * (J.T k j * J.p j) = J.Tpp * J.w ^ 2 := by
    rw [Finset.sum_comm]
    exact hS2
  have hS4 : ∑ j, ∑ k, J.w ^ 2 * (J.p j * (J.T j k * J.p k)) = J.w ^ 2 * J.Tpp := by
    simp only [← Finset.mul_sum, hTp]
    have : ∑ j, J.p j * (J.Tpp * J.p j) = J.Tpp * ∑ j, J.p j ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    rw [this, h.sum_p_sq, mul_one]
  have hTpp : J.Tpp = J.w * J.lam := by rw [ConeJets.lam, mul_div_cancel₀ _ hw.ne']
  rw [hsum]
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hS1, hS2, hS3, hS4, hTpp]
  ring

/-- **`∂_N w = w²(2λ - tr A³)`** in ambient form: the derivative of `w̃² = r²|D²F|²` at `x₀` in
the normal direction `N = ∇F(x₀)` is `2w · w²(2λ - tr A³)`. -/
theorem fderiv_rsq_jetNormSq_two_gradient (hw : 0 < J.w) {κ : Type*} [Fintype κ]
    (e : OrthonormalBasis κ ℝ (E n)) :
    fderiv ℝ (fun y ↦ ‖y‖ ^ 2 * jetNormSq e 2 F y) J.x₀ (∇ F J.x₀) =
      2 * (J.w ^ 3 * (2 * J.lam - ∑ j, ∑ k, ∑ l, J.A j k * J.A k l * J.A l j)) := by
  obtain ⟨U, hU, hF, -⟩ := h.nhds
  have hJ := h.isConeJet
  rw [h.gradient_eq, frameMap, map_sum]
  simp only [map_smul, smul_eq_mul, hJ.fderiv_rsq_jetNormSq_two_frame e (hF _ (mem_of_mem_nhds hU))]
  rw [← h.sum_p_T_B hw]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ by ring

end IsBoundaryJet

end OnePhaseDimension.ConeJets
