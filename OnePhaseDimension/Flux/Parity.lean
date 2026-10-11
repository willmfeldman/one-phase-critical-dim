/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Flux.Algebra
public import OnePhaseDimension.Geometry.BoundaryData

/-!
# Reflection parity at the free boundary

Let `p ∈ ℝ^m` be a unit vector and `R = I - 2 p ⊗ p` the reflection in `p^⊥`. If `A` is symmetric
with `Ap = λp`, then `RAR^T = A` and `Rp = -p`. Orthogonal equivariance of the certificate
coefficients and evenness of `U, K` in `p` then give, for the three-tensor
`F_{ijk} = p_l G_{lijk}(A, p, 0)`, the identity `R^{⊗3} F = -F`. Hence `F` pairs to zero with every
three-tensor `Y` that is fixed by `R^{⊗3}` (`sum_p_contractG_eq_zero_of_act3_eq`).

A fully symmetric three-tensor `Y` with `Y(p, a, c) = 0` for `a, c ⊥ p` and `Y(p, p, p) = 0` is
fixed by `R^{⊗3}` (`act3_reflectionAlong_eq_self`): only the components with an odd number of
normal slots change sign, and these vanish.

At a boundary point with `w > 0`, the odd normal components of `B/w²` are those of
`V_{ijk} = pᵢ(S₀)_{jk} + pⱼ(S₀)_{ki} + p_k(S₀)_{ij} + pᵢpⱼp_k`. Applied to `Y = B - w² V` this gives
(`IsBoundaryJet.sum_p_contractG_B`)

  `p_l G_{lijk} B_{ijk} = w² p_l G_{lijk} V_{ijk}`
    `= w² (U_{jk}(S₀ + p ⊗ p)_{jk} + C_{lijk} p_l V_{ijk})`.

## Differences from the source

The 2026-09-24 version argues in an orthonormal basis whose last vector is `p`: a component of
`F` with an even number of normal slots is fixed and negated by `R^{⊗3}`, so it vanishes. We work
without a basis: the pairing `⟨F, Y⟩` is `R`-invariant, so `⟨F, Y⟩ = -⟨F, Y⟩` whenever `Y` is
fixed by `R^{⊗3}`, and the invariance of `B - w² V` is checked by expanding `R = P - p ⊗ p`,
`I = P + p ⊗ p` with `P = I - p ⊗ p` multilinearly.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Finset EllipticBernoulli

@[expose] public noncomputable section

namespace OnePhaseDimension

namespace Gen

variable {m : ℕ}

/-! ### The reflection -/

/-- The reflection `R = I - 2 p ⊗ p` in the hyperplane `p^⊥`. -/
def reflectionAlong (p : Ten1 m) : Ten2 m := fun i j ↦ kron i j - 2 * p i * p j

theorem kron_comm (i j : Fin m) : kron i j = kron j i := by
  simp only [kron, eq_comm]

theorem reflectionAlong_symm (p : Ten1 m) (i j : Fin m) :
    reflectionAlong p i j = reflectionAlong p j i := by
  simp only [reflectionAlong, kron_comm i j]
  ring

theorem sum_kron_mul (v : Ten1 m) (i : Fin m) : ∑ a, kron i a * v a = v i := by
  simp only [kron, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]

/-- `(R v)ᵢ = vᵢ - 2 pᵢ ⟨p, v⟩`. -/
theorem sum_reflectionAlong_mul (p v : Ten1 m) (i : Fin m) :
    ∑ a, reflectionAlong p i a * v a = v i - 2 * p i * ∑ a, p a * v a := by
  simp only [reflectionAlong, sub_mul, sum_sub_distrib, sum_kron_mul, mul_sum]
  congr 1
  exact sum_congr rfl fun a _ ↦ by ring

theorem sum_mul_self_of_sq1 {p : Ten1 m} (hp : sq1 p = 1) : ∑ a, p a * p a = 1 := by
  simpa [sq1, sq] using hp

section Reflection

variable {p : Ten1 m} (hp : sq1 p = 1)
include hp

/-- `Rp = -p`. -/
theorem act1_reflectionAlong_self : act1 (reflectionAlong p) p = -p := by
  funext i
  simp only [act1, sum_reflectionAlong_mul, sum_mul_self_of_sq1 hp, Pi.neg_apply]
  ring

/-- `R` is orthogonal. -/
theorem isOrth_reflectionAlong : IsOrth (reflectionAlong p) := by
  intro i j
  have h1 : ∑ k, reflectionAlong p k i * reflectionAlong p k j =
      ∑ k, reflectionAlong p i k * reflectionAlong p k j :=
    sum_congr rfl fun k _ ↦ by rw [reflectionAlong_symm p k i]
  have h2 : ∑ a, p a * reflectionAlong p a j = -p j := by
    have := congrFun (act1_reflectionAlong_self hp) j
    simp only [act1, Pi.neg_apply] at this
    rw [← this]
    exact sum_congr rfl fun a _ ↦ by rw [reflectionAlong_symm p a j, mul_comm]
  rw [h1, sum_reflectionAlong_mul p (fun k ↦ reflectionAlong p k j) i, h2]
  simp only [reflectionAlong]
  ring

/-- **`RAR^T = A`** for a symmetric `A` with `Ap = λp`. -/
theorem act2_reflectionAlong_of_eigen {A : Ten2 m} {lam : ℝ} (hA : IsSymm2 A)
    (hAp : ∀ i, ∑ j, A i j * p j = lam * p i) : act2 (reflectionAlong p) A = A := by
  have hpp := sum_mul_self_of_sq1 hp
  have hpA : ∀ j, ∑ a, p a * A a j = lam * p j := fun j ↦ by
    rw [← hAp j]
    exact sum_congr rfl fun a _ ↦ by rw [hA a j, mul_comm]
  have hrow : ∀ a j, ∑ b, reflectionAlong p j b * A a b = A a j - 2 * lam * p a * p j :=
    fun a j ↦ by
      have hpa : ∑ b, p b * A a b = lam * p a := by
        rw [← hAp a]
        exact sum_congr rfl fun b _ ↦ mul_comm _ _
      rw [sum_reflectionAlong_mul p (fun b ↦ A a b) j, hpa]
      ring
  funext i j
  have h1 : act2 (reflectionAlong p) A i j =
      ∑ a, reflectionAlong p i a * ∑ b, reflectionAlong p j b * A a b := by
    simp only [act2, mul_sum, mul_assoc]
  have h2 : ∑ a, p a * (A a j - 2 * lam * p a * p j) = lam * p j - 2 * lam * p j := by
    have : ∀ a, p a * (A a j - 2 * lam * p a * p j) =
        p a * A a j - 2 * lam * p j * (p a * p a) := fun a ↦ by ring
    simp only [this, sum_sub_distrib, ← mul_sum, hpA, hpp, mul_one]
  rw [h1]
  simp only [hrow]
  rw [sum_reflectionAlong_mul p (fun a ↦ A a j - 2 * lam * p a * p j) i, h2]
  ring

end Reflection

/-! ### Evenness and the reflection identity -/

namespace Coeffs

variable {c : Coeffs m} {ε δ : ℝ}

theorem contractG_neg (hc : CertificateHolds m ε δ c) (A : Ten2 m) (p : Ten1 m) (g : ℝ) (X : Ten3 m)
    (l : Fin m) : c.contractG (A, -p, g) X l = c.contractG (A, p, g) X l := by
  simp only [contractG_eq, hc.even_U, hc.even_K]

/-- `G_{lijk} X_{ijk}` is linear in `X`. -/
theorem contractG_sub_smul (x : Ten2 m × Ten1 m × ℝ) (X Y : Ten3 m) (r : ℝ) (l : Fin m) :
    c.contractG x (fun i j k ↦ X i j k - r * Y i j k) l =
      c.contractG x X l - r * c.contractG x Y l := by
  simp only [contractG, mul_sub, sum_sub_distrib, mul_sum]
  congr 1
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring

theorem contractG_div (x : Ten2 m × Ten1 m × ℝ) (X : Ten3 m) (r : ℝ) (l : Fin m) :
    c.contractG x (fun i j k ↦ X i j k / r) l = c.contractG x X l / r := by
  simp only [contractG, sum_div]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring

section Parity

variable (hc : CertificateHolds m ε δ c) {A : Ten2 m} {p : Ten1 m} {lam : ℝ} (hp : sq1 p = 1)
  (hA : IsSymm2 A) (hAp : ∀ i, ∑ j, A i j * p j = lam * p i)
include hc hp hA hAp

/-- **`R^{⊗3}F = -F`** for `F_{ijk} = p_l G_{lijk}(A, p, 0)`, in paired form:
`⟨F, R^{⊗3} Y⟩ = -⟨F, Y⟩`. -/
theorem sum_p_contractG_act3_reflectionAlong (Y : Ten3 m) :
    ∑ l, p l * c.contractG (A, p, 0) (act3 (reflectionAlong p) Y) l =
      -∑ l, p l * c.contractG (A, p, 0) Y l := by
  set R := reflectionAlong p
  have hR : IsOrth R := isOrth_reflectionAlong hp
  have hRp : act1 R p = -p := act1_reflectionAlong_self hp
  have hcomm : ∀ l, c.contractG (A, p, 0) (act3 R Y) l = act1 R (c.contractG (A, p, 0) Y) l :=
    fun l ↦ by
      have := contractG_act hc hR A p 0 Y l
      rwa [act2_reflectionAlong_of_eigen hp hA hAp, hRp, contractG_neg hc] at this
  simp only [hcomm]
  calc ∑ l, p l * act1 R (c.contractG (A, p, 0) Y) l
      = -∑ l, act1 R p l * act1 R (c.contractG (A, p, 0) Y) l := by
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun l _ ↦ by rw [hRp, Pi.neg_apply]; ring
    _ = -∑ l, p l * c.contractG (A, p, 0) Y l := by rw [sum_act1_mul_act1 hR]

/-- **Parity.** If `Y` is fixed by the reflection, then `p_l G_{lijk}(A, p, 0) Y_{ijk} = 0`. -/
theorem sum_p_contractG_eq_zero_of_act3_eq {Y : Ten3 m} (hY : act3 (reflectionAlong p) Y = Y) :
    ∑ l, p l * c.contractG (A, p, 0) Y l = 0 := by
  have := sum_p_contractG_act3_reflectionAlong hc hp hA hAp Y
  rw [hY] at this
  linarith

end Parity

end Coeffs

/-! ### Tensors fixed by the reflection -/

/-- The trilinear form `Y(a, b, c) = ∑ aᵢ bⱼ c_k Y_{ijk}`. -/
def tri (Y : Ten3 m) (a b c : Ten1 m) : ℝ := ∑ i, ∑ j, ∑ k, a i * b j * c k * Y i j k

theorem tri_add_smul₁ (Y : Ten3 m) (a a' b c : Ten1 m) (r : ℝ) :
    tri Y (a + r • a') b c = tri Y a b c + r * tri Y a' b c := by
  simp only [tri, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring

theorem tri_add_smul₂ (Y : Ten3 m) (a b b' c : Ten1 m) (r : ℝ) :
    tri Y a (b + r • b') c = tri Y a b c + r * tri Y a b' c := by
  simp only [tri, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring

theorem tri_add_smul₃ (Y : Ten3 m) (a b c c' : Ten1 m) (r : ℝ) :
    tri Y a b (c + r • c') = tri Y a b c + r * tri Y a b c' := by
  simp only [tri, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring

theorem tri_swap₁₂ {Y : Ten3 m} (hY : ∀ i j k, Y i j k = Y j i k) (a b c : Ten1 m) :
    tri Y a b c = tri Y b a c := by
  simp only [tri]
  rw [sum_comm]
  exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by
    rw [hY]; ring

theorem tri_swap₂₃ {Y : Ten3 m} (hY : ∀ i j k, Y i j k = Y i k j) (a b c : Ten1 m) :
    tri Y a b c = tri Y a c b := by
  simp only [tri]
  exact sum_congr rfl fun i _ ↦ by
    rw [sum_comm]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by rw [hY]; ring

/-- `Y(p, a, c) = ∑ aⱼ c_k (pᵢ Y_{ijk})`. -/
theorem tri_eq_of_contract (Y : Ten3 m) (p a c : Ten1 m) :
    tri Y p a c = ∑ j, ∑ k, a j * c k * ∑ i, p i * Y i j k := by
  simp only [tri, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ ↦ ?_
  rw [sum_comm]
  exact sum_congr rfl fun k _ ↦ sum_congr rfl fun i _ ↦ by ring

/-- The projection `P = I - p ⊗ p`, row `i`. -/
def projRow (p : Ten1 m) (i : Fin m) : Ten1 m := fun a ↦ kron i a - p i * p a

theorem sum_projRow_mul_self {p : Ten1 m} (hp : sq1 p = 1) (i : Fin m) :
    ∑ a, projRow p i a * p a = 0 := by
  simp only [projRow, sub_mul, sum_sub_distrib, sum_kron_mul, mul_assoc, ← mul_sum,
    sum_mul_self_of_sq1 hp, mul_one, sub_self]

theorem kron_row_eq (p : Ten1 m) (i : Fin m) : (fun a ↦ kron i a) = projRow p i + p i • p := by
  funext a
  simp only [projRow, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem reflectionAlong_row_eq (p : Ten1 m) (i : Fin m) :
    reflectionAlong p i = projRow p i + (-p i) • p := by
  funext a
  simp only [reflectionAlong, projRow, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem tri_kron (Y : Ten3 m) (i j k : Fin m) :
    tri Y (fun a ↦ kron i a) (fun a ↦ kron j a) (fun a ↦ kron k a) = Y i j k := by
  simp only [tri]
  simp only [mul_assoc, ← mul_sum, sum_kron_mul]

/-- **Tensors fixed by the reflection.** A fully symmetric three-tensor whose odd normal
components vanish, `Y(p, a, c) = 0` for `a, c ⊥ p` and `Y(p, p, p) = 0`, is fixed by `R^{⊗3}`. -/
theorem act3_reflectionAlong_eq_self {p : Ten1 m} (hp : sq1 p = 1) {Y : Ten3 m}
    (hY₁₂ : ∀ i j k, Y i j k = Y j i k) (hY₂₃ : ∀ i j k, Y i j k = Y i k j)
    (hodd : ∀ a c : Ten1 m, ∑ i, a i * p i = 0 → ∑ i, c i * p i = 0 → tri Y p a c = 0)
    (hppp : tri Y p p p = 0) : act3 (reflectionAlong p) Y = Y := by
  funext i j k
  have hP := sum_projRow_mul_self hp
  have h1 : tri Y p (projRow p j) (projRow p k) = 0 := hodd _ _ (hP j) (hP k)
  have h2 : tri Y (projRow p i) p (projRow p k) = 0 := by
    rw [tri_swap₁₂ hY₁₂]; exact hodd _ _ (hP i) (hP k)
  have h3 : tri Y (projRow p i) (projRow p j) p = 0 := by
    rw [tri_swap₂₃ hY₂₃, tri_swap₁₂ hY₁₂]; exact hodd _ _ (hP i) (hP j)
  have hR : act3 (reflectionAlong p) Y i j k =
      tri Y (reflectionAlong p i) (reflectionAlong p j) (reflectionAlong p k) := rfl
  rw [hR, ← tri_kron Y i j k, kron_row_eq p i, kron_row_eq p j, kron_row_eq p k,
    reflectionAlong_row_eq p i, reflectionAlong_row_eq p j, reflectionAlong_row_eq p k]
  simp only [tri_add_smul₁, tri_add_smul₂, tri_add_smul₃]
  linear_combination (-2 * p i) * h1 + (-2 * p j) * h2 + (-2 * p k) * h3 +
    (-2 * p i * p j * p k) * hppp

end Gen

/-! ### The boundary contraction -/

namespace ConeJets.IsBoundaryJet

variable {n : ℕ} {F : E n → ℝ} {J : ConeJets n} (h : IsBoundaryJet F J)
include h

theorem sq1_p : Gen.sq1 J.p = 1 := h.sum_p_sq

theorem isSymm2_A : Gen.IsSymm2 J.A := h.A_symm

theorem isSTF2_A : Gen.IsSTF2 J.A := ⟨h.A_symm, h.A_trace⟩

theorem V_symm₁₂ (i j k : Fin (n - 1)) : J.V i j k = J.V j i k := by
  simp only [ConeJets.V, h.S₀_symm]
  ring

theorem V_symm₂₃ (i j k : Fin (n - 1)) : J.V i j k = J.V i k j := by
  simp only [ConeJets.V, h.S₀_symm]
  ring

theorem sum_p_S₀_p : ∑ j, ∑ k, J.p j * J.p k * J.S₀ j k = 0 := by
  have : ∀ j, ∑ k, J.p j * J.p k * J.S₀ j k = J.p j * ∑ k, J.S₀ j k * J.p k := fun j ↦ by
    rw [mul_sum]
    exact sum_congr rfl fun k _ ↦ by ring
  simp only [this, h.S₀_mulVec_p, mul_zero, sum_const_zero]

/-- `V(p, a, c) = S₀(a, c)` for `a, c ⊥ p`. -/
theorem tri_V_p (a c : Gen.Ten1 (n - 1)) (ha : ∑ i, a i * J.p i = 0) (_hc : ∑ i, c i * J.p i = 0) :
    Gen.tri J.V J.p a c = ∑ j, ∑ k, a j * c k * J.S₀ j k := by
  rw [Gen.tri_eq_of_contract]
  simp only [h.V_normal, mul_add, sum_add_distrib]
  have : ∑ j, ∑ k, a j * c k * (J.p j * J.p k) =
      (∑ j, a j * J.p j) * ∑ k, c k * J.p k := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring
  rw [this, ha, zero_mul, add_zero]

/-- `V(p, p, p) = 1`. -/
theorem tri_V_ppp : Gen.tri J.V J.p J.p J.p = 1 := by
  rw [Gen.tri_eq_of_contract]
  simp only [h.V_normal, mul_add, sum_add_distrib, h.sum_p_S₀_p, zero_add]
  have : ∑ j, ∑ k, J.p j * J.p k * (J.p j * J.p k) =
      (∑ j, J.p j * J.p j) * ∑ k, J.p k * J.p k := by
    rw [sum_mul_sum]
    exact sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring
  rw [this, Gen.sum_mul_self_of_sq1 h.sq1_p, one_mul]

/-- `pᵢ V_{ijk} = (S₀ + p ⊗ p)_{jk}` turns `p_l G_{lijk} V_{ijk}` into the boundary polynomial
terms `U_{jk}(S₀ + p ⊗ p)_{jk} + C_{lijk} p_l V_{ijk}`. -/
theorem sum_p_contractG_V (c : Gen.Coeffs (n - 1)) :
    ∑ l, J.p l * c.contractG (J.A, J.p, 0) J.V l =
      ∑ j, ∑ k, c.U (J.A, J.p, 0) j k * (J.S₀ j k + J.p j * J.p k) +
        ∑ l, ∑ i, ∑ j, ∑ k, c.C (J.A, J.p, 0) l i j k * J.p l * J.V i j k := by
  have hsplit : ∀ l, c.contractG (J.A, J.p, 0) J.V l =
      ∑ j, ∑ k, c.U (J.A, J.p, 0) j k * J.V l j k +
        ∑ i, ∑ j, ∑ k, c.C (J.A, J.p, 0) l i j k * J.V i j k := fun l ↦ by
    simp only [Gen.Coeffs.contractG, Gen.Coeffs.G, add_mul, sum_add_distrib]
    congr 1
    simp only [mul_assoc, ← mul_sum]
    exact Gen.sum_kron_mul (fun i ↦ ∑ j, ∑ k, c.U (J.A, J.p, 0) j k * J.V i j k) l
  calc ∑ l, J.p l * c.contractG (J.A, J.p, 0) J.V l
      = ∑ l, J.p l * ∑ j, ∑ k, c.U (J.A, J.p, 0) j k * J.V l j k +
          ∑ l, J.p l * ∑ i, ∑ j, ∑ k, c.C (J.A, J.p, 0) l i j k * J.V i j k := by
        rw [← sum_add_distrib]
        exact sum_congr rfl fun l _ ↦ by rw [hsplit l, mul_add]
    _ = _ := by
        congr 1
        · simp only [mul_sum]
          rw [sum_comm]
          refine sum_congr rfl fun j _ ↦ ?_
          rw [sum_comm]
          refine sum_congr rfl fun k _ ↦ ?_
          rw [← h.V_normal j k, mul_sum]
          exact sum_congr rfl fun i _ ↦ by ring
        · simp only [mul_sum]
          exact sum_congr rfl fun l _ ↦ sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦
            sum_congr rfl fun k _ ↦ by ring

variable (hw : 0 < J.w)
include hw

/-- `B - w² V` is fixed by the reflection in `p^⊥`: its odd normal components vanish. -/
theorem act3_reflectionAlong_B_sub_V :
    Gen.act3 (Gen.reflectionAlong J.p) (fun i j k ↦ J.B i j k - J.w ^ 2 * J.V i j k) =
      fun i j k ↦ J.B i j k - J.w ^ 2 * J.V i j k := by
  have hJ := h.isConeJet
  have hlin : ∀ a b c : Gen.Ten1 (n - 1), Gen.tri (fun i j k ↦ J.B i j k - J.w ^ 2 * J.V i j k) a b
      c =
      Gen.tri J.B a b c - J.w ^ 2 * Gen.tri J.V a b c := fun a b c ↦ by
    simp only [Gen.tri, mul_sub, sum_sub_distrib, mul_sum]
    congr 1
    exact sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ sum_congr rfl fun k _ ↦ by ring
  refine Gen.act3_reflectionAlong_eq_self h.sq1_p (fun i j k ↦ ?_) (fun i j k ↦ ?_)
    (fun a c ha hc ↦ ?_) ?_
  · simp only [hJ.B_symm₁₂ i j k, h.V_symm₁₂ i j k]
  · simp only [hJ.B_symm₂₃ i j k, h.V_symm₂₃ i j k]
  · rw [hlin, h.tri_V_p a c ha hc]
    have := h.B_odd_eq_S₀ hw a c ha hc
    simp only [Gen.tri]
    linear_combination this
  · rw [hlin, h.tri_V_ppp, mul_one]
    have := h.B_NNN_eq
    simp only [Gen.tri]
    linear_combination this

variable {c : Gen.Coeffs (n - 1)} {ε δ : ℝ} (hc : Gen.CertificateHolds (n - 1) ε δ c)
include hc

/-- **The boundary parity lemma**: `p_l G_{lijk} B_{ijk} = w² p_l G_{lijk} V_{ijk}` at a regular
boundary point, with `G` evaluated at `(A, p, 0)`. -/
theorem sum_p_contractG_B :
    ∑ l, J.p l * c.contractG (J.A, J.p, 0) J.B l =
      J.w ^ 2 * ∑ l, J.p l * c.contractG (J.A, J.p, 0) J.V l := by
  have h0 := Gen.Coeffs.sum_p_contractG_eq_zero_of_act3_eq hc h.sq1_p h.isSymm2_A h.A_mulVec_p
    (h.act3_reflectionAlong_B_sub_V hw)
  simp only [Gen.Coeffs.contractG_sub_smul, mul_sub, sum_sub_distrib] at h0
  have h1 : ∑ l, J.p l * (J.w ^ 2 * c.contractG (J.A, J.p, 0) J.V l) =
      J.w ^ 2 * ∑ l, J.p l * c.contractG (J.A, J.p, 0) J.V l := by
    rw [mul_sum]
    exact sum_congr rfl fun l _ ↦ by ring
  linarith

/-- **Boundary contraction**:
`p_l G_{lijk} B_{ijk} / w² = U_{jk}(S₀ + p ⊗ p)_{jk} + C_{lijk} p_l V_{ijk}`. -/
theorem boundary_contraction_eq_V :
    ∑ l, J.p l * c.contractG (J.A, J.p, 0) J.B l =
      J.w ^ 2 * (∑ j, ∑ k, c.U (J.A, J.p, 0) j k * (J.S₀ j k + J.p j * J.p k) +
        ∑ l, ∑ i, ∑ j, ∑ k, c.C (J.A, J.p, 0) l i j k * J.p l * J.V i j k) := by
  rw [h.sum_p_contractG_B hw hc, h.sum_p_contractG_V c]

end ConeJets.IsBoundaryJet

/-! ### Dimension five -/

theorem sum_kron_mul (v : Ten1) (i : Fin 5) : ∑ a, kron i a * v a = v i :=
  Gen.sum_kron_mul v i

end OnePhaseDimension
