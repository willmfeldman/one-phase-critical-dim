/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Ops
public import OnePhaseDimension.Certificate.Bounds.Contraction

/-!
# The connected components of scalar graphs with cubic vertices

After the edges between vectors are split off, a scalar graph retained by the closure lemma
(at most two copies of `X`, every copy with three incidences) is a product of connected
components of the following seven shapes, where a *leaf* is a copy of `p` or `ℓ`:

* `c100`: one `X`, three leaves;
* `c110`: one `X` with a self-edge and one leaf;
* `c201`, `c202`, `c203`: two copies joined by `r = 1, 2, 3` edges, the other slots at leaves;
* `c211`: two copies joined by one edge, the first with a self-edge, the second with two
  leaves;
* `c221`: two copies joined by one edge, each with a self-edge.

For each shape we compute the value of the graph key (`Comp.eval_eq`) and prove the bound
`(value)² ≤ L² ∏ |leaf|² |X|^{2·#X}` (`Comp.eval_sq_le`), with `L²` given by the product rule of
the 2026-09-24 version (section "Bounds for scalar graphs"): `θ^k` for an edge of power `k`
between distinct vertices, `5/7` or `θ^{k-1}` for a self-edge of power `k = 1` or `k ≥ 2`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate

open Matrix Finset

/-! ### Leaves -/

/-- The vector carried by a leaf endpoint (`0` for other endpoints). -/
def CertData.vec (d : CertData) : Endpoint → Fin 5 → ℝ
  | .p => d.p
  | .ell => d.ell
  | _ => 0

/-- Whether an endpoint is a copy of `p` or of `ℓ`. -/
def Endpoint.isLeaf : Endpoint → Bool
  | .p => true
  | .ell => true
  | _ => false

theorem Endpoint.isX_eq_false_of_isLeaf {u : Endpoint} (hu : u.isLeaf = true) :
    u.isX = false := by
  cases u <;> simp_all [Endpoint.isLeaf, Endpoint.isX]

theorem Endpoint.ne_x_of_isLeaf {u : Endpoint} (hu : u.isLeaf = true) (c : ℕ) : u ≠ .x c := by
  rintro rfl; simp [Endpoint.isLeaf] at hu

theorem CertData.weight_of_isLeaf (d : CertData) (ι : ℕ → Fin 5) {u : Endpoint}
    (hu : u.isLeaf = true) : d.weight ι u = d.vec u := by
  cases u with
  | p => funext a; rfl
  | ell => funext a; rfl
  | _ => simp [Endpoint.isLeaf] at hu

@[simp] theorem CertData.weight_x (d : CertData) (ι : ℕ → Fin 5) (c : ℕ) (a : Fin 5) :
    d.weight ι (.x c) a = 1 := rfl

/-! ### Unfolding the edge sums -/

section Unfold

variable (d : CertData) (ι : ℕ → Fin 5) (F : XRecord → ℝ)

theorem evalEdgesWith_nil (acc : XRecord) : evalEdgesWith d ι F [] acc = F acc := rfl

/-- An edge from a copy of `X` to a leaf contracts that slot with `A^k u`. -/
theorem evalEdgesWith_cons_leaf (c k : ℕ) {u : Endpoint} (hu : u.isLeaf = true)
    (es : List Edge) (acc : XRecord) :
    evalEdgesWith d ι F (⟨.x c, u, k⟩ :: es) acc =
      ∑ a, (d.A ^ k *ᵥ d.vec u) a * evalEdgesWith d ι F es (pushIdx acc (.x c) a) := by
  simp only [evalEdgesWith, pushEdge,
    pushIdx_of_isX_eq_false _ (Endpoint.isX_eq_false_of_isLeaf hu), d.weight_of_isLeaf ι hu,
    CertData.weight_x, one_mul, mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- An edge between copies of `X`. -/
theorem evalEdgesWith_cons_xx (c c' k : ℕ) (es : List Edge) (acc : XRecord) :
    evalEdgesWith d ι F (⟨.x c, .x c', k⟩ :: es) acc =
      ∑ a, ∑ b, (d.A ^ k) a b *
        evalEdgesWith d ι F es (pushIdx (pushIdx acc (.x c) a) (.x c') b) := by
  simp only [evalEdgesWith, pushEdge, CertData.weight_x, one_mul]

end Unfold

theorem xCopiesIn_nil (S : Finset ℕ) : XCopiesIn S [] := fun _ h => by simp at h

theorem xCopiesIn_cons_leaf {S : Finset ℕ} {c k : ℕ} (hc : c ∈ S) {u : Endpoint}
    (hu : u.isLeaf = true) {es : List Edge} (h : XCopiesIn S es) :
    XCopiesIn S (⟨.x c, u, k⟩ :: es) := by
  intro e he c' hc'
  rcases List.mem_cons.1 he with rfl | he
  · rcases hc' with hc' | hc'
    · cases hc'; exact hc
    · exact absurd hc' (Endpoint.ne_x_of_isLeaf hu c')
  · exact h e he c' hc'

theorem xCopiesIn_cons_xx {S : Finset ℕ} {c c' k : ℕ} (hc : c ∈ S) (hc' : c' ∈ S)
    {es : List Edge} (h : XCopiesIn S es) : XCopiesIn S (⟨.x c, .x c', k⟩ :: es) := by
  intro e he c'' hc''
  rcases List.mem_cons.1 he with rfl | he
  · rcases hc'' with hc'' | hc'' <;> cases hc'' <;> assumption
  · exact h e he c'' hc''

/-! ### Self-edges -/

/-- The bound factor of a self-edge of power `k` at a copy of `X`: `5/7` for `k = 1` and
`θ^{k-1}` for `k ≥ 2`. A power-zero self-edge is the trace of `X`, which vanishes. -/
def selfFactor : ℕ → ℚ
  | 0 => 0
  | 1 => 5 / 7
  | k + 2 => (4 / 5) ^ (k + 1)

theorem selfFactor_nonneg (k : ℕ) : 0 ≤ selfFactor k := by
  rcases k with _ | _ | k <;> simp only [selfFactor] <;> positivity

theorem sq1_contractX_pow_le {d : CertData} (hd : d.Admissible) (k : ℕ) :
    sq1 (contractX d.X (d.A ^ k)) ≤ (selfFactor k : ℝ) * sq3 d.X := by
  have hX : IsSymm3 d.X := ⟨hd.X_swap₁₂, hd.X_swap₂₃⟩
  rcases k with _ | _ | k
  · have : contractX d.X (d.A ^ 0) = 0 := by
      funext c
      simp only [contractX, pow_zero, Matrix.one_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true, Pi.zero_apply]
      exact hd.X_trace c
    rw [this]
    simp [sq1, selfFactor]
  · simp only [selfFactor, pow_one, zero_add]
    push_cast
    exact sq1_contract_le_five_sevenths hd.isSymm hd.trace_eq_zero hd.trace_sq_eq_one hX
      hd.X_trace
  · simp only [selfFactor]
    push_cast
    exact sq1_contract_pow_le hd.isSymm hd.trace_eq_zero hd.trace_sq_eq_one d.X k

/-! ### The components -/

/-- The connected components containing a copy of `X`. The leaf endpoints are recorded with
the powers of the edges leading to them. -/
inductive Comp where
  /-- One `X`, three leaves. -/
  | c100 (u₁ : Endpoint) (k₁ : ℕ) (u₂ : Endpoint) (k₂ : ℕ) (u₃ : Endpoint) (k₃ : ℕ)
  /-- One `X` with a self-edge of power `s` and one leaf. -/
  | c110 (s : ℕ) (u : Endpoint) (k : ℕ)
  /-- Two copies joined by one edge of power `m`, two leaves at each. -/
  | c201 (m : ℕ) (u₁ : Endpoint) (k₁ : ℕ) (u₂ : Endpoint) (k₂ : ℕ) (v₁ : Endpoint) (l₁ : ℕ)
      (v₂ : Endpoint) (l₂ : ℕ)
  /-- Two copies joined by two edges, one leaf at each. -/
  | c202 (m₁ m₂ : ℕ) (u : Endpoint) (k : ℕ) (v : Endpoint) (l : ℕ)
  /-- Two copies joined by three edges. -/
  | c203 (m₁ m₂ m₃ : ℕ)
  /-- Two copies joined by one edge, a self-edge at the first, two leaves at the second. -/
  | c211 (s m : ℕ) (v₁ : Endpoint) (l₁ : ℕ) (v₂ : Endpoint) (l₂ : ℕ)
  /-- Two copies joined by one edge, each with a self-edge. -/
  | c221 (s₁ s₂ m : ℕ)
  deriving DecidableEq, Repr

namespace Comp

/-- The edges of a component, with copies `X₀` (and `X₁`). -/
def edges : Comp → List Edge
  | c100 u₁ k₁ u₂ k₂ u₃ k₃ => [⟨.x 0, u₁, k₁⟩, ⟨.x 0, u₂, k₂⟩, ⟨.x 0, u₃, k₃⟩]
  | c110 s u k => [⟨.x 0, .x 0, s⟩, ⟨.x 0, u, k⟩]
  | c201 m u₁ k₁ u₂ k₂ v₁ l₁ v₂ l₂ =>
    [⟨.x 0, .x 1, m⟩, ⟨.x 0, u₁, k₁⟩, ⟨.x 0, u₂, k₂⟩, ⟨.x 1, v₁, l₁⟩, ⟨.x 1, v₂, l₂⟩]
  | c202 m₁ m₂ u k v l => [⟨.x 0, .x 1, m₁⟩, ⟨.x 0, .x 1, m₂⟩, ⟨.x 0, u, k⟩, ⟨.x 1, v, l⟩]
  | c203 m₁ m₂ m₃ => [⟨.x 0, .x 1, m₁⟩, ⟨.x 0, .x 1, m₂⟩, ⟨.x 0, .x 1, m₃⟩]
  | c211 s m v₁ l₁ v₂ l₂ => [⟨.x 0, .x 0, s⟩, ⟨.x 0, .x 1, m⟩, ⟨.x 1, v₁, l₁⟩, ⟨.x 1, v₂, l₂⟩]
  | c221 s₁ s₂ m => [⟨.x 0, .x 0, s₁⟩, ⟨.x 1, .x 1, s₂⟩, ⟨.x 0, .x 1, m⟩]

/-- The graph key of a component (rank `0`, no scalar factors). -/
def key (c : Comp) : Key := ⟨0, 0, 0, 0, [], c.edges⟩

/-- The leaf endpoints of a component. -/
def leaves : Comp → List Endpoint
  | c100 u₁ _ u₂ _ u₃ _ => [u₁, u₂, u₃]
  | c110 _ u _ => [u]
  | c201 _ u₁ _ u₂ _ v₁ _ v₂ _ => [u₁, u₂, v₁, v₂]
  | c202 _ _ u _ v _ => [u, v]
  | c203 .. => []
  | c211 _ _ v₁ _ v₂ _ => [v₁, v₂]
  | c221 .. => []

/-- The number of copies of `X`. -/
def nX : Comp → ℕ
  | c100 .. | c110 .. => 1
  | _ => 2

/-- The squared bound factor `L²` of a component. -/
def lsq : Comp → ℚ
  | c100 _ k₁ _ k₂ _ k₃ => (4 / 5) ^ (k₁ + k₂ + k₃)
  | c110 s _ k => selfFactor s * (4 / 5) ^ k
  | c201 m _ k₁ _ k₂ _ l₁ _ l₂ => (4 / 5) ^ (m + k₁ + k₂ + l₁ + l₂)
  | c202 m₁ m₂ _ k _ l => (4 / 5) ^ (m₁ + m₂ + k + l)
  | c203 m₁ m₂ m₃ => (4 / 5) ^ (m₁ + m₂ + m₃)
  | c211 s m _ l₁ _ l₂ => selfFactor s * (4 / 5) ^ (m + l₁ + l₂)
  | c221 s₁ s₂ m => selfFactor s₁ * selfFactor s₂ * (4 / 5) ^ m

/-- All leaves of the component are copies of `p` or `ℓ`. -/
def LeavesOK (c : Comp) : Prop := ∀ u ∈ c.leaves, u.isLeaf = true

end Comp

/-! ### Bounds for the component values

Each lemma bounds the nested sum produced by the edges of one component shape, for arbitrary
matrices with operator bounds and arbitrary leaf vectors. -/

section ShapeBounds

variable (X : Fin 5 → Fin 5 → Fin 5 → ℝ)

theorem sum_congr₃ {f g : Fin 5 → Fin 5 → Fin 5 → ℝ} (h : ∀ a b c, f a b c = g a b c) :
    ∑ a, ∑ b, ∑ c, f a b c = ∑ a, ∑ b, ∑ c, g a b c :=
  Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c _ => h a b c

theorem sum_congr₆ {f g : Fin 5 → Fin 5 → Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ}
    (h : ∀ a b c a' b' c', f a b c a' b' c' = g a b c a' b' c') :
    ∑ a, ∑ b, ∑ c, ∑ a', ∑ b', ∑ c', f a b c a' b' c' =
      ∑ a, ∑ b, ∑ c, ∑ a', ∑ b', ∑ c', g a b c a' b' c' :=
  sum_congr₃ fun a b c => sum_congr₃ fun a' b' c' => h a b c a' b' c'

theorem sum_comm₃' (H : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ a, ∑ b, ∑ c, H a b c = ∑ c, ∑ a, ∑ b, H a b c :=
  (sum_comm₃ H).trans (sum_comm₃ fun b c a => H a b c)

theorem bound_c100 (y₁ y₂ y₃ : Fin 5 → ℝ) :
    (∑ a, y₁ a * ∑ b, y₂ b * ∑ c, y₃ c * X a b c) ^ 2 ≤
      sq3 X * (sq1 y₁ * sq1 y₂ * sq1 y₃) := by
  have e : ∑ a, y₁ a * ∑ b, y₂ b * ∑ c, y₃ c * X a b c =
      ∑ a, ∑ b, ∑ c, X a b c * (y₁ a * y₂ b * y₃ c) := by
    simp only [Finset.mul_sum]
    exact sum_congr₃ fun a b c => by ring
  rw [e]
  exact sq_sum3_vec_le X y₁ y₂ y₃

theorem bound_c110 (S : Matrix (Fin 5) (Fin 5) ℝ) (y : Fin 5 → ℝ) :
    (∑ a, ∑ b, S a b * ∑ c, y c * X a b c) ^ 2 ≤ sq1 (contractX X S) * sq1 y := by
  have e : ∑ a, ∑ b, S a b * ∑ c, y c * X a b c = ∑ c, contractX X S c * y c := by
    simp only [contractX, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [sum_comm₃']
    exact sum_congr₃ fun a b c => by ring
  rw [e]
  exact sq_dot_le _ _

/-- `⟨P, M Q⟩² ≤ κ |P|² |Q|²`. -/
theorem sq_dot_op_le {M : Matrix (Fin 5) (Fin 5) ℝ} {κ : ℝ} (hM : OpBound M κ) (P Q : Fin 5 → ℝ) :
    (∑ a, P a * (M *ᵥ Q) a) ^ 2 ≤ κ * sq1 P * sq1 Q := by
  calc _ ≤ sq1 P * sq1 (M *ᵥ Q) := sq_dot_le _ _
    _ ≤ sq1 P * (κ * sq1 Q) := mul_le_mul_of_nonneg_left (hM Q) (sq1_nonneg P)
    _ = _ := by ring

theorem sum_mul_mulVec_eq (M : Matrix (Fin 5) (Fin 5) ℝ) (P Q : Fin 5 → ℝ) :
    ∑ a, ∑ b, M a b * (P a * Q b) = ∑ a, P a * (M *ᵥ Q) a := by
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem bound_c201 {M : Matrix (Fin 5) (Fin 5) ℝ} {κ : ℝ} (hM : OpBound M κ) (hκ : 0 ≤ κ)
    (y₁ y₂ z₁ z₂ : Fin 5 → ℝ) :
    (∑ a, ∑ b, M a b * ∑ a₁, y₁ a₁ * ∑ a₂, y₂ a₂ * ∑ b₁, z₁ b₁ * ∑ b₂, z₂ b₂ *
      (X a a₁ a₂ * X b b₁ b₂)) ^ 2 ≤
      κ * (sq3 X * sq1 y₁ * sq1 y₂) * (sq3 X * sq1 z₁ * sq1 z₂) := by
  have e : ∑ a, ∑ b, M a b * ∑ a₁, y₁ a₁ * ∑ a₂, y₂ a₂ * ∑ b₁, z₁ b₁ * ∑ b₂, z₂ b₂ *
      (X a a₁ a₂ * X b b₁ b₂) = ∑ a, ∑ b, M a b * (vecX X y₁ y₂ a * vecX X z₁ z₂ b) := by
    simp only [vecX]
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    exact sum_congr₆ fun a b c a' b' c' => by ring
  rw [e, sum_mul_mulVec_eq]
  refine (sq_dot_op_le hM _ _).trans ?_
  have h₁ := sq1_vecX_le X y₁ y₂
  have h₂ := sq1_vecX_le X z₁ z₂
  calc κ * sq1 (vecX X y₁ y₂) * sq1 (vecX X z₁ z₂)
      ≤ κ * (sq3 X * sq1 y₁ * sq1 y₂) * sq1 (vecX X z₁ z₂) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h₁ hκ) (sq1_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left h₂
        (mul_nonneg hκ (mul_nonneg (mul_nonneg (sq3_nonneg X) (sq1_nonneg y₁)) (sq1_nonneg y₂)))

theorem bound_c202 {M₁ M₂ : Matrix (Fin 5) (Fin 5) ℝ} {κ₁ κ₂ : ℝ} (hM₁ : OpBound M₁ κ₁)
    (hM₂ : OpBound M₂ κ₂) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) (y z : Fin 5 → ℝ) :
    (∑ a, ∑ b, M₁ a b * ∑ a', ∑ b', M₂ a' b' * ∑ a₁, y a₁ * ∑ b₁, z b₁ *
      (X a a' a₁ * X b b' b₁)) ^ 2 ≤ κ₁ * κ₂ * (sq3 X * sq1 y) * (sq3 X * sq1 z) := by
  set P := matX X y
  set Q := matX X z
  set R : Fin 5 → Fin 5 → ℝ := fun a a' => ∑ b, ∑ b', M₁ a b * M₂ a' b' * Q b b'
  have e : ∑ a, ∑ b, M₁ a b * ∑ a', ∑ b', M₂ a' b' * ∑ a₁, y a₁ * ∑ b₁, z b₁ *
      (X a a' a₁ * X b b' b₁) = ∑ a, ∑ a', P a a' * R a a' := by
    have e₁ : ∑ a, ∑ b, M₁ a b * ∑ a', ∑ b', M₂ a' b' * ∑ a₁, y a₁ * ∑ b₁, z b₁ *
        (X a a' a₁ * X b b' b₁) = ∑ a, ∑ b, ∑ a', ∑ b', M₁ a b * M₂ a' b' * (P a a' * Q b b') := by
      simp only [P, Q, matX]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      exact sum_congr₆ fun a b c a' b' c' => by ring
    rw [e₁]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    simp only [R, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun b' _ => by ring
  rw [e]
  have hR : sq2 R ≤ κ₁ * κ₂ * sq2 Q := sq2_biOp_le hM₁ hM₂ hκ₁ Q
  have hP : sq2 P ≤ sq3 X * sq1 y := sq2_matX_le X y
  have hQ : sq2 Q ≤ sq3 X * sq1 z := sq2_matX_le X z
  calc _ ≤ sq2 P * sq2 R := sum2_mul_sq_le P R
    _ ≤ (sq3 X * sq1 y) * (κ₁ * κ₂ * (sq3 X * sq1 z)) :=
        mul_le_mul hP (hR.trans (mul_le_mul_of_nonneg_left hQ (mul_nonneg hκ₁ hκ₂)))
          (sq2_nonneg R) (mul_nonneg (sq3_nonneg X) (sq1_nonneg y))
    _ = _ := by ring

theorem bound_c203 {M₁ M₂ M₃ : Matrix (Fin 5) (Fin 5) ℝ} {κ₁ κ₂ κ₃ : ℝ} (hM₁ : OpBound M₁ κ₁)
    (hM₂ : OpBound M₂ κ₂) (hM₃ : OpBound M₃ κ₃) (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) :
    (∑ a, ∑ b, M₁ a b * ∑ a', ∑ b', M₂ a' b' * ∑ a'', ∑ b'', M₃ a'' b'' *
      (X a a' a'' * X b b' b'')) ^ 2 ≤ κ₁ * κ₂ * κ₃ * sq3 X * sq3 X := by
  set W : Fin 5 → Fin 5 → Fin 5 → ℝ := fun a a' a'' =>
    ∑ b, M₁ a b * ∑ b', M₂ a' b' * ∑ b'', M₃ a'' b'' * X b b' b''
  have e : ∑ a, ∑ b, M₁ a b * ∑ a', ∑ b', M₂ a' b' * ∑ a'', ∑ b'', M₃ a'' b'' *
      (X a a' a'' * X b b' b'') = ∑ a, ∑ a', ∑ a'', X a a' a'' * W a a' a'' := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [W, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [sum_comm₃']
    exact Finset.sum_congr rfl fun a'' _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun b'' _ => by ring
  rw [e]
  have hW : sq3 W ≤ κ₁ * κ₂ * κ₃ * sq3 X := sq3_triOp_le hM₁ hM₂ hM₃ hκ₁ hκ₂ X
  calc _ ≤ sq3 X * sq3 W := sum3_mul_sq_le X W
    _ ≤ sq3 X * (κ₁ * κ₂ * κ₃ * sq3 X) := mul_le_mul_of_nonneg_left hW (sq3_nonneg X)
    _ = _ := by ring

theorem bound_c211 (S : Matrix (Fin 5) (Fin 5) ℝ) {M : Matrix (Fin 5) (Fin 5) ℝ} {κ : ℝ}
    (hM : OpBound M κ) (hκ : 0 ≤ κ) (z₁ z₂ : Fin 5 → ℝ) :
    (∑ a, ∑ b, S a b * ∑ a', ∑ b', M a' b' * ∑ b₁, z₁ b₁ * ∑ b₂, z₂ b₂ *
      (X a b a' * X b' b₁ b₂)) ^ 2 ≤ κ * sq1 (contractX X S) * (sq3 X * sq1 z₁ * sq1 z₂) := by
  set Q := vecX X z₁ z₂
  have e : ∑ a, ∑ b, S a b * ∑ a', ∑ b', M a' b' * ∑ b₁, z₁ b₁ * ∑ b₂, z₂ b₂ *
      (X a b a' * X b' b₁ b₂) = ∑ a', contractX X S a' * (M *ᵥ Q) a' := by
    have e₁ : ∑ a, ∑ b, S a b * ∑ a', ∑ b', M a' b' * ∑ b₁, z₁ b₁ * ∑ b₂, z₂ b₂ *
        (X a b a' * X b' b₁ b₂) = ∑ a, ∑ b, ∑ a', S a b * X a b a' * ∑ b', M a' b' * Q b' := by
      simp only [Q, vecX, Finset.mul_sum]
      exact sum_congr₆ fun a b c a' b' c' => by ring
    rw [e₁, sum_comm₃']
    simp only [contractX, mulVec, dotProduct, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a' _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => by ring
  rw [e]
  refine (sq_dot_op_le hM _ _).trans ?_
  exact mul_le_mul_of_nonneg_left (sq1_vecX_le X z₁ z₂) (mul_nonneg hκ (sq1_nonneg _))

theorem bound_c221 (S₁ S₂ : Matrix (Fin 5) (Fin 5) ℝ) {M : Matrix (Fin 5) (Fin 5) ℝ} {κ : ℝ}
    (hM : OpBound M κ) :
    (∑ a, ∑ b, S₁ a b * ∑ c, ∑ c', S₂ c c' * ∑ a', ∑ b', M a' b' *
      (X a b a' * X c c' b')) ^ 2 ≤ κ * sq1 (contractX X S₁) * sq1 (contractX X S₂) := by
  set η := contractX X S₂
  have e : ∑ a, ∑ b, S₁ a b * ∑ c, ∑ c', S₂ c c' * ∑ a', ∑ b', M a' b' *
      (X a b a' * X c c' b') = ∑ a', contractX X S₁ a' * (M *ᵥ η) a' := by
    have e₁ : ∀ a b, ∑ c, ∑ c', S₂ c c' * ∑ a', ∑ b', M a' b' * (X a b a' * X c c' b') =
        ∑ a', X a b a' * ∑ b', M a' b' * η b' := by
      intro a b
      simp only [η, contractX, Finset.mul_sum]
      rw [sum_comm₃']
      refine Finset.sum_congr rfl fun a' _ => ?_
      rw [sum_comm₃']
      exact Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun c' _ => by ring
    calc _ = ∑ a, ∑ b, S₁ a b * ∑ a', X a b a' * ∑ b', M a' b' * η b' :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [e₁]
      _ = ∑ a, ∑ b, ∑ a', S₁ a b * X a b a' * (M *ᵥ η) a' :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a' _ => by simp only [mulVec, dotProduct]; ring
      _ = _ := by
          rw [sum_comm₃']
          simp only [contractX, Finset.sum_mul]
          exact sum_congr₃ fun a' a b => by ring
  rw [e]
  exact sq_dot_op_le hM _ _

end ShapeBounds

/-! ### Values and bounds of the components -/

/-- Nonnegativity of the factors in the component bounds. -/
local macro "bound_nonneg" : tactic =>
  `(tactic| first
    | positivity
    | exact sq1_nonneg _
    | exact sq3_nonneg _
    | exact_mod_cast selfFactor_nonneg _)

namespace Comp

theorem xCopiesIn_edges {c : Comp} (hc : c.LeavesOK) : XCopiesIn (range 2) c.edges := by
  have h0 : (0 : ℕ) ∈ range 2 := by simp
  have h1 : (1 : ℕ) ∈ range 2 := by simp
  have n := xCopiesIn_nil (range 2)
  cases c <;> simp only [LeavesOK, leaves, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hc <;> simp only [edges]
  · exact xCopiesIn_cons_leaf h0 hc.1 (xCopiesIn_cons_leaf h0 hc.2.1
      (xCopiesIn_cons_leaf h0 hc.2.2 n))
  · exact xCopiesIn_cons_xx h0 h0 (xCopiesIn_cons_leaf h0 hc n)
  · exact xCopiesIn_cons_xx h0 h1 (xCopiesIn_cons_leaf h0 hc.1 (xCopiesIn_cons_leaf h0 hc.2.1
      (xCopiesIn_cons_leaf h1 hc.2.2.1 (xCopiesIn_cons_leaf h1 hc.2.2.2 n))))
  · exact xCopiesIn_cons_xx h0 h1 (xCopiesIn_cons_xx h0 h1 (xCopiesIn_cons_leaf h0 hc.1
      (xCopiesIn_cons_leaf h1 hc.2 n)))
  · exact xCopiesIn_cons_xx h0 h1 (xCopiesIn_cons_xx h0 h1 (xCopiesIn_cons_xx h0 h1 n))
  · exact xCopiesIn_cons_xx h0 h0 (xCopiesIn_cons_xx h0 h1 (xCopiesIn_cons_leaf h1 hc.1
      (xCopiesIn_cons_leaf h1 hc.2 n)))
  · exact xCopiesIn_cons_xx h0 h0 (xCopiesIn_cons_xx h1 h1 (xCopiesIn_cons_xx h0 h1 n))

/-- The value of a component key is the edge sum with the `X` factors of copies `0, 1`. -/
theorem eval_key {c : Comp} (hc : c.LeavesOK) (d : CertData) (ι : ℕ → Fin 5) :
    c.key.eval d ι = evalEdgesWith d ι (xProd d (range 2)) c.edges XRecord.empty := by
  rw [Key.eval_eq_of_xCopiesIn _ _ _ (xCopiesIn_edges hc)]
  simp [key, Key.prefactor]

theorem leaf_bound {d : CertData} (hd : d.Admissible) (u : Endpoint) (k : ℕ) :
    sq1 (d.A ^ k *ᵥ d.vec u) ≤ (4 / 5) ^ k * sq1 (d.vec u) :=
  sq1_pow_mulVec_le hd.isSymm hd.trace_eq_zero hd.trace_sq_eq_one k _

theorem opBound {d : CertData} (hd : d.Admissible) (k : ℕ) :
    OpBound (d.A ^ k) ((4 / 5) ^ k) :=
  opBound_pow hd.isSymm hd.trace_eq_zero hd.trace_sq_eq_one k

/-- The bound for one component: `(value)² ≤ L² ∏ |leaf|² |X|^{2·#X}`. -/
theorem eval_sq_le {c : Comp} (hc : c.LeavesOK) {d : CertData} (hd : d.Admissible)
    (ι : ℕ → Fin 5) :
    (c.key.eval d ι) ^ 2 ≤
      (c.lsq : ℝ) * (c.leaves.map fun u => sq1 (d.vec u)).prod * sq3 d.X ^ c.nX := by
  rw [eval_key hc]
  have hθ : ∀ k : ℕ, (0 : ℝ) ≤ (4 / 5) ^ k := fun k => by positivity
  have hX := sq3_nonneg d.X
  have hv := fun u => sq1_nonneg (d.vec u)
  have hs := fun k => (selfFactor_nonneg k : (0 : ℚ) ≤ _)
  cases c with
  | c100 u₁ k₁ u₂ k₂ u₃ k₃ =>
    have e : evalEdgesWith d ι (xProd d (range 2)) (c100 u₁ k₁ u₂ k₂ u₃ k₃).edges
        XRecord.empty = ∑ a, (d.A ^ k₁ *ᵥ d.vec u₁) a * ∑ b, (d.A ^ k₂ *ᵥ d.vec u₂) b *
          ∑ c, (d.A ^ k₃ *ᵥ d.vec u₃) c * d.X a b c := by
      simp only [LeavesOK, leaves, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hc
      simp only [edges, evalEdgesWith_cons_leaf _ _ _ _ _ hc.1,
        evalEdgesWith_cons_leaf _ _ _ _ _ hc.2.1, evalEdgesWith_cons_leaf _ _ _ _ _ hc.2.2,
        evalEdgesWith_nil, xProd, Finset.prod_range_succ, Finset.prod_range_zero, pushIdx,
        Function.update_apply]
      simp
    rw [e]
    refine (bound_c100 d.X _ _ _).trans ?_
    have h₁ := leaf_bound hd u₁ k₁
    have h₂ := leaf_bound hd u₂ k₂
    have h₃ := leaf_bound hd u₃ k₃
    calc sq3 d.X * (sq1 (d.A ^ k₁ *ᵥ d.vec u₁) * sq1 (d.A ^ k₂ *ᵥ d.vec u₂) *
          sq1 (d.A ^ k₃ *ᵥ d.vec u₃))
        ≤ sq3 d.X * ((4 / 5) ^ k₁ * sq1 (d.vec u₁) * ((4 / 5) ^ k₂ * sq1 (d.vec u₂)) *
          ((4 / 5) ^ k₃ * sq1 (d.vec u₃))) := by
          gcongr <;> (repeat' apply mul_nonneg) <;> bound_nonneg
      _ = _ := by simp only [lsq, leaves, nX, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil]; push_cast; ring
  | c110 s u k =>
    have e : evalEdgesWith d ι (xProd d (range 2)) (c110 s u k).edges XRecord.empty =
        ∑ a, ∑ b, (d.A ^ s) a b * ∑ c, (d.A ^ k *ᵥ d.vec u) c * d.X a b c := by
      simp only [LeavesOK, leaves, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hc
      simp only [edges, evalEdgesWith_cons_leaf _ _ _ _ _ hc,
        evalEdgesWith_cons_xx, evalEdgesWith_nil, xProd,
        Finset.prod_range_succ, Finset.prod_range_zero, pushIdx, Function.update_apply]
      simp
    rw [e]
    refine (bound_c110 d.X _ _).trans ?_
    have h₁ := leaf_bound hd u k
    have h₂ := sq1_contractX_pow_le hd s
    calc sq1 (contractX d.X (d.A ^ s)) * sq1 (d.A ^ k *ᵥ d.vec u)
        ≤ (selfFactor s : ℝ) * sq3 d.X * ((4 / 5) ^ k * sq1 (d.vec u)) := by
          gcongr <;> (repeat' apply mul_nonneg) <;> bound_nonneg
      _ = _ := by simp only [lsq, leaves, nX, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil]; push_cast; ring
  | c201 m u₁ k₁ u₂ k₂ v₁ l₁ v₂ l₂ =>
    have e : evalEdgesWith d ι (xProd d (range 2)) (c201 m u₁ k₁ u₂ k₂ v₁ l₁ v₂ l₂).edges
        XRecord.empty = ∑ a, ∑ b, (d.A ^ m) a b * ∑ a₁, (d.A ^ k₁ *ᵥ d.vec u₁) a₁ *
          ∑ a₂, (d.A ^ k₂ *ᵥ d.vec u₂) a₂ * ∑ b₁, (d.A ^ l₁ *ᵥ d.vec v₁) b₁ *
          ∑ b₂, (d.A ^ l₂ *ᵥ d.vec v₂) b₂ * (d.X a a₁ a₂ * d.X b b₁ b₂) := by
      simp only [LeavesOK, leaves, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hc
      simp only [edges, evalEdgesWith_cons_leaf _ _ _ _ _ hc.1,
        evalEdgesWith_cons_leaf _ _ _ _ _ hc.2.1,
        evalEdgesWith_cons_leaf _ _ _ _ _ hc.2.2.1,
        evalEdgesWith_cons_leaf _ _ _ _ _ hc.2.2.2,
        evalEdgesWith_cons_xx, evalEdgesWith_nil, xProd,
        Finset.prod_range_succ, Finset.prod_range_zero, pushIdx, Function.update_apply]
      simp
    rw [e]
    refine (bound_c201 d.X (opBound hd m) (hθ m) _ _ _ _).trans ?_
    have h₁ := leaf_bound hd u₁ k₁
    have h₂ := leaf_bound hd u₂ k₂
    have h₃ := leaf_bound hd v₁ l₁
    have h₄ := leaf_bound hd v₂ l₂
    calc (4 / 5) ^ m * (sq3 d.X * sq1 (d.A ^ k₁ *ᵥ d.vec u₁) * sq1 (d.A ^ k₂ *ᵥ d.vec u₂)) *
          (sq3 d.X * sq1 (d.A ^ l₁ *ᵥ d.vec v₁) * sq1 (d.A ^ l₂ *ᵥ d.vec v₂))
        ≤ (4 / 5) ^ m * (sq3 d.X * ((4 / 5) ^ k₁ * sq1 (d.vec u₁)) *
          ((4 / 5) ^ k₂ * sq1 (d.vec u₂))) * (sq3 d.X * ((4 / 5) ^ l₁ * sq1 (d.vec v₁)) *
          ((4 / 5) ^ l₂ * sq1 (d.vec v₂))) := by
          gcongr <;> (repeat' apply mul_nonneg) <;> bound_nonneg
      _ = _ := by simp only [lsq, leaves, nX, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil]; push_cast; ring
  | c202 m₁ m₂ u k v l =>
    have e : evalEdgesWith d ι (xProd d (range 2)) (c202 m₁ m₂ u k v l).edges
        XRecord.empty = ∑ a, ∑ b, (d.A ^ m₁) a b * ∑ a', ∑ b', (d.A ^ m₂) a' b' *
          ∑ a₁, (d.A ^ k *ᵥ d.vec u) a₁ * ∑ b₁, (d.A ^ l *ᵥ d.vec v) b₁ *
          (d.X a a' a₁ * d.X b b' b₁) := by
      simp only [LeavesOK, leaves, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hc
      simp only [edges, evalEdgesWith_cons_leaf _ _ _ _ _ hc.1,
        evalEdgesWith_cons_leaf _ _ _ _ _ hc.2,
        evalEdgesWith_cons_xx, evalEdgesWith_nil, xProd,
        Finset.prod_range_succ, Finset.prod_range_zero, pushIdx, Function.update_apply]
      simp
    rw [e]
    refine (bound_c202 d.X (opBound hd m₁) (opBound hd m₂) (hθ m₁) (hθ m₂) _ _).trans ?_
    have h₁ := leaf_bound hd u k
    have h₂ := leaf_bound hd v l
    calc (4 / 5) ^ m₁ * (4 / 5) ^ m₂ * (sq3 d.X * sq1 (d.A ^ k *ᵥ d.vec u)) *
          (sq3 d.X * sq1 (d.A ^ l *ᵥ d.vec v))
        ≤ (4 / 5) ^ m₁ * (4 / 5) ^ m₂ * (sq3 d.X * ((4 / 5) ^ k * sq1 (d.vec u))) *
          (sq3 d.X * ((4 / 5) ^ l * sq1 (d.vec v))) := by
          gcongr <;> (repeat' apply mul_nonneg) <;> bound_nonneg
      _ = _ := by simp only [lsq, leaves, nX, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil]; push_cast; ring
  | c203 m₁ m₂ m₃ =>
    have e : evalEdgesWith d ι (xProd d (range 2)) (c203 m₁ m₂ m₃).edges XRecord.empty =
        ∑ a, ∑ b, (d.A ^ m₁) a b * ∑ a', ∑ b', (d.A ^ m₂) a' b' * ∑ a'', ∑ b'',
          (d.A ^ m₃) a'' b'' * (d.X a a' a'' * d.X b b' b'') := by
      simp only [edges, evalEdgesWith_cons_xx, evalEdgesWith_nil, xProd,
        Finset.prod_range_succ, Finset.prod_range_zero, pushIdx, Function.update_apply]
      simp
    rw [e]
    refine (bound_c203 d.X (opBound hd m₁) (opBound hd m₂) (opBound hd m₃) (hθ m₁)
      (hθ m₂)).trans (le_of_eq ?_)
    simp only [lsq, leaves, nX, List.map_nil, List.prod_nil]; push_cast; ring
  | c211 s m v₁ l₁ v₂ l₂ =>
    have e : evalEdgesWith d ι (xProd d (range 2)) (c211 s m v₁ l₁ v₂ l₂).edges
        XRecord.empty = ∑ a, ∑ b, (d.A ^ s) a b * ∑ a', ∑ b', (d.A ^ m) a' b' *
          ∑ b₁, (d.A ^ l₁ *ᵥ d.vec v₁) b₁ * ∑ b₂, (d.A ^ l₂ *ᵥ d.vec v₂) b₂ *
          (d.X a b a' * d.X b' b₁ b₂) := by
      simp only [LeavesOK, leaves, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hc
      simp only [edges, evalEdgesWith_cons_leaf _ _ _ _ _ hc.1,
        evalEdgesWith_cons_leaf _ _ _ _ _ hc.2,
        evalEdgesWith_cons_xx, evalEdgesWith_nil, xProd,
        Finset.prod_range_succ, Finset.prod_range_zero, pushIdx, Function.update_apply]
      simp
    rw [e]
    refine (bound_c211 d.X _ (opBound hd m) (hθ m) _ _).trans ?_
    have h₁ := leaf_bound hd v₁ l₁
    have h₂ := leaf_bound hd v₂ l₂
    have h₃ := sq1_contractX_pow_le hd s
    calc (4 / 5) ^ m * sq1 (contractX d.X (d.A ^ s)) *
          (sq3 d.X * sq1 (d.A ^ l₁ *ᵥ d.vec v₁) * sq1 (d.A ^ l₂ *ᵥ d.vec v₂))
        ≤ (4 / 5) ^ m * ((selfFactor s : ℝ) * sq3 d.X) *
          (sq3 d.X * ((4 / 5) ^ l₁ * sq1 (d.vec v₁)) * ((4 / 5) ^ l₂ * sq1 (d.vec v₂))) := by
          gcongr <;> (repeat' apply mul_nonneg) <;> bound_nonneg
      _ = _ := by simp only [lsq, leaves, nX, List.map_cons, List.map_nil, List.prod_cons,
            List.prod_nil]; push_cast; ring
  | c221 s₁ s₂ m =>
    have e : evalEdgesWith d ι (xProd d (range 2)) (c221 s₁ s₂ m).edges XRecord.empty =
        ∑ a, ∑ b, (d.A ^ s₁) a b * ∑ c, ∑ c', (d.A ^ s₂) c c' * ∑ a', ∑ b', (d.A ^ m) a' b' *
          (d.X a b a' * d.X c c' b') := by
      simp only [edges, evalEdgesWith_cons_xx, evalEdgesWith_nil, xProd,
        Finset.prod_range_succ, Finset.prod_range_zero, pushIdx, Function.update_apply]
      simp
    rw [e]
    refine (bound_c221 d.X _ _ (opBound hd m)).trans ?_
    have h₁ := sq1_contractX_pow_le hd s₁
    have h₂ := sq1_contractX_pow_le hd s₂
    calc (4 / 5) ^ m * sq1 (contractX d.X (d.A ^ s₁)) * sq1 (contractX d.X (d.A ^ s₂))
        ≤ (4 / 5) ^ m * ((selfFactor s₁ : ℝ) * sq3 d.X) * ((selfFactor s₂ : ℝ) * sq3 d.X) := by
          gcongr <;> (repeat' apply mul_nonneg) <;> bound_nonneg
      _ = _ := by simp only [lsq, leaves, nX, List.map_nil, List.prod_nil]; push_cast; ring

end Comp

end OnePhaseDimension.Certificate
