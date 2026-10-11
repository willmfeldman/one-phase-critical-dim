/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Graph
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic

/-!
# Semantics of graph keys

`CertData` collects the data `A, p, ℓ, X, g, w, z` on `ℝ⁵`, and `CertData.Admissible` the
constraints under which the trace reductions hold: `A` symmetric and trace-free with
`tr A² = 1`, and `X` symmetric and trace-free.

`Key.eval k d ι` is the value of the monomial `k` at the data `d`, with free slot `i` set to
the coordinate index `ι i`. Each edge carries its own pair of summation indices for its two
endpoints; a `p` or `ℓ` endpoint contributes the corresponding coordinate, a free slot a
Kronecker delta, and the incidences at the copy `c` of `X` are collected in order of
occurrence and contribute one factor `X_{abc}`.

## Main results (keys without `X`)

* `Key.eval_eq_prod_of_hasX_eq_false`: the value factors over the edges.
* `Key.eval_canon_of_hasX_eq_false`: canonicalization is sound on admissible data.
* `Key.eval_mul_of_hasX_eq_false`: the tensor product evaluates to the product.

The general results (with copies of `X`) are in `OnePhaseDimension.Certificate.Ops`, built on
`evalEdgesWith` below.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

open Finset

/-- The data on which graph keys are evaluated. -/
structure CertData where
  /-- The symmetric matrix. -/
  A : Matrix (Fin 5) (Fin 5) ℝ
  /-- The vector `p`. -/
  p : Fin 5 → ℝ
  /-- The vector `ℓ`. -/
  ell : Fin 5 → ℝ
  /-- The cubic tensor. -/
  X : Fin 5 → Fin 5 → Fin 5 → ℝ
  /-- The scalar `g`. -/
  g : ℝ
  /-- The scalar `w`. -/
  w : ℝ
  /-- The scalar `z`. -/
  z : ℝ

namespace CertData

/-- The constraint set: `A` symmetric, trace-free, with `tr A² = 1`, and `X` symmetric and
trace-free. -/
structure Admissible (d : CertData) : Prop where
  isSymm : d.A.IsSymm
  trace_eq_zero : d.A.trace = 0
  trace_sq_eq_one : (d.A ^ 2).trace = 1
  X_swap₁₂ : ∀ a b c, d.X a b c = d.X b a c
  X_swap₂₃ : ∀ a b c, d.X a b c = d.X a c b
  X_trace : ∀ c, ∑ a, d.X a a c = 0

/-- The weight of an endpoint carrying the coordinate index `a`: a coordinate of `p` or `ℓ`, a
Kronecker delta for a free slot (with slot assignment `ι`), and `1` at an `X` incidence. -/
def weight (d : CertData) (ι : ℕ → Fin 5) : Endpoint → Fin 5 → ℝ
  | .p, a => d.p a
  | .ell, a => d.ell a
  | .x _, _ => 1
  | .slot i, a => if a = ι i then 1 else 0

/-- The value of one copy of `X` from the list of indices at its incidences. -/
def xFactor (d : CertData) : List (Fin 5) → ℝ
  | [] => 1
  | [a, b, c] => d.X a b c
  | _ => 0

/-- A symmetric cubic tensor is invariant under cyclic permutation of its slots. -/
theorem Admissible.X_cycle {d : CertData} (hd : d.Admissible) (a b c : Fin 5) :
    d.X a b c = d.X c a b := by
  rw [hd.X_swap₁₂, hd.X_swap₂₃ b a c, hd.X_swap₁₂ b c a, hd.X_swap₂₃ c b a]

end CertData

/-- Record the index `a` at an endpoint: incidences at the copy `c` of `X` are appended to the
list of that copy. -/
def pushIdx (acc : ℕ → List (Fin 5)) : Endpoint → Fin 5 → ℕ → List (Fin 5)
  | .x c, a => Function.update acc c (acc c ++ [a])
  | _, _ => acc

/-- The internal sum over a list of edges. `acc` holds the indices already placed at the
incidences of each copy of `X`, and `nX` bounds the copies of `X`. -/
def evalEdges (d : CertData) (ι : ℕ → Fin 5) (nX : ℕ) :
    List Edge → (ℕ → List (Fin 5)) → ℝ
  | [], acc => ∏ c ∈ range nX, d.xFactor (acc c)
  | e :: es, acc => ∑ a, ∑ b, d.weight ι e.u a * d.weight ι e.v b * (d.A ^ e.pow) a b *
      evalEdges d ι nX es (pushIdx (pushIdx acc e.u a) e.v b)

namespace Key

/-- The scalar prefactor `g^h w^a z^b ∏ tr A^k` of a key. -/
def prefactor (k : Key) (d : CertData) : ℝ :=
  d.g ^ k.gPow * d.w ^ k.wPow * d.z ^ k.zPow * (k.traces.map fun t => (d.A ^ t).trace).prod

/-- The value of a key at the data `d`, with free slot `i` assigned the index `ι i`. -/
def eval (k : Key) (d : CertData) (ι : ℕ → Fin 5) : ℝ :=
  k.prefactor d * evalEdges d ι k.xBound k.edges fun _ => []

end Key

/-- The value of an edge without `X` endpoints. -/
def Edge.val (d : CertData) (ι : ℕ → Fin 5) (e : Edge) : ℝ :=
  ∑ a, ∑ b, d.weight ι e.u a * d.weight ι e.v b * (d.A ^ e.pow) a b

/-- The value of a polynomial: the packed keys are unpacked. -/
def Poly.eval (P : Poly) (d : CertData) (ι : ℕ → Fin 5) : ℝ :=
  (P.map fun t => (t.2 : ℝ) * (Key.unpack t.1).eval d ι).sum

/-! ### Keys without `X` -/

theorem pushIdx_of_isX_eq_false (acc : ℕ → List (Fin 5)) {e : Endpoint} (he : e.isX = false)
    (a : Fin 5) : pushIdx acc e a = acc := by
  cases e <;> simp_all [pushIdx, Endpoint.isX]

theorem evalEdges_of_hasX_eq_false (d : CertData) (ι : ℕ → Fin 5) (nX : ℕ) :
    ∀ (es : List Edge) (acc : ℕ → List (Fin 5)), (∀ e ∈ es, e.hasX = false) →
      evalEdges d ι nX es acc = (es.map (Edge.val d ι)).prod * evalEdges d ι nX [] acc
  | [], acc, _ => by simp
  | e :: es, acc, h => by
    have he := h e (by simp)
    simp only [Edge.hasX, Bool.or_eq_false_iff] at he
    simp only [evalEdges, pushIdx_of_isX_eq_false _ he.1, pushIdx_of_isX_eq_false _ he.2,
      evalEdges_of_hasX_eq_false d ι nX es acc (fun f hf => h f (by simp [hf])),
      List.map_cons, List.prod_cons, Edge.val, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

namespace Key

theorem eval_eq_prod_of_hasX_eq_false {k : Key} (hk : k.hasX = false) (d : CertData)
    (ι : ℕ → Fin 5) : k.eval d ι = k.prefactor d * (k.edges.map (Edge.val d ι)).prod := by
  have h : ∀ e ∈ k.edges, e.hasX = false := by
    simpa [Key.hasX] using hk
  rw [eval, evalEdges_of_hasX_eq_false d ι _ _ _ h]
  simp [evalEdges, CertData.xFactor]

end Key

/-! ### Canonicalization -/

theorem reduceTraces_spec {d : CertData} (hd : d.Admissible) :
    ∀ ts : List ℕ, (ts.map fun t => (d.A ^ t).trace).prod =
      ((Key.reduceTraces ts).1 : ℝ) * ((Key.reduceTraces ts).2.map fun t => (d.A ^ t).trace).prod
  | [] => by simp [Key.reduceTraces]
  | t :: ts => by
    have ih := reduceTraces_spec hd ts
    simp only [Key.reduceTraces, List.map_cons, List.prod_cons]
    split_ifs with h0 h1 h2
    · subst h0; rw [ih]; simp [Matrix.trace_one]; ring
    · subst h1; simp [hd.trace_eq_zero]
    · subst h2; rw [ih, hd.trace_sq_eq_one, one_mul]
    · rw [ih]; simp only [List.map_cons, List.prod_cons]; ring

theorem Edge.val_orient (d : CertData) (hd : d.Admissible) (ι : ℕ → Fin 5) (e : Edge) :
    e.orient.val d ι = e.val d ι := by
  unfold Edge.orient
  split_ifs
  · simp only [Edge.val]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [(hd.isSymm.pow e.pow).apply b a]
    ring
  · rfl

theorem Edge.hasX_orient (e : Edge) : e.orient.hasX = e.hasX := by
  unfold Edge.orient Edge.hasX
  split_ifs <;> simp [Bool.or_comm]

namespace Key

theorem hasX_sortAll (k : Key) : k.sortAll.hasX = k.hasX := by
  simp only [hasX, sortAll]
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨e, he, hx⟩
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ((perm_sortBy _ _).mem_iff.1 he)
    exact ⟨f, hf, by rwa [Edge.hasX_orient] at hx⟩
  · rintro ⟨e, he, hx⟩
    exact ⟨e.orient, (perm_sortBy _ _).mem_iff.2 (List.mem_map_of_mem he),
      by rwa [Edge.hasX_orient]⟩

theorem eval_sortAll_of_hasX_eq_false {k : Key} (hk : k.hasX = false) {d : CertData}
    (hd : d.Admissible) (ι : ℕ → Fin 5) : k.sortAll.eval d ι = k.eval d ι := by
  rw [eval_eq_prod_of_hasX_eq_false hk, eval_eq_prod_of_hasX_eq_false ((hasX_sortAll k).trans hk)]
  simp only [prefactor, sortAll]
  congr 1
  · congr 1
    exact ((perm_sortBy _ _).map _).prod_eq
  · rw [((perm_sortBy _ _).map _).prod_eq, List.map_map]
    congr 1
    exact List.map_congr_left fun e _ => Edge.val_orient d hd ι e

theorem hasXTrace_eq_false {k : Key} (hk : k.hasX = false) : k.hasXTrace = false := by
  unfold hasXTrace
  rw [List.any_eq_false]
  intro e he h
  have h' := List.any_eq_false.1 hk e he
  simp only [Edge.hasX, Bool.or_eq_true, not_or, Bool.not_eq_true] at h'
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact absurd h.1.2 (by rw [h'.1]; simp)

/-- Soundness of canonicalization for keys without `X`, on admissible data. -/
theorem eval_canon_of_hasX_eq_false {k : Key} (hk : k.hasX = false) {d : CertData}
    (hd : d.Admissible) (ι : ℕ → Fin 5) :
    ((k.canon).1 : ℝ) * (k.canon).2.eval d ι = k.eval d ι := by
  have hk' : ({ k with traces := (reduceTraces k.traces).2 } : Key).hasX = false := hk
  simp only [canon, reduce, hasXTrace_eq_false hk, Bool.false_eq_true, ite_false, normalize, hk',
    eval_sortAll_of_hasX_eq_false hk' hd]
  rw [eval_eq_prod_of_hasX_eq_false hk', eval_eq_prod_of_hasX_eq_false hk]
  simp only [prefactor, reduceTraces_spec hd k.traces]
  ring

/-! ### Products -/

/-- Every free slot occurring in `k` is below its rank. -/
def SlotsBelowRank (k : Key) : Prop :=
  ∀ e ∈ k.edges, ∀ i, (e.u = .slot i ∨ e.v = .slot i) → i < k.rank

/-- The slot assignment of a product: slots below `r` are read from `ι₁`, the others from `ι₂`
after shifting by `r`. -/
def joinIdx (r : ℕ) (ι₁ ι₂ : ℕ → Fin 5) (i : ℕ) : Fin 5 := if i < r then ι₁ i else ι₂ (i - r)

theorem weight_joinIdx_left (d : CertData) {r : ℕ} (ι₁ ι₂ : ℕ → Fin 5) {e : Endpoint}
    (he : ∀ i, e = .slot i → i < r) : d.weight (joinIdx r ι₁ ι₂) e = d.weight ι₁ e := by
  cases e with
  | slot i => funext a; simp [CertData.weight, joinIdx, he i rfl]
  | _ => rfl

theorem weight_joinIdx_shift (d : CertData) (r s : ℕ) (ι₁ ι₂ : ℕ → Fin 5) (e : Endpoint) :
    d.weight (joinIdx r ι₁ ι₂) (e.shift r s) = d.weight ι₂ e := by
  cases e with
  | slot i => funext a; simp [CertData.weight, joinIdx, Endpoint.shift]
  | _ => rfl

theorem Endpoint.isX_shift (r s : ℕ) (e : Endpoint) : (e.shift r s).isX = e.isX := by
  cases e <;> rfl

/-- The tensor product of keys without `X` evaluates to the product of the values. -/
theorem eval_mul_of_hasX_eq_false {s t : Key} (hs : s.hasX = false) (ht : t.hasX = false)
    (hsr : s.SlotsBelowRank) (d : CertData) (ι₁ ι₂ : ℕ → Fin 5) :
    (s.mul t).eval d (joinIdx s.rank ι₁ ι₂) = s.eval d ι₁ * t.eval d ι₂ := by
  have hst : (s.mul t).hasX = false := by
    simp only [hasX, mul, List.any_append, List.any_map, Bool.or_eq_false_iff] at hs ht ⊢
    refine ⟨hs, ?_⟩
    rw [List.any_eq_false] at ht ⊢
    intro e he
    simpa [Edge.hasX, Edge.mapEnds, Endpoint.isX_shift] using ht e he
  rw [eval_eq_prod_of_hasX_eq_false hst, eval_eq_prod_of_hasX_eq_false hs,
    eval_eq_prod_of_hasX_eq_false ht]
  have h₁ : (s.edges.map (Edge.val d (joinIdx s.rank ι₁ ι₂))) = s.edges.map (Edge.val d ι₁) :=
    List.map_congr_left fun e he => by
      simp only [Edge.val]
      rw [weight_joinIdx_left d ι₁ ι₂ fun i hi => hsr e he i (Or.inl hi),
        weight_joinIdx_left d ι₁ ι₂ fun i hi => hsr e he i (Or.inr hi)]
  have h₂ : (t.edges.map (Edge.mapEnds (Endpoint.shift s.rank s.xBound))).map
      (Edge.val d (joinIdx s.rank ι₁ ι₂)) = t.edges.map (Edge.val d ι₂) := by
    rw [List.map_map]
    exact List.map_congr_left fun e _ => by
      simp only [Function.comp, Edge.val, Edge.mapEnds, weight_joinIdx_shift]
  simp only [prefactor, mul, List.map_append, List.prod_append, h₁, h₂, pow_add]
  ring

end Key

/-! ### The decoding examples of the paper

The three examples of the decimal encoding in the 2026-09-24 version:
`𝓜₀(200550) = g²|p|²`, `𝓜₄(000500520131)_{lijk} = p_l p_j A_{ik}` and
`𝓜₁(000771700)_l = q_l = X_{lij} A_{ij}`. -/

example (d : CertData) (ι : ℕ → Fin 5) :
    (decodeWord 0 (wordDigits 6 200550)).eval d ι = d.g ^ 2 * ∑ a, d.p a ^ 2 := by
  rw [show decodeWord 0 (wordDigits 6 200550) = ⟨0, 2, 0, 0, [], [⟨.p, .p, 0⟩]⟩ from rfl]
  simp [Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges, CertData.weight,
    Matrix.one_apply, sq]

example (d : CertData) (ι : ℕ → Fin 5) :
    (decodeWord 4 (wordDigits 12 500520131)).eval d ι =
      d.p (ι 0) * d.p (ι 2) * d.A (ι 1) (ι 3) := by
  rw [show decodeWord 4 (wordDigits 12 500520131) =
    ⟨4, 0, 0, 0, [], [⟨.p, .slot 0, 0⟩, ⟨.p, .slot 2, 0⟩, ⟨.slot 1, .slot 3, 1⟩]⟩ from rfl]
  simp [Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges, CertData.weight,
    Matrix.one_apply]
  ring

example (d : CertData) (hd : d.Admissible) (ι : ℕ → Fin 5) :
    (decodeWord 1 (wordDigits 9 771700)).eval d ι = ∑ i, ∑ j, d.X (ι 0) i j * d.A i j := by
  rw [show decodeWord 1 (wordDigits 9 771700) =
    ⟨1, 0, 0, 0, [], [⟨.x 0, .x 0, 1⟩, ⟨.x 0, .slot 0, 0⟩]⟩ from rfl]
  calc _ = ∑ i, ∑ j, d.A i j * d.X i j (ι 0) := by
        simp [Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges, CertData.weight,
          Matrix.one_apply, pushIdx, CertData.xFactor, Function.update_apply]
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [hd.X_cycle, mul_comm]


/-! ### Evaluation with a general final functional

`evalEdgesWith d ι F es acc` runs the nested sums over the index pairs of the edges `es`,
recording the indices at the copies of `X` in `acc`, and applies `F` to the final record.
`evalEdges` is the case where `F` is the product of the `X` factors over a range of copies. -/

/-- A record of the indices placed at the incidences of each copy of `X`. -/
abbrev XRecord := ℕ → List (Fin 5)

/-- The empty record. -/
abbrev XRecord.empty : XRecord := fun _ => []

/-- Record the indices `a, b` at the two endpoints of an edge. -/
def pushEdge (acc : XRecord) (e : Edge) (a b : Fin 5) : XRecord :=
  pushIdx (pushIdx acc e.u a) e.v b

/-- The internal sum over a list of edges, followed by the final functional `F`. -/
def evalEdgesWith (d : CertData) (ι : ℕ → Fin 5) (F : XRecord → ℝ) : List Edge → XRecord → ℝ
  | [], acc => F acc
  | e :: es, acc => ∑ a, ∑ b, d.weight ι e.u a * d.weight ι e.v b * (d.A ^ e.pow) a b *
      evalEdgesWith d ι F es (pushEdge acc e a b)

/-- The product of the `X` factors over a finite set of copies. -/
def xProd (d : CertData) (S : Finset ℕ) (acc : XRecord) : ℝ := ∏ c ∈ S, d.xFactor (acc c)

section EvalEdgesWith

variable (d : CertData) (ι : ℕ → Fin 5)

theorem evalEdges_eq_evalEdgesWith (nX : ℕ) :
    ∀ (es : List Edge) (acc : XRecord),
      evalEdges d ι nX es acc = evalEdgesWith d ι (xProd d (range nX)) es acc
  | [], _ => rfl
  | e :: es, acc => by
    simp only [evalEdges, evalEdgesWith, pushEdge, evalEdges_eq_evalEdgesWith nX es]

theorem Key.eval_eq_evalEdgesWith (k : Key) :
    k.eval d ι = k.prefactor d * evalEdgesWith d ι (xProd d (range k.xBound)) k.edges
      XRecord.empty := by
  rw [Key.eval, evalEdges_eq_evalEdgesWith]

theorem evalEdgesWith_cons (F : XRecord → ℝ) (e : Edge) (es : List Edge) (acc : XRecord) :
    evalEdgesWith d ι F (e :: es) acc = ∑ a, ∑ b, d.weight ι e.u a * d.weight ι e.v b *
      (d.A ^ e.pow) a b * evalEdgesWith d ι F es (pushEdge acc e a b) := rfl

theorem evalEdgesWith_append (F : XRecord → ℝ) :
    ∀ (l₁ l₂ : List Edge) (acc : XRecord),
      evalEdgesWith d ι F (l₁ ++ l₂) acc = evalEdgesWith d ι (evalEdgesWith d ι F l₂) l₁ acc
  | [], _, _ => rfl
  | e :: l₁, l₂, acc => by
    simp only [List.cons_append, evalEdgesWith, evalEdgesWith_append F l₁ l₂]

/-- Two final functionals that agree give the same value. -/
theorem evalEdgesWith_congr {F G : XRecord → ℝ} (h : ∀ acc, F acc = G acc) :
    ∀ (es : List Edge) (acc : XRecord), evalEdgesWith d ι F es acc = evalEdgesWith d ι G es acc
  | [], acc => h acc
  | e :: es, acc => by simp only [evalEdgesWith, evalEdgesWith_congr h es]

theorem evalEdgesWith_zero :
    ∀ (es : List Edge) (acc : XRecord), evalEdgesWith d ι (fun _ => 0) es acc = 0
  | [], _ => rfl
  | e :: es, acc => by simp [evalEdgesWith, evalEdgesWith_zero es]

/-- A map of records that commutes with the recording of the edges of `es` can be moved into
the final functional. -/
theorem evalEdgesWith_comp (F : XRecord → ℝ) (τ : XRecord → XRecord) :
    ∀ (es : List Edge) (acc : XRecord),
      (∀ e ∈ es, ∀ acc a b, τ (pushEdge acc e a b) = pushEdge (τ acc) e a b) →
      evalEdgesWith d ι F es (τ acc) = evalEdgesWith d ι (F ∘ τ) es acc
  | [], _, _ => rfl
  | e :: es, acc, h => by
    simp only [evalEdgesWith]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [← h e (by simp) acc a b, evalEdgesWith_comp F τ es _ fun f hf => h f (by simp [hf])]

/-- A factor of the final functional that is not changed by recording the edges of `es` can be
pulled out. -/
theorem evalEdgesWith_mul_left (G F : XRecord → ℝ) :
    ∀ (es : List Edge) (acc : XRecord),
      (∀ e ∈ es, ∀ acc a b, G (pushEdge acc e a b) = G acc) →
      evalEdgesWith d ι (fun acc => G acc * F acc) es acc = G acc * evalEdgesWith d ι F es acc
  | [], _, _ => rfl
  | e :: es, acc, h => by
    simp only [evalEdgesWith, evalEdgesWith_mul_left G F es _ (fun f hf => h f (by simp [hf])),
      h e (by simp), mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

theorem evalEdgesWith_sum {κ : Type*} (s : Finset κ) (F : κ → XRecord → ℝ) :
    ∀ (es : List Edge) (acc : XRecord),
      evalEdgesWith d ι (fun acc => ∑ x ∈ s, F x acc) es acc =
        ∑ x ∈ s, evalEdgesWith d ι (F x) es acc
  | [], _ => rfl
  | e :: es, acc => by
    simp only [evalEdgesWith, evalEdgesWith_sum s F es, mul_sum]
    exact (sum_congr rfl fun _ _ => Finset.sum_comm).trans Finset.sum_comm

/-- Relabelling the endpoints of the edges: `φ` renames endpoints, `f` renames copies of `X`
(so that recording at `φ e` and then reading through `f` is recording at `e`), and the
weights of the renamed endpoints at `ι'` are those of the original ones at `ι`. -/
theorem evalEdgesWith_map {ι' : ℕ → Fin 5} (φ : Endpoint → Endpoint) (f : ℕ → ℕ)
    (F F' : XRecord → ℝ) (hF : ∀ acc, F acc = F' (acc ∘ f))
    (hpush : ∀ (acc : XRecord) (e : Endpoint) (a : Fin 5),
      pushIdx acc (φ e) a ∘ f = pushIdx (acc ∘ f) e a) :
    ∀ (es : List Edge) (acc : XRecord),
      (∀ e ∈ es, d.weight ι' (φ e.u) = d.weight ι e.u ∧ d.weight ι' (φ e.v) = d.weight ι e.v) →
      evalEdgesWith d ι' F (es.map (Edge.mapEnds φ)) acc = evalEdgesWith d ι F' es (acc ∘ f)
  | [], acc, _ => hF acc
  | e :: es, acc, h => by
    obtain ⟨hu, hv⟩ := h e (by simp)
    simp only [List.map_cons, evalEdgesWith, Edge.mapEnds, hu, hv]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [evalEdgesWith_map φ f F F' hF hpush es _ fun g hg => h g (by simp [hg])]
    simp only [pushEdge, hpush]

end EvalEdgesWith

/-! ### Invariance under reordering, using the symmetry of `X` -/

/-- Two records that agree up to reordering at each copy. -/
def XRecord.Equiv (acc acc' : XRecord) : Prop := ∀ c, (acc c).Perm (acc' c)

theorem XRecord.Equiv.refl (acc : XRecord) : acc.Equiv acc := fun _ => List.Perm.refl _

theorem XRecord.Equiv.pushIdx {acc acc' : XRecord} (h : acc.Equiv acc') (e : Endpoint)
    (a : Fin 5) : XRecord.Equiv (OnePhaseDimension.Certificate.pushIdx acc e a)
      (OnePhaseDimension.Certificate.pushIdx acc' e a) := by
  intro c
  cases e with
  | x c' =>
    simp only [OnePhaseDimension.Certificate.pushIdx, Function.update_apply]
    split_ifs with hc
    · subst hc; exact (h c).append_right _
    · exact h c
  | _ => exact h c

theorem XRecord.Equiv.pushEdge {acc acc' : XRecord} (h : acc.Equiv acc') (e : Edge)
    (a b : Fin 5) : XRecord.Equiv (OnePhaseDimension.Certificate.pushEdge acc e a b)
      (OnePhaseDimension.Certificate.pushEdge acc' e a b) :=
  (h.pushIdx e.u a).pushIdx e.v b

theorem pushIdx_comm_equiv (acc : XRecord) (e f : Endpoint) (a b : Fin 5) :
    XRecord.Equiv (pushIdx (pushIdx acc e a) f b) (pushIdx (pushIdx acc f b) e a) := by
  intro c
  cases e <;> cases f <;> simp only [pushIdx] <;> try exact List.Perm.refl _
  rename_i c₁ c₂
  simp only [Function.update_apply]
  by_cases h₁ : c = c₁ <;> by_cases h₂ : c = c₂
  · subst h₁ h₂
    simp only [ite_true, List.append_assoc, List.cons_append, List.nil_append]
    exact List.Perm.append_left _ (List.Perm.swap _ _ _)
  · subst h₁
    simp [h₂]
  · subst h₂
    simp [h₁]
  · simp [h₁, h₂]

/-- A final functional that only depends on the records up to reordering. -/
def RespectsEquiv (F : XRecord → ℝ) : Prop := ∀ acc acc', acc.Equiv acc' → F acc = F acc'

theorem respectsEquiv_evalEdgesWith (d : CertData) (ι : ℕ → Fin 5) {F : XRecord → ℝ}
    (hF : RespectsEquiv F) : ∀ es, RespectsEquiv (evalEdgesWith d ι F es)
  | [], acc, acc', h => hF acc acc' h
  | e :: es, acc, acc', h => by
    simp only [evalEdgesWith]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [respectsEquiv_evalEdgesWith d ι hF es _ _ (h.pushEdge e a b)]

theorem sum_comm₄ (H : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, H a b c e = ∑ c, ∑ e, ∑ a, ∑ b, H a b c e := by
  calc _ = ∑ a, ∑ c, ∑ b, ∑ e, H a b c e := sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ e, H a b c e := Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ e, ∑ b, H a b c e :=
      sum_congr rfl fun c _ => sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := sum_congr rfl fun c _ => Finset.sum_comm

theorem evalEdgesWith_swap (d : CertData) (ι : ℕ → Fin 5) {F : XRecord → ℝ}
    (hF : RespectsEquiv F) (e f : Edge) (es : List Edge) (acc : XRecord) :
    evalEdgesWith d ι F (e :: f :: es) acc = evalEdgesWith d ι F (f :: e :: es) acc := by
  simp only [evalEdgesWith, mul_sum]
  rw [sum_comm₄]
  refine sum_congr rfl fun a' _ => sum_congr rfl fun b' _ => sum_congr rfl fun a _ =>
    sum_congr rfl fun b _ => ?_
  have h : XRecord.Equiv (pushEdge (pushEdge acc e a b) f a' b')
      (pushEdge (pushEdge acc f a' b') e a b) := by
    simp only [pushEdge]
    intro c
    refine (((pushIdx_comm_equiv _ _ _ _ _).pushIdx _ _) c).trans ?_
    refine ((pushIdx_comm_equiv _ _ _ _ _) c).trans ?_
    refine ((((pushIdx_comm_equiv _ _ _ _ _).pushIdx _ _).pushIdx _ _) c).trans ?_
    refine ((((pushIdx_comm_equiv _ _ _ _ _).pushIdx _ _)) c).trans ?_
    exact List.Perm.refl _
  rw [respectsEquiv_evalEdgesWith d ι hF es _ _ h]
  ring

/-- The value does not depend on the order of the edges. -/
theorem evalEdgesWith_perm (d : CertData) (ι : ℕ → Fin 5) {F : XRecord → ℝ}
    (hF : RespectsEquiv F) {es es' : List Edge} (h : es.Perm es') (acc : XRecord) :
    evalEdgesWith d ι F es acc = evalEdgesWith d ι F es' acc := by
  induction h generalizing acc with
  | nil => rfl
  | cons e _ ih => simp only [evalEdgesWith, ih]
  | swap e f es => exact evalEdgesWith_swap d ι hF f e es acc
  | trans _ _ ih₁ ih₂ => exact (ih₁ acc).trans (ih₂ acc)

/-- Reversing an edge does not change the value, for symmetric `A`. -/
theorem evalEdgesWith_flip (d : CertData) (hA : d.A.IsSymm) (ι : ℕ → Fin 5) {F : XRecord → ℝ}
    (hF : RespectsEquiv F) (e : Edge) (es : List Edge) (acc : XRecord) :
    evalEdgesWith d ι F (⟨e.v, e.u, e.pow⟩ :: es) acc = evalEdgesWith d ι F (e :: es) acc := by
  simp only [evalEdgesWith]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  have h : XRecord.Equiv (pushEdge acc ⟨e.v, e.u, e.pow⟩ b a) (pushEdge acc e a b) :=
    pushIdx_comm_equiv acc e.v e.u b a
  rw [respectsEquiv_evalEdgesWith d ι hF es _ _ h, (hA.pow e.pow).apply a b]
  ring

theorem evalEdgesWith_orient (d : CertData) (hA : d.A.IsSymm) (ι : ℕ → Fin 5) {F : XRecord → ℝ}
    (hF : RespectsEquiv F) (e : Edge) (es : List Edge) (acc : XRecord) :
    evalEdgesWith d ι F (e.orient :: es) acc = evalEdgesWith d ι F (e :: es) acc := by
  unfold Edge.orient
  split_ifs
  · exact evalEdgesWith_flip d hA ι hF e es acc
  · rfl

theorem evalEdgesWith_map_orient (d : CertData) (hA : d.A.IsSymm) (ι : ℕ → Fin 5)
    {F : XRecord → ℝ} (hF : RespectsEquiv F) :
    ∀ (es : List Edge) (acc : XRecord),
      evalEdgesWith d ι F (es.map Edge.orient) acc = evalEdgesWith d ι F es acc
  | [], _ => rfl
  | e :: es, acc => by
    rw [List.map_cons, evalEdgesWith_orient d hA ι hF]
    simp only [evalEdgesWith, evalEdgesWith_map_orient d hA ι hF es]


/-! ### The `X` factors -/

namespace CertData

variable (d : CertData)

@[simp] theorem xFactor_nil : d.xFactor [] = 1 := rfl
@[simp] theorem xFactor_singleton (a : Fin 5) : d.xFactor [a] = 0 := rfl
@[simp] theorem xFactor_pair (a b : Fin 5) : d.xFactor [a, b] = 0 := rfl
@[simp] theorem xFactor_triple (a b c : Fin 5) : d.xFactor [a, b, c] = d.X a b c := rfl
@[simp] theorem xFactor_cons₄ (a b c e : Fin 5) (l : List (Fin 5)) :
    d.xFactor (a :: b :: c :: e :: l) = 0 := rfl
@[simp] theorem xFactor_of_ne_nil (a b c : Fin 5) {l : List (Fin 5)} (hl : l ≠ []) :
    d.xFactor (a :: b :: c :: l) = 0 := by
  obtain ⟨e, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  rfl

theorem xFactor_append_perm {d : CertData} (hd : d.Admissible) {l₁ l₂ : List (Fin 5)}
    (h : l₁.Perm l₂) : ∀ pre, d.xFactor (pre ++ l₁) = d.xFactor (pre ++ l₂) := by
  induction h with
  | nil => intro; rfl
  | cons x _ ih => intro pre; simpa using ih (pre ++ [x])
  | swap x y l =>
    intro pre
    rcases pre with _ | ⟨a₁, _ | ⟨a₂, _ | ⟨a₃, pre⟩⟩⟩ <;> rcases l with _ | ⟨z, _ | ⟨w, l⟩⟩ <;>
      simp [hd.X_swap₁₂ y x, fun a => hd.X_swap₂₃ a y x]
  | trans _ _ ih₁ ih₂ => intro pre; exact (ih₁ pre).trans (ih₂ pre)

/-- For symmetric `X`, the value of a copy of `X` does not depend on the order of its
indices. -/
theorem xFactor_perm {d : CertData} (hd : d.Admissible) {l₁ l₂ : List (Fin 5)}
    (h : l₁.Perm l₂) : d.xFactor l₁ = d.xFactor l₂ :=
  xFactor_append_perm hd h []

end CertData

theorem respectsEquiv_xProd {d : CertData} (hd : d.Admissible) (S : Finset ℕ) :
    RespectsEquiv (xProd d S) := fun _ _ h =>
  prod_congr rfl fun c _ => CertData.xFactor_perm hd (h c)

@[simp] theorem xProd_empty (d : CertData) (S : Finset ℕ) : xProd d S XRecord.empty = 1 := by
  simp [xProd]

/-! ### Copies of `X` used by a list of edges -/

/-- Every copy of `X` at an endpoint of the edges `es` lies in `S`. -/
def XCopiesIn (S : Finset ℕ) (es : List Edge) : Prop :=
  ∀ e ∈ es, ∀ c, (e.u = .x c ∨ e.v = .x c) → c ∈ S

theorem pushIdx_apply_of_ne (acc : XRecord) {e : Endpoint} {c : ℕ} (h : e ≠ .x c) (a : Fin 5) :
    pushIdx acc e a c = acc c := by
  cases e with
  | x c' =>
    have : c ≠ c' := fun h' => h (by rw [h'])
    simp [pushIdx, this]
  | _ => rfl

theorem pushEdge_apply_of_ne (acc : XRecord) {e : Edge} {c : ℕ} (hu : e.u ≠ .x c)
    (hv : e.v ≠ .x c) (a b : Fin 5) : pushEdge acc e a b c = acc c := by
  rw [pushEdge, pushIdx_apply_of_ne _ hv, pushIdx_apply_of_ne _ hu]

/-- Recording the edges of `es` does not change the copies outside `S`. -/
theorem xProd_pushEdge_of_disjoint (d : CertData) {S T : Finset ℕ} (hST : Disjoint S T)
    {es : List Edge} (hes : XCopiesIn S es) :
    ∀ e ∈ es, ∀ acc a b, xProd d T (pushEdge acc e a b) = xProd d T acc := by
  intro e he acc a b
  refine prod_congr rfl fun c hc => ?_
  have hc' : c ∉ S := fun h => Finset.disjoint_left.1 hST h hc
  rw [pushEdge_apply_of_ne acc (fun h => hc' (hes e he c (Or.inl h)))
    (fun h => hc' (hes e he c (Or.inr h)))]

/-- Enlarging the set of copies in the product of the `X` factors does not change the value. -/
theorem evalEdgesWith_xProd_union (d : CertData) (ι : ℕ → Fin 5) {S : Finset ℕ}
    {es : List Edge} (hes : XCopiesIn S es) (T : Finset ℕ) :
    evalEdgesWith d ι (xProd d (S ∪ T)) es XRecord.empty =
      evalEdgesWith d ι (xProd d S) es XRecord.empty := by
  have h : ∀ acc, xProd d (S ∪ T) acc = xProd d (T \ S) acc * xProd d S acc := fun acc => by
    rw [xProd, xProd, xProd, ← prod_union Finset.sdiff_disjoint, Finset.sdiff_union_self_eq_union,
      Finset.union_comm]
  rw [evalEdgesWith_congr d ι h, evalEdgesWith_mul_left d ι _ _ es _
    (xProd_pushEdge_of_disjoint d Finset.disjoint_sdiff hes), xProd_empty, one_mul]

namespace Key

theorem le_xBound_foldr {e : Edge} :
    ∀ {es : List Edge}, e ∈ es →
      max (xBound.bound e.u) (xBound.bound e.v) ≤
        es.foldr (fun e acc => max acc (max (xBound.bound e.u) (xBound.bound e.v))) 0
  | f :: es, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_right _ _
    · exact (le_xBound_foldr h).trans (le_max_left _ _)

theorem le_xBound {k : Key} {e : Edge} (he : e ∈ k.edges) :
    max (xBound.bound e.u) (xBound.bound e.v) ≤ k.xBound :=
  le_xBound_foldr he

theorem xBound.bound_x (c : ℕ) : xBound.bound (.x c) = c + 1 := rfl

theorem xCopiesIn_range_xBound (k : Key) : XCopiesIn (range k.xBound) k.edges := by
  intro e he c hc
  have h := le_xBound he
  rw [Finset.mem_range]
  rcases hc with hc | hc <;> rw [hc, xBound.bound_x] at h <;> omega

/-- The value of a key, with the product of the `X` factors over any finite set of copies
containing those that occur. -/
theorem eval_eq_of_xCopiesIn (k : Key) (d : CertData) (ι : ℕ → Fin 5) {S : Finset ℕ}
    (hS : XCopiesIn S k.edges) :
    k.eval d ι = k.prefactor d * evalEdgesWith d ι (xProd d S) k.edges XRecord.empty := by
  rw [eval_eq_evalEdgesWith, ← evalEdgesWith_xProd_union d ι (xCopiesIn_range_xBound k) S,
    Finset.union_comm, evalEdgesWith_xProd_union d ι hS]

end Key

end OnePhaseDimension.Certificate
