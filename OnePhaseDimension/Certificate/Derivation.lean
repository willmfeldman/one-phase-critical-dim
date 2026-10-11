/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Ops

/-!
# The graph derivative

The derivation `D_l` acts on functions of `(A, p, g)` along the generator
`D_l A = X_l - q_l A`, `D_l p = w A_{l·} - g z δ_{l·}`, `D_l g = z p_l`. On a graph key without
copies of `X` it is computed by the product rule (the 2026-09-24 version, Section "Exact
contraction and differentiation rules"):

* an edge carrying `A^k` between `u` and `v` gives, for `0 ≤ h < k`, the path `u — A^h — X —
  A^{k-1-h} — v` through a new copy of `X` whose third slot is the derivative index;
* a trace `tr A^k` gives `k tr(A^{k-1} X_l)`;
* the terms `-q_l A` of all matrix factors combine into `-(total A-degree) q_l` times the key;
* each `p` endpoint is replaced by `w A_{l·} - g z δ_{l·}`;
* a factor `g^h` gives `h z g^{h-1} p_l`.

The derivative index is the new free slot `r` (the rank of the key), and the new copy of `X`
is the copy `0` (the key has no copy of `X`). The result is a list of integer coefficients and
keys of rank `r + 1`; `Key.deriv` collects it into a polynomial.

This file contains the definitions and the values of the inserted blocks of edges; the identity
with the directional derivative is in `OnePhaseDimension.Certificate.DerivationSound`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

open Finset

/-- A term of the derivative of a list of edges: a coefficient, the increments of the power of
`w` and of the powers of `g` and `z` (both by `dgz`), the edges kept, and the inserted block of
edges replacing the differentiated edge. -/
structure DTerm where
  /-- The coefficient. -/
  c : ℤ
  /-- The increment of the power of `w`. -/
  dw : ℕ
  /-- The increment of the powers of `g` and `z`. -/
  dgz : ℕ
  /-- The edges that are not differentiated. -/
  free : List Edge
  /-- The block replacing the differentiated edge. -/
  block : List Edge

/-- The path through a new copy `0` of `X` replacing an edge `A^k` (`0 ≤ h < k`). -/
def pathBlock (r : ℕ) (u v : Endpoint) (h m : ℕ) : List Edge :=
  [⟨u, .x 0, h⟩, ⟨.x 0, v, m⟩, ⟨.x 0, .slot r, 0⟩]

/-- The terms of the derivative of one edge (without the `-q_l A` part): the path insertions
and the replacement of a `p` endpoint by `w A_{l·}` and by `-g z δ_{l·}`. Each entry is
`(coefficient, dw, dgz, block)`. -/
def edgeDeriv (r : ℕ) (e : Edge) : List (ℤ × ℕ × ℕ × List Edge) :=
  ((List.range e.pow).map fun h => ((1 : ℤ), 0, 0, pathBlock r e.u e.v h (e.pow - 1 - h))) ++
    ((if e.u = .p then [((1 : ℤ), 1, 0, [⟨.slot r, e.v, e.pow + 1⟩]),
        (-1, 0, 1, [⟨.slot r, e.v, e.pow⟩])] else []) ++
      (if e.v = .p then [((1 : ℤ), 1, 0, [⟨e.u, .slot r, e.pow + 1⟩]),
        (-1, 0, 1, [⟨e.u, .slot r, e.pow⟩])] else []))

/-- The product rule over a list of edges. -/
def edgesDeriv (r : ℕ) : List Edge → List DTerm
  | [] => []
  | e :: es =>
    (edgeDeriv r e).map (fun t => ⟨t.1, t.2.1, t.2.2.1, es, t.2.2.2⟩) ++
      (edgesDeriv r es).map fun t => { t with free := e :: t.free }

/-- The block `tr(A^{k-1} X_l)` replacing a trace factor `tr A^k`. -/
def traceBlock (r k : ℕ) : List Edge := [⟨.x 0, .x 0, k - 1⟩, ⟨.x 0, .slot r, 0⟩]

/-- The product rule over the trace factors: `(k, remaining traces, block)`. -/
def tracesDeriv (r : ℕ) : List ℕ → List (ℤ × List ℕ × List Edge)
  | [] => []
  | t :: ts => ((t : ℤ), ts, traceBlock r t) ::
      (tracesDeriv r ts).map fun u => (u.1, t :: u.2.1, u.2.2)

/-- The total degree in `A` of a key: the sum of the powers of its edges and traces. -/
def Key.degA (k : Key) : ℕ := (k.edges.map Edge.pow).sum + k.traces.sum

namespace Key

/-- The key of the derivative term of an edge-derivative term `t`. -/
def edgeTermKey (k : Key) (t : DTerm) : Key :=
  { k with rank := k.rank + 1, gPow := k.gPow + t.dgz, wPow := k.wPow + t.dw,
           zPow := k.zPow + t.dgz, edges := t.free ++ t.block }

/-- The key of the derivative term of a trace factor. -/
def traceTermKey (k : Key) (t : ℤ × List ℕ × List Edge) : Key :=
  { k with rank := k.rank + 1, traces := t.2.1, edges := k.edges ++ t.2.2 }

/-- The key of the derivative term of the factor `g^h`: `g^{h-1} z p_l`. -/
def gTermKey (k : Key) : Key :=
  { k with rank := k.rank + 1, gPow := k.gPow - 1, zPow := k.zPow + 1,
           edges := k.edges ++ [⟨.p, .slot k.rank, 0⟩] }

/-- The key `q_l · k`. -/
def qTermKey (k : Key) : Key :=
  { k with rank := k.rank + 1, edges := k.edges ++ [⟨.x 0, .x 0, 1⟩, ⟨.x 0, .slot k.rank, 0⟩] }

/-- The terms of the graph derivative `D_l k`, with `l` the new free slot `k.rank`, as a list
of integer coefficients and keys (before canonicalization). Meaningful for keys without copies
of `X`. -/
def derivTerms (k : Key) : List (ℤ × Key) :=
  ((edgesDeriv k.rank k.edges).map fun t => (t.c, k.edgeTermKey t)) ++
    ((tracesDeriv k.rank k.traces).map fun t => (t.1, k.traceTermKey t)) ++
    [((k.gPow : ℤ), k.gTermKey), (-(k.degA : ℤ), k.qTermKey)]

/-- The graph derivative `D_l k` collected into a polynomial. -/
def deriv (k : Key) : Poly := Poly.mergeAll (k.derivTerms.map fun t => Key.term t.1 t.2)

end Key

/-! ### Values of keys made of free edges and a block -/

/-- The value of a block of edges whose copies of `X` are among `{0}`. -/
def blockVal (d : CertData) (ι : ℕ → Fin 5) (B : List Edge) : ℝ :=
  evalEdgesWith d ι (xProd d {0}) B XRecord.empty

theorem evalEdgesWith_of_hasX_eq_false' (d : CertData) (ι : ℕ → Fin 5) (F : XRecord → ℝ) :
    ∀ (es : List Edge) (acc : XRecord), (∀ e ∈ es, e.hasX = false) →
      evalEdgesWith d ι F es acc = (es.map (Edge.val d ι)).prod * F acc
  | [], _, _ => by simp [evalEdgesWith]
  | e :: es, acc, h => by
    have he := h e (by simp)
    simp only [Edge.hasX, Bool.or_eq_false_iff] at he
    simp only [evalEdgesWith, pushEdge, pushIdx_of_isX_eq_false _ he.1,
      pushIdx_of_isX_eq_false _ he.2,
      evalEdgesWith_of_hasX_eq_false' d ι F es acc (fun f hf => h f (by simp [hf])),
      List.map_cons, List.prod_cons, Edge.val, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/-- A key whose edges are free edges (without `X`) followed by a block using only the copy `0`
of `X`. -/
theorem Key.eval_free_append_block (K : Key) {free block : List Edge}
    (hK : K.edges = free ++ block) (hfree : ∀ e ∈ free, e.hasX = false)
    (hblock : XCopiesIn {0} block) (d : CertData) (ι : ℕ → Fin 5) :
    K.eval d ι = K.prefactor d * ((free.map (Edge.val d ι)).prod * blockVal d ι block) := by
  have hS : XCopiesIn {0} K.edges := by
    rw [hK]
    intro e he c hc
    rcases List.mem_append.1 he with he | he
    · have h := hfree e he
      simp only [Edge.hasX, Bool.or_eq_false_iff] at h
      rcases hc with hc | hc <;> simp [hc, Endpoint.isX] at h
    · exact hblock e he c hc
  rw [eval_eq_of_xCopiesIn K d ι hS, hK, evalEdgesWith_append,
    evalEdgesWith_of_hasX_eq_false' d ι _ free _ hfree, blockVal]

/-! ### The blocks -/

section Blocks

variable (d : CertData) (ι : ℕ → Fin 5)

@[simp] theorem weight_x (c : ℕ) (a : Fin 5) : d.weight ι (.x c) a = 1 := rfl

omit d ι in
theorem pushIdx_x (acc : XRecord) (c : ℕ) (a : Fin 5) :
    pushIdx acc (.x c) a = Function.update acc c (acc c ++ [a]) := rfl

theorem weight_slot (i : ℕ) (a : Fin 5) : d.weight ι (.slot i) a = if a = ι i then 1 else 0 :=
  rfl

theorem blockVal_pathBlock {u v : Endpoint} (hu : u.isX = false) (hv : v.isX = false)
    (r h m : ℕ) :
    blockVal d ι (pathBlock r u v h m) = ∑ a, ∑ c, ∑ e, ∑ b, d.weight ι u a * (d.A ^ h) a c *
      (d.weight ι v b * (d.A ^ m) e b * d.X c e (ι r)) := by
  simp only [blockVal, pathBlock, evalEdgesWith, pushEdge, pushIdx_of_isX_eq_false _ hu,
    pushIdx_of_isX_eq_false _ hv, pushIdx_slot, weight_x, weight_slot, pow_zero,
    Matrix.one_apply, xProd, Finset.prod_singleton, pushIdx_x, Function.update_apply,
    XRecord.empty]
  simp only [ite_true, List.nil_append, List.cons_append, CertData.xFactor_triple, mul_one,
    one_mul, mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq, sum_ite_eq', mem_univ]
  simp only [mul_sum]

theorem blockVal_traceBlock (r k : ℕ) :
    blockVal d ι (traceBlock r k) = ∑ a, ∑ b, (d.A ^ (k - 1)) a b * d.X a b (ι r) := by
  simp only [blockVal, traceBlock, evalEdgesWith, pushEdge, pushIdx_slot, weight_x, weight_slot,
    pow_zero, Matrix.one_apply, xProd, Finset.prod_singleton, pushIdx_x, Function.update_apply,
    XRecord.empty]
  simp only [ite_true, List.nil_append, List.cons_append, CertData.xFactor_triple, mul_one,
    one_mul, mul_ite, mul_zero, ite_mul, zero_mul, sum_ite_eq, sum_ite_eq', mem_univ]

theorem blockVal_of_hasX_eq_false {B : List Edge} (hB : ∀ e ∈ B, e.hasX = false) :
    blockVal d ι B = (B.map (Edge.val d ι)).prod := by
  rw [blockVal, evalEdgesWith_of_hasX_eq_false' d ι _ B _ hB]
  simp [xProd]

end Blocks

end OnePhaseDimension.Certificate
