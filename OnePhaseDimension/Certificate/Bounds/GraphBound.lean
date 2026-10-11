/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Bounds.GraphShapes
public import Mathlib.Data.Rat.BigOperators

/-!
# The complete graph bound

For a scalar graph key `t` of degree two in `(w, z, ℓ, X)` we prove

  `(𝓜(t))² ≤ L_t² · y_i² · y_j²`  on `g² + |p|² ≤ 1`,

where `y = (|w|, |z|, |ℓ|, |X|)`, `(i, j)` are the two degree types of `t`, and `L_t²` is the
product rule of the 2026-09-24 version (section "Bounds for scalar graphs"):

* a factor `θ^{k-2}` for each trace `tr A^k`, replaced by `9/20` for `k = 3`;
* `θ^k` for an edge of power `k` between distinct vertices (separate occurrences of `p` count as
  distinct vertices);
* `5/7` or `θ^{k-1}` for a self-edge of power `k = 1` or `k ≥ 2` at a copy of `X`;
* the mixed factor `(h/(h+b))^h (b/(h+b))^b`, where `h` is the power of `g` and `b` the number
  of `p` endpoints (this is `1` when `h = 0` or `b = 0`).

`Lsq : Key → ℚ` computes `L_t²` from the key. The proof goes through a *witness*: the key is
split into its scalar factors, its edges between vectors, and connected components containing
a copy of `X` (`Comp`). `classify` builds the witness from the key and checks, by computation,
that the normal form of the witness key is `t`, that the witness bound is `Lsq t`, and that the
degree types agree. `graph_bound` then holds for every key accepted by `classify`.

The 2026-09-24 version proves the bound by a case analysis of graph components; we prove it
for each of the seven component shapes and certify by computation that a given key is a product
of such components.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate

open Matrix Finset

/-! ### The product rule -/

/-- `θ = 4/5`. -/
abbrev theta : ℚ := 4 / 5

/-- The bound factor of a trace `tr A^k`: `θ^{k-2}`, and `9/20` for `k = 3` (also `25, 0, 1`
for `k = 0, 1, 2`, the exact values of `(tr A^k)²`). -/
def traceFactor : ℕ → ℚ
  | 0 => 25
  | 1 => 0
  | 2 => 1
  | 3 => 9 / 20
  | k + 4 => theta ^ (k + 2)

/-- Whether an edge is a self-edge at a copy of `X`. -/
def Edge.isSelf (e : Edge) : Bool := e.u.isX && e.u == e.v

/-- The bound factor of an edge: `selfFactor k` for a self-edge, `θ^k` otherwise. -/
def edgeFactor (e : Edge) : ℚ := if e.isSelf then selfFactor e.pow else theta ^ e.pow

/-- The mixed factor `(h/(h+b))^h (b/(h+b))^b`. -/
def mixedFactor (h b : ℕ) : ℚ := ((h : ℚ) / (h + b)) ^ h * ((b : ℚ) / (h + b)) ^ b

/-- Number of occurrences of an endpoint at the ends of a list of edges. -/
def endCount (x : Endpoint) (es : List Edge) : ℕ :=
  (es.map fun e => (if e.u = x then 1 else 0) + (if e.v = x then 1 else 0)).sum

/-- The squared bound factor `L_t²` of a key. -/
def Lsq (t : Key) : ℚ :=
  (t.traces.map traceFactor).prod * (t.edges.map edgeFactor).prod *
    mixedFactor t.gPow (endCount .p t.edges)

/-! ### Degree types -/

/-- The degree types of a key, `1 = w`, `2 = z`, `3 = ℓ`, `4 = X`, with multiplicity. -/
def Key.types (t : Key) : List ℕ :=
  List.replicate t.wPow 1 ++ List.replicate t.zPow 2 ++
    List.replicate (endCount .ell t.edges) 3 ++ List.replicate t.xBound 4

/-- The first degree type. -/
def Key.typeI (t : Key) : ℕ := t.types.getD 0 0

/-- The second degree type. -/
def Key.typeJ (t : Key) : ℕ := t.types.getD 1 0

/-- The squared norms `y_i²`: `w²`, `z²`, `|ℓ|²`, `|X|²` for `i = 1, 2, 3, 4`. -/
def ysq (i : ℕ) (d : CertData) : ℝ :=
  match i with
  | 1 => d.w ^ 2
  | 2 => d.z ^ 2
  | 3 => sq1 d.ell
  | 4 => sq3 d.X
  | _ => 0

/-- The norms `y_i = (|w|, |z|, |ℓ|, |X|)_i`. -/
def yNorm (i : ℕ) (d : CertData) : ℝ := Real.sqrt (ysq i d)

theorem ysq_nonneg (i : ℕ) (d : CertData) : 0 ≤ ysq i d := by
  unfold ysq
  split
  · positivity
  · positivity
  · exact sq1_nonneg _
  · exact sq3_nonneg _
  · exact le_rfl

/-! ### Witnesses -/

/-- The key of a list of components (their product). -/
def compsKey : List Comp → Key
  | [] => ⟨0, 0, 0, 0, [], []⟩
  | c :: cs => c.key.mul (compsKey cs)

/-- A decomposition of a scalar graph key: scalar factors, edges between vectors, and
components containing copies of `X`. -/
structure Witness where
  /-- Power of `g`. -/
  gPow : ℕ
  /-- Power of `w`. -/
  wPow : ℕ
  /-- Power of `z`. -/
  zPow : ℕ
  /-- Trace powers. -/
  traces : List ℕ
  /-- Edges between two vectors. -/
  leafEdges : List Edge
  /-- Components containing a copy of `X`. -/
  comps : List Comp
  deriving DecidableEq, Repr

namespace Witness

/-- The scalar part of the witness key. -/
def pre (w : Witness) : Key := ⟨0, w.gPow, w.wPow, w.zPow, w.traces, w.leafEdges⟩

/-- The key of a witness. -/
def key (w : Witness) : Key := w.pre.mul (compsKey w.comps)

/-- All leaf endpoints, with multiplicity. -/
def leaves (w : Witness) : List Endpoint :=
  w.leafEdges.flatMap (fun e => [e.u, e.v]) ++ w.comps.flatMap Comp.leaves

/-- Number of copies of `X`. -/
def nX (w : Witness) : ℕ := (w.comps.map Comp.nX).sum

/-- The squared bound factor of a witness. -/
def lsq (w : Witness) : ℚ :=
  (w.traces.map traceFactor).prod * (w.leafEdges.map fun e => theta ^ e.pow).prod *
    (w.comps.map Comp.lsq).prod * mixedFactor w.gPow (w.leaves.count .p)

/-- The degree types of a witness. -/
def types (w : Witness) : List ℕ :=
  List.replicate w.wPow 1 ++ List.replicate w.zPow 2 ++
    List.replicate (w.leaves.count .ell) 3 ++ List.replicate w.nX 4

/-- All leaf endpoints are copies of `p` or `ℓ` (Boolean form). -/
def valid (w : Witness) : Bool :=
  w.leafEdges.all (fun e => e.u.isLeaf && e.v.isLeaf) && w.comps.all fun c => c.leaves.all
    Endpoint.isLeaf

end Witness

/-! ### Building the witness of a key -/

/-- The leaf (with the power of the edge) joined to the copy `c` of `X` by `e`, if any. -/
def leafAt (c : ℕ) (e : Edge) : Option (Endpoint × ℕ) :=
  if e.u = .x c ∧ e.v.isLeaf = true then some (e.v, e.pow)
  else if e.v = .x c ∧ e.u.isLeaf = true then some (e.u, e.pow) else none

/-- The power of `e` if it is a self-edge at the copy `c`. -/
def selfAt (c : ℕ) (e : Edge) : Option ℕ :=
  if e.u = .x c ∧ e.v = .x c then some e.pow else none

/-- The power of `e` if it joins the copies `0` and `1`. -/
def crossPow (e : Edge) : Option ℕ :=
  if (e.u = .x 0 ∧ e.v = .x 1) ∨ (e.u = .x 1 ∧ e.v = .x 0) then some e.pow else none

/-- A component with one copy of `X`, from its leaves and self-edges. -/
def singleComp : List (Endpoint × ℕ) → List ℕ → Option Comp
  | [(u₁, k₁), (u₂, k₂), (u₃, k₃)], [] => some (.c100 u₁ k₁ u₂ k₂ u₃ k₃)
  | [(u, k)], [s] => some (.c110 s u k)
  | _, _ => none

/-- A connected component with two copies of `X`. -/
def pairComp (cr : List ℕ) (l₀ : List (Endpoint × ℕ)) (s₀ : List ℕ) (l₁ : List (Endpoint × ℕ))
    (s₁ : List ℕ) : Option Comp :=
  match cr, l₀, s₀, l₁, s₁ with
  | [m], [(u₁, k₁), (u₂, k₂)], [], [(v₁, l₁), (v₂, l₂)], [] =>
    some (.c201 m u₁ k₁ u₂ k₂ v₁ l₁ v₂ l₂)
  | [m], [], [s], [(v₁, l₁), (v₂, l₂)], [] => some (.c211 s m v₁ l₁ v₂ l₂)
  | [m], [(v₁, l₁), (v₂, l₂)], [], [], [s] => some (.c211 s m v₁ l₁ v₂ l₂)
  | [m], [], [s₁], [], [s₂] => some (.c221 s₁ s₂ m)
  | [m₁, m₂], [(u, k)], [], [(v, l)], [] => some (.c202 m₁ m₂ u k v l)
  | [m₁, m₂, m₃], [], [], [], [] => some (.c203 m₁ m₂ m₃)
  | _, _, _, _, _ => none

/-- The components of the edges `es` with `nX` copies of `X`. -/
def parseComps (es : List Edge) (nX : ℕ) : Option (List Comp) :=
  let l₀ := es.filterMap (leafAt 0)
  let l₁ := es.filterMap (leafAt 1)
  let s₀ := es.filterMap (selfAt 0)
  let s₁ := es.filterMap (selfAt 1)
  let cr := es.filterMap crossPow
  match nX with
  | 0 => some []
  | 1 => (singleComp l₀ s₀).map fun c => [c]
  | 2 =>
    if cr = [] then
      match singleComp l₀ s₀, singleComp l₁ s₁ with
      | some a, some b => some [a, b]
      | _, _ => none
    else (pairComp cr l₀ s₀ l₁ s₁).map fun c => [c]
  | _ => none

/-- The witness read off a key (not yet checked). -/
def parseWitness (t : Key) : Option Witness :=
  (parseComps (t.edges.filter Edge.hasX) t.xBound).map fun cs =>
    ⟨t.gPow, t.wPow, t.zPow, t.traces, t.edges.filter fun e => !e.hasX, cs⟩

/-- The checked witness of a scalar graph key: the parsed witness, provided that it is valid,
that the normal form of its key is `t`, that its bound is `Lsq t`, and that its degree types
are those of `t` and are two in number. -/
def classify (t : Key) : Option Witness :=
  match parseWitness t with
  | some w =>
    if w.valid = true ∧ w.key.normalize = t ∧ w.lsq = Lsq t ∧ w.types = t.types ∧
        t.types.length = 2 then some w else none
  | none => none

/-! ### Bounds for the factors -/

/-- Squares of products of bounded factors. -/
theorem sq_list_prod_le {α : Type*} (l : List α) (f g : α → ℝ)
    (h : ∀ a ∈ l, f a ^ 2 ≤ g a) : (l.map f).prod ^ 2 ≤ (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, mul_pow]
    exact mul_le_mul (h a (by simp)) (ih fun b hb => h b (by simp [hb])) (sq_nonneg _)
      ((sq_nonneg _).trans (h a (by simp)))

theorem cast_list_prod_map {α : Type*} (l : List α) (f : α → ℚ) :
    (((l.map f).prod : ℚ) : ℝ) = (l.map fun a => (f a : ℝ)).prod := by
  rw [Rat.cast_list_prod, List.map_map]
  rfl

theorem trace_sq_le_traceFactor {d : CertData} (hd : d.Admissible) (k : ℕ) :
    (d.A ^ k).trace ^ 2 ≤ (traceFactor k : ℝ) := by
  have hA := hd.isSymm
  have h0 := hd.trace_eq_zero
  have h1 := hd.trace_sq_eq_one
  match k with
  | 0 => simp [traceFactor, Matrix.trace_one]; norm_num
  | 1 => simp [traceFactor, h0]
  | 2 => simp [traceFactor, h1]
  | 3 => simpa [traceFactor] using trace_cube_sq_le hA h0 h1
  | k + 4 =>
    have := trace_pow_sq_le hA h0 h1 (k + 2)
    simpa [traceFactor] using this

/-- The value of an edge between two vectors is bounded by `θ^k |u|² |v|²`. -/
theorem Edge.val_sq_le {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5) {e : Edge}
    (hu : e.u.isLeaf = true) (hv : e.v.isLeaf = true) :
    (e.val d ι) ^ 2 ≤ (4 / 5) ^ e.pow * (sq1 (d.vec e.u) * sq1 (d.vec e.v)) := by
  have e₁ : e.val d ι = ∑ a, d.vec e.u a * (d.A ^ e.pow *ᵥ d.vec e.v) a := by
    simp only [Edge.val, d.weight_of_isLeaf ι hu, d.weight_of_isLeaf ι hv, mulVec, dotProduct,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e₁]
  refine (sq_dot_op_le (Comp.opBound hd e.pow) _ _).trans (le_of_eq ?_)
  ring

/-! ### Products of components -/

theorem Comp.lsq_nonneg (c : Comp) : 0 ≤ c.lsq := by
  have := selfFactor_nonneg
  cases c <;> simp only [Comp.lsq]
  · positivity
  · exact mul_nonneg (this _) (by positivity)
  · positivity
  · positivity
  · positivity
  · exact mul_nonneg (this _) (by positivity)
  · exact mul_nonneg (mul_nonneg (this _) (this _)) (by positivity)

theorem joinIdx_zero (ι : ℕ → Fin 5) : Key.joinIdx 0 ι ι = ι := by
  funext i
  simp [Key.joinIdx]

theorem Comp.slotsBelowRank {c : Comp} (hc : c.LeavesOK) : c.key.SlotsBelowRank := by
  intro e he i hi
  have h := Comp.xCopiesIn_edges hc
  exfalso
  cases c <;> simp only [key, edges, List.mem_cons, List.not_mem_nil, or_false] at he <;>
    simp only [LeavesOK, leaves, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hc <;>
    rcases he with rfl | rfl | rfl | rfl | rfl <;>
    simp_all [Endpoint.isLeaf]

theorem eval_compsKey_nil (d : CertData) (ι : ℕ → Fin 5) : (compsKey []).eval d ι = 1 := by
  simp [compsKey, Key.eval, Key.prefactor, Key.xBound, evalEdges]

theorem eval_compsKey_sq_le {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5) :
    ∀ cs : List Comp, (∀ c ∈ cs, c.LeavesOK) →
      (compsKey cs).eval d ι ^ 2 ≤ ((cs.map Comp.lsq).prod : ℝ) *
        ((cs.flatMap Comp.leaves).map fun u => sq1 (d.vec u)).prod *
          sq3 d.X ^ (cs.map Comp.nX).sum
  | [], _ => by simp [eval_compsKey_nil]
  | c :: cs, h => by
    have hc := h c (by simp)
    have ih := eval_compsKey_sq_le hd ι cs fun c' hc' => h c' (by simp [hc'])
    have hmul := Key.eval_mul (t := compsKey cs) (Comp.slotsBelowRank hc) d ι ι
    rw [show c.key.rank = 0 from rfl, joinIdx_zero] at hmul
    simp only [compsKey]
    rw [hmul, mul_pow]
    have hb := Comp.eval_sq_le hc hd ι
    calc c.key.eval d ι ^ 2 * (compsKey cs).eval d ι ^ 2
        ≤ ((c.lsq : ℝ) * (c.leaves.map fun u => sq1 (d.vec u)).prod * sq3 d.X ^ c.nX) *
          (((cs.map Comp.lsq).prod : ℝ) *
            ((cs.flatMap Comp.leaves).map fun u => sq1 (d.vec u)).prod *
              sq3 d.X ^ (cs.map Comp.nX).sum) :=
          mul_le_mul hb ih (sq_nonneg _) ((sq_nonneg _).trans hb)
      _ = _ := by
          simp only [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
            List.prod_append, List.sum_cons, pow_add]
          push_cast
          ring

/-! ### Counting leaves -/

theorem prod_map_sq1_vec {d : CertData} :
    ∀ L : List Endpoint, (∀ u ∈ L, u.isLeaf = true) →
      (L.map fun u => sq1 (d.vec u)).prod =
        sq1 d.p ^ L.count .p * sq1 d.ell ^ L.count .ell
  | [], _ => by simp
  | u :: L, h => by
    have hu := h u (by simp)
    rw [List.map_cons, List.prod_cons, prod_map_sq1_vec L fun v hv => h v (by simp [hv]),
      List.count_cons, List.count_cons]
    cases u <;> simp [Endpoint.isLeaf] at hu <;> simp [CertData.vec, pow_succ] <;> ring

/-! ### The bound for a witness -/

namespace Witness

theorem pre_slotsBelowRank {w : Witness} (hw : ∀ e ∈ w.leafEdges, e.u.isLeaf = true ∧
    e.v.isLeaf = true) : w.pre.SlotsBelowRank := by
  intro e he i hi
  obtain ⟨hu, hv⟩ := hw e he
  rcases hi with h | h
  · rw [h] at hu; simp [Endpoint.isLeaf] at hu
  · rw [h] at hv; simp [Endpoint.isLeaf] at hv

theorem pre_hasX {w : Witness} (hw : ∀ e ∈ w.leafEdges, e.u.isLeaf = true ∧
    e.v.isLeaf = true) : w.pre.hasX = false := by
  simp only [Key.hasX, pre, List.any_eq_false]
  intro e he
  obtain ⟨hu, hv⟩ := hw e he
  simp [Edge.hasX, Endpoint.isX_eq_false_of_isLeaf hu, Endpoint.isX_eq_false_of_isLeaf hv]

theorem prod_leafEdges {d : CertData} :
    ∀ es : List Edge, (es.map fun e => sq1 (d.vec e.u) * sq1 (d.vec e.v)).prod =
      ((es.flatMap fun e => [e.u, e.v]).map fun u => sq1 (d.vec u)).prod
  | [] => by simp
  | e :: es => by
    simp only [List.map_cons, List.prod_cons, List.flatMap_cons, List.map_append,
      List.prod_append, prod_leafEdges es]
    simp [mul_assoc]

/-- The bound for the key of a valid witness. -/
theorem eval_sq_le {w : Witness} (hw : w.valid = true) {d : CertData} (hd : d.Admissible)
    (hgp : d.g ^ 2 + sq1 d.p ≤ 1) (ι : ℕ → Fin 5) :
    w.key.eval d ι ^ 2 ≤ (w.lsq : ℝ) * (w.types.map fun i => ysq i d).prod := by
  simp only [valid, Bool.and_eq_true, List.all_eq_true] at hw
  have hle : ∀ e ∈ w.leafEdges, e.u.isLeaf = true ∧ e.v.isLeaf = true :=
    fun e he => by simpa using hw.1 e he
  have hcs : ∀ c ∈ w.comps, c.LeavesOK := fun c hc u hu => hw.2 c hc u hu
  have hleaves : ∀ u ∈ w.leaves, u.isLeaf = true := by
    intro u hu
    simp only [leaves, List.mem_append, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false] at hu
    rcases hu with ⟨e, he, rfl | rfl⟩ | ⟨c, hc, hu⟩
    · exact (hle e he).1
    · exact (hle e he).2
    · exact hcs c hc u hu
  set h : Endpoint → ℝ := fun u => sq1 (d.vec u)
  -- the value factors
  have hmul := Key.eval_mul (t := compsKey w.comps) (pre_slotsBelowRank hle) d ι ι
  rw [show w.pre.rank = 0 from rfl, joinIdx_zero] at hmul
  have hpre := Key.eval_eq_prod_of_hasX_eq_false (pre_hasX hle) d ι
  simp only [key]
  rw [hmul, hpre]
  simp only [pre, Key.prefactor]
  -- bounds for the factors
  have hT := sq_list_prod_le w.traces (fun t => (d.A ^ t).trace) (fun t => (traceFactor t : ℝ))
    fun t _ => trace_sq_le_traceFactor hd t
  have hE := sq_list_prod_le w.leafEdges (Edge.val d ι)
    (fun e => (4 / 5 : ℝ) ^ e.pow * (h e.u * h e.v))
    fun e he => Edge.val_sq_le hd ι (hle e he).1 (hle e he).2
  have hC := eval_compsKey_sq_le hd ι w.comps hcs
  have hmix := mixed_pow_le (sq_nonneg d.g) (sq1_nonneg d.p) hgp w.gPow (w.leaves.count .p)
  -- the leaves
  have hL : (w.leaves.map h).prod = sq1 d.p ^ w.leaves.count .p * sq1 d.ell ^ w.leaves.count .ell :=
    prod_map_sq1_vec _ hleaves
  have hLsplit : (w.leaves.map h).prod = (w.leafEdges.map fun e => h e.u * h e.v).prod *
      ((w.comps.flatMap Comp.leaves).map h).prod := by
    rw [prod_leafEdges, leaves, List.map_append, List.prod_append]
  have hEsplit : (w.leafEdges.map fun e => (4 / 5 : ℝ) ^ e.pow * (h e.u * h e.v)).prod =
      (w.leafEdges.map fun e => (4 / 5 : ℝ) ^ e.pow).prod *
        (w.leafEdges.map fun e => h e.u * h e.v).prod := List.prod_map_mul
  -- the types
  have hty : (w.types.map fun i => ysq i d).prod =
      (d.w ^ 2) ^ w.wPow * (d.z ^ 2) ^ w.zPow * sq1 d.ell ^ w.leaves.count .ell *
        sq3 d.X ^ w.nX := by
    simp only [types, List.map_append, List.map_replicate, List.prod_append,
      List.prod_replicate, ysq]
  -- assembling
  set T := (w.traces.map fun t => (traceFactor t : ℝ)).prod
  set Θ := (w.leafEdges.map fun e => (4 / 5 : ℝ) ^ e.pow).prod
  set K := ((w.comps.map Comp.lsq).prod : ℝ)
  set Hl := (w.leafEdges.map fun e => h e.u * h e.v).prod
  set Hc := ((w.comps.flatMap Comp.leaves).map h).prod
  set M := ((w.gPow : ℝ) / (w.gPow + w.leaves.count .p)) ^ w.gPow *
    ((w.leaves.count .p : ℝ) / (w.gPow + w.leaves.count .p)) ^ w.leaves.count .p
  have hT0 : 0 ≤ T := (sq_nonneg _).trans hT
  have hΘ0 : 0 ≤ Θ := List.prod_nonneg fun x hx => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hx; positivity
  have hK0 : 0 ≤ K := by
    have : (0 : ℚ) ≤ (w.comps.map Comp.lsq).prod := List.prod_nonneg fun x hx => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hx
      exact Comp.lsq_nonneg c
    exact Rat.cast_nonneg.mpr this
  have hlsq : (w.lsq : ℝ) = T * Θ * K * M := by
    simp only [lsq, mixedFactor, T, Θ, K, M]
    push_cast
    simp only [List.map_map, Function.comp_def, theta]
    push_cast
    ring
  have hgx : 0 ≤ (d.g ^ 2) ^ w.gPow := by positivity
  have hwz : 0 ≤ (d.w ^ 2) ^ w.wPow * (d.z ^ 2) ^ w.zPow := by positivity
  have hP0 := sq1_nonneg d.p
  have hl0 := sq1_nonneg d.ell
  have hX0 := sq3_nonneg d.X
  calc (d.g ^ w.gPow * d.w ^ w.wPow * d.z ^ w.zPow *
        (w.traces.map fun t => (d.A ^ t).trace).prod * (w.leafEdges.map (Edge.val d ι)).prod *
        (compsKey w.comps).eval d ι) ^ 2
      = (d.g ^ 2) ^ w.gPow * ((d.w ^ 2) ^ w.wPow * (d.z ^ 2) ^ w.zPow) *
        (w.traces.map fun t => (d.A ^ t).trace).prod ^ 2 *
        (w.leafEdges.map (Edge.val d ι)).prod ^ 2 * (compsKey w.comps).eval d ι ^ 2 := by
        ring
    _ ≤ (d.g ^ 2) ^ w.gPow * ((d.w ^ 2) ^ w.wPow * (d.z ^ 2) ^ w.zPow) * T *
        (Θ * Hl) * (K * Hc * sq3 d.X ^ w.nX) := by
        rw [← hEsplit]
        gcongr
        · exact mul_nonneg (mul_nonneg (mul_nonneg hgx hwz) hT0) ((sq_nonneg _).trans hE)
        · exact hC
    _ = (T * Θ * K) * ((d.g ^ 2) ^ w.gPow * (Hl * Hc)) *
        ((d.w ^ 2) ^ w.wPow * (d.z ^ 2) ^ w.zPow * sq3 d.X ^ w.nX) := by ring
    _ = (T * Θ * K) * ((d.g ^ 2) ^ w.gPow * sq1 d.p ^ w.leaves.count .p) *
        ((d.w ^ 2) ^ w.wPow * (d.z ^ 2) ^ w.zPow * sq1 d.ell ^ w.leaves.count .ell *
          sq3 d.X ^ w.nX) := by
        rw [← hLsplit, hL]; ring
    _ ≤ (T * Θ * K) * M * ((d.w ^ 2) ^ w.wPow * (d.z ^ 2) ^ w.zPow *
          sq1 d.ell ^ w.leaves.count .ell * sq3 d.X ^ w.nX) := by
        gcongr
    _ = _ := by rw [hlsq, hty]

end Witness

/-! ### The graph bound -/

theorem eq_getD_of_length_eq_two {l : List ℕ} (h : l.length = 2) :
    l = [l.getD 0 0, l.getD 1 0] := by
  match l, h with
  | [a, b], _ => rfl

/-- **The complete graph bound.** For a scalar graph key accepted by `classify`, on admissible
data with `g² + |p|² ≤ 1`: `(𝓜(t))² ≤ L_t² y_i² y_j²`. -/
theorem graph_bound {t : Key} (ht : (classify t).isSome = true) {d : CertData}
    (hd : d.Admissible) (hgp : d.g ^ 2 + sq1 d.p ≤ 1) (ι : ℕ → Fin 5) :
    t.eval d ι ^ 2 ≤ (Lsq t : ℝ) * ysq t.typeI d * ysq t.typeJ d := by
  unfold classify at ht
  split at ht
  · rename_i w _
    split_ifs at ht with hc
    swap
    · simp at ht
    obtain ⟨hv, hn, hL, hT, hlen⟩ := hc
    subst hn
    rw [Key.eval_normalize _ hd, ← hL, mul_assoc]
    have h2 := eq_getD_of_length_eq_two hlen
    have hb := Witness.eval_sq_le hv hd hgp ι
    rw [hT, h2] at hb
    simpa [Key.typeI, Key.typeJ] using hb
  · simp at ht

/-- The graph bound in absolute value, with any `L ≥ 0` such that `L_t² ≤ L²`:
`|𝓜(t)| ≤ L y_i y_j`. -/
theorem abs_eval_le {t : Key} (ht : (classify t).isSome = true) {d : CertData}
    (hd : d.Admissible) (hgp : d.g ^ 2 + sq1 d.p ≤ 1) (ι : ℕ → Fin 5) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : (Lsq t : ℝ) ≤ L ^ 2) :
    |t.eval d ι| ≤ L * yNorm t.typeI d * yNorm t.typeJ d := by
  have hb := graph_bound ht hd hgp ι
  have hi := ysq_nonneg t.typeI d
  have hj := ysq_nonneg t.typeJ d
  have hR : 0 ≤ L * yNorm t.typeI d * yNorm t.typeJ d := by
    unfold yNorm; positivity
  rw [← abs_of_nonneg hR, ← sq_le_sq]
  calc t.eval d ι ^ 2 ≤ (Lsq t : ℝ) * ysq t.typeI d * ysq t.typeJ d := hb
    _ ≤ L ^ 2 * ysq t.typeI d * ysq t.typeJ d := by gcongr
    _ = (L * yNorm t.typeI d * yNorm t.typeJ d) ^ 2 := by
        simp only [yNorm, mul_pow, Real.sq_sqrt hi, Real.sq_sqrt hj]

end OnePhaseDimension.Certificate
