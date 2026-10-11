/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Eval

/-!
# Soundness of the operations on graph keys

For every operation of the certificate engine we prove that it acts on values as intended:

* `Key.eval_sortAll`, `Key.eval_swapX`, `Key.eval_normalize`: sorting and the exchange of the
  two copies of `X` do not change the value (sorting uses the symmetry of `A` and `X`);
* `Key.eval_reduce`, `Key.eval_canon`: the trace reductions `tr A⁰ = 5`, `tr A = 0`,
  `tr A² = 1` and the vanishing of traces of `X` hold on admissible data;
* `Key.eval_permSlots`: renaming the free slots;
* `Key.eval_mul`: the tensor product evaluates to the product of the values;
* `Key.eval_contract`: contraction of two free slots is the sum over a common index;
* `Key.bounded_normalize`: normalization preserves the bound on the packed digits;
* `Poly.eval_merge`, `Poly.eval_mergeAll`, `Key.eval_term`: the polynomial operations.

All statements are on the data `CertData`; where symmetry of `A` and `X` or the trace
reductions are used, the data is assumed `CertData.Admissible`.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

open Finset

/-! ### Relabelling copies of `X` -/

/-- Rename the copies of `X` by `f`; other endpoints are unchanged. -/
def Endpoint.mapX (f : ℕ → ℕ) : Endpoint → Endpoint
  | .x c => .x (f c)
  | e => e

theorem pushIdx_mapX {f : ℕ → ℕ} (hf : Function.Injective f) (acc : XRecord) (e : Endpoint)
    (a : Fin 5) : pushIdx acc (e.mapX f) a ∘ f = pushIdx (acc ∘ f) e a := by
  cases e with
  | x c =>
    simp only [Endpoint.mapX, pushIdx]
    exact Function.update_comp_eq_of_injective acc hf c _
  | _ => rfl

theorem weight_mapX (d : CertData) (ι : ℕ → Fin 5) (f : ℕ → ℕ) (e : Endpoint) :
    d.weight ι (e.mapX f) = d.weight ι e := by
  cases e <;> rfl

theorem xCopiesIn_map {φ : Endpoint → Endpoint} {g : ℕ → ℕ} {S S' : Finset ℕ}
    (hφ : ∀ e c, φ e = .x c → ∃ c', e = .x c' ∧ g c' = c) (hg : ∀ c ∈ S, g c ∈ S')
    {es : List Edge} (h : XCopiesIn S es) : XCopiesIn S' (es.map (Edge.mapEnds φ)) := by
  intro e he c hc
  obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
  rcases hc with hc | hc
  · obtain ⟨c', hc', rfl⟩ := hφ _ _ hc
    exact hg _ (h e' he' c' (Or.inl hc'))
  · obtain ⟨c', hc', rfl⟩ := hφ _ _ hc
    exact hg _ (h e' he' c' (Or.inr hc'))

theorem XCopiesIn.mono {S S' : Finset ℕ} (hS : S ⊆ S') {es : List Edge} (h : XCopiesIn S es) :
    XCopiesIn S' es := fun e he c hc => hS (h e he c hc)

/-! ### Sorting -/

theorem Edge.orient_eq_x_iff (e : Edge) (c : ℕ) :
    (e.orient.u = .x c ∨ e.orient.v = .x c) ↔ (e.u = .x c ∨ e.v = .x c) := by
  unfold Edge.orient
  split_ifs
  · exact or_comm
  · exact Iff.rfl

namespace Key

theorem xCopiesIn_sortAll (k : Key) : XCopiesIn (range k.xBound) k.sortAll.edges := by
  intro e he c hc
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ((perm_sortBy _ _).mem_iff.1 he)
  exact xCopiesIn_range_xBound k f hf c ((Edge.orient_eq_x_iff f c).1 hc)

/-- Sorting the traces, the endpoints of each edge and the edges does not change the value. -/
theorem eval_sortAll (k : Key) {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5) :
    k.sortAll.eval d ι = k.eval d ι := by
  rw [eval_eq_of_xCopiesIn _ d ι k.xCopiesIn_sortAll, eval_eq_evalEdgesWith]
  congr 1
  · simp only [prefactor, sortAll]
    rw [((perm_sortBy _ _).map _).prod_eq]
  · simp only [sortAll]
    rw [evalEdgesWith_perm d ι (respectsEquiv_xProd hd _) (perm_sortBy _ _),
      evalEdgesWith_map_orient d hd.isSymm ι (respectsEquiv_xProd hd _)]

/-! ### Exchange of the two copies of `X` -/

theorem _root_.OnePhaseDimension.Certificate.Endpoint.swapX_eq_mapX (e : Endpoint) :
    e.swapX = e.mapX (Equiv.swap 0 1) := by
  rcases e with _ | _ | (_ | _ | c) | _ <;> rfl

theorem xCopiesIn_swapX (k : Key) :
    XCopiesIn (range (max 2 k.xBound)) k.swapX.edges := by
  refine xCopiesIn_map (g := Equiv.swap 0 1) (fun e c h => ?_) (fun c hc => ?_)
    ((xCopiesIn_range_xBound k).mono (range_subset_range.2 (le_max_right 2 k.xBound)))
  · rw [Endpoint.swapX_eq_mapX] at h
    cases e <;> simp_all [Endpoint.mapX]
  · simp only [mem_range] at hc ⊢
    rcases Nat.lt_or_ge c 2 with h | h
    · rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;> simp
    · rwa [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]

theorem xProd_comp_swap (d : CertData) {n : ℕ} (hn : 2 ≤ n) (acc : XRecord) :
    xProd d (range n) acc = xProd d (range n) (acc ∘ Equiv.swap 0 1) := by
  simp only [xProd, Function.comp_apply]
  refine ((Equiv.swap 0 1).prod_comp (range n) (fun c => d.xFactor (acc c)) ?_).symm
  intro c hc
  simp only [Set.mem_ofPred_eq] at hc
  rw [coe_range, Set.mem_Iio]
  by_contra h
  exact hc (Equiv.swap_apply_of_ne_of_ne (by omega) (by omega))

/-- Exchanging the two copies of `X` does not change the value (for all data). -/
theorem eval_swapX (k : Key) (d : CertData) (ι : ℕ → Fin 5) :
    k.swapX.eval d ι = k.eval d ι := by
  have h₁ := (xCopiesIn_range_xBound k).mono (range_subset_range.2 (le_max_right 2 k.xBound))
  rw [eval_eq_of_xCopiesIn _ d ι k.xCopiesIn_swapX, eval_eq_of_xCopiesIn _ d ι h₁]
  congr 1
  simp only [swapX]
  rw [show Endpoint.swapX = Endpoint.mapX (Equiv.swap 0 1) from funext Endpoint.swapX_eq_mapX]
  exact evalEdgesWith_map d ι (Endpoint.mapX (Equiv.swap 0 1)) (Equiv.swap 0 1) _ _
    (xProd_comp_swap d (le_max_left _ _)) (pushIdx_mapX (Equiv.injective _)) _ _
    fun e _ => ⟨weight_mapX _ _ _ _, weight_mapX _ _ _ _⟩

/-- Normalization does not change the value on admissible data. -/
theorem eval_normalize (k : Key) {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5) :
    k.normalize.eval d ι = k.eval d ι := by
  simp only [normalize]
  split
  · split <;> simp only [eval_sortAll _ hd, eval_swapX]
  · exact eval_sortAll _ hd ι

/-! ### Trace reductions -/

/-- The record map that puts the list `L` in front of the indices of copy `c`. -/
def prependAt (c : ℕ) (L : List (Fin 5)) (acc : XRecord) : XRecord :=
  Function.update acc c (L ++ acc c)

theorem prependAt_pushIdx (c : ℕ) (L : List (Fin 5)) (acc : XRecord) (e : Endpoint) (a : Fin 5) :
    prependAt c L (pushIdx acc e a) = pushIdx (prependAt c L acc) e a := by
  cases e with
  | x c' =>
    funext n
    simp only [prependAt, pushIdx, Function.update_apply]
    by_cases h₁ : n = c <;> by_cases h₂ : n = c' <;> simp_all
  | _ => rfl

theorem prependAt_pushEdge (c : ℕ) (L : List (Fin 5)) (acc : XRecord) (e : Edge) (a b : Fin 5) :
    prependAt c L (pushEdge acc e a b) = pushEdge (prependAt c L acc) e a b := by
  simp only [pushEdge, prependAt_pushIdx]

theorem sum_xFactor_trace {d : CertData} (hd : d.Admissible) (L : List (Fin 5)) :
    ∑ a, d.xFactor (a :: a :: L) = 0 := by
  rcases L with _ | ⟨z, _ | ⟨w, L⟩⟩
  · simp
  · simpa using hd.X_trace z
  · simp

/-- A key with a power-zero loop at a copy of `X` (a trace of `X`) vanishes on admissible
data. -/
theorem eval_eq_zero_of_hasXTrace {k : Key} (hk : k.hasXTrace = true) {d : CertData}
    (hd : d.Admissible) (ι : ℕ → Fin 5) : k.eval d ι = 0 := by
  obtain ⟨e, he, h⟩ := List.any_eq_true.1 hk
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hp, hx⟩, huv⟩ := h
  obtain ⟨c, hc⟩ : ∃ c, e.u = .x c := by
    cases hu : e.u with
    | x c => exact ⟨c, rfl⟩
    | _ => simp [hu, Endpoint.isX] at hx
  have hcS : c ∈ range k.xBound := xCopiesIn_range_xBound k e he c (Or.inl hc)
  have hF := respectsEquiv_xProd hd (range k.xBound)
  rw [eval_eq_evalEdgesWith, evalEdgesWith_perm d ι hF (List.perm_cons_erase he),
    evalEdgesWith_cons]
  have hpush : ∀ a b, pushEdge XRecord.empty e a b = prependAt c [a, b] XRecord.empty := by
    intro a b
    funext n
    simp only [pushEdge, ← huv, hc, pushIdx, prependAt, Function.update_apply]
    split_ifs <;> simp
  have hsum : ∀ acc, ∑ a, xProd d (range k.xBound) (prependAt c [a, a] acc) = 0 := by
    intro acc
    simp only [xProd]
    have : ∀ a, ∏ c' ∈ range k.xBound, d.xFactor (prependAt c [a, a] acc c') =
        d.xFactor (a :: a :: acc c) * ∏ c' ∈ (range k.xBound).erase c, d.xFactor (acc c') := by
      intro a
      rw [← mul_prod_erase _ _ hcS]
      congr 1
      · simp [prependAt]
      · refine prod_congr rfl fun c' hc' => ?_
        simp [prependAt, ne_of_mem_erase hc']
    simp only [this, ← sum_mul, sum_xFactor_trace hd, zero_mul]
  simp only [CertData.weight, ← huv, hc, hp, pow_zero, Matrix.one_apply, mul_one, one_mul,
    mul_ite, mul_zero, hpush, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  simp only [evalEdgesWith_comp d ι _ (prependAt c _) _ _ fun e _ acc a b =>
    prependAt_pushEdge c _ acc e a b]
  rw [← evalEdgesWith_sum d ι univ (fun a => xProd d (range k.xBound) ∘ prependAt c [a, a]),
    evalEdgesWith_congr d ι (G := fun _ => 0)
      (F := fun acc => ∑ x, (xProd d (range k.xBound) ∘ prependAt c [x, x]) acc)
      (fun acc => hsum acc), evalEdgesWith_zero,
    mul_zero]

/-- Soundness of the reductions on admissible data. -/
theorem eval_reduce (k : Key) {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5) :
    ((k.reduce).1 : ℝ) * (k.reduce).2.eval d ι = k.eval d ι := by
  unfold reduce
  split_ifs with h
  · simp [eval_eq_zero_of_hasXTrace h hd]
  · simp only [eval, prefactor, reduceTraces_spec hd k.traces]
    rw [show ({ k with traces := (reduceTraces k.traces).2 } : Key).xBound = k.xBound from rfl]
    ring

/-- Soundness of canonicalization on admissible data: `eval k = c · eval k'` where
`(c, k') = canon k`. -/
theorem eval_canon (k : Key) {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5) :
    ((k.canon).1 : ℝ) * (k.canon).2.eval d ι = k.eval d ι := by
  simp only [canon, eval_normalize _ hd, eval_reduce _ hd]

/-! ### Renaming free slots -/

theorem _root_.OnePhaseDimension.Certificate.pushIdx_permSlot (σ : List ℕ) (acc : XRecord)
    (e : Endpoint) (a : Fin 5) : pushIdx acc (e.permSlot σ) a ∘ id = pushIdx (acc ∘ id) e a := by
  cases e <;> rfl

/-- Renaming the free slots by `σ` (slot `i` becomes slot `σ[i]`) amounts to reading the slot
assignment through `σ`. -/
theorem eval_permSlots (k : Key) (σ : List ℕ) (d : CertData) (ι : ℕ → Fin 5) :
    (k.permSlots σ).eval d ι = k.eval d (fun i => ι (σ.getD i i)) := by
  have h : XCopiesIn (range k.xBound) (k.permSlots σ).edges :=
    xCopiesIn_map (g := id) (fun e c h => by cases e <;> simp_all [Endpoint.permSlot])
      (fun c hc => hc) (xCopiesIn_range_xBound k)
  rw [eval_eq_of_xCopiesIn _ d ι h, eval_eq_evalEdgesWith]
  congr 1
  exact evalEdgesWith_map d (fun i => ι (σ.getD i i)) (Endpoint.permSlot σ) id _ _ (fun _ => rfl)
    (pushIdx_permSlot σ) _ _
    fun e _ => ⟨by cases e.u <;> rfl, by cases e.v <;> rfl⟩

end Key


/-! ### Products -/

theorem evalEdgesWith_congr_weight (d : CertData) {ι ι' : ℕ → Fin 5} (F : XRecord → ℝ) :
    ∀ (es : List Edge) (acc : XRecord),
      (∀ e ∈ es, d.weight ι e.u = d.weight ι' e.u ∧ d.weight ι e.v = d.weight ι' e.v) →
      evalEdgesWith d ι F es acc = evalEdgesWith d ι' F es acc
  | [], _, _ => rfl
  | e :: es, acc, h => by
    obtain ⟨hu, hv⟩ := h e (by simp)
    simp only [evalEdgesWith, hu, hv,
      evalEdgesWith_congr_weight d F es _ fun f hf => h f (by simp [hf])]

/-- Recording at endpoints that never sit at a common copy of `X` commutes. -/
theorem pushIdx_comm_of_ne (acc : XRecord) {e f : Endpoint} (h : ∀ c, e = .x c → f ≠ .x c)
    (a b : Fin 5) : pushIdx (pushIdx acc e a) f b = pushIdx (pushIdx acc f b) e a := by
  cases e with
  | x c =>
    cases f with
    | x c' =>
      have hc : c ≠ c' := fun hc => h c rfl (by rw [hc])
      funext n
      simp only [pushIdx, Function.update_apply]
      by_cases h₁ : n = c <;> by_cases h₂ : n = c' <;> simp_all
    | _ => rfl
  | _ => cases f <;> rfl

theorem pushEdge_comm_of_disjoint {S T : Finset ℕ} (hST : Disjoint S T) {e f : Edge}
    (he : XCopiesIn S [e]) (hf : XCopiesIn T [f]) (acc : XRecord) (a b a' b' : Fin 5) :
    pushEdge (pushEdge acc e a b) f a' b' = pushEdge (pushEdge acc f a' b') e a b := by
  have key : ∀ x y : Endpoint, (x = e.u ∨ x = e.v) → (y = f.u ∨ y = f.v) →
      ∀ c, x = .x c → y ≠ .x c := by
    rintro x y hx hy c rfl rfl
    have h₁ := he e (by simp) c (by rcases hx with h | h <;> simp [h])
    have h₂ := hf f (by simp) c (by rcases hy with h | h <;> simp [h])
    exact Finset.disjoint_left.1 hST h₁ h₂
  simp only [pushEdge]
  rw [pushIdx_comm_of_ne _ (key _ _ (Or.inr rfl) (Or.inl rfl)),
    pushIdx_comm_of_ne _ (key _ _ (Or.inl rfl) (Or.inl rfl)),
    pushIdx_comm_of_ne _ (fun c h h' => key _ _ (Or.inr rfl) (Or.inr rfl) c h h'),
    pushIdx_comm_of_ne _ (fun c h h' => key _ _ (Or.inl rfl) (Or.inr rfl) c h h')]

theorem pushIdx_shift (r t : ℕ) (acc : XRecord) (e : Endpoint) (a : Fin 5) :
    pushIdx acc (e.shift r t) a ∘ (· + t) = pushIdx (acc ∘ (· + t)) e a := by
  cases e with
  | x c =>
    simp only [Endpoint.shift, pushIdx]
    exact Function.update_comp_eq_of_injective acc (add_left_injective t) c _
  | _ => rfl

namespace Key

theorem prefactor_mul (s t : Key) (d : CertData) :
    (s.mul t).prefactor d = s.prefactor d * t.prefactor d := by
  simp only [prefactor, mul, pow_add, List.map_append, List.prod_append]
  ring

/-- The tensor product evaluates to the product of the values: the free slots of the second
factor are numbered after those of the first. -/
theorem eval_mul {s t : Key} (hsr : s.SlotsBelowRank) (d : CertData) (ι₁ ι₂ : ℕ → Fin 5) :
    (s.mul t).eval d (joinIdx s.rank ι₁ ι₂) = s.eval d ι₁ * t.eval d ι₂ := by
  set n₁ := s.xBound
  set n₂ := t.xBound
  set ι := joinIdx s.rank ι₁ ι₂
  set l₂ := t.edges.map (Edge.mapEnds (Endpoint.shift s.rank n₁))
  have h₁ : XCopiesIn (range n₁) s.edges := xCopiesIn_range_xBound s
  have h₂ : XCopiesIn (range (n₁ + n₂) \ range n₁) l₂ :=
    xCopiesIn_map (g := (· + n₁)) (fun e c h => by cases e <;> simp_all [Endpoint.shift])
      (fun c hc => by simp only [mem_sdiff, mem_range] at hc ⊢; omega) (xCopiesIn_range_xBound t)
  have hdisj : Disjoint (range n₁) (range (n₁ + n₂) \ range n₁) := disjoint_sdiff
  have hS : XCopiesIn (range (n₁ + n₂)) (s.mul t).edges := by
    intro e he c hc
    rcases List.mem_append.1 he with he | he
    · exact range_subset_range.2 (Nat.le_add_right _ _) (h₁ e he c hc)
    · exact sdiff_subset (h₂ e he c hc)
  set H : XRecord → ℝ := fun acc => xProd d (range n₂) (acc ∘ (· + n₁))
  have hsplit : ∀ acc, xProd d (range (n₁ + n₂)) acc = xProd d (range n₁) acc * H acc := by
    intro acc
    simp only [xProd, H, prod_range_add, Function.comp_apply]
    exact congrArg _ (prod_congr rfl fun c _ => by rw [add_comm])
  set K := evalEdgesWith d ι H l₂
  -- the factor of the copies of `X` of `t` is not changed by recording the edges of `s`
  have hK : ∀ e ∈ s.edges, ∀ acc a b, K (pushEdge acc e a b) = K acc := by
    intro e he acc a b
    have hτ : ∀ f ∈ l₂, ∀ acc' a' b', pushEdge (pushEdge acc' f a' b') e a b =
        pushEdge (pushEdge acc' e a b) f a' b' := fun f hf acc' a' b' =>
      (pushEdge_comm_of_disjoint hdisj (fun e' he' => h₁ e' (by simp_all))
        (fun f' hf' => h₂ f' (by simp_all)) acc' a b a' b').symm
    simp only [K]
    rw [evalEdgesWith_comp d ι H (fun acc => pushEdge acc e a b) l₂ acc hτ]
    refine evalEdgesWith_congr d ι (fun acc' => ?_) l₂ acc
    simp only [Function.comp_apply, H]
    refine prod_congr rfl fun c _ => ?_
    simp only [Function.comp_apply]
    rw [pushEdge_apply_of_ne]
    · intro hc; have := h₁ e he _ (Or.inl hc); simp at this
    · intro hc; have := h₁ e he _ (Or.inr hc); simp at this
  rw [eval_eq_of_xCopiesIn _ d ι hS, eval_eq_evalEdgesWith d ι₁ s, eval_eq_evalEdgesWith d ι₂ t,
    prefactor_mul]
  have hmain : evalEdgesWith d ι (xProd d (range (n₁ + n₂))) (s.mul t).edges XRecord.empty =
      K XRecord.empty * evalEdgesWith d ι (xProd d (range n₁)) s.edges XRecord.empty := by
    rw [evalEdgesWith_congr d ι hsplit]
    change evalEdgesWith d ι _ (s.edges ++ l₂) _ = _
    rw [evalEdgesWith_append]
    rw [evalEdgesWith_congr d ι (G := fun acc => K acc * xProd d (range n₁) acc) (fun acc => by
      rw [evalEdgesWith_mul_left d ι _ _ l₂ acc (xProd_pushEdge_of_disjoint d hdisj.symm h₂),
        mul_comm])]
    exact evalEdgesWith_mul_left d ι _ _ s.edges _ hK
  have hs : evalEdgesWith d ι (xProd d (range n₁)) s.edges XRecord.empty =
      evalEdgesWith d ι₁ (xProd d (range n₁)) s.edges XRecord.empty :=
    evalEdgesWith_congr_weight d _ _ _ fun e he =>
      ⟨weight_joinIdx_left d ι₁ ι₂ fun i hi => hsr e he i (Or.inl hi),
        weight_joinIdx_left d ι₁ ι₂ fun i hi => hsr e he i (Or.inr hi)⟩
  have ht : K XRecord.empty = evalEdgesWith d ι₂ (xProd d (range n₂)) t.edges XRecord.empty :=
    evalEdgesWith_map d ι₂ (Endpoint.shift s.rank n₁) (· + n₁) H _ (fun _ => rfl)
      (pushIdx_shift s.rank n₁) t.edges XRecord.empty fun e _ =>
        ⟨weight_joinIdx_shift d _ _ ι₁ ι₂ e.u, weight_joinIdx_shift d _ _ ι₁ ι₂ e.v⟩
  rw [hmain, hs, ht]
  ring

end Key


/-! ### Contraction -/

/-- The slot assignment before contracting slots `i < j`, both set to `m`, given the
assignment `ι` after the contraction (where the remaining slots are renumbered). -/
def insertIdx (i j : ℕ) (m : Fin 5) (ι : ℕ → Fin 5) (n : ℕ) : Fin 5 :=
  if n = i ∨ n = j then m else if n < i then ι n else if n < j then ι (n - 1) else ι (n - 2)

/-- The number of endpoints equal to `s` among the edges `es`. -/
def slotCount (s : Endpoint) (es : List Edge) : ℕ := (es.flatMap fun e => [e.u, e.v]).count s

theorem slotCount_cons (s : Endpoint) (e : Edge) (es : List Edge) :
    slotCount s (e :: es) = [e.u, e.v].count s + slotCount s es := by
  simp only [slotCount, List.flatMap_cons, List.count_append]

theorem slotCount_perm (s : Endpoint) {es es' : List Edge} (h : es.Perm es') :
    slotCount s es = slotCount s es' :=
  (h.flatMap_right _).count_eq s

theorem ne_of_slotCount_eq_zero {s : Endpoint} {es : List Edge} (h : slotCount s es = 0)
    {e : Edge} (he : e ∈ es) : e.u ≠ s ∧ e.v ≠ s := by
  have := List.count_eq_zero.1 h
  constructor <;> intro h' <;> exact this (List.mem_flatMap.2 ⟨e, he, by simp [h']⟩)

theorem count_ends (s : Endpoint) (e : Edge) :
    [e.u, e.v].count s = (if e.u = s then 1 else 0) + (if e.v = s then 1 else 0) := by
  by_cases hu : e.u = s <;> by_cases hv : e.v = s <;> simp [hu, hv]

theorem exists_mem_of_slotCount_pos {s : Endpoint} {es : List Edge} (h : 0 < slotCount s es) :
    ∃ e ∈ es, e.u = s ∨ e.v = s := by
  obtain ⟨e, he, hs⟩ := List.mem_flatMap.1 (List.count_pos_iff.1 h)
  exact ⟨e, he, by simpa [eq_comm] using hs⟩

theorem Endpoint.isSlot_iff (e : Endpoint) (i : ℕ) : e.isSlot i = true ↔ e = .slot i := by
  cases e <;> simp [Endpoint.isSlot]

theorem weight_insertIdx (d : CertData) {i j : ℕ} (m : Fin 5) (ι : ℕ → Fin 5) {o : Endpoint}
    (hi : o ≠ .slot i) (hj : o ≠ .slot j) :
    d.weight (insertIdx i j m ι) o = d.weight ι (o.dropSlots i j) := by
  cases o with
  | slot k =>
    have hki : k ≠ i := fun h => hi (by rw [h])
    have hkj : k ≠ j := fun h => hj (by rw [h])
    funext a
    simp only [CertData.weight, insertIdx, Endpoint.dropSlots, hki, hkj, or_self, ite_false]
    split_ifs <;> rfl
  | _ => rfl

theorem weight_insertIdx_left (d : CertData) (i j : ℕ) (m : Fin 5) (ι : ℕ → Fin 5) (a : Fin 5) :
    d.weight (insertIdx i j m ι) (.slot i) a = if a = m then 1 else 0 := by
  simp [CertData.weight, insertIdx]

theorem weight_insertIdx_right (d : CertData) (i j : ℕ) (m : Fin 5) (ι : ℕ → Fin 5) (a : Fin 5) :
    d.weight (insertIdx i j m ι) (.slot j) a = if a = m then 1 else 0 := by
  simp [CertData.weight, insertIdx]

@[simp] theorem pushIdx_slot (acc : XRecord) (i : ℕ) (a : Fin 5) :
    pushIdx acc (.slot i) a = acc := rfl

@[simp] theorem pushIdx_dropSlots (acc : XRecord) (i j : ℕ) (e : Endpoint) (a : Fin 5) :
    pushIdx acc (e.dropSlots i j) a = pushIdx acc e a := by
  cases e <;> rfl

/-- Edges without the slots `i, j`, renumbered, evaluate as before at `insertIdx i j m ι`. -/
theorem evalEdgesWith_dropSlots (d : CertData) {i j : ℕ} (m : Fin 5) (ι : ℕ → Fin 5)
    (F : XRecord → ℝ) {N : List Edge}
    (hN : ∀ e ∈ N, (e.u ≠ .slot i ∧ e.v ≠ .slot i) ∧ (e.u ≠ .slot j ∧ e.v ≠ .slot j))
    (acc : XRecord) :
    evalEdgesWith d ι F (N.map (Edge.mapEnds (Endpoint.dropSlots i j))) acc =
      evalEdgesWith d (insertIdx i j m ι) F N acc :=
  evalEdgesWith_map d (insertIdx i j m ι) (Endpoint.dropSlots i j) id F F (fun _ => rfl)
    (fun acc e a => by cases e <;> rfl) N acc fun e he =>
      ⟨(weight_insertIdx d m ι (hN e he).1.1 (hN e he).2.1).symm,
        (weight_insertIdx d m ι (hN e he).1.2 (hN e he).2.2).symm⟩

theorem sum_comm₃ (H : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ a, ∑ b, ∑ c, H a b c = ∑ b, ∑ c, ∑ a, H a b c := by
  rw [Finset.sum_comm]
  exact sum_congr rfl fun b _ => Finset.sum_comm

theorem sum_sum_ite_mul (m : Fin 5) (G : Fin 5 → Fin 5 → ℝ) :
    ∑ a, ∑ b, (if a = m then 1 else 0) * G a b = ∑ b, G m b := by
  rw [Finset.sum_comm]
  exact sum_congr rfl fun b _ => by simp [ite_mul]

/-- Joining two edges at the contracted slots. -/
theorem sum_evalEdgesWith_join (d : CertData) (hA : d.A.IsSymm) {i j : ℕ} (ι : ℕ → Fin 5)
    (F : XRecord → ℝ) {o₁ o₂ : Endpoint} (h₁i : o₁ ≠ .slot i) (h₁j : o₁ ≠ .slot j)
    (h₂i : o₂ ≠ .slot i) (h₂j : o₂ ≠ .slot j) (p q : ℕ) {N : List Edge}
    (hN : ∀ e ∈ N, (e.u ≠ .slot i ∧ e.v ≠ .slot i) ∧ (e.u ≠ .slot j ∧ e.v ≠ .slot j))
    (acc : XRecord) :
    ∑ m, evalEdgesWith d (insertIdx i j m ι) F (⟨.slot i, o₁, p⟩ :: ⟨.slot j, o₂, q⟩ :: N) acc =
      evalEdgesWith d ι F (⟨o₁.dropSlots i j, o₂.dropSlots i j, p + q⟩ ::
        N.map (Edge.mapEnds (Endpoint.dropSlots i j))) acc := by
  have hpow : ∀ b b', (d.A ^ (p + q)) b b' = ∑ m, (d.A ^ p) m b * (d.A ^ q) m b' := by
    intro b b'
    rw [pow_add, Matrix.mul_apply]
    exact sum_congr rfl fun m _ => by rw [(hA.pow p).apply]
  simp only [evalEdgesWith, pushEdge, pushIdx_slot, pushIdx_dropSlots,
    ← evalEdgesWith_dropSlots d _ ι F hN, weight_insertIdx_left, weight_insertIdx_right,
    weight_insertIdx d _ ι h₁i h₁j, weight_insertIdx d _ ι h₂i h₂j, mul_assoc]
  simp only [sum_sum_ite_mul]
  simp only [hpow, mul_sum, sum_mul]
  rw [sum_comm₃]
  refine sum_congr rfl fun b _ => sum_congr rfl fun b' _ => sum_congr rfl fun m _ => ?_
  ring


/-- Put the endpoint `slot i` of an edge first. -/
theorem evalEdgesWith_cons_eq_slot_first (d : CertData) (hA : d.A.IsSymm) (ι : ℕ → Fin 5)
    {F : XRecord → ℝ} (hF : RespectsEquiv F) {e : Edge} {i : ℕ}
    (h : e.u = .slot i ∨ e.v = .slot i) (es : List Edge) (acc : XRecord) :
    evalEdgesWith d ι F (e :: es) acc =
      evalEdgesWith d ι F (⟨.slot i, if e.u.isSlot i then e.v else e.u, e.pow⟩ :: es) acc := by
  by_cases hu : e.u = .slot i
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ((Endpoint.isSlot_iff _ _).2 hu)), ← hu]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false (by rwa [Endpoint.isSlot_iff])), ← h.resolve_left hu]
    exact (evalEdgesWith_flip d hA ι hF e es acc).symm

theorem evalEdgesWith_cons_congr (d : CertData) (ι : ℕ → Fin 5) (F : XRecord → ℝ) (e : Edge)
    {es es' : List Edge} (h : ∀ acc, evalEdgesWith d ι F es acc = evalEdgesWith d ι F es' acc)
    (acc : XRecord) : evalEdgesWith d ι F (e :: es) acc = evalEdgesWith d ι F (e :: es') acc := by
  simp only [evalEdgesWith, h]

theorem ends_of_count_add_eq_one {s : Endpoint} {e : Edge} {n : ℕ}
    (h : [e.u, e.v].count s + n = 1) (hs : e.u = s ∨ e.v = s) :
    n = 0 ∧ (e.u = s → e.v ≠ s) := by
  rw [count_ends] at h
  by_cases hu : e.u = s <;> by_cases hv : e.v = s <;> simp only [hu, hv, ite_true, ite_false] at h
  · omega
  · exact ⟨by omega, fun _ => hv⟩
  · exact ⟨by omega, fun h' => absurd h' hu⟩
  · simp_all

theorem other_ne_of_ends {e : Edge} {t : Endpoint} {i : ℕ} (hu : e.u ≠ t) (hv : e.v ≠ t) :
    (if e.u.isSlot i then e.v else e.u) ≠ t := by
  split_ifs <;> assumption

namespace Key

/-- Contraction of two free slots `i < j`, each occurring exactly once, is the sum over a
common index (on admissible data: the symmetry of `A` and `X` is used to reorder). -/
theorem eval_contract {k : Key} {i j : ℕ} (hij : i < j)
    (hi : slotCount (.slot i) k.edges = 1) (hj : slotCount (.slot j) k.edges = 1)
    {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5) :
    (k.contract i j).eval d ι = ∑ m, k.eval d (insertIdx i j m ι) := by
  have hF := respectsEquiv_xProd hd (range k.xBound)
  have hA := hd.isSymm
  have hne : (Endpoint.slot i) ≠ .slot j := by simp only [ne_eq, Endpoint.slot.injEq]; omega
  have hat : ∀ (n : ℕ) (e : Edge),
      (e.u.isSlot n || e.v.isSlot n) = true ↔ (e.u = .slot n ∨ e.v = .slot n) := by
    intro n e; simp [Endpoint.isSlot_iff]
  obtain ⟨e, hfe⟩ : ∃ e, k.edges.find? (fun e => e.u.isSlot i || e.v.isSlot i) = some e := by
    obtain ⟨e, he, hs⟩ := exists_mem_of_slotCount_pos (hi ▸ Nat.one_pos)
    exact Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨e, he, (hat i e).2 hs⟩)
  obtain ⟨f, hff⟩ : ∃ f, k.edges.find? (fun e => e.u.isSlot j || e.v.isSlot j) = some f := by
    obtain ⟨e, he, hs⟩ := exists_mem_of_slotCount_pos (hj ▸ Nat.one_pos)
    exact Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨e, he, (hat j e).2 hs⟩)
  have he := List.mem_of_find?_eq_some hfe
  have hei₀ : (e.u.isSlot i || e.v.isSlot i) = true :=
    List.find?_some (p := fun e : Edge => e.u.isSlot i || e.v.isSlot i) hfe
  have hei := (hat i e).1 hei₀
  have hf := List.mem_of_find?_eq_some hff
  have hfj₀ : (f.u.isSlot j || f.v.isSlot j) = true :=
    List.find?_some (p := fun e : Edge => e.u.isSlot j || e.v.isSlot j) hff
  have hfj := (hat j f).1 hfj₀
  set R := k.edges.erase e
  have hLR : k.edges.Perm (e :: R) := List.perm_cons_erase he
  have hcnt : ∀ s, slotCount s k.edges = [e.u, e.v].count s + slotCount s R := fun s =>
    (slotCount_perm s hLR).trans (slotCount_cons s e R)
  obtain ⟨hRi, hei'⟩ := ends_of_count_add_eq_one ((hcnt _).symm.trans hi) hei
  have hS' : ∀ es : List Edge, (∀ g ∈ es, g ∈ k.edges) →
      XCopiesIn (range k.xBound) (es.map (Edge.mapEnds (Endpoint.dropSlots i j))) :=
    fun es hes => xCopiesIn_map (g := id)
      (fun o c h => by cases o <;> simp_all [Endpoint.dropSlots])
      (fun c hc => hc) fun g hg => xCopiesIn_range_xBound k g (hes g hg)
  have hpre : ∀ m, k.eval d (insertIdx i j m ι) =
      k.prefactor d * evalEdgesWith d (insertIdx i j m ι) (xProd d (range k.xBound))
        k.edges XRecord.empty := fun m => eval_eq_evalEdgesWith _ _ k
  simp only [contract, hfe, hff, hpre, ← mul_sum]
  by_cases hej : (e.u.isSlot j || e.v.isSlot j) = true
  · -- the two slots lie on the same edge, which closes to a trace
    simp only [hej, ite_true]
    have hej' := (hat j e).1 hej
    obtain ⟨hRj, -⟩ := ends_of_count_add_eq_one ((hcnt _).symm.trans hj) hej'
    have hN : ∀ g ∈ R, (g.u ≠ .slot i ∧ g.v ≠ .slot i) ∧ (g.u ≠ .slot j ∧ g.v ≠ .slot j) :=
      fun g hg => ⟨ne_of_slotCount_eq_zero hRi hg, ne_of_slotCount_eq_zero hRj hg⟩
    have hfilt : (k.edges.filter fun e => !((e.u.isSlot i || e.v.isSlot i) ||
        (e.u.isSlot j || e.v.isSlot j))).Perm R := by
      refine (hLR.filter _).trans ?_
      rw [List.filter_cons_of_neg (by simp [hei₀]), List.filter_eq_self.2]
      intro g hg
      simpa [Bool.eq_false_iff, Endpoint.isSlot_iff] using hN g hg
    have hother : (if e.u.isSlot i then e.v else e.u) = .slot j := by
      split_ifs with hu
      · rw [Endpoint.isSlot_iff] at hu
        exact hej'.resolve_left (fun h => hne (hu.symm.trans h))
      · rw [Endpoint.isSlot_iff] at hu
        exact hej'.resolve_right (fun h => hne ((hei.resolve_left hu).symm.trans h))
    rw [eval_eq_of_xCopiesIn _ d ι (hS' _ fun g hg => List.mem_of_mem_filter hg)]
    simp only [evalEdgesWith_perm d _ hF hLR,
      evalEdgesWith_cons_eq_slot_first d hA _ hF hei, hother, evalEdgesWith_cons, pushEdge,
      pushIdx_slot, ← evalEdgesWith_dropSlots d _ ι _ hN, weight_insertIdx_left,
      weight_insertIdx_right]
    rw [evalEdgesWith_perm d ι hF (hfilt.map _)]
    simp only [prefactor, List.map_cons, List.prod_cons, Matrix.trace, Matrix.diag, sum_mul,
      mul_sum, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq', mem_univ,
      ite_true]
    refine sum_congr rfl fun m _ => ?_
    ring
  · -- the two slots lie on different edges, which are joined
    simp only [hej, Bool.false_eq_true, ite_false]
    have hej' : ¬(e.u = .slot j ∨ e.v = .slot j) := fun h => hej ((hat j e).2 h)
    have hfe' : f ≠ e := fun h => hej' (h ▸ hfj)
    have hfR : f ∈ R := (List.mem_erase_of_ne hfe').2 hf
    set N := R.erase f
    have hRN : R.Perm (f :: N) := List.perm_cons_erase hfR
    have hRcnt : ∀ s, slotCount s R = [f.u, f.v].count s + slotCount s N := fun s =>
      (slotCount_perm s hRN).trans (slotCount_cons s f N)
    have hej0 : [e.u, e.v].count (.slot j) = 0 := by
      have h₁ : e.u ≠ .slot j := fun h => hej' (Or.inl h)
      have h₂ : e.v ≠ .slot j := fun h => hej' (Or.inr h)
      simp [h₁, h₂]
    obtain ⟨hNj, hfj'⟩ := ends_of_count_add_eq_one
      ((hRcnt _).symm.trans (by rw [hcnt, hej0] at hj; omega)) hfj
    have hfi : f.u ≠ .slot i ∧ f.v ≠ .slot i := ne_of_slotCount_eq_zero hRi hfR
    have hNi : slotCount (.slot i) N = 0 := by rw [hRcnt] at hRi; omega
    have hN : ∀ g ∈ N, (g.u ≠ .slot i ∧ g.v ≠ .slot i) ∧ (g.u ≠ .slot j ∧ g.v ≠ .slot j) :=
      fun g hg => ⟨ne_of_slotCount_eq_zero hNi hg, ne_of_slotCount_eq_zero hNj hg⟩
    have hL : k.edges.Perm (e :: f :: N) := hLR.trans (hRN.cons e)
    have hfilt : (k.edges.filter fun e => !((e.u.isSlot i || e.v.isSlot i) ||
        (e.u.isSlot j || e.v.isSlot j))).Perm N := by
      refine (hL.filter _).trans ?_
      rw [List.filter_cons_of_neg (by simp [hei₀]),
        List.filter_cons_of_neg (by simp [hfj₀]), List.filter_eq_self.2]
      intro g hg
      simpa [Bool.eq_false_iff, Endpoint.isSlot_iff] using hN g hg
    have h₁i : (if e.u.isSlot i then e.v else e.u) ≠ .slot i := by
      split_ifs with hu
      · exact hei' ((Endpoint.isSlot_iff _ _).1 hu)
      · rwa [Endpoint.isSlot_iff] at hu
    have h₁j : (if e.u.isSlot i then e.v else e.u) ≠ .slot j :=
      other_ne_of_ends (fun h => hej' (Or.inl h)) (fun h => hej' (Or.inr h))
    have h₂j : (if f.u.isSlot j then f.v else f.u) ≠ .slot j := by
      split_ifs with hu
      · exact hfj' ((Endpoint.isSlot_iff _ _).1 hu)
      · rwa [Endpoint.isSlot_iff] at hu
    have h₂i : (if f.u.isSlot j then f.v else f.u) ≠ .slot i := other_ne_of_ends hfi.1 hfi.2
    have hS : XCopiesIn (range k.xBound) (Edge.mapEnds (Endpoint.dropSlots i j)
        ⟨if e.u.isSlot i then e.v else e.u, if f.u.isSlot j then f.v else f.u, e.pow + f.pow⟩ ::
        (k.edges.filter fun e => !((e.u.isSlot i || e.v.isSlot i) ||
          (e.u.isSlot j || e.v.isSlot j))).map (Edge.mapEnds (Endpoint.dropSlots i j))) := by
      intro g hg c hc
      rcases List.mem_cons.1 hg with rfl | hg
      · simp only [Edge.mapEnds] at hc
        rcases hc with hc | hc
        · have : (if e.u.isSlot i then e.v else e.u) = .x c := by
            revert hc; cases (if e.u.isSlot i then e.v else e.u) <;> simp [Endpoint.dropSlots]
          refine xCopiesIn_range_xBound k e he c ?_
          split_ifs at this <;> simp [this]
        · have : (if f.u.isSlot j then f.v else f.u) = .x c := by
            revert hc; cases (if f.u.isSlot j then f.v else f.u) <;> simp [Endpoint.dropSlots]
          refine xCopiesIn_range_xBound k f hf c ?_
          split_ifs at this <;> simp [this]
      · exact hS' _ (fun g hg => List.mem_of_mem_filter hg) g hg c hc
    rw [eval_eq_of_xCopiesIn _ d ι hS]
    simp only [evalEdgesWith_perm d _ hF hL, evalEdgesWith_cons_eq_slot_first d hA _ hF hei,
      evalEdgesWith_cons_congr d _ _ _ (evalEdgesWith_cons_eq_slot_first d hA _ hF hfj N)]
    rw [sum_evalEdgesWith_join d hA ι _ h₁i h₁j h₂i h₂j _ _ hN]
    congr 1
    exact evalEdgesWith_cons_congr d ι _ _
      (evalEdgesWith_perm d ι hF ((hfilt.map _))) _

end Key


/-! ### Boundedness of packed digits -/

namespace Key

theorem bounded_iff (k : Key) : k.Bounded ↔
    (k.rank < packBase ∧ k.gPow < packBase ∧ k.wPow < packBase ∧ k.zPow < packBase) ∧
      (k.traces.length < packBase ∧ ∀ t ∈ k.traces, t < packBase) ∧
      (k.edges.length < packBase ∧
        ∀ e ∈ k.edges, e.u.code < packBase ∧ e.v.code < packBase ∧ e.pow < packBase) := by
  simp only [Bounded, digits, List.cons_append, List.mem_cons, List.mem_append,
    List.mem_flatMap, Edge.digits, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · intro h
    refine ⟨⟨h _ (by simp), h _ (by simp), h _ (by simp), h _ (by simp)⟩,
      ⟨h _ (by simp), fun t ht => h _ (by simp [ht])⟩,
      ⟨h _ (by simp), fun e he => ⟨h _ ?_, h _ ?_, h _ ?_⟩⟩⟩ <;>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, he, by simp⟩)))))) 
  · rintro ⟨⟨h₁, h₂, h₃, h₄⟩, ⟨h₅, h₆⟩, ⟨h₇, h₈⟩⟩ n hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | hn | rfl | ⟨e, he, hn⟩
    any_goals assumption
    · exact h₆ n (by simpa using hn)
    · rcases hn with rfl | rfl | rfl
      exacts [(h₈ e he).1, (h₈ e he).2.1, (h₈ e he).2.2]

theorem Edge.code_bound_orient (e : Edge) :
    (e.orient.u.code < packBase ∧ e.orient.v.code < packBase ∧ e.orient.pow < packBase) ↔
      (e.u.code < packBase ∧ e.v.code < packBase ∧ e.pow < packBase) := by
  unfold Edge.orient
  split_ifs
  · simp only; tauto
  · exact Iff.rfl

theorem bounded_sortAll {k : Key} (hk : k.Bounded) : k.sortAll.Bounded := by
  rw [bounded_iff] at hk ⊢
  obtain ⟨h₁, ⟨h₂, h₃⟩, ⟨h₄, h₅⟩⟩ := hk
  refine ⟨h₁, ⟨?_, fun t ht => h₃ t ((perm_sortBy _ _).mem_iff.1 ht)⟩, ⟨?_, fun e he => ?_⟩⟩
  · simpa [sortAll, (perm_sortBy _ _).length_eq] using h₂
  · simpa [sortAll, (perm_sortBy _ _).length_eq] using h₄
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.1 ((perm_sortBy _ _).mem_iff.1 he)
    exact (Edge.code_bound_orient f).2 (h₅ f hf)

theorem code_swapX_lt {e : Endpoint} (h : e.code < packBase) : e.swapX.code < packBase := by
  rcases e with _ | _ | (_ | _ | c) | _ <;> first | exact h | decide

theorem bounded_swapX {k : Key} (hk : k.Bounded) : k.swapX.Bounded := by
  rw [bounded_iff] at hk ⊢
  obtain ⟨h₁, h₂, ⟨h₄, h₅⟩⟩ := hk
  refine ⟨h₁, h₂, ⟨by simpa [swapX] using h₄, fun e he => ?_⟩⟩
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 he
  exact ⟨code_swapX_lt (h₅ f hf).1, code_swapX_lt (h₅ f hf).2.1, (h₅ f hf).2.2⟩

/-- Normalization (sorting and the exchange of the copies of `X`) preserves the bound on the
packed digits. -/
theorem bounded_normalize {k : Key} (hk : k.Bounded) : k.normalize.Bounded := by
  simp only [normalize]
  split
  · split
    · exact bounded_sortAll (bounded_swapX hk)
    · exact bounded_sortAll hk
  · exact bounded_sortAll hk

theorem boundedB_iff (k : Key) : k.boundedB = true ↔ k.Bounded := by
  simp [boundedB, Bounded, List.all_eq_true, Nat.blt_eq]

end Key

/-! ### Polynomials -/

namespace Poly

@[simp] theorem eval_nil (d : CertData) (ι : ℕ → Fin 5) : Poly.eval [] d ι = 0 := rfl

@[simp] theorem eval_cons (a : ℕ) (c : ℤ) (P : Poly) (d : CertData) (ι : ℕ → Fin 5) :
    Poly.eval ((a, c) :: P) d ι = c * (Key.unpack a).eval d ι + P.eval d ι := by
  simp [Poly.eval]

theorem eval_append (P Q : Poly) (d : CertData) (ι : ℕ → Fin 5) :
    Poly.eval (P ++ Q) d ι = P.eval d ι + Q.eval d ι := by
  simp [Poly.eval]

theorem eval_mergeAux (a : ℕ) (c : ℤ) (P : Poly) (mp : Poly → Poly) (d : CertData)
    (ι : ℕ → Fin 5) (hmp : ∀ Q, (mp Q).eval d ι = P.eval d ι + Q.eval d ι) :
    ∀ Q, (mergeAux a c P mp Q).eval d ι = c * (Key.unpack a).eval d ι + P.eval d ι + Q.eval d ι
  | [] => by simp [mergeAux]
  | (b, e) :: Q => by
    unfold mergeAux
    split_ifs with h₁ h₂ h₃
    · simp only [eval_cons, hmp]; ring
    · simp only [eval_cons, eval_mergeAux a c P mp d ι hmp Q]; ring
    · have hab : a = b := by omega
      subst hab
      simp only [hmp, eval_cons]
      have : (c : ℝ) + e = 0 := by exact_mod_cast h₃
      rw [eq_neg_of_add_eq_zero_right this]
      ring
    · have hab : a = b := by omega
      subst hab
      simp only [eval_cons, hmp, Int.cast_add]; ring

/-- Merging adds values (no sortedness is needed). -/
theorem eval_merge (d : CertData) (ι : ℕ → Fin 5) :
    ∀ P Q : Poly, (merge P Q).eval d ι = P.eval d ι + Q.eval d ι
  | [], Q => by simp [merge]
  | (a, c) :: P, Q => by
    rw [merge, eval_mergeAux a c P (merge P) d ι (eval_merge d ι P), eval_cons]

theorem eval_mergePairs (d : CertData) (ι : ℕ → Fin 5) :
    ∀ l : List Poly, ((mergePairs l).map fun P => P.eval d ι).sum =
      (l.map fun P => P.eval d ι).sum
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    simp only [mergePairs, List.map_cons, List.sum_cons, eval_merge, eval_mergePairs d ι l]
    ring

theorem length_mergePairs : ∀ l : List Poly, (mergePairs l).length = (l.length + 1) / 2
  | [] => rfl
  | [_] => by simp [mergePairs]
  | a :: b :: l => by
    simp only [mergePairs, List.length_cons, length_mergePairs l]
    omega

theorem eval_mergeAllAux (d : CertData) (ι : ℕ → Fin 5) :
    ∀ (n : ℕ) (l : List Poly), ((mergeAllAux n l).map fun P => P.eval d ι).sum =
      (l.map fun P => P.eval d ι).sum
  | 0, _ => rfl
  | n + 1, l => by rw [mergeAllAux, eval_mergeAllAux d ι n, eval_mergePairs]

theorem length_mergeAllAux_le :
    ∀ (n : ℕ) (l : List Poly), l.length ≤ n + 1 → (mergeAllAux n l).length ≤ 1
  | 0, _, h => h
  | n + 1, l, h => length_mergeAllAux_le n _ (by rw [length_mergePairs]; omega)

/-- The balanced merge of a list of polynomials evaluates to the sum of the values. -/
theorem eval_mergeAll (l : List Poly) (d : CertData) (ι : ℕ → Fin 5) :
    (mergeAll l).eval d ι = (l.map fun P => P.eval d ι).sum := by
  rw [mergeAll, ← eval_mergeAllAux d ι l.length l]
  have h := length_mergeAllAux_le l.length l (Nat.le_succ _)
  rcases hl : mergeAllAux l.length l with _ | ⟨P, _ | ⟨Q, rest⟩⟩
  · rfl
  · simp
  · simp [hl] at h

end Poly

/-- The single-term polynomial `Key.term c k` evaluates to `c · eval k` on admissible data,
provided the reduced key fits the packing (otherwise the result is the overflow marker). -/
theorem Key.eval_term (c : ℤ) (k : Key) (hk : k.reduce.2.boundedB = true) {d : CertData}
    (hd : d.Admissible) (ι : ℕ → Fin 5) : (Key.term c k).eval d ι = c * k.eval d ι := by
  rw [← k.eval_reduce hd ι]
  simp only [Key.term]
  split_ifs with h₀
  · have : ((k.reduce.1 : ℝ) * c) = 0 := by exact_mod_cast h₀
    rw [Poly.eval_nil, ← mul_assoc, mul_comm (c : ℝ), this, zero_mul]
  · rw [Poly.eval_cons, Poly.eval_nil, add_zero,
      Key.unpack_pack (Key.bounded_normalize ((Key.boundedB_iff _).1 hk)),
      Key.eval_normalize _ hd, Int.cast_mul]
    ring

end OnePhaseDimension.Certificate
