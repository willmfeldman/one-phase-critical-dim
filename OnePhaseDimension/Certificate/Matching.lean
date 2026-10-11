/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Ops
public import OnePhaseDimension.Certificate.Projection
public import OnePhaseDimension.Certificate.Spike.ExpandHook

/-!
# From graph keys to tensors: the pair terms of the Gram blocks

A key is *linear* if each free slot below its rank occurs exactly once and no other slot occurs
(every Table I and Table II monomial is linear). For linear keys:

* contraction of two slots, products and slot permutations give linear keys;
* `Key.eval_contractPairs`: the successive contraction of slot `0` with slot `n`, …, `0` with
  `1` of a linear key of rank `2n` is the full contraction `∑_α K(α, α)`;
* the pair terms of the Gram blocks (`Expand.pairTerms`, `Expand.hookTerms`) evaluate to
  `⟨T, Π S⟩` for the tensors `S, T` of the two rows (`pairTerms_*_eq`).
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

open Finset

/-! ### Slot counts under contraction -/

/-- The slot that is renumbered to `m` when the slots `i < j` are deleted. -/
def liftSlot (i j m : ℕ) : ℕ := if m < i then m else if m + 1 < j then m + 1 else m + 2

theorem dropSlots_eq_slot_iff {i j : ℕ} (_hij : i < j) {a : Endpoint} (hi : a ≠ .slot i)
    (hj : a ≠ .slot j) (m : ℕ) : a.dropSlots i j = .slot m ↔ a = .slot (liftSlot i j m) := by
  cases a with
  | slot n =>
    have hn₁ : n ≠ i := fun h => hi (by rw [h])
    have hn₂ : n ≠ j := fun h => hj (by rw [h])
    simp only [Endpoint.dropSlots, Endpoint.slot.injEq, liftSlot]
    split_ifs <;> omega
  | _ => simp [Endpoint.dropSlots]

theorem liftSlot_ne_left {i j : ℕ} (_hij : i < j) (m : ℕ) : liftSlot i j m ≠ i := by
  unfold liftSlot; split_ifs <;> omega

theorem liftSlot_ne_right {i j : ℕ} (hij : i < j) (m : ℕ) : liftSlot i j m ≠ j := by
  unfold liftSlot; split_ifs <;> omega

theorem count_ends_dropSlots {i j : ℕ} (hij : i < j) {a b : Endpoint} (hai : a ≠ .slot i)
    (haj : a ≠ .slot j) (hbi : b ≠ .slot i) (hbj : b ≠ .slot j) (m : ℕ) :
    [a.dropSlots i j, b.dropSlots i j].count (.slot m) = [a, b].count (.slot (liftSlot i j m)) := by
  have ha := dropSlots_eq_slot_iff hij hai haj m
  have hb := dropSlots_eq_slot_iff hij hbi hbj m
  simp only [List.count_cons, List.count_nil, beq_iff_eq, ha, hb]

theorem slotCount_map_dropSlots {i j : ℕ} (hij : i < j) (m : ℕ) : ∀ N : List Edge,
    (∀ g ∈ N, (g.u ≠ .slot i ∧ g.v ≠ .slot i) ∧ (g.u ≠ .slot j ∧ g.v ≠ .slot j)) →
      slotCount (.slot m) (N.map (Edge.mapEnds (Endpoint.dropSlots i j))) =
        slotCount (.slot (liftSlot i j m)) N
  | [], _ => rfl
  | g :: N, h => by
    obtain ⟨⟨h₁, h₂⟩, h₃, h₄⟩ := h g (by simp)
    rw [List.map_cons, slotCount_cons, slotCount_cons,
      slotCount_map_dropSlots hij m N fun g' hg' => h g' (by simp [hg'])]
    simp only [Edge.mapEnds]
    rw [count_ends_dropSlots hij h₁ h₃ h₂ h₄]

theorem count_other {e : Edge} {i : ℕ} {s : Endpoint} (hs : s ≠ .slot i)
    (h : e.u = .slot i ∨ e.v = .slot i) :
    [e.u, e.v].count s = [if e.u.isSlot i then e.v else e.u].count s := by
  by_cases hu : e.u = .slot i
  · have : e.u.isSlot i = true := (Endpoint.isSlot_iff _ _).2 hu
    simp only [this, ite_true]
    simp only [List.count_cons, List.count_nil, beq_iff_eq, hu]
    simp [Ne.symm hs]
  · have : e.u.isSlot i = false := by
      rw [Bool.eq_false_iff]; intro h'; exact hu ((Endpoint.isSlot_iff _ _).1 h')
    have hv := h.resolve_left hu
    simp only [this, Bool.false_eq_true, ite_false, List.count_cons, List.count_nil,
      beq_iff_eq, hv]
    simp [Ne.symm hs]

namespace Key

theorem rank_contract (k : Key) (i j : ℕ) : (k.contract i j).rank = k.rank - 2 := by
  simp only [contract]
  split
  · split <;> rfl
  · rfl

/-- The slot counts after contracting two slots that occur exactly once. -/
theorem slotCount_contract {k : Key} {i j : ℕ} (hij : i < j)
    (hi : slotCount (.slot i) k.edges = 1) (hj : slotCount (.slot j) k.edges = 1) (m : ℕ) :
    slotCount (.slot m) (k.contract i j).edges =
      slotCount (.slot (liftSlot i j m)) k.edges := by
  have hne : (Endpoint.slot i) ≠ .slot j := by simp only [ne_eq, Endpoint.slot.injEq]; omega
  have hli : (Endpoint.slot (liftSlot i j m)) ≠ .slot i := by
    simpa using liftSlot_ne_left hij m
  have hlj : (Endpoint.slot (liftSlot i j m)) ≠ .slot j := by
    simpa using liftSlot_ne_right hij m
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
  simp only [contract, hfe, hff]
  by_cases hej : (e.u.isSlot j || e.v.isSlot j) = true
  · simp only [hej, ite_true]
    have hej' := (hat j e).1 hej
    obtain ⟨hRj, hej''⟩ := ends_of_count_add_eq_one ((hcnt _).symm.trans hj) hej'
    have hN : ∀ g ∈ R, (g.u ≠ .slot i ∧ g.v ≠ .slot i) ∧ (g.u ≠ .slot j ∧ g.v ≠ .slot j) :=
      fun g hg => ⟨ne_of_slotCount_eq_zero hRi hg, ne_of_slotCount_eq_zero hRj hg⟩
    have hfilt : (k.edges.filter fun e => !((e.u.isSlot i || e.v.isSlot i) ||
        (e.u.isSlot j || e.v.isSlot j))).Perm R := by
      refine (hLR.filter _).trans ?_
      rw [List.filter_cons_of_neg (by simp [hei₀]), List.filter_eq_self.2]
      intro g hg
      simpa [Bool.eq_false_iff, Endpoint.isSlot_iff] using hN g hg
    have heu : e.u ≠ .slot (liftSlot i j m) := by
      rcases hei with h | h
      · rw [h]; exact hli.symm
      · rcases hej' with h' | h'
        · rw [h']; exact hlj.symm
        · exact absurd (h.symm.trans h') hne
    have hev : e.v ≠ .slot (liftSlot i j m) := by
      rcases hei with h | h
      · rcases hej' with h' | h'
        · exact absurd (h.symm.trans h') hne
        · rw [h']; exact hlj.symm
      · rw [h]; exact hli.symm
    rw [slotCount_perm _ (hfilt.map _), slotCount_map_dropSlots hij m R hN, hcnt]
    simp [heu, hev]
  · simp only [hej, Bool.false_eq_true, ite_false]
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
    rw [slotCount_cons, slotCount_perm _ (hfilt.map _), slotCount_map_dropSlots hij m N hN,
      hcnt, hRcnt, count_other hli hei, count_other hlj hfj]
    simp only [Edge.mapEnds]
    rw [count_ends_dropSlots hij h₁i h₁j h₂i h₂j]
    simp only [List.count_cons, List.count_nil]
    ring

end Key


/-! ### Linear keys -/

namespace Key

/-- Each free slot below the rank occurs exactly once, and no other slot occurs. -/
def Linear (k : Key) : Prop := ∀ m, slotCount (.slot m) k.edges = if m < k.rank then 1 else 0

theorem Linear.slotsBelowRank {k : Key} (hk : k.Linear) : k.SlotsBelowRank := by
  intro e he i hi
  have hpos : 0 < slotCount (.slot i) k.edges := by
    apply List.count_pos_iff.2
    exact List.mem_flatMap.2 ⟨e, he, by rcases hi with h | h <;> simp [h]⟩
  rw [hk i] at hpos
  split_ifs at hpos with h
  · exact h
  · omega

theorem Linear.contract {k : Key} (hk : k.Linear) {i j : ℕ} (hij : i < j) (hjr : j < k.rank) :
    (k.contract i j).Linear := by
  have hi : slotCount (.slot i) k.edges = 1 := by rw [hk]; simp; omega
  have hj : slotCount (.slot j) k.edges = 1 := by rw [hk]; simp [hjr]
  intro m
  rw [slotCount_contract hij hi hj, hk, rank_contract]
  unfold liftSlot
  split_ifs <;> omega

/-- The value of a key only depends on the slot assignment below its rank. -/
theorem eval_congr_idx {k : Key} (hk : k.SlotsBelowRank) (d : CertData) {ι ι' : ℕ → Fin 5}
    (h : ∀ i < k.rank, ι i = ι' i) : k.eval d ι = k.eval d ι' := by
  rw [eval_eq_evalEdgesWith, eval_eq_evalEdgesWith]
  congr 1
  refine evalEdgesWith_congr_weight d _ _ _ fun e he => ⟨?_, ?_⟩
  · cases hu : e.u with
    | slot n => funext a; simp [CertData.weight, h n (hk e he n (Or.inl hu))]
    | _ => rfl
  · cases hv : e.v with
    | slot n => funext a; simp [CertData.weight, h n (hk e he n (Or.inr hv))]
    | _ => rfl

theorem shift_eq_slot_iff (r t : ℕ) (a : Endpoint) (m : ℕ) :
    a.shift r t = .slot m ↔ r ≤ m ∧ a = .slot (m - r) := by
  cases a with
  | slot n => simp only [Endpoint.shift, Endpoint.slot.injEq]; omega
  | x c => simp [Endpoint.shift]
  | _ => simp [Endpoint.shift]

theorem slotCount_map_shift (r t m : ℕ) : ∀ L : List Edge,
    slotCount (.slot m) (L.map (Edge.mapEnds (Endpoint.shift r t))) =
      if r ≤ m then slotCount (.slot (m - r)) L else 0
  | [] => by simp [slotCount]
  | g :: L => by
    rw [List.map_cons, slotCount_cons, slotCount_cons, slotCount_map_shift r t m L]
    simp only [Edge.mapEnds, List.count_cons, List.count_nil, beq_iff_eq,
      shift_eq_slot_iff]
    split_ifs <;> simp_all

theorem slotCount_append (a : Endpoint) (L₁ L₂ : List Edge) :
    slotCount a (L₁ ++ L₂) = slotCount a L₁ + slotCount a L₂ := by
  simp only [slotCount, List.flatMap_append, List.count_append]

theorem Linear.mul {s t : Key} (hs : s.Linear) (ht : t.Linear) : (s.mul t).Linear := by
  intro m
  change slotCount (.slot m)
      (s.edges ++ t.edges.map (Edge.mapEnds (Endpoint.shift s.rank s.xBound))) =
    if m < s.rank + t.rank then 1 else 0
  rw [slotCount_append, slotCount_map_shift, hs m]
  split_ifs <;> (try rw [ht]) <;> (try split_ifs) <;> omega

theorem permSlot_eq_slot_iff {σ τ : List ℕ} (h₁ : ∀ n, τ.getD (σ.getD n n) (σ.getD n n) = n)
    (h₂ : ∀ m, σ.getD (τ.getD m m) (τ.getD m m) = m) (a : Endpoint) (m : ℕ) :
    a.permSlot σ = .slot m ↔ a = .slot (τ.getD m m) := by
  cases a with
  | slot n =>
    simp only [Endpoint.permSlot, Endpoint.slot.injEq]
    constructor
    · rintro rfl; exact (h₁ n).symm
    · rintro rfl; exact h₂ m
  | _ => simp [Endpoint.permSlot]

theorem slotCount_map_permSlot {σ τ : List ℕ} (h₁ : ∀ n, τ.getD (σ.getD n n) (σ.getD n n) = n)
    (h₂ : ∀ m, σ.getD (τ.getD m m) (τ.getD m m) = m) (m : ℕ) : ∀ L : List Edge,
    slotCount (.slot m) (L.map (Edge.mapEnds (Endpoint.permSlot σ))) =
      slotCount (.slot (τ.getD m m)) L
  | [] => rfl
  | g :: L => by
    rw [List.map_cons, slotCount_cons, slotCount_cons, slotCount_map_permSlot h₁ h₂ m L]
    simp only [Edge.mapEnds, List.count_cons, List.count_nil, beq_iff_eq,
      permSlot_eq_slot_iff h₁ h₂]

/-- Renaming the slots by a permutation `σ` with inverse `τ` that preserves the slots below the
rank keeps a key linear. -/
theorem Linear.permSlots {k : Key} (hk : k.Linear) {σ τ : List ℕ}
    (h₁ : ∀ n, τ.getD (σ.getD n n) (σ.getD n n) = n)
    (h₂ : ∀ m, σ.getD (τ.getD m m) (τ.getD m m) = m)
    (h₃ : ∀ m, τ.getD m m < k.rank ↔ m < k.rank) : (k.permSlots σ).Linear := by
  intro m
  change slotCount (.slot m) (k.edges.map (Edge.mapEnds (Endpoint.permSlot σ))) =
    if m < k.rank then 1 else 0
  rw [slotCount_map_permSlot h₁ h₂, hk]
  simp only [h₃]

/-! ### Full contraction -/

/-- The slot assignment `j ↦ α j` for `j < n` and `j ↦ α (j - n)` for `n ≤ j < 2n`. -/
def pairIdx (n : ℕ) (α : Fin n → Fin 5) (j : ℕ) : Fin 5 :=
  if h : j < n then α ⟨j, h⟩ else if h' : j - n < n then α ⟨j - n, h'⟩ else 0

theorem cons_apply_of_pos {n : ℕ} (m : Fin 5) (β : Fin n → Fin 5) {s : ℕ} (h₀ : 0 < s)
    (hs : s < n + 1) : (Fin.cons m β : Fin (n + 1) → Fin 5) ⟨s, hs⟩ = β ⟨s - 1, by omega⟩ := by
  rw [show (⟨s, hs⟩ : Fin (n + 1)) = Fin.succ ⟨s - 1, by omega⟩ from Fin.ext (by simp; omega)]
  rfl

theorem insertIdx_pairIdx (n : ℕ) (m : Fin 5) (β : Fin n → Fin 5) {s : ℕ}
    (hs : s < 2 * (n + 1)) :
    insertIdx 0 (n + 1) m (pairIdx n β) s = pairIdx (n + 1) (Fin.cons m β) s := by
  simp only [insertIdx, pairIdx]
  by_cases h0 : s = 0
  · subst h0; simp
  by_cases h1 : s = n + 1
  · subst h1; simp
  by_cases h2 : s < n + 1
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      dite_eq_left (by omega), dite_eq_left h2, cons_apply_of_pos m β (by omega) h2]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      dite_eq_right (by omega), dite_eq_left (by omega), dite_eq_right h2,
      dite_eq_left (by omega),
      cons_apply_of_pos m β (by omega) (by omega)]
    congr 1
    ext
    simp only
    omega

/-- The successive contraction of slot `0` with slot `n`, …, `0` with `1` of a linear key of
rank `2n` is the full contraction `∑_α K(α, α)`. -/
theorem eval_contractPairs {d : CertData} (hd : d.Admissible) :
    ∀ (n : ℕ) (K : Key), K.Linear → K.rank = 2 * n → ∀ ι : ℕ → Fin 5,
      (K.contractPairs n).eval d ι = ∑ α : Fin n → Fin 5, K.eval d (pairIdx n α)
  | 0, K, hK, hr, ι => by
    rw [Fintype.sum_unique]
    exact eval_congr_idx hK.slotsBelowRank d fun i hi => by omega
  | n + 1, K, hK, hr, ι => by
    have h0 : slotCount (.slot 0) K.edges = 1 := by rw [hK]; simp [hr]
    have hn : slotCount (.slot (n + 1)) K.edges = 1 := by rw [hK]; simp [hr]
    have hK' := hK.contract (i := 0) (j := n + 1) (by omega) (by omega)
    have hr' : (K.contract 0 (n + 1)).rank = 2 * n := by rw [rank_contract]; omega
    rw [contractPairs, eval_contractPairs hd n _ hK' hr' ι]
    simp only [eval_contract (by omega : 0 < n + 1) h0 hn hd]
    rw [Finset.sum_comm, ← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
    refine sum_congr rfl fun m _ => sum_congr rfl fun β _ => ?_
    exact eval_congr_idx hK.slotsBelowRank d fun s hs =>
      insertIdx_pairIdx n m β (by omega)

end Key


/-! ### Tensors of keys -/

/-- The slot assignment `0 ↦ i`, `1 ↦ j`, `2 ↦ k` (and `k` beyond). -/
def idx3 (i j k : Fin 5) (n : ℕ) : Fin 5 := if n = 0 then i else if n = 1 then j else k

@[simp] theorem idx3_zero (i j k : Fin 5) : idx3 i j k 0 = i := rfl
@[simp] theorem idx3_one (i j k : Fin 5) : idx3 i j k 1 = j := rfl
@[simp] theorem idx3_two (i j k : Fin 5) : idx3 i j k 2 = k := rfl

/-- The slot assignment `0 ↦ i`, `1 ↦ j` (and `j` beyond). -/
def idx2 (i j : Fin 5) (n : ℕ) : Fin 5 := if n = 0 then i else j

namespace Key

/-- The vector of a key of rank one. -/
def ten1 (K : Key) (d : CertData) : Fin 5 → ℝ := fun k => K.eval d fun _ => k

/-- The two-tensor of a key of rank two. -/
def ten2 (K : Key) (d : CertData) : Fin 5 → Fin 5 → ℝ := fun i j => K.eval d (idx2 i j)

/-- The three-tensor of a key of rank three. -/
def ten3 (K : Key) (d : CertData) : Fin 5 → Fin 5 → Fin 5 → ℝ :=
  fun i j k => K.eval d (idx3 i j k)

theorem lt_three {n : ℕ} (h : n < 3) : n = 0 ∨ n = 1 ∨ n = 2 := by omega

theorem eval_eq_ten3 {K : Key} (hK : K.Linear) (h3 : K.rank = 3) (d : CertData)
    {ι : ℕ → Fin 5} {i j k : Fin 5} (h₀ : ι 0 = i) (h₁ : ι 1 = j) (h₂ : ι 2 = k) :
    K.eval d ι = K.ten3 d i j k :=
  eval_congr_idx hK.slotsBelowRank d fun n hn => by
    rcases lt_three (h3 ▸ hn) with rfl | rfl | rfl <;> simp [idx3, *]

theorem eval_eq_ten2 {K : Key} (hK : K.Linear) (h2 : K.rank = 2) (d : CertData)
    {ι : ℕ → Fin 5} {i j : Fin 5} (h₀ : ι 0 = i) (h₁ : ι 1 = j) :
    K.eval d ι = K.ten2 d i j :=
  eval_congr_idx hK.slotsBelowRank d fun n hn => by
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp [idx2, *]

theorem eval_eq_ten1 {K : Key} (hK : K.Linear) (h1 : K.rank = 1) (d : CertData)
    {ι : ℕ → Fin 5} {k : Fin 5} (h₀ : ι 0 = k) : K.eval d ι = K.ten1 d k :=
  eval_congr_idx hK.slotsBelowRank d fun n hn => by
    rcases (by omega : n = 0) with rfl; simp [*]

/-- The full contraction of two linear keys of rank `n`. -/
theorem eval_contractPairs_mul {d : CertData} (hd : d.Admissible) {S T : Key} (hS : S.Linear)
    (hT : T.Linear) {n : ℕ} (hSn : S.rank = n) (hTn : T.rank = n) (ι : ℕ → Fin 5) :
    ((S.mul T).contractPairs n).eval d ι =
      ∑ α : Fin n → Fin 5, S.eval d (pairIdx n α) * T.eval d (pairIdx n α) := by
  rw [eval_contractPairs hd n _ (hS.mul hT) (by simp [mul, hSn, hTn]; omega)]
  refine sum_congr rfl fun α _ => ?_
  rw [← eval_mul hS.slotsBelowRank d]
  refine eval_congr_idx (hS.mul hT).slotsBelowRank d fun s hs => ?_
  simp only [mul, hSn, hTn] at hs
  simp only [joinIdx, pairIdx, hSn]
  split_ifs <;> first | rfl | omega

theorem sum_fin3 (g : Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ α : Fin 3 → Fin 5, g (α 0) (α 1) (α 2) = ∑ i, ∑ j, ∑ k, g i j k := by
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun j _ => ?_
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun k _ => ?_
  simp only [Fintype.sum_unique]
  rfl

theorem sum_fin2 (g : Fin 5 → Fin 5 → ℝ) :
    ∑ α : Fin 2 → Fin 5, g (α 0) (α 1) = ∑ i, ∑ j, g i j := by
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun j _ => ?_
  simp

theorem sum_fin1 (g : Fin 5 → ℝ) : ∑ α : Fin 1 → Fin 5, g (α 0) = ∑ i, g i := by
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  simp

end Key


/-! ### Permutation, trace and contraction terms -/

/-- `σ` renames the slots by a permutation with inverse `τ` preserving the slots below `r`. -/
def PermOK (r : ℕ) (σ τ : List ℕ) : Prop :=
  (∀ n, τ.getD (σ.getD n n) (σ.getD n n) = n) ∧ (∀ m, σ.getD (τ.getD m m) (τ.getD m m) = m) ∧
    ∀ m, τ.getD m m < r ↔ m < r

theorem permOK_012 : PermOK 3 [0, 1, 2] [0, 1, 2] := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩ <;> rcases n with _ | _ | _ | n <;> simp
theorem permOK_021 : PermOK 3 [0, 2, 1] [0, 2, 1] := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩ <;> rcases n with _ | _ | _ | n <;> simp
theorem permOK_102 : PermOK 3 [1, 0, 2] [1, 0, 2] := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩ <;> rcases n with _ | _ | _ | n <;> simp
theorem permOK_120 : PermOK 3 [1, 2, 0] [2, 0, 1] := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩ <;> rcases n with _ | _ | _ | n <;> simp
theorem permOK_201 : PermOK 3 [2, 0, 1] [1, 2, 0] := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩ <;> rcases n with _ | _ | _ | n <;> simp
theorem permOK_210 : PermOK 3 [2, 1, 0] [2, 1, 0] := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩ <;> rcases n with _ | _ | _ | n <;> simp
theorem permOK_10 : PermOK 2 [1, 0] [1, 0] := by
  refine ⟨fun n => ?_, fun n => ?_, fun n => ?_⟩ <;> rcases n with _ | _ | n <;> simp

namespace Key

variable {d : CertData} (hd : d.Admissible) {S T : Key}
include hd

/-- A permutation term `⟨S^σ, T⟩` of rank three. -/
theorem eval_permTerm3 (hS : S.Linear) (hT : T.Linear) (hS3 : S.rank = 3) (hT3 : T.rank = 3)
    {σ τ : List ℕ} (hσ : PermOK 3 σ τ) (ι : ℕ → Fin 5) :
    (((S.permSlots σ).mul T).contractPairs 3).eval d ι =
      ∑ i, ∑ j, ∑ k, S.ten3 d (idx3 i j k (σ.getD 0 0)) (idx3 i j k (σ.getD 1 1))
        (idx3 i j k (σ.getD 2 2)) * T.ten3 d i j k := by
  obtain ⟨h₁, h₂, h₃⟩ := hσ
  have hS' := hS.permSlots h₁ h₂ (by rw [hS3]; exact h₃)
  rw [eval_contractPairs_mul hd hS' hT (by simp [permSlots, hS3]) hT3]
  rw [← sum_fin3 (fun i j k => S.ten3 d (idx3 i j k (σ.getD 0 0)) (idx3 i j k (σ.getD 1 1))
    (idx3 i j k (σ.getD 2 2)) * T.ten3 d i j k)]
  refine sum_congr rfl fun α _ => ?_
  have hp : ∀ m < 3, pairIdx 3 α m = idx3 (α 0) (α 1) (α 2) m := fun m hm => by
    rcases lt_three hm with rfl | rfl | rfl <;> rfl
  rw [eval_permSlots, eval_eq_ten3 hT hT3 d (hp 0 (by norm_num)) (hp 1 (by norm_num))
    (hp 2 (by norm_num))]
  congr 1
  refine eval_eq_ten3 hS hS3 d ?_ ?_ ?_ <;>
    exact hp _ ((h₃ _).1 (by rw [h₁]; norm_num))


/-- A permutation term `⟨S^σ, T⟩` of rank two. -/
theorem eval_permTerm2 (hS : S.Linear) (hT : T.Linear) (hS2 : S.rank = 2) (hT2 : T.rank = 2)
    {σ τ : List ℕ} (hσ : PermOK 2 σ τ) (ι : ℕ → Fin 5) :
    (((S.permSlots σ).mul T).contractPairs 2).eval d ι =
      ∑ i, ∑ j, S.ten2 d (idx2 i j (σ.getD 0 0)) (idx2 i j (σ.getD 1 1)) * T.ten2 d i j := by
  obtain ⟨h₁, h₂, h₃⟩ := hσ
  have hS' := hS.permSlots h₁ h₂ (by rw [hS2]; exact h₃)
  rw [eval_contractPairs_mul hd hS' hT (by simp [permSlots, hS2]) hT2]
  rw [← sum_fin2 (fun i j => S.ten2 d (idx2 i j (σ.getD 0 0)) (idx2 i j (σ.getD 1 1)) *
    T.ten2 d i j)]
  refine sum_congr rfl fun α _ => ?_
  have hp : ∀ m < 2, pairIdx 2 α m = idx2 (α 0) (α 1) m := fun m hm => by
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;> rfl
  rw [eval_permSlots, eval_eq_ten2 hT hT2 d (hp 0 (by norm_num)) (hp 1 (by norm_num))]
  congr 1
  refine eval_eq_ten2 hS hS2 d ?_ ?_ <;>
    exact hp _ ((h₃ _).1 (by rw [h₁]; norm_num))

omit hd in
theorem slotCount_eq_one (hS : S.Linear) {m : ℕ} (hm : m < S.rank) :
    slotCount (.slot m) S.edges = 1 := by
  rw [hS m, ite_eq_left hm]

/-- The partial traces of a linear rank-three key. -/
theorem ten1_contract01 (hS : S.Linear) (hS3 : S.rank = 3) :
    (S.contract 0 1).ten1 d = Proj.tr12 (S.ten3 d) := by
  funext k
  rw [ten1, eval_contract (by norm_num) (slotCount_eq_one hS (by omega))
    (slotCount_eq_one hS (by omega)) hd]
  exact sum_congr rfl fun m _ => eval_eq_ten3 hS hS3 d (by simp [insertIdx])
    (by simp [insertIdx]) (by simp [insertIdx])

theorem ten1_contract02 (hS : S.Linear) (hS3 : S.rank = 3) :
    (S.contract 0 2).ten1 d = Proj.tr13 (S.ten3 d) := by
  funext k
  rw [ten1, eval_contract (by norm_num) (slotCount_eq_one hS (by omega))
    (slotCount_eq_one hS (by omega)) hd]
  exact sum_congr rfl fun m _ => eval_eq_ten3 hS hS3 d (by simp [insertIdx])
    (by simp [insertIdx]) (by simp [insertIdx])

theorem ten1_contract12 (hS : S.Linear) (hS3 : S.rank = 3) :
    (S.contract 1 2).ten1 d = Proj.tr23 (S.ten3 d) := by
  funext k
  rw [ten1, eval_contract (by norm_num) (slotCount_eq_one hS (by omega))
    (slotCount_eq_one hS (by omega)) hd]
  exact sum_congr rfl fun m _ => eval_eq_ten3 hS hS3 d (by simp [insertIdx])
    (by simp [insertIdx]) (by simp [insertIdx])

/-- The trace of a linear rank-two key. -/
theorem eval_contract01_rank2 (hS : S.Linear) (hS2 : S.rank = 2) (ι : ℕ → Fin 5) :
    (S.contract 0 1).eval d ι = Proj.tr2 (S.ten2 d) := by
  rw [eval_contract (by norm_num) (slotCount_eq_one hS (by omega))
    (slotCount_eq_one hS (by omega)) hd]
  exact sum_congr rfl fun m _ => eval_eq_ten2 hS hS2 d (by simp [insertIdx])
    (by simp [insertIdx])

omit hd in
theorem rank_contract_of (S : Key) (i j : ℕ) {r : ℕ} (h : S.rank = r + 2) :
    (S.contract i j).rank = r := by
  rw [rank_contract]; omega

/-- The contraction of two linear keys of rank one. -/
theorem eval_contractPairs_one {a b : Key} (ha : a.Linear) (hb : b.Linear) (ha1 : a.rank = 1)
    (hb1 : b.rank = 1) (ι : ℕ → Fin 5) :
    ((a.mul b).contractPairs 1).eval d ι = Proj.inner1 (a.ten1 d) (b.ten1 d) := by
  rw [eval_contractPairs_mul hd ha hb ha1 hb1, Proj.inner1,
    ← sum_fin1 (fun k => a.ten1 d k * b.ten1 d k)]
  refine sum_congr rfl fun α _ => ?_
  rw [eval_eq_ten1 ha ha1 d (k := α 0) rfl, eval_eq_ten1 hb hb1 d (k := α 0) rfl]

omit hd in
/-- The product of two keys of rank zero. -/
theorem eval_mul_rank0 {a b : Key} (ha : a.Linear) (ha0 : a.rank = 0) (ι : ℕ → Fin 5) :
    (a.mul b).eval d ι = a.eval d ι * b.eval d ι := by
  have := eval_mul ha.slotsBelowRank d ι ι (t := b)
  have hj : joinIdx 0 ι ι = ι := funext fun i => by simp [joinIdx]
  rwa [ha0, hj] at this

end Key


/-! ### The pair terms of the Gram blocks -/

section PairTerms

variable {d : CertData} (hd : d.Admissible) {S T : Key} (hS : S.Linear) (hT : T.Linear)
include hd hS hT

/-- `none`: the pair terms evaluate to the full contraction `⟨T, S⟩`. -/
theorem pairTerms_none {r : ℕ} (hSr : S.rank = r) (hTr : T.rank = r) (ι : ℕ → Fin 5) :
    ((Expand.pairTerms 0 r S T).map fun e => (e.1 : ℝ) * e.2.eval d ι).sum =
      ∑ α : Fin r → Fin 5, S.eval d (Key.pairIdx r α) * T.eval d (Key.pairIdx r α) := by
  simp only [Expand.pairTerms, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Int.cast_one, one_mul, add_zero]
  exact Key.eval_contractPairs_mul hd hS hT hSr hTr ι

theorem eval_mulTerm2 (hS2 : S.rank = 2) (hT2 : T.rank = 2) (ι : ℕ → Fin 5) :
    ((S.mul T).contractPairs 2).eval d ι = ∑ i, ∑ j, S.ten2 d i j * T.ten2 d i j := by
  rw [Key.eval_contractPairs_mul hd hS hT hS2 hT2, ← Key.sum_fin2 (fun i j => S.ten2 d i j *
    T.ten2 d i j)]
  refine sum_congr rfl fun α _ => ?_
  have hp : ∀ m < 2, Key.pairIdx 2 α m = idx2 (α 0) (α 1) m := fun m hm => by
    rcases (by omega : m = 0 ∨ m = 1) with rfl | rfl <;> rfl
  rw [Key.eval_eq_ten2 hS hS2 d (hp 0 (by norm_num)) (hp 1 (by norm_num)),
    Key.eval_eq_ten2 hT hT2 d (hp 0 (by norm_num)) (hp 1 (by norm_num))]
  rfl

/-- `sym`, rank two: the pair terms evaluate to `⟨T, Π S⟩`. -/
theorem pairTerms_sym2 (hS2 : S.rank = 2) (hT2 : T.rank = 2) (ι : ℕ → Fin 5) :
    ((Expand.pairTerms 1 2 S T).map fun e => (e.1 : ℝ) * e.2.eval d ι).sum =
      Proj.inner2 (T.ten2 d) (Proj.projSym2 (S.ten2 d)) := by
  have hc : ∀ (K : Key), K.Linear → K.rank = 2 → (K.contract 0 1).Linear ∧
      (K.contract 0 1).rank = 0 := fun K hK h2 =>
    ⟨hK.contract (by norm_num) (by omega), Key.rank_contract_of K 0 1 h2⟩
  simp only [Expand.pairTerms, one_ne_zero, ↓reduceIte, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  rw [eval_mulTerm2 hd hS hT hS2 hT2, Key.eval_permTerm2 hd hS hT hS2 hT2 permOK_10,
    Key.eval_mul_rank0 (hc S hS hS2).1 (hc S hS hS2).2,
    Key.eval_contract01_rank2 hd hS hS2, Key.eval_contract01_rank2 hd hT hT2,
    Proj.inner_projSym2]
  simp only [Proj.inner2, Proj.swap2, idx2, List.getD_cons_zero, List.getD_cons_succ]
  push_cast
  simp only [mul_comm]
  ring

/-- `sym`, rank three: the pair terms evaluate to `⟨T, Π S⟩`. -/
theorem pairTerms_sym3 (hS3 : S.rank = 3) (hT3 : T.rank = 3) (ι : ℕ → Fin 5) :
    ((Expand.pairTerms 1 3 S T).map fun e => (e.1 : ℝ) * e.2.eval d ι).sum =
      Proj.inner3 (T.ten3 d) (Proj.projSym3 (S.ten3 d)) := by
  have hc : ∀ (K : Key), K.Linear → K.rank = 3 → ∀ i j, i < j → j < 3 →
      (K.contract i j).Linear ∧ (K.contract i j).rank = 1 := fun K hK h3 i j hij hj =>
    ⟨hK.contract hij (by omega), Key.rank_contract_of K i j h3⟩
  rw [Expand.pairTerms, ite_eq_right (by decide : (1 : ℕ) ≠ 0),
    ite_eq_right (by decide : (3 : ℕ) ≠ 2)]
  simp only [Expand.perms3, Expand.traces3, List.map_cons, List.map_nil, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.cons_append, List.nil_append, List.sum_cons,
    List.sum_nil, add_zero]
  rw [Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_012,
    Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_021, Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_102,
    Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_120, Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_201,
    Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_210]
  have h01S := hc S hS hS3 0 1 (by norm_num) (by norm_num)
  have h02S := hc S hS hS3 0 2 (by norm_num) (by norm_num)
  have h12S := hc S hS hS3 1 2 (by norm_num) (by norm_num)
  have h01T := hc T hT hT3 0 1 (by norm_num) (by norm_num)
  have h02T := hc T hT hT3 0 2 (by norm_num) (by norm_num)
  have h12T := hc T hT hT3 1 2 (by norm_num) (by norm_num)
  simp only [Key.eval_contractPairs_one hd h01S.1 h01T.1 h01S.2 h01T.2,
    Key.eval_contractPairs_one hd h01S.1 h02T.1 h01S.2 h02T.2,
    Key.eval_contractPairs_one hd h01S.1 h12T.1 h01S.2 h12T.2,
    Key.eval_contractPairs_one hd h02S.1 h01T.1 h02S.2 h01T.2,
    Key.eval_contractPairs_one hd h02S.1 h02T.1 h02S.2 h02T.2,
    Key.eval_contractPairs_one hd h02S.1 h12T.1 h02S.2 h12T.2,
    Key.eval_contractPairs_one hd h12S.1 h01T.1 h12S.2 h01T.2,
    Key.eval_contractPairs_one hd h12S.1 h02T.1 h12S.2 h02T.2,
    Key.eval_contractPairs_one hd h12S.1 h12T.1 h12S.2 h12T.2,
    Key.ten1_contract01 hd hS hS3, Key.ten1_contract02 hd hS hS3, Key.ten1_contract12 hd hS hS3,
    Key.ten1_contract01 hd hT hT3, Key.ten1_contract02 hd hT hT3, Key.ten1_contract12 hd hT hT3]
  rw [Proj.inner_projSym3]
  simp only [Proj.innerPerms3, Proj.inner3, Proj.inner1, Proj.tau, List.getD_cons_zero,
    List.getD_cons_succ, idx3_zero, idx3_one, idx3_two]
  simp only [mul_comm (T.ten3 d _ _ _), mul_comm (Proj.tr12 (S.ten3 d) _),
    mul_comm (Proj.tr13 (S.ten3 d) _), mul_comm (Proj.tr23 (S.ten3 d) _), add_mul, mul_add,
    sum_add_distrib]
  push_cast
  ring

/-- `hook`: the pair terms evaluate to `⟨T, Π S⟩`. -/
theorem hookTerms_eq (hS3 : S.rank = 3) (hT3 : T.rank = 3) (ι : ℕ → Fin 5) :
    ((Expand.hookTerms S T).map fun e => (e.1 : ℝ) * e.2.eval d ι).sum =
      Proj.inner3 (T.ten3 d) (Proj.projHook (S.ten3 d)) := by
  have hc : ∀ (K : Key), K.Linear → K.rank = 3 → ∀ i j, i < j → j < 3 →
      (K.contract i j).Linear ∧ (K.contract i j).rank = 1 := fun K hK h3 i j hij hj =>
    ⟨hK.contract hij (by omega), Key.rank_contract_of K i j h3⟩
  simp only [Expand.hookTerms, Expand.hookPerms, Expand.hookTraces, List.map_cons, List.map_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
    List.nil_append, List.sum_cons, List.sum_nil, add_zero]
  rw [Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_012,
    Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_021, Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_102,
    Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_120, Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_201,
    Key.eval_permTerm3 hd hS hT hS3 hT3 permOK_210]
  have h01S := hc S hS hS3 0 1 (by norm_num) (by norm_num)
  have h02S := hc S hS hS3 0 2 (by norm_num) (by norm_num)
  have h12S := hc S hS hS3 1 2 (by norm_num) (by norm_num)
  have h01T := hc T hT hT3 0 1 (by norm_num) (by norm_num)
  have h02T := hc T hT hT3 0 2 (by norm_num) (by norm_num)
  have h12T := hc T hT hT3 1 2 (by norm_num) (by norm_num)
  simp only [Key.eval_contractPairs_one hd h01S.1 h01T.1 h01S.2 h01T.2,
    Key.eval_contractPairs_one hd h01S.1 h02T.1 h01S.2 h02T.2,
    Key.eval_contractPairs_one hd h01S.1 h12T.1 h01S.2 h12T.2,
    Key.eval_contractPairs_one hd h02S.1 h01T.1 h02S.2 h01T.2,
    Key.eval_contractPairs_one hd h02S.1 h02T.1 h02S.2 h02T.2,
    Key.eval_contractPairs_one hd h02S.1 h12T.1 h02S.2 h12T.2,
    Key.eval_contractPairs_one hd h12S.1 h01T.1 h12S.2 h01T.2,
    Key.eval_contractPairs_one hd h12S.1 h02T.1 h12S.2 h02T.2,
    Key.eval_contractPairs_one hd h12S.1 h12T.1 h12S.2 h12T.2,
    Key.ten1_contract01 hd hS hS3, Key.ten1_contract02 hd hS hS3, Key.ten1_contract12 hd hS hS3,
    Key.ten1_contract01 hd hT hT3, Key.ten1_contract02 hd hT hT3, Key.ten1_contract12 hd hT hT3]
  rw [Proj.inner_projHook]
  simp only [Proj.inner3, Proj.inner1, Proj.hookW, List.getD_cons_zero, List.getD_cons_succ,
    idx3_zero, idx3_one, idx3_two]
  simp only [mul_comm (T.ten3 d _ _ _), mul_comm (Proj.tr12 (S.ten3 d) _),
    mul_comm (Proj.tr13 (S.ten3 d) _), mul_comm (Proj.tr23 (S.ten3 d) _), sub_mul, mul_sub,
    sum_sub_distrib, mul_assoc, ← mul_sum]
  push_cast
  simp only [mul_left_comm _ (2 : ℝ), ← mul_sum]
  ring

end PairTerms

end OnePhaseDimension.Certificate
