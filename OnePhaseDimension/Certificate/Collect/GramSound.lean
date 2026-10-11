/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Gram
public import OnePhaseDimension.Certificate.Collect.GramPSD
public import OnePhaseDimension.Certificate.Collect.Sound
public import OnePhaseDimension.Certificate.Polynomials

/-!
# The collected Gram blocks are nonnegative

On admissible data, a collected Gram block (a merge of chunks of single-term polynomials) without
the overflow marker evaluates to the Gram sum over unordered row pairs of the values of the pair
terms. For linear rows of the block's rank, the pair terms evaluate to `⟨T, Π S⟩`, a symmetric
positive semidefinite bilinear form in the tensors of the rows; hence the block is nonnegative.
Multiplication by `χ = 1 - |p|² - g²` multiplies the value by `χ`, which is nonnegative under
`g² + |p|² ≤ 1`.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Expand Data Finset

variable (d : CertData) (ι : ℕ → Fin 5)

/-- The value of the pair terms of `(S, T)`. -/
noncomputable def pairVal (pt : Key → Key → List (ℤ × Key)) (S T : Key) : ℝ :=
  ((pt S T).map fun e => (e.1 : ℝ) * e.2.eval d ι).sum

/-- The Gram sum of the pairs `(s, t)`, `t ≥ s`, with `s` among the first `n` rows. -/
noncomputable def upperN (pt : Key → Key → List (ℤ × Key)) : ℕ → List Row → ℝ
  | 0, _ => 0
  | _ + 1, [] => 0
  | n + 1, s :: ts => (dot s.2 s.2 : ℝ) * pairVal d ι pt s.1 s.1 +
      (ts.map fun t => ((2 * dot s.2 t.2 : ℤ) : ℝ) * pairVal d ι pt s.1 t.1).sum +
      upperN pt n ts

/-! ### Terms -/

/-- A polynomial is a single term. -/
def IsTerm (P : Poly) : Prop := ∃ c k, P = Key.term c k

theorem IsTerm.lin_nonneg {P : Poly} (h : IsTerm P) : 0 ≤ P.lin Poly.ind0 := by
  obtain ⟨c, k, rfl⟩ := h; exact Key.lin_ind0_term_nonneg c k

theorem isTerm_weightedWith (pt : Key → Key → List (ℤ × Key)) (w : ℤ) (S T : Key) :
    ∀ P ∈ weightedWith pt w S T, IsTerm P := by
  intro P hP
  unfold weightedWith at hP
  split_ifs at hP
  · simp at hP
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hP; exact ⟨_, _, rfl⟩

theorem isTerm_blockTermsWith (pt : Key → Key → List (ℤ × Key)) :
    ∀ (n : ℕ) (rows : List Row), ∀ P ∈ blockTermsWith pt n rows, IsTerm P
  | 0, _ => by simp [blockTermsWith]
  | _ + 1, [] => by simp [blockTermsWith]
  | n + 1, s :: ts => by
    intro P hP
    simp only [blockTermsWith, pairsFromWith, List.mem_append, List.mem_flatMap] at hP
    rcases hP with (hP | ⟨t, -, hP⟩) | hP
    · exact isTerm_weightedWith _ _ _ _ P hP
    · exact isTerm_weightedWith _ _ _ _ P hP
    · exact isTerm_blockTermsWith pt n ts P hP

theorem sum_flatMap_map {α β : Type*} (L : List α) (g : α → List β) (f : β → ℝ) :
    ((L.flatMap g).map f).sum = (L.map fun a => ((g a).map f).sum).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp [List.flatMap_cons, ih]

variable {d}

theorem sum_eval_weightedWith (hd : d.Admissible) (pt : Key → Key → List (ℤ × Key)) (w : ℤ)
    (S T : Key) (h : ∀ P ∈ weightedWith pt w S T, P.lin Poly.ind0 = 0) :
    ((weightedWith pt w S T).map fun P => P.eval d ι).sum = w * pairVal d ι pt S T := by
  by_cases hw : w = 0
  · simp [weightedWith, hw]
  · have h' : ∀ e ∈ pt S T, (Key.term (w * e.1) e.2).lin Poly.ind0 = 0 := fun e he =>
      h _ (by simp only [weightedWith, hw, ite_false]; exact List.mem_map.2 ⟨e, he, rfl⟩)
    simp only [weightedWith, hw, ite_false]
    rw [List.map_map, pairVal, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun e he => ?_
    simp only [Function.comp_apply]
    rw [Key.eval_term_of_lin (h' e he) hd ι]
    push_cast
    ring

theorem sum_eval_blockTermsWith (hd : d.Admissible) (pt : Key → Key → List (ℤ × Key)) :
    ∀ (n : ℕ) (rows : List Row), (∀ P ∈ blockTermsWith pt n rows, P.lin Poly.ind0 = 0) →
      ((blockTermsWith pt n rows).map fun P => P.eval d ι).sum = upperN d ι pt n rows
  | 0, _, _ => by simp [blockTermsWith, upperN]
  | _ + 1, [], _ => by simp [blockTermsWith, upperN]
  | n + 1, s :: ts, h => by
    simp only [blockTermsWith, pairsFromWith, List.map_append, List.sum_append] at h ⊢
    rw [sum_eval_weightedWith ι hd pt _ _ _ fun P hP => h P (by simp [hP]),
      sum_eval_blockTermsWith hd pt n ts fun P hP => h P (by simp [hP]), upperN]
    congr 2
    rw [sum_flatMap_map]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    exact sum_eval_weightedWith ι hd pt _ _ _ fun P hP =>
      h P (List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.2 ⟨t, ht, hP⟩)))

/-! ### Chunks and cuts -/

theorem upperN_add (pt : Key → Key → List (ℤ × Key)) :
    ∀ (n m : ℕ) (L : List Row), upperN d ι pt (n + m) L =
      upperN d ι pt n L + upperN d ι pt m (L.drop n)
  | 0, m, L => by simp [upperN]
  | n + 1, m, [] => by cases m <;> simp [upperN]
  | n + 1, m, s :: ts => by
    rw [show n + 1 + m = (n + m) + 1 by omega, upperN, upperN, upperN_add pt n m ts,
      List.drop_succ_cons]
    ring

theorem le_of_cutsCover : ∀ (cs : List (ℕ × ℕ)) (a N : ℕ), cutsCover cs a N = true → a ≤ N
  | [], a, N, h => by simp [cutsCover] at h; omega
  | c :: cs, a, N, h => by
    simp only [cutsCover, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    have := le_of_cutsCover cs _ N h.2
    omega

theorem upperN_cuts (pt : Key → Key → List (ℤ × Key)) (rows : List Row) :
    ∀ (cs : List (ℕ × ℕ)) (a N : ℕ), cutsCover cs a N = true →
      upperN d ι pt (N - a) (rows.drop a) = (cs.map fun c => upperN d ι pt c.2 (rows.drop c.1)).sum
  | [], a, N, h => by
    simp only [cutsCover, beq_iff_eq] at h
    simp [h, upperN]
  | c :: cs, a, N, h => by
    have hN := le_of_cutsCover _ _ _ h
    simp only [cutsCover, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨hc1, -⟩, hcs⟩ := h
    have hle := le_of_cutsCover cs _ N hcs
    rw [List.map_cons, List.sum_cons, ← upperN_cuts pt rows cs _ N hcs, hc1,
      show N - a = c.2 + (N - (a + c.2)) by omega, upperN_add, List.drop_drop]

/-- The value of a chunk without the overflow marker. -/
theorem eval_gramChunk (hd : d.Admissible) (pj : Proj) (r a n : ℕ) (rows : List Row)
    (h : (gramChunk pj r a n rows).lin Poly.ind0 = 0) :
    (gramChunk pj r a n rows).eval d ι = upperN d ι (gramPairTerms pj r) n (rows.drop a) := by
  rw [gramChunk, Poly.eval_mergeAll]
  refine sum_eval_blockTermsWith ι hd _ n _ (Poly.lin_ind0_eq_zero_of_mergeAll ?_ h)
  exact fun P hP => (isTerm_blockTermsWith _ n _ P hP).lin_nonneg

theorem lin_gramChunk_nonneg (pj : Proj) (r a n : ℕ) (rows : List Row) :
    0 ≤ (gramChunk pj r a n rows).lin Poly.ind0 := by
  rw [gramChunk, Poly.lin_mergeAll]
  exact List.sum_nonneg fun x hx => by
    obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hx
    exact (isTerm_blockTermsWith _ n _ P hP).lin_nonneg

/-- The value of a collected block before the multiplier, without the overflow marker. -/
theorem eval_gramPre (hd : d.Admissible) (b : Block) (cuts : List (ℕ × ℕ))
    (hcov : cutsCover cuts 0 (blockRows b).length = true)
    (h : (gramPre b cuts).lin Poly.ind0 = 0) :
    (gramPre b cuts).eval d ι = upperN d ι (gramPairTerms b.proj b.rank.toNat)
      (blockRows b).length (blockRows b) := by
  have h' := Poly.lin_ind0_eq_zero_of_mergeAll (fun P hP => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.1 hP; exact lin_gramChunk_nonneg _ _ _ _ _) h
  rw [gramPre, Poly.eval_mergeAll, List.map_map]
  have := upperN_cuts (d := d) ι (gramPairTerms b.proj b.rank.toNat) (blockRows b) cuts 0 _ hcov
  rw [Nat.sub_zero, List.drop_zero] at this
  rw [this]
  congr 1
  refine List.map_congr_left fun c hc => ?_
  exact eval_gramChunk ι hd _ _ _ _ _ (h' _ (List.mem_map.2 ⟨c, hc, rfl⟩))

/-! ### Gram sums of forms -/

theorem upperN_eq_upperSum {V : Type*} [AddCommGroup V] [Module ℝ V]
    (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (pt : Key → Key → List (ℤ × Key)) (vec : Key → V) :
    ∀ rows : List Row, (∀ s ∈ rows, ∀ t ∈ rows, pairVal d ι pt s.1 t.1 = β (vec s.1) (vec t.1)) →
      upperN d ι pt rows.length rows = upperSum β (rows.map fun s => (vec s.1, s.2))
  | [], _ => by simp [upperN, upperSum]
  | s :: ts, h => by
    have h2 : (ts.map fun t => ((2 * dot s.2 t.2 : ℤ) : ℝ) * pairVal d ι pt s.1 t.1).sum =
        ((ts.map fun s => (vec s.1, s.2)).map fun t =>
          ((2 * dot s.2 t.2 : ℤ) : ℝ) * β (vec s.1) t.1).sum := by
      rw [List.map_map]
      congr 1
      exact List.map_congr_left fun t ht => by
        simp only [Function.comp_apply]; rw [h s (by simp) t (by simp [ht])]
    rw [List.length_cons, upperN, List.map_cons, upperSum,
      upperN_eq_upperSum β pt vec ts fun a ha b hb => h a (by simp [ha]) b (by simp [hb]),
      h s (by simp) s (by simp), h2]

/-! ### The forms of the projections -/

/-- The projection label and rank are among those of the tables. -/
def formOK : Proj → ℕ → Bool
  | .none, _ => true
  | .sym, r => r == 2 || r == 3
  | .anti, r => r == 2
  | .hook, r => r == 3

/-- The rows of a block are linear keys of the block's rank, and its label is supported. -/
def rowsOK (b : Block) : Bool :=
  formOK b.proj b.rank.toNat &&
    (blockRows b).all fun s => s.1.linearB && s.1.rank == b.rank.toNat

theorem upperN_nonneg (hd : d.Admissible) (pj : Proj) (r : ℕ) (hf : formOK pj r = true)
    (rows : List Row) (hrows : ∀ s ∈ rows, s.1.Linear ∧ s.1.rank = r) :
    0 ≤ upperN d ι (gramPairTerms pj r) rows.length rows := by
  cases pj with
  | none =>
    rw [upperN_eq_upperSum ι (formNone r) _ (fun S α => S.eval d (Key.pairIdx r α)) rows
      fun s hs t ht => ?_]
    · exact upperSum_nonneg _ (mkForm_symm _ _ _ _ _) (formNone_nonneg r) _
    · rw [pairVal, gramPairTerms, pairTerms_none hd (hrows s hs).1 (hrows t ht).1
        (hrows s hs).2 (hrows t ht).2, formNone, mkForm_apply, ipNone]
      simp only [id, mul_comm]
  | sym =>
    simp only [formOK, Bool.or_eq_true, beq_iff_eq] at hf
    rcases hf with rfl | rfl
    · rw [upperN_eq_upperSum ι formSym2 _ (fun S => S.ten2 d) rows fun s hs t ht => ?_]
      · exact upperSum_nonneg _ (mkForm_symm _ _ _ _ _) formSym2_nonneg _
      · rw [pairVal, gramPairTerms, pairTerms_sym2 hd (hrows s hs).1 (hrows t ht).1
          (hrows s hs).2 (hrows t ht).2]
        rfl
    · rw [upperN_eq_upperSum ι formSym3 _ (fun S => S.ten3 d) rows fun s hs t ht => ?_]
      · exact upperSum_nonneg _ (mkForm_symm _ _ _ _ _) formSym3_nonneg _
      · rw [pairVal, gramPairTerms, pairTerms_sym3 hd (hrows s hs).1 (hrows t ht).1
          (hrows s hs).2 (hrows t ht).2]
        rfl
  | anti =>
    simp only [formOK, beq_iff_eq] at hf
    subst hf
    rw [upperN_eq_upperSum ι formAnti2 _ (fun S => S.ten2 d) rows fun s hs t ht => ?_]
    · exact upperSum_nonneg _ (mkForm_symm _ _ _ _ _) formAnti2_nonneg _
    · rw [pairVal, gramPairTerms, antiTerms_eq hd (hrows s hs).1 (hrows t ht).1
        (hrows s hs).2 (hrows t ht).2]
      rfl
  | hook =>
    simp only [formOK, beq_iff_eq] at hf
    subst hf
    rw [upperN_eq_upperSum ι formHook _ (fun S => S.ten3 d) rows fun s hs t ht => ?_]
    · exact upperSum_nonneg _ (mkForm_symm _ _ _ _ _) formHook_nonneg _
    · rw [pairVal, gramPairTerms, hookTerms_eq hd (hrows s hs).1 (hrows t ht).1
        (hrows s hs).2 (hrows t ht).2]
      rfl

theorem gramPre_eval_nonneg (hd : d.Admissible) (b : Block) (cuts : List (ℕ × ℕ))
    (hcov : cutsCover cuts 0 (blockRows b).length = true) (hrows : rowsOK b = true)
    (h : (gramPre b cuts).lin Poly.ind0 = 0) : 0 ≤ (gramPre b cuts).eval d ι := by
  rw [eval_gramPre ι hd b cuts hcov h]
  simp only [rowsOK, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hrows
  exact upperN_nonneg ι hd _ _ hrows.1 _ fun s hs =>
    ⟨Key.linear_of_linearB (hrows.2 s hs).1, (hrows.2 s hs).2⟩

/-! ### The multiplier `χ` -/

theorem eval_chi_keys :
    Key.eval ⟨0, 0, 0, 0, [], []⟩ d ι = 1 ∧
      Key.eval ⟨0, 0, 0, 0, [], [⟨.p, .p, 0⟩]⟩ d ι = ∑ a, d.p a ^ 2 ∧
      Key.eval ⟨0, 2, 0, 0, [], []⟩ d ι = d.g ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges, CertData.weight,
      Matrix.one_apply, sq]

/-- Multiplication by `χ` of a polynomial in linear rank-zero keys, without overflow. -/
theorem eval_mulChi (hd : d.Admissible) {P : Poly} (h : (mulChi P).lin Poly.ind0 = 0)
    (hP : ∀ t ∈ P, (Key.unpack t.1).Linear ∧ (Key.unpack t.1).rank = 0) :
    (mulChi P).eval d ι = (1 - ∑ a, d.p a ^ 2 - d.g ^ 2) * P.eval d ι := by
  have h0 := Poly.lin_ind0_eq_zero_of_mergeAll (fun Q hQ => by
    obtain ⟨t, -, hQ⟩ := List.mem_flatMap.1 hQ
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hQ
    exact Key.lin_ind0_term_nonneg _ _) h
  rw [mulChi, Poly.eval_mergeAll, sum_flatMap_map, Poly.eval, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  obtain ⟨hl, hr⟩ := hP t ht
  obtain ⟨e1, e2, e3⟩ := eval_chi_keys ι (d := d)
  simp only [chi, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  have hmem : ∀ e ∈ chi, (Key.term (e.1 * t.2) ((Key.unpack t.1).mul e.2)).lin Poly.ind0 = 0 :=
    fun e he => h0 _ (List.mem_flatMap.2 ⟨t, ht, List.mem_map.2 ⟨e, he, rfl⟩⟩)
  rw [Key.eval_term_of_lin (hmem (1, ⟨0, 0, 0, 0, [], []⟩) (by simp [chi])) hd,
    Key.eval_term_of_lin (hmem (-1, ⟨0, 0, 0, 0, [], [⟨.p, .p, 0⟩]⟩) (by simp [chi])) hd,
    Key.eval_term_of_lin (hmem (-1, ⟨0, 2, 0, 0, [], []⟩) (by simp [chi])) hd,
    Key.eval_mul_rank0 hl hr, Key.eval_mul_rank0 hl hr, Key.eval_mul_rank0 hl hr, e1, e2, e3]
  push_cast
  ring

/-! ### Blocks -/

/-- The checks on a block and its two reference lists (before and after the multiplier). -/
def blockOK (b : Block) (cuts : List (ℕ × ℕ)) (pre post : Poly) : Bool :=
  cutsCover cuts 0 (blockRows b).length && rowsOK b && pre.all (fun t => t.1 != 0) &&
    post.all (fun t => t.1 != 0) &&
    (b.mode != .B || pre.all fun t => (Key.unpack t.1).linearB && (Key.unpack t.1).rank == 0)

/-- A collected Gram block is nonnegative under `g² + |p|² ≤ 1`. -/
theorem gramBlock_eval_nonneg (hd : d.Admissible) (hχ : ∑ a, d.p a ^ 2 + d.g ^ 2 ≤ 1)
    {b : Block} {cuts : List (ℕ × ℕ)} {pre post : Poly} (hpre : gramPre b cuts = pre)
    (hpost : gramBlock b cuts = post) (hok : blockOK b cuts pre post = true) :
    0 ≤ (gramBlock b cuts).eval d ι := by
  simp only [blockOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hok
  obtain ⟨⟨⟨⟨hcov, hrows⟩, hpre0⟩, hpost0⟩, hB⟩ := hok
  have hP : (gramPre b cuts).lin Poly.ind0 = 0 := hpre ▸ Poly.lin_ind0_of_all hpre0
  have hnn := gramPre_eval_nonneg ι hd b cuts hcov hrows hP
  cases hm : b.mode with
  | B =>
    have hg : gramBlock b cuts = mulChi (gramPre b cuts) := by simp [gramBlock, hm]
    rcases hB with hB | hB
    · exact absurd hm hB
    have hpost' : (mulChi (gramPre b cuts)).lin Poly.ind0 = 0 := by
      rw [← hg, hpost]; exact Poly.lin_ind0_of_all hpost0
    rw [hg, eval_mulChi ι hd hpost' fun t ht => by
      rw [hpre] at ht
      simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at hB
      exact ⟨Key.linear_of_linearB (hB t ht).1, (hB t ht).2⟩]
    exact mul_nonneg (by linarith) hnn
  | I =>
    have hg : gramBlock b cuts = gramPre b cuts := by simp [gramBlock, hm]
    rw [hg]; exact hnn
  | H =>
    have hg : gramBlock b cuts = gramPre b cuts := by simp [gramBlock, hm]
    rw [hg]; exact hnn

end OnePhaseDimension.Certificate.Collect
