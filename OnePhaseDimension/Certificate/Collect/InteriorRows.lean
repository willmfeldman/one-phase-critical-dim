/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.InteriorSound

/-!
# The value of the terms of one row of the first table

For a row `(F, m, c)` of the first table, on admissible data, the terms `rowTerms` evaluate to
`250000 c` times the row's contribution `rowSem F m` to the interior expression (with unit
coefficient), written with the directional derivative `D_l` of the polynomial maps of `m` at the
data. Here `250000 c = Q² (c/Q)`.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Finset Data

variable {d : CertData}

/-! ### Auxiliary identities -/

theorem Key.evalFun_congr {k : Key} (hk : k.SlotsBelowRank) (d : CertData) {ι ι' : ℕ → Fin 5}
    (h : ∀ i < k.rank, ι i = ι' i) : k.evalFun d ι = k.evalFun d ι' :=
  funext fun _ => Key.eval_congr_idx hk _ h

theorem Key.evalFun_mul {s t : Key} (hs : s.SlotsBelowRank) (d : CertData) (ι : ℕ → Fin 5) :
    (s.mul t).evalFun d ι = fun y => s.evalFun d ι y * t.evalFun d (fun i => ι (i + s.rank)) y :=
  funext fun _ => eval_mul' hs ι

theorem sum_fin4 (g : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ α : Fin 4 → Fin 5, g (α 0) (α 1) (α 2) (α 3) = ∑ l, ∑ i, ∑ j, ∑ k, g l i j k := by
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun l _ => ?_
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun j _ => ?_
  rw [← (Fin.consEquiv fun _ => Fin 5).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun k _ => ?_
  simp only [Fintype.sum_unique]
  rfl

/-- The value of the terms of a row. -/
noncomputable def rowVal (d : CertData) (ι : ℕ → Fin 5) (row : TableIRow) : ℝ :=
  ((rowTerms row).map fun e => (e.1 : ℝ) * e.2.eval d ι).sum

/-- The derivative terms of a key are linear keys of one more slot. -/
def DerivLinear (k : Key) : Prop := ∀ u ∈ k.derivTerms, u.2.Linear ∧ u.2.rank = k.rank + 1

theorem derivLinear_of_check {k : Key}
    (h : (k.derivTerms.all fun u => u.2.linearB && u.2.rank == k.rank + 1) = true) :
    DerivLinear k := by
  simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact fun u hu => ⟨Key.linear_of_linearB (h u hu).1, (h u hu).2⟩

/-- `D_l` at the data. -/
noncomputable abbrev DlD (d : CertData) (F : Ten2 × Ten1 × ℝ → ℝ) (l : Fin 5) : ℝ :=
  Dl F d.A d.X d.p d.g d.w d.z l

/-! ### Rows of the families `M` and `P` -/

theorem divTerms_one_val {m : Key} (hm : m.Linear) (h1 : m.rank = 1) (hX : m.hasX = false)
    (hD : DerivLinear m) (hd : d.Admissible) (ι : ℕ → Fin 5) (s κ : ℤ) (T : Key)
    (hT : T.rank = 0 ∧ T.edges = []) :
    ((divTerms 1 s κ [(1, m)]).map fun e => (e.1 : ℝ) * (e.2.mul T).eval d ι).sum =
      T.eval d ι * (s * ∑ l, DlD d (m.evalFun d fun _ => l) l +
        κ * ∑ l, qVec d.X d.A l * m.eval d (fun _ => l)) := by
  have hT' : ∀ K : Key, K.SlotsBelowRank → (K.mul T).eval d ι = K.eval d ι * T.eval d ι :=
    fun K hK => by
      rw [eval_mul' hK]
      exact congrArg _ (Key.eval_congr_idx (by intro e he; simp [hT.2] at he) d
        fun i hi => by simp [hT.1] at hi)
  simp only [divTerms, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
    List.map_map, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    Function.comp_def, mul_one, add_zero]
  have hc : ∀ u ∈ m.derivTerms, (u.2.contract 0 1).SlotsBelowRank := fun u hu =>
    ((hD u hu).1.contract (by norm_num) (by rw [(hD u hu).2, h1]; norm_num)).slotsBelowRank
  have hq : ((qKey.mul m).contract 0 1).SlotsBelowRank :=
    (((Key.linear_of_linearB (by decide) : qKey.Linear).mul hm).contract (by norm_num)
      (by simp [Key.mul, h1, qKey])).slotsBelowRank
  have h2 : (m.derivTerms.map fun u => ((s * u.1 : ℤ) : ℝ) * ((u.2.contract 0 1).mul T).eval d ι) =
      m.derivTerms.map fun u => T.eval d ι * s * ((u.1 : ℝ) * (u.2.contract 0 1).eval d ι) :=
    List.map_congr_left fun u hu => by rw [hT' _ (hc u hu)]; push_cast; ring
  rw [h2, List.sum_map_mul_left, hT' _ hq]
  have h3 := sum_derivTerms_contract hX hD (by rw [h1]; norm_num) hd ι
  rw [h1] at h3
  rw [h3, eval_qContract hm (r := 0) h1 hd ι]
  have h4 : ∀ l, m.evalFun d (insertIdx 0 1 l ι) = m.evalFun d fun _ => l := fun l =>
    Key.evalFun_congr hm.slotsBelowRank d fun i hi => by
      rw [h1] at hi; rcases (by omega : i = 0) with rfl; simp [insertIdx]
  have h5 : ∀ l, m.eval d (fun n => insertIdx 0 1 l ι (n + 1)) = m.eval d fun _ => l := fun l =>
    Key.eval_congr_idx hm.slotsBelowRank d fun i hi => by
      rw [h1] at hi; rcases (by omega : i = 0) with rfl; simp [insertIdx]
  simp only [h4, h5]
  ring

theorem rowVal_M {row : TableIRow} (hF : row.fam = .M) (hm : row.key.Linear)
    (h1 : row.key.rank = 1) (hX : row.key.hasX = false) (hD : DerivLinear row.key)
    (hd : d.Admissible) (ι : ℕ → Fin 5) :
    rowVal d ι row = 250000 * row.coef * d.w * ∑ l, DlD d (row.key.evalFun d fun _ => l) l +
      540000 * row.coef * d.w * ∑ l, qVec d.X d.A l * row.key.eval d (fun _ => l) := by
  obtain ⟨F, len, w, c⟩ := row
  subst hF
  simp only [rowVal, rowTerms, List.map_map, Function.comp_def]
  rw [divTerms_one_val hm h1 hX hD hd ι _ _ wKey ⟨rfl, rfl⟩, eval_wKey]
  push_cast
  ring

theorem rowVal_P {row : TableIRow} (hF : row.fam = .P) (hm : row.key.Linear)
    (h1 : row.key.rank = 1) (hX : row.key.hasX = false) (hD : DerivLinear row.key)
    (hd : d.Admissible) (ι : ℕ → Fin 5) :
    rowVal d ι row = 250000 * row.coef * d.z * ∑ l, DlD d (row.key.evalFun d fun _ => l) l +
      290000 * row.coef * d.z * ∑ l, qVec d.X d.A l * row.key.eval d (fun _ => l) := by
  obtain ⟨F, len, w, c⟩ := row
  subst hF
  simp only [rowVal, rowTerms, List.map_map, Function.comp_def]
  rw [divTerms_one_val hm h1 hX hD hd ι _ _ (zKey 1) ⟨rfl, rfl⟩, eval_zKey, pow_one]
  push_cast
  ring

theorem eval_rank0 {m : Key} (hm : m.Linear) (h0 : m.rank = 0) (ι ι' : ℕ → Fin 5) :
    m.eval d ι = m.eval d ι' :=
  Key.eval_congr_idx hm.slotsBelowRank d fun i hi => by omega

theorem rowVal_f {row : TableIRow} (hF : row.fam = .f) (hm : row.key.Linear)
    (h0 : row.key.rank = 0) (hX : row.key.hasX = false) (hD : DerivLinear row.key)
    (hd : d.Admissible) (ι : ℕ → Fin 5) :
    rowVal d ι row = -1000000 * row.coef * d.z ^ 2 * row.key.eval d (fun _ => 0) +
      250000 * row.coef * row.key.eval d (fun _ => 0) * ∑ a, d.ell a ^ 2 -
      250000 * row.coef * ∑ k, d.ell k * DlD d (row.key.evalFun d fun _ => k) k -
      290000 * row.coef * row.key.eval d (fun _ => 0) * ∑ k, qVec d.X d.A k * d.ell k := by
  obtain ⟨F, len, w, c⟩ := row
  subst hF
  set m := TableIRow.key ⟨.f, len, w, c⟩
  have hql : qKey.Linear := Key.linear_of_linearB (by decide)
  have hq : (qKey.mul m).Linear := hql.mul hm
  have hq1 : (qKey.mul m).rank = 1 := by simp [Key.mul, h0, qKey]
  have he : ∀ ι' : ℕ → Fin 5, m.eval d ι' = m.eval d (fun _ => 0) := fun ι' =>
    eval_rank0 hm h0 _ _
  simp only [rowVal, rowTerms, List.map_append, List.map_cons, List.map_nil, List.map_map,
    Function.comp_def, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
  rw [eval_mul' hm.slotsBelowRank, eval_mul' hm.slotsBelowRank, eval_zKey, eval_ellSqKey,
    eval_withEll hq hq1 hd, he ι]
  have hu : (m.derivTerms.map fun u => ((-250000 * c * u.1 : ℤ) : ℝ) *
      ((u.2.mul ellKey).contractPairs 1).eval d ι) =
      m.derivTerms.map fun u => -250000 * (c : ℝ) *
        ∑ k, d.ell k * ((u.1 : ℝ) * u.2.eval d (fun _ => k)) :=
    List.map_congr_left fun u hu => by
      have h1 : u.2.rank = 1 := by rw [(hD u hu).2, h0]
      rw [eval_withEll (hD u hu).1 h1 hd, mul_sum, mul_sum]
      push_cast
      refine sum_congr rfl fun k _ => by ring
  rw [hu, List.sum_map_mul_left, list_sum_finset_sum]
  have hDl : ∀ k : Fin 5, (m.derivTerms.map fun u => d.ell k * ((u.1 : ℝ) * u.2.eval d
      (fun _ => k))).sum = d.ell k * DlD d (m.evalFun d fun _ => k) k := fun k => by
    rw [List.sum_map_mul_left, Key.sum_derivTerms_eq_Dl hX hd]
  have hqm : ∑ k, (qKey.mul m).eval d (fun _ => k) * d.ell k =
      m.eval d (fun _ => 0) * ∑ k, qVec d.X d.A k * d.ell k := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [eval_mul' hql.slotsBelowRank, eval_qKey _ _ hd, he]
    ring
  simp only [hDl, hqm]
  push_cast
  ring

theorem list_sum_finset_sum' {κ ν : Type*} [Fintype ν] (L : List κ) (F : κ → ν → ℝ) :
    (L.map fun t => ∑ a, F t a).sum = ∑ a, (L.map fun t => F t a).sum := by
  induction L with
  | nil => simp
  | cons t L ih => simp only [List.map_cons, List.sum_cons, ih, sum_add_distrib]

theorem list_sum_finset_sum3 {κ : Type*} (L : List κ) (F : κ → Fin 5 → Fin 5 → Fin 5 → ℝ) :
    (L.map fun t => ∑ i, ∑ j, ∑ k, F t i j k).sum =
      ∑ i, ∑ j, ∑ k, (L.map fun t => F t i j k).sum := by
  rw [list_sum_finset_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [list_sum_finset_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [list_sum_finset_sum]

/-- The `X`-contracted divergence terms of a key `G` of rank `4`. -/
theorem divX_val {G : Key} (h4 : G.rank = 4) (hX : G.hasX = false)
    (hD : DerivLinear G) (hd : d.Admissible) (ι : ℕ → Fin 5) (a s : ℤ) :
    (((G.derivTerms.map fun u => (s * a * u.1, u.2.contract 0 4)).map withX).map fun e =>
      (e.1 : ℝ) * e.2.eval d ι).sum =
      s * a * ∑ i, ∑ j, ∑ k, (∑ l, DlD d (G.evalFun d (insertIdx 0 4 l (idx3 i j k))) l) *
        d.X i j k := by
  have hc : ∀ u ∈ G.derivTerms, (u.2.contract 0 4).Linear ∧ (u.2.contract 0 4).rank = 3 :=
    fun u hu => ⟨(hD u hu).1.contract (by norm_num) (by rw [(hD u hu).2, h4]; norm_num),
      by rw [Key.rank_contract, (hD u hu).2, h4]⟩
  simp only [List.map_map, Function.comp_def, withX]
  have h1 : (G.derivTerms.map fun u => ((s * a * u.1 : ℤ) : ℝ) *
      ((u.2.contract 0 4).mul xKey |>.contractPairs 3).eval d ι) =
      G.derivTerms.map fun u => (s * a : ℝ) * ∑ i, ∑ j, ∑ k,
        (u.1 : ℝ) * (u.2.contract 0 4).eval d (idx3 i j k) * d.X i j k :=
    List.map_congr_left fun u hu => by
      rw [eval_withX (hc u hu).1 (hc u hu).2 hd]
      simp only [mul_sum, Key.ten3]
      push_cast
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring
  rw [h1, List.sum_map_mul_left, list_sum_finset_sum3]
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  have := sum_derivTerms_contract hX hD (by rw [h4]; norm_num) hd (idx3 i j k)
  rw [h4] at this
  rw [List.sum_map_mul_right, this]

/-- The `X`-contracted `q`-terms of a key `G` of rank `4`. -/
theorem qX_val {G : Key} (hG : G.Linear) (h4 : G.rank = 4) (hd : d.Admissible)
    (ι : ℕ → Fin 5) :
    (((qKey.mul G).contract 0 1).mul xKey |>.contractPairs 3).eval d ι =
      ∑ i, ∑ j, ∑ k, (∑ l, qVec d.X d.A l *
        G.eval d (fun n => insertIdx 0 1 l (idx3 i j k) (n + 1))) * d.X i j k := by
  have hq : qKey.Linear := Key.linear_of_linearB (by decide)
  have hK : ((qKey.mul G).contract 0 1).Linear :=
    (hq.mul hG).contract (by norm_num) (by simp [Key.mul, h4, qKey])
  have hK3 : ((qKey.mul G).contract 0 1).rank = 3 := by
    rw [Key.rank_contract]; simp [Key.mul, h4, qKey]
  rw [eval_withX hK hK3 hd]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  rw [Key.ten3, eval_qContract hG (r := 3) h4 hd]

theorem rowVal_U {row : TableIRow} (hF : row.fam = .U) (hm : row.key.Linear)
    (h2 : row.key.rank = 2) (hX : (deltaKey.mul row.key).hasX = false)
    (hD : DerivLinear (deltaKey.mul row.key)) (hd : d.Admissible) (ι : ℕ → Fin 5) :
    rowVal d ι row = 1250000 * row.coef * d.z ^ 2 *
        ∑ j, ∑ k, row.key.eval d (idx2 j k) * d.A j k +
      250000 * row.coef * ∑ i, ∑ j, ∑ k,
        (∑ l, DlD d (fun y => kron l i * row.key.evalFun d (idx2 j k) y) l) * d.X i j k +
      40000 * row.coef * ∑ i, ∑ j, ∑ k,
        (∑ l, qVec d.X d.A l * (kron l i * row.key.eval d (idx2 j k))) * d.X i j k := by
  obtain ⟨F, len, w, c⟩ := row
  subst hF
  set m := TableIRow.key ⟨.U, len, w, c⟩
  have hδ : deltaKey.Linear := Key.linear_of_linearB (by decide)
  have ha : aKey.Linear := Key.linear_of_linearB (by decide)
  have hG : (deltaKey.mul m).Linear := hδ.mul hm
  have hG4 : (deltaKey.mul m).rank = 4 := by simp [Key.mul, h2, deltaKey]
  have hma : ((m.mul aKey).contractPairs 2).SlotsBelowRank :=
    (Key.Linear.contractPairs 2 (hm.mul ha) (by simp [Key.mul, h2, aKey])).slotsBelowRank
  simp only [rowVal, rowTerms, divTerms, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_cons, List.map_append, List.map_nil, List.sum_cons, List.sum_append, List.sum_nil,
    add_zero]
  rw [eval_mul' hma, eval_zKey, eval_mulTerm2 hd hm ha h2 rfl,
    divX_val hG4 hX hD hd ι 1 (250000 * c)]
  simp only [withX, mul_one]
  rw [qX_val hG hG4 hd]
  have hfun : ∀ i j k l, (deltaKey.mul m).evalFun d (insertIdx 0 4 l (idx3 i j k)) =
      fun y => kron l i * m.evalFun d (idx2 j k) y := fun i j k l => by
    rw [Key.evalFun_mul hδ.slotsBelowRank]
    funext y
    rw [show deltaKey.evalFun d (insertIdx 0 4 l (idx3 i j k)) y = kron l i from by
      rw [Key.evalFun, eval_deltaKey]; simp [insertIdx]]
    congr 1
    exact congrFun (Key.evalFun_congr hm.slotsBelowRank d fun n hn => by
      rw [h2] at hn
      rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp [insertIdx, deltaKey, idx2]) y
  have hval : ∀ i j k l, (deltaKey.mul m).eval d (fun n => insertIdx 0 1 l (idx3 i j k) (n + 1)) =
      kron l i * m.eval d (idx2 j k) := fun i j k l => by
    rw [eval_mul' hδ.slotsBelowRank, eval_deltaKey]
    refine congrArg₂ (· * ·) (by simp [insertIdx]) (Key.eval_congr_idx hm.slotsBelowRank d
      fun n hn => ?_)
    rw [h2] at hn
    rcases (by omega : n = 0 ∨ n = 1) with rfl | rfl <;> simp [insertIdx, deltaKey, idx2]
  simp only [hfun, hval]
  have hA : ∀ j k, aKey.ten2 d j k = d.A j k := fun j k => by
    rw [Key.ten2, eval_aKey]; rfl
  simp only [hA]
  simp only [Key.ten2]
  push_cast
  ring

/-- The value of a key of rank `4` at the slot assignment of a full contraction. -/
theorem eval_pairIdx4 {K : Key} (hK : K.SlotsBelowRank) (h4 : K.rank = 4)
    (α : Fin 4 → Fin 5) : K.eval d (Key.pairIdx 4 α) = K.eval d (idx4 (α 0) (α 1) (α 2) (α 3)) :=
  Key.eval_congr_idx hK d fun n hn => by
    rw [h4] at hn
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl <;> rfl

/-- The `z²` terms of a key of rank `4` against `δ_{lj}A_{ik} + δ_{lk}A_{ij}`. -/
theorem zTest_val {K : Key} (hK : K.Linear) (h4 : K.rank = 4) (hd : d.Admissible)
    (ι : ℕ → Fin 5) (t : ℤ) :
    ((zTestKeys.map fun b => (t * b.1, ((K.mul b.2).contractPairs 4).mul (zKey 2))).map
      fun e => (e.1 : ℝ) * e.2.eval d ι).sum =
      t * d.z ^ 2 * ∑ l, ∑ i, ∑ j, ∑ k, K.eval d (idx4 l i j k) *
        (kron l j * d.A i k + kron l k * d.A i j) := by
  have hb : ∀ b ∈ zTestKeys, b.2.Linear ∧ b.2.rank = 4 := by
    intro b hb
    simp only [zTestKeys, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact ⟨Key.linear_of_linearB (by decide), rfl⟩
  have hv : ∀ b ∈ zTestKeys, (((K.mul b.2).contractPairs 4).mul (zKey 2)).eval d ι =
      d.z ^ 2 * ∑ α : Fin 4 → Fin 5, K.eval d (Key.pairIdx 4 α) * b.2.eval d (Key.pairIdx 4 α) :=
    fun b hb' => by
      rw [eval_mul' (Key.Linear.contractPairs 4 (hK.mul (hb b hb').1)
        (by simp [Key.mul, h4, (hb b hb').2])).slotsBelowRank, eval_zKey,
        Key.eval_contractPairs_mul hd hK (hb b hb').1 h4 (hb b hb').2, mul_comm]
  rw [List.map_map]
  have h1 : (zTestKeys.map ((fun e : ℤ × Key => (e.1 : ℝ) * e.2.eval d ι) ∘
      fun b => (t * b.1, ((K.mul b.2).contractPairs 4).mul (zKey 2)))) =
      zTestKeys.map fun b => t * d.z ^ 2 * ∑ α : Fin 4 → Fin 5,
        K.eval d (Key.pairIdx 4 α) * ((b.1 : ℝ) * b.2.eval d (Key.pairIdx 4 α)) :=
    List.map_congr_left fun b hb' => by
      simp only [Function.comp_apply, hv b hb', mul_sum]
      push_cast
      refine sum_congr rfl fun α _ => by ring
  rw [h1, List.sum_map_mul_left, list_sum_finset_sum']
  congr 1
  rw [← sum_fin4 (fun l i j k => K.eval d (idx4 l i j k) *
    (kron l j * d.A i k + kron l k * d.A i j))]
  refine sum_congr rfl fun α _ => ?_
  rw [List.sum_map_mul_left, eval_zTestKeys, eval_pairIdx4 hK.slotsBelowRank h4]
  rfl

theorem rowVal_K {row : TableIRow} (hF : row.fam = .K) (hm : row.key.Linear)
    (h4 : row.key.rank = 4) (hX : row.key.hasX = false)
    (hX' : (row.key.permSlots [1, 0]).hasX = false) (hm' : (row.key.permSlots [1, 0]).Linear)
    (hD : DerivLinear row.key) (hD' : DerivLinear (row.key.permSlots [1, 0]))
    (hd : d.Admissible) (ι : ℕ → Fin 5) :
    rowVal d ι row = 250000 * row.coef * d.z ^ 2 * ∑ l, ∑ i, ∑ j, ∑ k,
        (row.key.eval d (idx4 l i j k) - row.key.eval d (idx4 i l j k)) *
          (kron l j * d.A i k + kron l k * d.A i j) +
      250000 * row.coef * (∑ i, ∑ j, ∑ k,
        (∑ l, DlD d (row.key.evalFun d (idx4 l i j k)) l) * d.X i j k -
        ∑ i, ∑ j, ∑ k, (∑ l, DlD d (row.key.evalFun d (idx4 i l j k)) l) * d.X i j k) +
      40000 * row.coef * (∑ i, ∑ j, ∑ k,
        (∑ l, qVec d.X d.A l * row.key.eval d (idx4 l i j k)) * d.X i j k -
        ∑ i, ∑ j, ∑ k, (∑ l, qVec d.X d.A l * row.key.eval d (idx4 i l j k)) * d.X i j k) := by
  obtain ⟨F, len, w, c⟩ := row
  subst hF
  set m := TableIRow.key ⟨.K, len, w, c⟩
  set m' := m.permSlots [1, 0]
  have h4' : m'.rank = 4 := h4
  simp only [rowVal, rowTerms, divTerms, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    add_zero]
  rw [zTest_val hm h4 hd, zTest_val hm' h4' hd, divX_val h4 hX hD hd ι 1 (250000 * c),
    divX_val h4' hX' hD' hd ι (-1) (250000 * c)]
  simp only [withX]
  rw [qX_val hm h4 hd, qX_val hm' h4' hd]
  have hperm : ∀ ι' : ℕ → Fin 5, m'.eval d ι' = m.eval d (fun n => ι' ([1, 0].getD n n)) :=
    fun ι' => Key.eval_permSlots m [1, 0] d ι'
  have e1 : ∀ i j k l, m.evalFun d (insertIdx 0 4 l (idx3 i j k)) = m.evalFun d (idx4 l i j k) :=
    fun i j k l => Key.evalFun_congr hm.slotsBelowRank d fun n hn => by
      rw [h4] at hn
      rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl <;>
        simp [insertIdx, idx4]
  have e2 : ∀ i j k l, m'.evalFun d (insertIdx 0 4 l (idx3 i j k)) =
      m.evalFun d (idx4 i l j k) := fun i j k l => by
    funext y
    simp only [Key.evalFun]
    rw [Key.eval_permSlots]
    exact Key.eval_congr_idx hm.slotsBelowRank _ fun n hn => by
      rw [h4] at hn
      rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl <;>
        simp [insertIdx, idx4]
  have e3 : ∀ i j k l, m.eval d (fun n => insertIdx 0 1 l (idx3 i j k) (n + 1)) =
      m.eval d (idx4 l i j k) := fun i j k l =>
    Key.eval_congr_idx hm.slotsBelowRank d fun n hn => by
      rw [h4] at hn
      rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl <;>
        simp [insertIdx, idx4]
  have e4 : ∀ i j k l, m'.eval d (fun n => insertIdx 0 1 l (idx3 i j k) (n + 1)) =
      m.eval d (idx4 i l j k) := fun i j k l => by
    rw [hperm]
    exact Key.eval_congr_idx hm.slotsBelowRank d fun n hn => by
      rw [h4] at hn
      rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl <;>
        simp [insertIdx, idx4]
  have e5 : ∀ l i j k, m'.eval d (idx4 l i j k) = m.eval d (idx4 i l j k) := fun l i j k => by
    rw [hperm]
    exact Key.eval_congr_idx hm.slotsBelowRank d fun n hn => by
      rw [h4] at hn
      rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3) with rfl | rfl | rfl | rfl <;>
        simp [idx4]
  simp only [e1, e2, e3, e4, e5]
  simp only [sub_mul, sum_sub_distrib]
  push_cast
  ring

end OnePhaseDimension.Certificate.Collect
