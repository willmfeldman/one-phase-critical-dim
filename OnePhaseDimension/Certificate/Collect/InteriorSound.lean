/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.InteriorPoly
public import OnePhaseDimension.Certificate.Collect.Sound
public import OnePhaseDimension.Certificate.Polynomials

/-!
# Values of the terms of the interior expression

On admissible data, the terms produced by `rowTerms` for one row of the first table evaluate to
`Q² (c/Q)` times the row's contribution to the interior expression, written with the directional
derivative `D_l` of the polynomial maps of the keys. This file contains the values of the fixed
keys and the generic contraction and divergence lemmas.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Finset

variable {d : CertData}

/-! ### Fixed keys -/

section Fixed

variable (d) (ι : ℕ → Fin 5)

theorem eval_zKey (n : ℕ) : (zKey n).eval d ι = d.z ^ n := by
  simp [zKey, Key.eval, Key.prefactor, Key.xBound, evalEdges]

theorem eval_wKey : wKey.eval d ι = d.w := by
  simp [wKey, Key.eval, Key.prefactor, Key.xBound, evalEdges]

theorem eval_ellSqKey : ellSqKey.eval d ι = ∑ a, d.ell a ^ 2 := by
  simp [ellSqKey, Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges,
    CertData.weight, Matrix.one_apply, sq]

theorem eval_ellKey : ellKey.eval d ι = d.ell (ι 0) := by
  simp [ellKey, Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges,
    CertData.weight, Matrix.one_apply]

theorem eval_aKey : aKey.eval d ι = d.A (ι 0) (ι 1) := by
  simp [aKey, Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges,
    CertData.weight]

theorem eval_deltaKey : deltaKey.eval d ι = kron (ι 0) (ι 1) := by
  simp [deltaKey, Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges,
    CertData.weight, Matrix.one_apply, kron, eq_comm]

theorem eval_xKey : xKey.eval d ι = d.X (ι 0) (ι 1) (ι 2) := by
  simp [xKey, Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges,
    CertData.weight, Matrix.one_apply, pushIdx, CertData.xFactor, Function.update_apply]

theorem eval_qKey (hd : d.Admissible) : qKey.eval d ι = qVec d.X d.A (ι 0) := by
  calc qKey.eval d ι = ∑ i, ∑ j, d.A i j * d.X i j (ι 0) := by
        simp [qKey, Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges,
          CertData.weight, Matrix.one_apply, pushIdx, CertData.xFactor, Function.update_apply]
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [hd.X_cycle, mul_comm]

theorem eval_zTestKeys :
    (zTestKeys.map fun b => (b.1 : ℝ) * b.2.eval d ι).sum =
      kron (ι 0) (ι 2) * d.A (ι 1) (ι 3) + kron (ι 0) (ι 3) * d.A (ι 1) (ι 2) := by
  simp [zTestKeys, Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges,
    CertData.weight, Matrix.one_apply, kron, eq_comm]

end Fixed

/-! ### Products, contractions, divergence -/

/-- The value of a product, with the slots of the second factor read after those of the
first. -/
theorem eval_mul' {s t : Key} (hs : s.SlotsBelowRank) (ι : ℕ → Fin 5) :
    (s.mul t).eval d ι = s.eval d ι * t.eval d (fun i => ι (i + s.rank)) := by
  rw [← Key.eval_mul hs d ι]
  congr 1
  funext i
  simp only [Key.joinIdx]
  split_ifs with h
  · rfl
  · congr 1; omega

theorem Key.Linear.contractPairs : ∀ (n : ℕ) {K : Key}, K.Linear → K.rank = 2 * n →
    (K.contractPairs n).Linear
  | 0, _, hK, _ => hK
  | n + 1, K, hK, hr => by
    rw [Key.contractPairs]
    exact Key.Linear.contractPairs n (hK.contract (by omega) (by omega))
      (by rw [Key.rank_contract]; omega)

theorem rank_contractPairs : ∀ (n : ℕ) (K : Key), (K.contractPairs n).rank = K.rank - 2 * n
  | 0, _ => rfl
  | n + 1, K => by
    rw [Key.contractPairs, rank_contractPairs n, Key.rank_contract]; omega

/-- The contraction of slots `0` and `r` of a key of rank `r + 1` in which both occur once. -/
theorem eval_contract_last {u : Key} (hu : u.Linear) {r : ℕ} (hr : 0 < r) (hur : u.rank = r + 1)
    (hd : d.Admissible) (ι : ℕ → Fin 5) :
    (u.contract 0 r).eval d ι = ∑ l, u.eval d (insertIdx 0 r l ι) := by
  have h0 : slotCount (.slot 0) u.edges = 1 := by rw [hu]; simp [hur]
  have hr' : slotCount (.slot r) u.edges = 1 := by rw [hu]; simp [hur]
  exact Key.eval_contract hr h0 hr' hd ι

/-- The divergence `∑_l D_l F_{l…}` of the polynomial map of a key `k` of rank `r ≥ 1`:
the graph derivative with its derivative index (the last slot) contracted with slot `0`. -/
theorem sum_derivTerms_contract {k : Key} (hk : k.hasX = false)
    (hlin : ∀ u ∈ k.derivTerms, u.2.Linear ∧ u.2.rank = k.rank + 1) (hr : 0 < k.rank)
    (hd : d.Admissible) (ι : ℕ → Fin 5) :
    (k.derivTerms.map fun u => (u.1 : ℝ) * (u.2.contract 0 k.rank).eval d ι).sum =
      ∑ l, Dl (k.evalFun d (insertIdx 0 k.rank l ι)) d.A d.X d.p d.g d.w d.z l := by
  have h1 : (k.derivTerms.map fun u => (u.1 : ℝ) * (u.2.contract 0 k.rank).eval d ι) =
      k.derivTerms.map fun u => ∑ l, (u.1 : ℝ) * u.2.eval d (insertIdx 0 k.rank l ι) :=
    List.map_congr_left fun u hu => by
      rw [eval_contract_last (hlin u hu).1 hr (hlin u hu).2 hd, mul_sum]
  rw [h1, list_sum_finset_sum]
  refine sum_congr rfl fun l _ => ?_
  have := Key.sum_derivTerms_eq_Dl hk hd (insertIdx 0 k.rank l ι)
  simp only [insertIdx, or_true, ite_true] at this
  exact this

/-- The full contraction of a linear key of rank `3` with `X`. -/
theorem eval_withX {K : Key} (hK : K.Linear) (h3 : K.rank = 3) (hd : d.Admissible)
    (ι : ℕ → Fin 5) :
    ((K.mul xKey).contractPairs 3).eval d ι = ∑ i, ∑ j, ∑ k, K.ten3 d i j k * d.X i j k := by
  have hx : xKey.Linear := Key.linear_of_linearB (by decide)
  rw [Key.eval_contractPairs_mul hd hK hx h3 rfl, ← Key.sum_fin3]
  refine sum_congr rfl fun α _ => ?_
  have hp : ∀ m < 3, Key.pairIdx 3 α m = idx3 (α 0) (α 1) (α 2) m := fun m hm => by
    rcases Key.lt_three hm with rfl | rfl | rfl <;> rfl
  rw [Key.eval_eq_ten3 hK h3 d (hp 0 (by norm_num)) (hp 1 (by norm_num)) (hp 2 (by norm_num)),
    eval_xKey]
  simp only [Key.pairIdx]
  rfl

/-- The contraction of a linear key of rank `1` with `ℓ`. -/
theorem eval_withEll {K : Key} (hK : K.Linear) (h1 : K.rank = 1) (hd : d.Admissible)
    (ι : ℕ → Fin 5) :
    ((K.mul ellKey).contractPairs 1).eval d ι = ∑ k, K.eval d (fun _ => k) * d.ell k := by
  have hl : ellKey.Linear := Key.linear_of_linearB (by decide)
  rw [Key.eval_contractPairs_one hd hK hl h1 rfl, Proj.inner1]
  refine sum_congr rfl fun k _ => ?_
  rw [Key.ten1, Key.ten1, eval_ellKey]

/-- `q_l F_{l…}`: the product `q ⊗ K` contracted in its slots `0, 1`. -/
theorem eval_qContract {K : Key} (hK : K.Linear) {r : ℕ} (hr : K.rank = r + 1)
    (hd : d.Admissible) (ι : ℕ → Fin 5) :
    ((qKey.mul K).contract 0 1).eval d ι =
      ∑ l, qVec d.X d.A l * K.eval d (fun n => insertIdx 0 1 l ι (n + 1)) := by
  have hq : qKey.Linear := Key.linear_of_linearB (by decide)
  have hm := hq.mul hK
  have hmr : (qKey.mul K).rank = r + 2 := by simp [Key.mul, hr, qKey]; omega
  have h0 : slotCount (.slot 0) (qKey.mul K).edges = 1 := by rw [hm]; simp [hmr]
  have h1 : slotCount (.slot 1) (qKey.mul K).edges = 1 := by rw [hm]; simp [hmr]
  rw [Key.eval_contract (by norm_num) h0 h1 hd ι]
  refine sum_congr rfl fun l _ => ?_
  rw [eval_mul' hq.slotsBelowRank, eval_qKey _ _ hd]
  simp only [insertIdx, true_or, ite_true]
  rfl

end OnePhaseDimension.Certificate.Collect
