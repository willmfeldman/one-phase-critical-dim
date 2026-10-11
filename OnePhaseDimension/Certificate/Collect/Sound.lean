/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Ops

/-!
# Soundness of collected sums of terms

A collected polynomial is a balanced merge of single-term polynomials `Key.term c k`. Its value
is the sum of the values `c · eval k`, provided no term overflowed the packing. An overflowing
term is the marker key `0` with coefficient `+1`; merging adds coefficients at equal keys, so the
total coefficient of the key `0` in a merge is the number of overflowing terms. Hence a merged
result without the key `0` certifies that no term overflowed.

We express this with the linear functionals `Poly.lin φ P = ∑ c · φ(key)` (the value `Poly.eval` is
the case `φ = eval ∘ unpack`; the coefficient of the key `0` is the case `φ = ind0`).
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

open Finset

namespace Poly

/-- The linear functional `∑ c · φ(key)` on polynomials. -/
noncomputable def lin (φ : ℕ → ℝ) (P : Poly) : ℝ := (P.map fun t => (t.2 : ℝ) * φ t.1).sum

variable (φ : ℕ → ℝ)

@[simp] theorem lin_nil : lin φ [] = 0 := rfl

@[simp] theorem lin_cons (a : ℕ) (c : ℤ) (P : Poly) :
    lin φ ((a, c) :: P) = c * φ a + lin φ P := by
  simp [lin]

theorem eval_eq_lin (P : Poly) (d : CertData) (ι : ℕ → Fin 5) :
    P.eval d ι = lin (fun a => (Key.unpack a).eval d ι) P := rfl

theorem lin_mergeAux (a : ℕ) (c : ℤ) (P : Poly) (mp : Poly → Poly)
    (hmp : ∀ Q, lin φ (mp Q) = lin φ P + lin φ Q) :
    ∀ Q, lin φ (mergeAux a c P mp Q) = c * φ a + lin φ P + lin φ Q
  | [] => by simp [mergeAux]
  | (b, e) :: Q => by
    unfold mergeAux
    split_ifs with h₁ h₂ h₃
    · simp only [lin_cons, hmp]; ring
    · simp only [lin_cons, lin_mergeAux a c P mp hmp Q]; ring
    · have hab : a = b := by omega
      subst hab
      simp only [hmp, lin_cons]
      have : (c : ℝ) + e = 0 := by exact_mod_cast h₃
      rw [eq_neg_of_add_eq_zero_right this]
      ring
    · have hab : a = b := by omega
      subst hab
      simp only [lin_cons, hmp, Int.cast_add]; ring

theorem lin_merge : ∀ P Q : Poly, lin φ (merge P Q) = lin φ P + lin φ Q
  | [], Q => by simp [merge]
  | (a, c) :: P, Q => by
    rw [merge, lin_mergeAux φ a c P (merge P) (lin_merge P), lin_cons]

theorem lin_mergePairs : ∀ l : List Poly, ((mergePairs l).map (lin φ)).sum = (l.map (lin φ)).sum
  | [] => rfl
  | [_] => rfl
  | a :: b :: l => by
    simp only [mergePairs, List.map_cons, List.sum_cons, lin_merge, lin_mergePairs l]
    ring

theorem lin_mergeAllAux : ∀ (n : ℕ) (l : List Poly),
    ((mergeAllAux n l).map (lin φ)).sum = (l.map (lin φ)).sum
  | 0, _ => rfl
  | n + 1, l => by rw [mergeAllAux, lin_mergeAllAux n, lin_mergePairs]

/-- The balanced merge adds the values of any linear functional. -/
theorem lin_mergeAll (l : List Poly) : lin φ (mergeAll l) = (l.map (lin φ)).sum := by
  rw [mergeAll, ← lin_mergeAllAux φ l.length l]
  have h := length_mergeAllAux_le l.length l (Nat.le_succ _)
  rcases hl : mergeAllAux l.length l with _ | ⟨P, _ | ⟨Q, rest⟩⟩
  · rfl
  · simp
  · simp [hl] at h

theorem lin_append (P Q : Poly) : lin φ (P ++ Q) = lin φ P + lin φ Q := by
  simp [lin]

theorem lin_smul (c : ℤ) (P : Poly) : lin φ (smul c P) = c * lin φ P := by
  unfold smul
  split_ifs with h
  · simp [h]
  · simp only [lin, List.map_map, Function.comp_def, Int.cast_mul, mul_assoc,
      ← List.sum_map_mul_left]

/-- The indicator of the key `0` (the overflow marker). -/
noncomputable def ind0 (a : ℕ) : ℝ := if a = 0 then 1 else 0

/-- The coefficient of the key `0` vanishes when no key is `0`. -/
theorem lin_ind0_of_all {P : Poly} (h : (P.all fun t => t.1 != 0) = true) : lin ind0 P = 0 := by
  induction P with
  | nil => rfl
  | cons t P ih =>
    obtain ⟨a, c⟩ := t
    simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    rw [lin_cons, ih h.2, ind0, ite_eq_right_iff.2 (fun h' => absurd h' h.1)]
    ring

end Poly

namespace Key

theorem pack_pos (k : Key) : 0 < k.pack := by
  rw [pack, packDigits, foldl_pack_eq]
  positivity

/-- The coefficient of the overflow marker in a single term is `0` or `1`. -/
theorem lin_ind0_term_nonneg (c : ℤ) (k : Key) : 0 ≤ (term c k).lin Poly.ind0 := by
  simp only [term]
  split_ifs <;> simp [Poly.ind0, overflowTerm, (pack_pos _).ne']

/-- A single term without overflow evaluates to `c · eval k`. -/
theorem eval_term_of_lin {c : ℤ} {k : Key} (h : (term c k).lin Poly.ind0 = 0) {d : CertData}
    (hd : d.Admissible) (ι : ℕ → Fin 5) : (term c k).eval d ι = c * k.eval d ι := by
  by_cases hb : k.reduce.2.boundedB = true
  · exact eval_term c k hb hd ι
  · simp only [term] at h ⊢
    split_ifs at h ⊢ with h₀
    · have : ((k.reduce.1 : ℝ) * c) = 0 := by exact_mod_cast h₀
      rw [Poly.eval_nil, ← k.eval_reduce hd ι, ← mul_assoc, mul_comm (c : ℝ), this, zero_mul]
    · simp [Poly.ind0, overflowTerm] at h

end Key

namespace Poly

/-- If the merge of nonnegative-marker polynomials has no marker, none of them has one. -/
theorem lin_ind0_eq_zero_of_mergeAll {L : List Poly} (hL : ∀ P ∈ L, 0 ≤ P.lin ind0)
    (h : (mergeAll L).lin ind0 = 0) : ∀ P ∈ L, P.lin ind0 = 0 := by
  rw [lin_mergeAll] at h
  induction L with
  | nil => simp
  | cons Q L ih =>
    simp only [List.map_cons, List.sum_cons] at h
    have hQ := hL Q (by simp)
    have hS : 0 ≤ (L.map (lin ind0)).sum := List.sum_nonneg fun x hx => by
      obtain ⟨R, hR, rfl⟩ := List.mem_map.1 hx; exact hL R (by simp [hR])
    intro P hP
    rcases List.mem_cons.1 hP with rfl | hP
    · linarith
    · exact ih (fun R hR => hL R (by simp [hR])) (by linarith) P hP

/-- The merge of the single-term polynomials of a list of terms, if free of the overflow
marker, evaluates to the sum of the terms. -/
theorem eval_mergeAll_terms {ts : List (ℤ × Key)}
    (h : (mergeAll (ts.map fun e => Key.term e.1 e.2)).lin ind0 = 0) {d : CertData}
    (hd : d.Admissible) (ι : ℕ → Fin 5) :
    (mergeAll (ts.map fun e => Key.term e.1 e.2)).eval d ι =
      (ts.map fun e => (e.1 : ℝ) * e.2.eval d ι).sum := by
  have h0 := lin_ind0_eq_zero_of_mergeAll (fun P hP => by
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hP; exact Key.lin_ind0_term_nonneg _ _) h
  rw [eval_mergeAll, List.map_map]
  congr 1
  refine List.map_congr_left fun e he => ?_
  exact Key.eval_term_of_lin (h0 _ (List.mem_map.2 ⟨e, he, rfl⟩)) hd ι

theorem eval_smul (c : ℤ) (P : Poly) (d : CertData) (ι : ℕ → Fin 5) :
    (smul c P).eval d ι = c * P.eval d ι :=
  lin_smul (fun a => (Key.unpack a).eval d ι) c P

end Poly

end OnePhaseDimension.Certificate
