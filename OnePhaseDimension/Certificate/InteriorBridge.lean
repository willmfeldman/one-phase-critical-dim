/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.InteriorSplit
public import OnePhaseDimension.Certificate.Collect.InteriorRows
public import OnePhaseDimension.Certificate.Collect.InteriorTotal
public import OnePhaseDimension.Certificate.Data.TableChecks
public import OnePhaseDimension.Certificate.Collect.GammaNonneg
public import OnePhaseDimension.Certificate.Bounds.TensorBounds

/-!
# The collected interior polynomial is `Q² 𝓘`

On the constrained data, the collected interior polynomial `interiorPoly` (the merge of the
contributions of the five families of the first table) evaluates to `Q²` times the interior
expression `𝓘` of the coefficient maps of the first table.

The proof goes row by row: the terms of a row evaluate to `Q² (c/Q)` times its contribution,
written with the directional derivative of the polynomial map of its key
(`OnePhaseDimension.Certificate.Collect.InteriorRows`); the interior expression splits into
five parts, one per family, each affine-linear in its family
(`OnePhaseDimension.Certificate.InteriorSplit`). No term of the collected polynomial overflowed
the packing, since the reference results contain no key `0`.
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate

open Data Collect Finset

/-- The denominator `Q = 250000`. -/
def certQ : ℝ := 250000

/-- The coefficient maps defined by the first table, with denominator `Q`. -/
def tableCoeffs : Coeffs :=
  rowsCoeffs (famEntries .f) (famEntries .U) (famEntries .K) (famEntries .M) (famEntries .P) certQ

/-- The certificate data as a record of the graph semantics. -/
def certDataOf (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) (ℓ : Ten1) : CertData :=
  ⟨Matrix.of A, p, ℓ, X, g, w, z⟩

variable {A : Ten2} {X : Ten3} {p : Ten1} {g w z : ℝ} {ℓ : Ten1}

@[simp] theorem certDataOf_z : (certDataOf A X p g w z ℓ).z = z := rfl
@[simp] theorem certDataOf_w : (certDataOf A X p g w z ℓ).w = w := rfl
@[simp] theorem certDataOf_ell : (certDataOf A X p g w z ℓ).ell = ℓ := rfl
@[simp] theorem certDataOf_X : (certDataOf A X p g w z ℓ).X = X := rfl
@[simp] theorem certDataOf_p : (certDataOf A X p g w z ℓ).p = p := rfl
@[simp] theorem certDataOf_g : (certDataOf A X p g w z ℓ).g = g := rfl
@[simp] theorem qVec_certDataOf (l : Fin 5) :
    qVec X (certDataOf A X p g w z ℓ).A l = qVec X A l := rfl
@[simp] theorem certDataOf_A_apply (i j : Fin 5) : (certDataOf A X p g w z ℓ).A i j = A i j :=
  rfl

/-- The constrained data are admissible. -/
theorem admissible_certDataOf (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X) :
    (certDataOf A X p g w z ℓ).Admissible where
  isSymm := Matrix.IsSymm.ext fun i j => (hA.1 i j).symm
  trace_eq_zero := hA.2
  trace_sq_eq_one := by
    rw [← hA1]
    simp only [certDataOf, Matrix.trace, Matrix.diag, sq, Matrix.mul_apply, Matrix.of_apply, sq2]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hA.1 j i]
  X_swap₁₂ := hX.1
  X_swap₂₃ := hX.2.1
  X_trace := hX.2.2

/-! ### Checks on the rows -/

/-- The derivative terms of a key are linear with one more slot (Boolean check). -/
def derivB (k : Key) : Bool := k.derivTerms.all fun u => u.2.linearB && u.2.rank == k.rank + 1

/-- The checks on a row of the first table used for the value of its terms. -/
def rowCheck (r : TableIRow) : Bool :=
  r.key.plainB && r.key.linearB && r.key.rank == r.fam.rank && !r.key.hasX &&
    match r.fam with
    | .U => !(deltaKey.mul r.key).hasX && derivB (deltaKey.mul r.key)
    | .K => derivB r.key && derivB (r.key.permSlots [1, 0]) &&
        !(r.key.permSlots [1, 0]).hasX && (r.key.permSlots [1, 0]).linearB
    | _ => derivB r.key

theorem rowCheck_tableI : tableI.all rowCheck = true := by decide +kernel

theorem rowCheck_of_mem {F : Fam} {r : TableIRow} (hr : r ∈ famRows F) : rowCheck r = true := by
  have h := rowCheck_tableI
  rw [List.all_eq_true] at h
  exact h r (List.mem_of_mem_filter hr)

theorem fam_of_mem {F : Fam} {r : TableIRow} (hr : r ∈ famRows F) : r.fam = F := by
  have := (List.mem_filter.1 hr).2
  simpa using this

/-! ### Values of the parts on one row -/

section Rows

variable (A X p g w z ℓ)

/-- The data `certDataOf A X p g w z ℓ`. -/
local notation "dD" => certDataOf A X p g w z ℓ

theorem DlD_certDataOf (F : Ten2 × Ten1 × ℝ → ℝ) (l : Fin 5) :
    DlD (certDataOf A X p g w z ℓ) F l = Dl F A X p g w z l := rfl

theorem evalFun_certDataOf (k : Key) (ι : ℕ → Fin 5) :
    k.evalFun (certDataOf A X p g w z ℓ) ι (A, p, g) = k.eval (certDataOf A X p g w z ℓ) ι :=
  rfl

variable {A X p g w z ℓ}

theorem comm4 (H : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ l, ∑ i, ∑ j, ∑ k, H l i j k = ∑ i, ∑ j, ∑ k, ∑ l, H l i j k := by
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]

theorem sum4_split (F G : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ) (κ : ℝ) :
    ∑ l, ∑ i, ∑ j, ∑ k, (F l i j k + κ * G l i j k) * X i j k =
      ∑ i, ∑ j, ∑ k, (∑ l, F l i j k) * X i j k +
        κ * ∑ i, ∑ j, ∑ k, (∑ l, G l i j k) * X i j k := by
  rw [comm4]
  simp only [add_mul, sum_add_distrib, sum_mul, mul_sum]
  congr 1
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_congr rfl fun k _ =>
    sum_congr rfl fun l _ => by ring

theorem rowVal_eq_f {r : TableIRow} (hF : r.fam = .f) (hc : rowCheck r = true)
    (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X) (ι : ℕ → Fin 5) :
    rowVal (certDataOf A X p g w z ℓ) ι r = certQ ^ 2 * ((r.coef / certQ : ℝ) *
      iPartF A X p g w z ℓ (r.key.evalFun CertData.base fun _ => 0)) := by
  simp only [rowCheck, hF, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨hp, hl⟩, hr⟩, hx⟩, hD⟩ := hc
  have hr : r.key.rank = 0 := hr
  have hm := Key.linear_of_linearB hl
  have hpl : r.key.Plain := Key.plain_of_plainB hp
  rw [rowVal_f hF hm hr hx (derivLinear_of_check hD) (admissible_certDataOf hA hA1 hX)]
  rw [hpl.evalFun_eq CertData.base (certDataOf A X p g w z ℓ), iPartF, evalFun_certDataOf]
  have hfun : ∀ l : Fin 5, r.key.evalFun (certDataOf A X p g w z ℓ) (fun _ => 0) =
      r.key.evalFun (certDataOf A X p g w z ℓ) fun _ => l := fun l =>
    Key.evalFun_congr hm.slotsBelowRank _ fun i hi => by rw [hr] at hi; omega
  have hs : ∑ l, (Dl (r.key.evalFun (certDataOf A X p g w z ℓ) fun _ => 0) A X p g w z l +
      2 * aExp * qVec X A l * r.key.eval (certDataOf A X p g w z ℓ) (fun _ => 0)) * ℓ l =
      ∑ k, ℓ k * DlD (certDataOf A X p g w z ℓ)
        (r.key.evalFun (certDataOf A X p g w z ℓ) fun _ => k) k +
      2 * aExp * r.key.eval (certDataOf A X p g w z ℓ) (fun _ => 0) * ∑ k, qVec X A k * ℓ k := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [hfun l, DlD_certDataOf]
    ring
  rw [hs]
  simp only [certQ, aExp, sq1, certDataOf_z, certDataOf_ell, certDataOf_X, qVec_certDataOf]
  ring

theorem sum4_lin (F : Fin 5 → Fin 5 → Fin 5 → Fin 5 → ℝ) :
    ∑ l, ∑ i, ∑ j, ∑ k, F l i j k * X i j k = ∑ i, ∑ j, ∑ k, (∑ l, F l i j k) * X i j k := by
  rw [comm4]
  simp only [sum_mul]

theorem rowVal_eq_U {r : TableIRow} (hF : r.fam = .U) (hc : rowCheck r = true)
    (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X) (ι : ℕ → Fin 5) :
    rowVal (certDataOf A X p g w z ℓ) ι r = certQ ^ 2 * ((r.coef / certQ : ℝ) *
      iPartU A X p g w z (fun y j k => r.key.evalFun CertData.base (idx2 j k) y)) := by
  simp only [rowCheck, hF, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨hp, hl⟩, hr⟩, hx⟩, hxG, hD⟩ := hc
  have hr : r.key.rank = 2 := hr
  have hm := Key.linear_of_linearB hl
  have hpl : r.key.Plain := Key.plain_of_plainB hp
  rw [rowVal_U hF hm hr hxG (derivLinear_of_check hD) (admissible_certDataOf hA hA1 hX)]
  simp only [iPartU, hpl.evalFun_eq CertData.base dD, evalFun_certDataOf]
  have h2 : ∑ l, ∑ i, ∑ j, ∑ k, (Dl (fun y => kron l i * r.key.evalFun dD (idx2 j k) y)
      A X p g w z l + (2 * aExp - 1) * qVec X A l * (kron l i * r.key.eval dD (idx2 j k))) *
        X i j k =
      ∑ i, ∑ j, ∑ k, (∑ l, DlD dD (fun y => kron l i * r.key.evalFun dD (idx2 j k) y) l) *
        (dD).X i j k + (2 * aExp - 1) * ∑ i, ∑ j, ∑ k,
          (∑ l, qVec (dD).X (dD).A l * (kron l i * r.key.eval dD (idx2 j k))) * (dD).X i j k := by
    rw [← sum4_split]
    refine sum_congr rfl fun l _ => sum_congr rfl fun i _ => sum_congr rfl fun j _ =>
      sum_congr rfl fun k _ => ?_
    simp only [DlD_certDataOf, certDataOf_X, qVec_certDataOf]
    ring
  rw [h2]
  simp only [certQ, aExp, certDataOf_z, certDataOf_A_apply]
  ring

theorem Dl_sub' {F G : Ten2 × Ten1 × ℝ → ℝ} (hF : DifferentiableAt ℝ F (A, p, g))
    (hG : DifferentiableAt ℝ G (A, p, g)) (l : Fin 5) :
    Dl (fun y => F y - G y) A X p g w z l = Dl F A X p g w z l - Dl G A X p g w z l := by
  have e : (fun y => F y - G y) = fun y => (-1) * G y + F y := by funext y; ring
  rw [e, Dl_smul_add (-1) hG hF]
  ring

theorem rowVal_eq_K {r : TableIRow} (hF : r.fam = .K) (hc : rowCheck r = true)
    (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X) (ι : ℕ → Fin 5) :
    rowVal (certDataOf A X p g w z ℓ) ι r = certQ ^ 2 * ((r.coef / certQ : ℝ) *
      iPartK A X p g w z (fun y l i j k => r.key.evalFun CertData.base (idx4 l i j k) y)) := by
  simp only [rowCheck, hF, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨⟨hp, hl⟩, hr⟩, hx⟩, ⟨⟨hD, hD'⟩, hx'⟩, hl'⟩ := hc
  have hr : r.key.rank = 4 := hr
  have hm := Key.linear_of_linearB hl
  have hpl : r.key.Plain := Key.plain_of_plainB hp
  rw [rowVal_K hF hm hr hx hx' (Key.linear_of_linearB hl') (derivLinear_of_check hD)
    (derivLinear_of_check hD') (admissible_certDataOf hA hA1 hX)]
  simp only [iPartK, hpl.evalFun_eq CertData.base dD, evalFun_certDataOf]
  have hdiff : ∀ ι' : ℕ → Fin 5, DifferentiableAt ℝ (r.key.evalFun dD ι') (A, p, g) := fun ι' =>
    (Key.contDiff_evalFun (n := 1) hx dD ι').differentiable one_ne_zero _
  have h2 : ∑ l, ∑ i, ∑ j, ∑ k, (Dl (fun y => r.key.evalFun dD (idx4 l i j k) y -
      r.key.evalFun dD (idx4 i l j k) y) A X p g w z l + (2 * aExp - 1) * qVec X A l *
        (r.key.eval dD (idx4 l i j k) - r.key.eval dD (idx4 i l j k))) * X i j k =
      (∑ i, ∑ j, ∑ k, (∑ l, DlD dD (r.key.evalFun dD (idx4 l i j k)) l) * (dD).X i j k -
        ∑ i, ∑ j, ∑ k, (∑ l, DlD dD (r.key.evalFun dD (idx4 i l j k)) l) * (dD).X i j k) +
      (2 * aExp - 1) * (∑ i, ∑ j, ∑ k,
        (∑ l, qVec (dD).X (dD).A l * r.key.eval dD (idx4 l i j k)) * (dD).X i j k -
        ∑ i, ∑ j, ∑ k, (∑ l, qVec (dD).X (dD).A l * r.key.eval dD (idx4 i l j k)) *
          (dD).X i j k) := by
    simp only [← sum4_lin, ← sum_sub_distrib, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => sum_congr rfl fun i _ => sum_congr rfl fun j _ =>
      sum_congr rfl fun k _ => ?_
    rw [Dl_sub' (hdiff _) (hdiff _)]
    simp only [DlD_certDataOf, certDataOf_X, qVec_certDataOf]
    ring
  rw [h2]
  simp only [certQ, aExp, certDataOf_z, certDataOf_A_apply]
  ring

theorem rowVal_eq_V {r : TableIRow} {κ s : ℝ} (hc : rowCheck r = true)
    (hF : r.fam = .M ∧ κ = 2 * aExp + 1 ∧ s = w ∨ r.fam = .P ∧ κ = 2 * aExp ∧ s = z)
    (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X) (ι : ℕ → Fin 5) :
    rowVal (certDataOf A X p g w z ℓ) ι r = certQ ^ 2 * ((r.coef / certQ : ℝ) *
      iPartV A X p g w z κ s (fun y l => r.key.evalFun CertData.base (fun _ => l) y)) := by
  have hfam : r.fam = .M ∨ r.fam = .P := by rcases hF with h | h; exacts [Or.inl h.1, Or.inr h.1]
  have hc' := hc
  simp only [rowCheck, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc'
  obtain ⟨⟨⟨⟨hp, hl⟩, hr⟩, hx⟩, hD₀⟩ := hc'
  have hr : r.key.rank = 1 := by rcases hfam with h | h <;> rw [hr, h] <;> rfl
  have hD : derivB r.key = true := by
    rcases hfam with h | h <;> rw [h] at hD₀ <;> exact hD₀
  have hm := Key.linear_of_linearB hl
  have hpl : r.key.Plain := Key.plain_of_plainB hp
  have hs : ∑ l, (Dl (fun y => r.key.evalFun dD (fun _ => l) y) A X p g w z l +
      κ * qVec X A l * r.key.eval dD (fun _ => l)) =
      ∑ l, DlD dD (r.key.evalFun dD fun _ => l) l +
        κ * ∑ l, qVec (dD).X (dD).A l * r.key.eval dD (fun _ => l) := by
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun l _ => ?_
    simp only [DlD_certDataOf, certDataOf_X, qVec_certDataOf]
    ring
  rcases hF with ⟨hF, hκ, hs'⟩ | ⟨hF, hκ, hs'⟩
  · rw [hs']
    rw [rowVal_M hF hm hr hx (derivLinear_of_check hD) (admissible_certDataOf hA hA1 hX)]
    simp only [iPartV, hpl.evalFun_eq CertData.base dD, evalFun_certDataOf]
    rw [hs, hκ]
    simp only [certQ, aExp, certDataOf_w]
    ring
  · rw [hs']
    rw [rowVal_P hF hm hr hx (derivLinear_of_check hD) (admissible_certDataOf hA hA1 hX)]
    simp only [iPartV, hpl.evalFun_eq CertData.base dD, evalFun_certDataOf]
    rw [hs, hκ]
    simp only [certQ, aExp, certDataOf_z]
    ring

end Rows

/-! ### The collected interior polynomial -/

theorem eval_rowsPoly {rows : List TableIRow} (h : (rowsPoly rows).lin Poly.ind0 = 0)
    {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5) :
    (rowsPoly rows).eval d ι = (rows.map fun r => rowVal d ι r).sum := by
  have h0 := Poly.lin_ind0_eq_zero_of_mergeAll (fun P hP => by
    obtain ⟨r, -, hP⟩ := List.mem_flatMap.1 hP
    obtain ⟨e, -, rfl⟩ := List.mem_map.1 hP
    exact Key.lin_ind0_term_nonneg _ _) h
  rw [rowsPoly, Poly.eval_mergeAll, sum_flatMap_map]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  rw [rowVal, rowPolys, List.map_map]
  congr 1
  refine List.map_congr_left fun e he => ?_
  exact Key.eval_term_of_lin (h0 _ (List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨e, he, rfl⟩⟩)) hd ι

theorem lin_rowsPoly_famRows (F : Fam) : (rowsPoly (famRows F)).lin Poly.ind0 = 0 := by
  cases F
  · rw [rowsPoly_famRows_f]; exact Poly.lin_ind0_of_all (by decide +kernel)
  · rw [rowsPoly_famRows_U]; exact Poly.lin_ind0_of_all (by decide +kernel)
  · rw [rowsPoly_famRows_K]; exact Poly.lin_ind0_of_all (by decide +kernel)
  · rw [rowsPoly_famRows_M]; exact Poly.lin_ind0_of_all (by decide +kernel)
  · rw [rowsPoly_famRows_P]; exact Poly.lin_ind0_of_all (by decide +kernel)

theorem famEntries_eq (F : Fam) : famEntries F = (famRows F).map fun r => (r.coef, r.key) := rfl

/-- **The collected interior polynomial is `Q² 𝓘`** on the constrained data. -/
theorem interiorPoly_eval (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X) (ι : ℕ → Fin 5) :
    interiorPoly.eval (certDataOf A X p g w z ℓ) ι =
      certQ ^ 2 * tableCoeffs.interiorExpr A X p g w z ℓ := by
  have hd := admissible_certDataOf (p := p) (g := g) (w := w) (z := z) (ℓ := ℓ) hA hA1 hX
  have hev : ∀ F, (rowsPoly (famRows F)).eval (certDataOf A X p g w z ℓ) ι =
      ((famRows F).map fun r => rowVal (certDataOf A X p g w z ℓ) ι r).sum := fun F =>
    eval_rowsPoly (lin_rowsPoly_famRows F) hd ι
  have hxf : ∀ F, RowsXFree (famEntries F) := fun F => by
    cases F
    exacts [rowsOfRank_famEntries_f.plain.xFree, rowsOfRank_famEntries_U.plain.xFree,
      rowsOfRank_famEntries_K.plain.xFree, rowsOfRank_famEntries_M.plain.xFree,
      rowsOfRank_famEntries_P.plain.xFree]
  rw [interiorExpr_split tableCoeffs
    (fun j k => (contDiff_polyMap (n := 1) (hxf .U) certQ _).differentiable one_ne_zero _)
    (fun l i j k => (contDiff_polyMap (n := 1) (hxf .K) certQ _).differentiable one_ne_zero _)]
  rw [show tableCoeffs.f = polyMap (famEntries .f) certQ (fun _ => 0) from rfl,
    show tableCoeffs.U = famTen2 (famEntries .U) certQ from rfl,
    show tableCoeffs.K = famTen4 (famEntries .K) certQ from rfl,
    show tableCoeffs.M = famVec (famEntries .M) certQ from rfl,
    show tableCoeffs.P = famVec (famEntries .P) certQ from rfl,
    iPartF_polyMap _ _ _ _ _ _ _ _ _ _ (hxf .f), iPartU_famTen2 _ _ _ _ _ _ _ _ (hxf .U),
    iPartK_famTen4 _ _ _ _ _ _ _ _ (hxf .K), iPartV_famVec _ _ _ _ _ _ _ _ _ _ (hxf .M),
    iPartV_famVec _ _ _ _ _ _ _ _ _ _ (hxf .P)]
  simp only [famEntries_eq, List.map_map, Function.comp_def, mul_add, ← List.sum_map_mul_left]
  rw [interiorPoly, Poly.eval_mergeAll]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hev]
  have e1 := List.map_congr_left fun r (hr : r ∈ famRows .f) =>
    rowVal_eq_f (p := p) (g := g) (w := w) (z := z) (ℓ := ℓ) (fam_of_mem hr) (rowCheck_of_mem hr)
      hA hA1 hX ι
  have e2 := List.map_congr_left fun r (hr : r ∈ famRows .U) =>
    rowVal_eq_U (p := p) (g := g) (w := w) (z := z) (ℓ := ℓ) (fam_of_mem hr) (rowCheck_of_mem hr)
      hA hA1 hX ι
  have e3 := List.map_congr_left fun r (hr : r ∈ famRows .K) =>
    rowVal_eq_K (p := p) (g := g) (w := w) (z := z) (ℓ := ℓ) (fam_of_mem hr) (rowCheck_of_mem hr)
      hA hA1 hX ι
  have e4 := List.map_congr_left fun r (hr : r ∈ famRows .M) =>
    rowVal_eq_V (p := p) (g := g) (w := w) (z := z) (ℓ := ℓ) (κ := 2 * aExp + 1) (s := w)
      (rowCheck_of_mem hr) (Or.inl ⟨fam_of_mem hr, rfl, rfl⟩) hA hA1 hX ι
  have e5 := List.map_congr_left fun r (hr : r ∈ famRows .P) =>
    rowVal_eq_V (p := p) (g := g) (w := w) (z := z) (ℓ := ℓ) (κ := 2 * aExp) (s := z)
      (rowCheck_of_mem hr) (Or.inr ⟨fam_of_mem hr, rfl, rfl⟩) hA hA1 hX ι
  rw [e1, e2, e3, e4, e5]
  ring

end OnePhaseDimension.Certificate
