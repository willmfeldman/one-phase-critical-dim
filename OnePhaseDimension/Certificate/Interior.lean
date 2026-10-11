/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.InteriorBridge
public import OnePhaseDimension.Certificate.Collect.Rounding

/-!
# The interior inequality

With `y = (|w|, |z|, |ℓ|, |X|)` and `d = (2/25, 2/25, 1/4, 1)`, the remainder
`E = Γ + ∑ d_i y_i² − 𝓘` is the collected polynomial `remainderRef` (scaled by `Q²`). Since
`Γ ≥ 0` and `|E| ≤ yᵀ D₀ y ≤ yᵀ D̄ y ≤ ∑_i ((D̄ν)_i/ν_i) y_i²` (weighted Young inequalities with
`ν = (2484, 1440, 996, 304)`), the interior expression is at least `∑_i s_i y_i²` with the
positive slacks `s = (673/18400, 438907/12000000, 2844869/24900000, 3479389/7600000)`; as
`s₂ = ε*` and `s₃ > ε*`, this gives `𝓘 ≥ ε*(z² + |ℓ|²)`. Specializing `X = 0`, `w = z = 0`,
`|ℓ| = 1` gives `f ≥ ε*`.

The ingredients: the identity of the collected remainder with `Q² (Γ + ∑ d_i y_i² − 𝓘)` on the
constrained data (`interiorPoly_eval` and the values of the squares), `Γ ≥ 0`
(`gammaPoly_eval_nonneg_of`), the bound `|𝓜(t)| ≤ L_t y_i y_j` of each remainder key
(`abs_eval_le`, with the kernel checks of the classification and of the rounding), the ten sums
of `D₀`, entrywise `D₀ ≤ D̄`, the Young step and the slacks.
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate

open Data Collect Finset

/-- The quadratic form `yᵀ M y` on `ℝ⁴`. -/
def quad4 (M : Fin 4 → Fin 4 → ℝ) (y : Fin 4 → ℝ) : ℝ := ∑ i, ∑ j, M i j * y i * y j

/-- The matrix `D₀`, from the printed integers `2·10⁵ Q² (D₀)_{ij}`. -/
def dZero (i j : Fin 4) : ℝ :=
  (![![321268243322644, 96616799870252, 294707669526536, 385792585960684],
    ![96616799870252, 269583307398596, 115717471031956, 125155603107368],
    ![294707669526536, 115717471031956, 605509501361296, 618424270356936],
    ![385792585960684, 125155603107368, 618424270356936, 1004504025266456]] i j : ℝ) /
    (2 * 10 ^ 5 * 62500000000)

/-- The matrix `D̄`. -/
def dBar (i j : Fin 4) : ℝ :=
  (![![2571, 773, 2358, 3087], ![773, 2157, 926, 1002], ![2358, 926, 4845, 4948],
    ![3087, 1002, 4948, 8037]] i j : ℝ) / 10 ^ 5

/-- The vector of magnitudes `y = (|w|, |z|, |ℓ|, |X|)` as a function on `Fin 4`. -/
def yVec (d : CertData) : Fin 4 → ℝ := fun i => yNorm (i.val + 1) d

/-! ### The collection identity and the Gram part -/

section Identity

variable {A : Ten2} {X : Ten3} {p : Ten1} {g w z : ℝ} {ℓ : Ten1}

theorem eval_wSqKey (d : CertData) (ι : ℕ → Fin 5) : wSqKey.eval d ι = d.w ^ 2 := by
  simp [wSqKey, Key.eval, Key.prefactor, Key.xBound, evalEdges]

theorem eval_xSqKey (d : CertData) (ι : ℕ → Fin 5) : xSqKey.eval d ι = sq3 d.X := by
  simp [xSqKey, Key.eval, Key.prefactor, Key.xBound, Key.xBound.bound, evalEdges,
    CertData.weight, Matrix.one_apply, pushIdx, CertData.xFactor, Function.update_apply, sq3, sq,
    Finset.prod_range_succ]

theorem ySqPoly_eval {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5) :
    ySqPoly.eval d ι = certQ ^ 2 * (2 / 25 * d.w ^ 2 + 2 / 25 * d.z ^ 2 +
      1 / 4 * ∑ a, d.ell a ^ 2 + sq3 d.X) := by
  rw [show ySqPoly = Poly.mergeAll ([(5000000000, wSqKey), (5000000000, zKey 2),
      (15625000000, ellSqKey), (62500000000, xSqKey)].map fun e => Key.term e.1 e.2) from rfl,
    Poly.eval_mergeAll_terms (Poly.lin_ind0_of_all (by decide +kernel)) hd]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, eval_wSqKey,
    eval_zKey, eval_ellSqKey, eval_xSqKey, certQ]
  push_cast
  ring

/-- **Collection identity**: on the constrained data the collected remainder is
`Q² (Γ + ∑ d_i y_i² − 𝓘)`, with `Q² Γ` the value of the collected Gram polynomial. -/
theorem remainderPoly_eval (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X) (ι : ℕ → Fin 5) :
    Poly.eval remainderPoly (certDataOf A X p g w z ℓ) ι =
      Poly.eval gammaPoly (certDataOf A X p g w z ℓ) ι +
        certQ ^ 2 * (2 / 25 * w ^ 2 + 2 / 25 * z ^ 2 + 1 / 4 * sq1 ℓ + sq3 X) -
        certQ ^ 2 * tableCoeffs.interiorExpr A X p g w z ℓ := by
  have hd := admissible_certDataOf (p := p) (g := g) (w := w) (z := z) (ℓ := ℓ) hA hA1 hX
  rw [remainderPoly, Poly.eval_mergeAll]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [Poly.eval_smul, interiorPoly_eval hA hA1 hX, ySqPoly_eval hd]
  simp only [certDataOf_w, certDataOf_z, certDataOf_ell, certDataOf_X, sq1]
  push_cast
  ring

/-- **Positivity of the Gram part** on the constrained data with `χ ≥ 0`. -/
theorem gammaPoly_eval_nonneg (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X)
    (hgp : g ^ 2 + sq1 p ≤ 1) (ι : ℕ → Fin 5) :
    0 ≤ Poly.eval gammaPoly (certDataOf A X p g w z ℓ) ι :=
  gammaPoly_eval_nonneg_of (admissible_certDataOf hA hA1 hX)
    (by simp only [certDataOf_p, certDataOf_g]; rw [sq1] at hgp; linarith) ι

end Identity

/-! ### The error bound `|E| ≤ yᵀ D₀ y` -/

/-- The product of the magnitudes of the two types in a list of types. -/
def pairY (y : ℕ → ℝ) (ts : List ℕ) : ℝ := y (ts.getD 0 0) * y (ts.getD 1 0)

/-- The weight of the sum with type index `k` in `yᵀ D₀ y` (per unit of `2·10⁵ Q² (D₀)_{ij}`). -/
def bucketY (y : ℕ → ℝ) (k : ℕ) : ℝ :=
  pairY y (yPairs.getD k []) / (10 ^ 5 * (if isDiagIdx k then 2 else 1))

/-- The linear combination `∑_k acc_k · bucketY (k₀ + k)`. -/
def linAux (y : ℕ → ℝ) : ℕ → List ℕ → ℝ
  | _, [] => 0
  | k, a :: l => a * bucketY y k + linAux y (k + 1) l

theorem length_addAt (a : ℕ) : ∀ (i : ℕ) (acc : List ℕ), (addAt a i acc).length = acc.length
  | i, [] => by cases i <;> rfl
  | 0, _ :: _ => rfl
  | i + 1, _ :: l => by simp [addAt, length_addAt a i l]

theorem linAux_addAt (y : ℕ → ℝ) (a : ℕ) : ∀ (i k : ℕ) (acc : List ℕ), i < acc.length →
    linAux y k (addAt a i acc) = linAux y k acc + a * bucketY y (k + i)
  | _, _, [], h => absurd h (Nat.not_lt_zero _)
  | 0, k, x :: l, _ => by simp only [addAt, linAux, Nat.cast_add, add_zero]; ring
  | i + 1, k, x :: l, h => by
    simp only [addAt, linAux]
    rw [linAux_addAt y a i (k + 1) l (by simpa using h), show k + 1 + i = k + (i + 1) by omega]
    ring

theorem length_d0Sums (data : List (ℕ × ℤ × ℕ)) : (d0Sums data).length = 11 := by
  induction data with
  | nil => rfl
  | cons t data ih => simp only [d0Sums, List.foldr_cons] at ih ⊢; rw [length_addAt, ih]

theorem typeIdx_lt (k : Key) : typeIdx k < 11 :=
  Nat.lt_succ_of_le (List.findIdx_le_length (xs := yPairs))

theorem linAux_d0Sums (y : ℕ → ℝ) (data : List (ℕ × ℤ × ℕ)) :
    linAux y 0 (d0Sums data) = (data.map fun t =>
      ((t.2.1.natAbs * t.2.2 * (if isDiagIdx (typeIdx (Key.unpack t.1)) then 2 else 1) : ℕ) : ℝ) *
        bucketY y (typeIdx (Key.unpack t.1))).sum := by
  induction data with
  | nil =>
    simp only [d0Sums, List.foldr_nil, List.map_nil, List.sum_nil]
    simp [linAux, List.replicate]
  | cons t data ih =>
    have h : d0Sums (t :: data) = addAt (t.2.1.natAbs * t.2.2 *
        (if isDiagIdx (typeIdx (Key.unpack t.1)) then 2 else 1)) (typeIdx (Key.unpack t.1))
        (d0Sums data) := rfl
    rw [h, linAux_addAt _ _ _ _ _ (by rw [length_d0Sums]; exact typeIdx_lt _), ih,
      List.map_cons, List.sum_cons, zero_add, add_comm]

/-- The term of one key in the bound. -/
theorem term_bucket (y : ℕ → ℝ) (e : ℤ) (n i : ℕ) :
    ((e.natAbs * n * (if isDiagIdx i then 2 else 1) : ℕ) : ℝ) * bucketY y i =
      |(e : ℝ)| * (n / 10 ^ 5) * pairY y (yPairs.getD i []) := by
  have hc : ((e.natAbs : ℕ) : ℝ) = |(e : ℝ)| := by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  simp only [bucketY]
  split_ifs <;> push_cast [hc] <;> field_simp

/-- The bound `∑_t |Q² e_t| (n_t/10⁵) y_{i_t} y_{j_t}` equals `Q² yᵀ D₀ y`. -/
theorem boundSum_eq (d : CertData) :
    (remainderData.map fun t => |(t.2.1 : ℝ)| * (t.2.2 / 10 ^ 5) *
      pairY (fun i => yNorm i d) (Key.unpack t.1).types).sum =
      certQ ^ 2 * quad4 dZero (yVec d) := by
  have hT := yTypes_remainderData
  simp only [List.all_eq_true, beq_iff_eq] at hT
  have h1 : (remainderData.map fun t => |(t.2.1 : ℝ)| * (t.2.2 / 10 ^ 5) *
      pairY (fun i => yNorm i d) (Key.unpack t.1).types) = (remainderData.map fun t =>
      ((t.2.1.natAbs * t.2.2 * (if isDiagIdx (typeIdx (Key.unpack t.1)) then 2 else 1) : ℕ) : ℝ) *
        bucketY (fun i => yNorm i d) (typeIdx (Key.unpack t.1))) :=
    List.map_congr_left fun t ht => by rw [term_bucket, hT t ht]
  rw [h1, ← linAux_d0Sums, d0Sums_remainderData]
  simp only [d0Printed, List.cons_append, List.nil_append, linAux, bucketY, pairY, yPairs,
    isDiagIdx, quad4, dZero, yVec, Fin.sum_univ_four, List.getD_cons_zero, List.getD_cons_succ,
    List.getD_nil]
  norm_num [certQ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  ring

/-- The absolute value of a sum is at most the sum of termwise bounds. -/
theorem abs_list_sum_le {κ : Type*} (l : List κ) (f g : κ → ℝ) (h : ∀ t ∈ l, |f t| ≤ g t) :
    |(l.map f).sum| ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (abs_add_le _ _).trans (add_le_add (h a (by simp))
      (ih fun t ht => h t (by simp [ht])))

theorem lsq_le_of_mem {t : ℕ × ℤ × ℕ} (ht : t ∈ remainderData) :
    (classify (Key.unpack t.1)).isSome = true ∧
      (Lsq (Key.unpack t.1) : ℝ) ≤ ((t.2.2 : ℝ) / 10 ^ 5) ^ 2 := by
  have hR := roundingOK_remainderData
  simp only [roundingOK, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hR
  obtain ⟨h1, h2⟩ := hR t ht
  refine ⟨h1, ?_⟩
  have : ((10 ^ 10 * Lsq (Key.unpack t.1) : ℚ) : ℝ) ≤ (((t.2.2 : ℚ) ^ 2 : ℚ) : ℝ) := by
    exact_mod_cast h2
  push_cast at this
  rw [div_pow]
  rw [le_div_iff₀ (by positivity)]
  nlinarith

/-- **Error bound** `|Q² E| ≤ Q² yᵀ D₀ y`, from the graph bound of each key, the rounding
`n_t² ≥ 10¹⁰ L_t²` and the sums of `D₀`. -/
theorem remainderRef_eval_abs_le {A : Ten2} {X : Ten3} {p : Ten1} {g w z : ℝ} {ℓ : Ten1}
    (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X) (hgp : g ^ 2 + sq1 p ≤ 1)
    (ι : ℕ → Fin 5) :
    |Poly.eval remainderRef (certDataOf A X p g w z ℓ) ι| ≤
      certQ ^ 2 * quad4 dZero (yVec (certDataOf A X p g w z ℓ)) := by
  rw [← boundSum_eq]
  have hd := admissible_certDataOf (p := p) (g := g) (w := w) (z := z) (ℓ := ℓ) hA hA1 hX
  simp only [Poly.eval, remainderRef, List.map_map]
  refine abs_list_sum_le _ _ _ fun t ht => ?_
  simp only [Function.comp_apply, abs_mul]
  obtain ⟨hc, hL⟩ := lsq_le_of_mem ht
  have hb := abs_eval_le hc hd hgp ι (by positivity) hL
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left (hb.trans_eq ?_) (abs_nonneg _)
  simp only [pairY, Key.typeI, Key.typeJ, mul_assoc]

/-! ### The quadratic-form arithmetic -/

theorem quad4_eq (M : Fin 4 → Fin 4 → ℝ) (y : Fin 4 → ℝ) :
    quad4 M y = ∑ i, ∑ j, M i j * (y i * y j) := by
  simp only [quad4, mul_assoc]

/-- `D₀ ≤ D̄` entrywise. -/
theorem dZero_le_dBar (i j : Fin 4) : dZero i j ≤ dBar i j := by
  fin_cases i <;> fin_cases j <;> norm_num [dZero, dBar]

/-- Monotonicity of the quadratic form in the matrix for `y ≥ 0`. -/
theorem quad4_dZero_le (y : Fin 4 → ℝ) (hy : ∀ i, 0 ≤ y i) :
    quad4 dZero y ≤ quad4 dBar y := by
  rw [quad4_eq, quad4_eq]
  exact sum_le_sum fun i _ => sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (dZero_le_dBar i j) (mul_nonneg (hy i) (hy j))

/-- The weighted Young step with `ν = (2484, 1440, 996, 304)`: `yᵀ D̄ y ≤ ∑ (D̄ν)_i/ν_i y_i²`. -/
theorem quad4_dBar_le (y : Fin 4 → ℝ) :
    quad4 dBar y ≤
      (2571 * 2484 + 773 * 1440 + 2358 * 996 + 3087 * 304) / (10 ^ 5 * 2484) * y 0 ^ 2 +
      (773 * 2484 + 2157 * 1440 + 926 * 996 + 1002 * 304) / (10 ^ 5 * 1440) * y 1 ^ 2 +
      (2358 * 2484 + 926 * 1440 + 4845 * 996 + 4948 * 304) / (10 ^ 5 * 996) * y 2 ^ 2 +
      (3087 * 2484 + 1002 * 1440 + 4948 * 996 + 8037 * 304) / (10 ^ 5 * 304) * y 3 ^ 2 := by
  simp only [quad4, dBar, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  nlinarith [sq_nonneg (1440 * y 0 - 2484 * y 1), sq_nonneg (996 * y 0 - 2484 * y 2),
    sq_nonneg (304 * y 0 - 2484 * y 3), sq_nonneg (996 * y 1 - 1440 * y 2),
    sq_nonneg (304 * y 1 - 1440 * y 3), sq_nonneg (304 * y 2 - 996 * y 3)]

/-! ### Conclusions -/

theorem sq_yVec (d : CertData) :
    yVec d 0 ^ 2 = d.w ^ 2 ∧ yVec d 1 ^ 2 = d.z ^ 2 ∧ yVec d 2 ^ 2 = sq1 d.ell ∧
      yVec d 3 ^ 2 = sq3 d.X := by
  refine ⟨Real.sq_sqrt (ysq_nonneg 1 d), Real.sq_sqrt (ysq_nonneg 2 d),
    Real.sq_sqrt (ysq_nonneg 3 d), Real.sq_sqrt (ysq_nonneg 4 d)⟩

theorem yVec_nonneg (d : CertData) (i : Fin 4) : 0 ≤ yVec d i := Real.sqrt_nonneg _

/-- **The interior inequality** `𝓘 ≥ ε*(z² + |ℓ|²)` for the coefficients of the first table. -/
theorem interior_inequality {A : Ten2} {X : Ten3} {p : Ten1} {g w z : ℝ} {ℓ : Ten1}
    (hA : IsSTF2 A) (hA1 : sq2 A = 1) (hX : IsSTF3 X) (hgp : g ^ 2 + sq1 p ≤ 1) :
    εStar * (z ^ 2 + sq1 ℓ) ≤ tableCoeffs.interiorExpr A X p g w z ℓ := by
  set ι : ℕ → Fin 5 := fun _ => 0
  have hE := remainderPoly_eval (p := p) (g := g) (w := w) (z := z) (ℓ := ℓ) hA hA1 hX ι
  rw [collect_E] at hE
  have hΓ := gammaPoly_eval_nonneg (w := w) (z := z) (ℓ := ℓ) hA hA1 hX hgp ι
  have hB := remainderRef_eval_abs_le (w := w) (z := z) (ℓ := ℓ) hA hA1 hX hgp ι
  have hD := quad4_dZero_le _ (yVec_nonneg (certDataOf A X p g w z ℓ))
  have hY := quad4_dBar_le (yVec (certDataOf A X p g w z ℓ))
  obtain ⟨h0, h1, h2, h3⟩ := sq_yVec (certDataOf A X p g w z ℓ)
  rw [h0, h1, h2, h3] at hY
  simp only [certDataOf_w, certDataOf_z, certDataOf_ell, certDataOf_X] at hY
  have hX0 : 0 ≤ sq3 X := sq3_nonneg X
  have hl0 : 0 ≤ sq1 ℓ := sum_nonneg fun i _ => sq_nonneg _
  have hQ : (0 : ℝ) < certQ ^ 2 := by norm_num [certQ]
  have key : certQ ^ 2 * (εStar * (z ^ 2 + sq1 ℓ)) ≤
      certQ ^ 2 * tableCoeffs.interiorExpr A X p g w z ℓ := by
    have : εStar * (z ^ 2 + sq1 ℓ) ≤ 2 / 25 * w ^ 2 + 2 / 25 * z ^ 2 + 1 / 4 * sq1 ℓ + sq3 X -
        quad4 dZero (yVec (certDataOf A X p g w z ℓ)) := by
      norm_num [εStar] at hY ⊢
      linarith [sq_nonneg w]
    have h1 := mul_le_mul_of_nonneg_left this hQ.le
    have h2 := le_abs_self (Poly.eval remainderRef (certDataOf A X p g w z ℓ) ι)
    nlinarith
  exact le_of_mul_le_mul_left key hQ

/-- With `X = 0`, `w = z = 0`, the interior expression reduces to `f |ℓ|²`. -/
theorem interiorExpr_zero (c : Coeffs) (A : Ten2) (p : Ten1) (g : ℝ) (ℓ : Ten1) :
    c.interiorExpr A 0 p g 0 0 ℓ = c.f (A, p, g) * sq1 ℓ := by
  have hgen : ∀ l, gen A 0 p g 0 0 l = 0 := fun l => by
    simp only [gen, qVec, Pi.zero_apply, zero_mul, sum_const_zero, mul_zero, sub_zero]
    rfl
  simp only [Coeffs.interiorExpr, Coeffs.termZ, Coeffs.termG, Coeffs.termM, Coeffs.termP,
    Coeffs.termF, Dl, hgen, map_zero, qVec, Pi.zero_apply, zero_mul, sum_const_zero, mul_zero,
    zero_add, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero]

/-- **`f ≥ ε*`** on `g² + |p|² ≤ 1`, for the coefficients of the first table. -/
theorem certF_ge_eps {A : Ten2} {p : Ten1} {g : ℝ} (hA : IsSTF2 A) (hA1 : sq2 A = 1)
    (hgp : g ^ 2 + sq1 p ≤ 1) : εStar ≤ tableCoeffs.f (A, p, g) := by
  set ℓ : Ten1 := fun i => if i = 0 then 1 else 0
  have hℓ : sq1 ℓ = 1 := by simp [sq1, ℓ]
  have hX : IsSTF3 0 := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ => by simp⟩
  have h := interior_inequality (X := 0) (w := 0) (z := 0) (ℓ := ℓ) hA hA1 hX hgp
  rw [interiorExpr_zero, hℓ] at h
  simpa using h

end OnePhaseDimension.Certificate
