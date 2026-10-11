/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Boundary.Poly4
public import OnePhaseDimension.Certificate.Interior

/-!
# Graph keys at diagonal boundary data

At the boundary data `p = e₅`, `g = 0`, `A = diag(x₁, x₂, x₃, x₄, λ)` with `λ = -∑ xᵢ`, every
key without copies of `X` evaluates to a polynomial in `x ∈ ℝ⁴`:

* an edge `A^k` between two endpoints carrying the coordinate indices `a, b` (the index `5` for a
  copy of `p`, the assigned index for a free slot) contributes `δ_{ab} d_a^k`, where
  `d = (x₁, x₂, x₃, x₄, λ)`;
* a trace `tr A^k` contributes `∑ᵢ xᵢ^k + λ^k`;
* a positive power of `g`, `w` or `z` makes the key vanish (these scalars are zero here).

`keyPoly` computes this polynomial and `eval_keyPoly` proves it sound. No trace reduction is used:
the polynomial is the exact value for every `x`, not only on `R(x) = 1`.

Indices are `0, …, 4` in Lean; the distinguished index (written `5` in the source) is `4`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate.Boundary

open Finset Poly4

/-! ### The diagonal data -/

/-- The diagonal `d = (x₁, x₂, x₃, x₄, -∑ xᵢ)`. -/
def dvec (x : Fin 4 → ℝ) (a : Fin 5) : ℝ :=
  if h : a.val < 4 then x ⟨a.val, h⟩ else -∑ i, x i

/-- The matrix `diag(x₁, x₂, x₃, x₄, -∑ xᵢ)`. -/
def diagA (x : Fin 4 → ℝ) : Ten2 := fun i j => if i = j then dvec x i else 0

/-- The unit vector `e₅` (index `4`). -/
def e5 : Ten1 := fun i => if i = 4 then 1 else 0

/-- The boundary data at the diagonal point: `A = diag(x, λ)`, `p = e₅`, and all other data
zero. -/
def diagData (x : Fin 4 → ℝ) : CertData := CertData.base.withAPG (diagA x, e5, 0)

/-! ### The polynomials of the entries -/

/-- `λ = -(x₁ + x₂ + x₃ + x₄)`. -/
def lamPoly : Poly4 := smul (-1) (Poly4.sum ((List.finRange 4).map var))

/-- The polynomial of the diagonal entry `d_a`. -/
def dPoly (a : Fin 5) : Poly4 := if h : a.val < 4 then var ⟨a.val, h⟩ else lamPoly

/-- The coordinate index carried by an endpoint without `X` (none for `ℓ`, whose weight is
zero here). -/
def endIdx (ι : ℕ → Fin 5) : Endpoint → Option (Fin 5)
  | .p => some 4
  | .slot i => some (ι i)
  | _ => none

/-- The polynomial of an edge. -/
def edgePoly (ι : ℕ → Fin 5) (e : Edge) : Poly4 :=
  match endIdx ι e.u, endIdx ι e.v with
  | some a, some b => if a = b then Poly4.pow (dPoly a) e.pow else []
  | _, _ => []

/-- The polynomial of a trace `tr A^k`. -/
def tracePoly (k : ℕ) : Poly4 := Poly4.sum ((List.finRange 5).map fun a => Poly4.pow (dPoly a) k)

/-- The polynomial of a key at the diagonal data, with slot assignment `ι`. -/
def keyPoly (ι : ℕ → Fin 5) (k : Key) : Poly4 :=
  if k.gPow = 0 ∧ k.wPow = 0 ∧ k.zPow = 0 then
    k.edges.foldr (fun e acc => mul (edgePoly ι e) acc)
      (k.traces.foldr (fun t acc => mul (tracePoly t) acc) (const 1))
  else []

/-- The polynomial `∑ c · key` of a list of rows (`Q` times the coefficient map). -/
def rowsPoly (rows : List (ℤ × Key)) (ι : ℕ → Fin 5) : Poly4 :=
  Poly4.sum (rows.map fun t => smul t.1 (keyPoly ι t.2))

/-- Sum over the five indices. -/
def sum5 (F : Fin 5 → Poly4) : Poly4 := Poly4.sum ((List.finRange 5).map F)

/-! ### The boundary expression -/

open Data in
/-- The polynomial of `Q f`. -/
def fPoly : Poly4 := rowsPoly (famEntries .f) fun _ => 0

open Data in
/-- The polynomial of `Q U_{jk}`. -/
def uPoly (j k : Fin 5) : Poly4 := rowsPoly (famEntries .U) (idx2 j k)

open Data in
/-- The polynomial of `Q K_{lijk}`. -/
def kPoly (l i j k : Fin 5) : Poly4 := rowsPoly (famEntries .K) (idx4 l i j k)

open Data in
/-- The polynomial of `Q M_l`. -/
def mPoly (l : Fin 5) : Poly4 := rowsPoly (famEntries .M) fun _ => l

/-- The polynomial of `(S₀)_{jk} = λ A_{jk} - (A²)_{jk}` at the diagonal data. -/
def s0Poly (j k : Fin 5) : Poly4 :=
  if j = k then merge (mul lamPoly (dPoly j)) (smul (-1) (Poly4.pow (dPoly j) 2)) else []

/-- The polynomial of `p_i` at `p = e₅`. -/
def pPoly (i : Fin 5) : Poly4 := if i = 4 then const 1 else []

/-- The polynomial of `V_{ijk}`. -/
def vPoly (i j k : Fin 5) : Poly4 :=
  Poly4.sum [mul (pPoly i) (s0Poly j k), mul (pPoly j) (s0Poly k i), mul (pPoly k) (s0Poly i j),
    mul (pPoly i) (mul (pPoly j) (pPoly k))]

/-- The polynomial of `Q 𝓢` at the diagonal data. Factors that vanish for most indices are put
first, so that the other factor is not computed. -/
def sPoly : Poly4 :=
  Poly4.sum [
    mul (smul (-1) lamPoly) fPoly,
    sum5 fun j => sum5 fun k => mul (merge (s0Poly j k) (mul (pPoly j) (pPoly k))) (uPoly j k),
    sum5 fun l => sum5 fun i => sum5 fun j => sum5 fun k =>
      mul (mul (pPoly l) (vPoly i j k)) (merge (kPoly l i j k) (smul (-1) (kPoly i l j k))),
    sum5 fun l => mul (pPoly l) (mPoly l)]

/-! ### Soundness -/

section Soundness

variable (x : Fin 4 → ℝ)

theorem eval_sum5 (F : Fin 5 → Poly4) : eval (sum5 F) x = ∑ i, eval (F i) x := by
  rw [sum5, eval_sum, List.map_map, Fin.sum_univ_def]
  rfl

theorem eval_lamPoly : eval lamPoly x = -∑ i, x i := by
  rw [lamPoly, eval_smul, eval_sum, List.map_map, Fin.sum_univ_def]
  simp [Function.comp_def, eval_var]

theorem eval_dPoly (a : Fin 5) : eval (dPoly a) x = dvec x a := by
  unfold dPoly dvec
  split_ifs
  · exact eval_var _ x
  · exact eval_lamPoly x

theorem of_diagA : Matrix.of (diagA x) = Matrix.diagonal (dvec x) := by
  ext i j
  simp [diagA, Matrix.diagonal_apply]

theorem diagData_A : (diagData x).A = Matrix.diagonal (dvec x) := of_diagA x

/-- The weight of an endpoint as an indicator. -/
def ind (o : Option (Fin 5)) (a : Fin 5) : ℝ :=
  match o with
  | some b => if a = b then 1 else 0
  | none => 0

theorem weight_diagData (ι : ℕ → Fin 5) {u : Endpoint} (hu : u.isX = false) (a : Fin 5) :
    (diagData x).weight ι u a = ind (endIdx ι u) a := by
  cases u with
  | p => simp [diagData, CertData.withAPG, CertData.weight, endIdx, ind, e5]
  | ell => simp [diagData, CertData.withAPG, CertData.weight, endIdx, ind, CertData.base]
  | x c => simp [Endpoint.isX] at hu
  | slot i => simp [CertData.weight, endIdx, ind]

theorem sum_ind_ind (o o' : Option (Fin 5)) (F : Fin 5 → ℝ) :
    ∑ a, ∑ b, ind o a * ind o' b * (if a = b then F a else 0) =
      match o, o' with
      | some a, some b => if a = b then F a else 0
      | _, _ => 0 := by
  rcases o with _ | a <;> rcases o' with _ | b
  · simp [ind]
  · simp [ind]
  · simp [ind]
  · simp only [ind, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
    simp [Finset.sum_ite_eq', Finset.sum_ite_eq]
    split_ifs <;> simp_all

theorem val_diagData (ι : ℕ → Fin 5) {e : Edge} (he : e.hasX = false) :
    e.val (diagData x) ι = eval (edgePoly ι e) x := by
  simp only [Edge.hasX, Bool.or_eq_false_iff] at he
  simp only [Edge.val, weight_diagData x ι he.1, weight_diagData x ι he.2, diagData_A,
    Matrix.diagonal_pow, Matrix.diagonal_apply, sum_ind_ind, edgePoly]
  rcases endIdx ι e.u with _ | a <;> rcases endIdx ι e.v with _ | b
  · rfl
  · rfl
  · rfl
  · simp only
    split_ifs
    · rw [eval_pow, eval_dPoly]; rfl
    · rfl

theorem trace_diagData (t : ℕ) : ((diagData x).A ^ t).trace = eval (tracePoly t) x := by
  rw [diagData_A, Matrix.diagonal_pow, Matrix.trace_diagonal, tracePoly, eval_sum,
    List.map_map, Fin.sum_univ_def]
  simp [Function.comp_def, eval_pow, eval_dPoly]
  rfl

theorem eval_foldr_mul {α : Type*} (F : α → Poly4) (l : List α) (P : Poly4) :
    eval (l.foldr (fun e acc => mul (F e) acc) P) x = (l.map fun e => eval (F e) x).prod *
      eval P x := by
  induction l with
  | nil => simp
  | cons e l ih => simp only [List.foldr_cons, eval_mul, ih, List.map_cons, List.prod_cons]; ring

/-- **Soundness of the diagonal evaluation** for keys without copies of `X`. -/
theorem eval_keyPoly (ι : ℕ → Fin 5) {k : Key} (hk : k.hasX = false) :
    k.eval (diagData x) ι = eval (keyPoly ι k) x := by
  have hE : ∀ e ∈ k.edges, e.hasX = false := by simpa [Key.hasX] using hk
  rw [Key.eval_eq_prod_of_hasX_eq_false hk, Key.prefactor, keyPoly]
  have hg : (diagData x).g = 0 := rfl
  have hw : (diagData x).w = 0 := rfl
  have hz : (diagData x).z = 0 := rfl
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := h
    rw [eval_foldr_mul, eval_foldr_mul, eval_const, h1, h2, h3]
    simp only [pow_zero, one_mul, Int.cast_one, mul_one]
    rw [mul_comm]
    congr 1
    · exact congrArg List.prod (List.map_congr_left fun e he => val_diagData x ι (hE e he))
    · exact congrArg List.prod (List.map_congr_left fun t _ => trace_diagData x t)
  · rw [hg, hw, hz, eval_nil]
    rcases Nat.eq_zero_or_pos k.gPow with h1 | h1
    · rcases Nat.eq_zero_or_pos k.wPow with h2 | h2
      · have h3 : k.zPow ≠ 0 := fun h3 => h ⟨h1, h2, h3⟩
        simp [zero_pow h3]
      · simp [zero_pow h2.ne']
    · simp [zero_pow h1.ne']

theorem eval_rowsPoly {rows : List (ℤ × Key)} (h : RowsXFree rows) (ι : ℕ → Fin 5) :
    eval (rowsPoly rows ι) x = certQ * polyMap rows certQ ι (diagA x, e5, 0) := by
  rw [rowsPoly, eval_sum, List.map_map, polyMap, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  simp only [Function.comp_apply, eval_smul, Key.evalFun]
  rw [← eval_keyPoly x ι (h t ht)]
  simp only [diagData, certQ]
  field_simp

end Soundness

section Boundary

open Data

variable (x : Fin 4 → ℝ)

theorem eval_fPoly : eval fPoly x = certQ * tableCoeffs.f (diagA x, e5, 0) :=
  eval_rowsPoly x rowsOfRank_famEntries_f.plain.xFree _

theorem eval_uPoly (j k : Fin 5) :
    eval (uPoly j k) x = certQ * tableCoeffs.U (diagA x, e5, 0) j k :=
  eval_rowsPoly x rowsOfRank_famEntries_U.plain.xFree _

theorem eval_kPoly (l i j k : Fin 5) :
    eval (kPoly l i j k) x = certQ * tableCoeffs.K (diagA x, e5, 0) l i j k :=
  eval_rowsPoly x rowsOfRank_famEntries_K.plain.xFree _

theorem eval_mPoly (l : Fin 5) : eval (mPoly l) x = certQ * tableCoeffs.M (diagA x, e5, 0) l :=
  eval_rowsPoly x rowsOfRank_famEntries_M.plain.xFree _

theorem dvec_four : dvec x 4 = -∑ i, x i := by simp [dvec]

theorem eval_lamPoly' : eval lamPoly x = dvec x 4 := by rw [eval_lamPoly, dvec_four]

theorem bdryS0_diagA (lam : ℝ) (j k : Fin 5) :
    Coeffs.bdryS0 (diagA x) lam j k = if j = k then lam * dvec x j - dvec x j ^ 2 else 0 := by
  simp only [Coeffs.bdryS0, diagA, mul_ite, ite_mul, mul_zero, zero_mul]
  split_ifs with h
  · subst h; simp [sq]
  · simp [h]

theorem eval_s0Poly (j k : Fin 5) :
    eval (s0Poly j k) x = Coeffs.bdryS0 (diagA x) (dvec x 4) j k := by
  rw [bdryS0_diagA, s0Poly]
  split_ifs
  · rw [eval_merge, eval_mul, eval_smul, eval_pow, eval_lamPoly', eval_dPoly]; push_cast; ring
  · rfl

theorem eval_pPoly (i : Fin 5) : eval (pPoly i) x = e5 i := by
  unfold pPoly e5; split_ifs <;> simp [eval_const]

theorem eval_vPoly (i j k : Fin 5) :
    eval (vPoly i j k) x = Coeffs.bdryV (diagA x) e5 (dvec x 4) i j k := by
  simp only [vPoly, eval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, eval_mul,
    eval_pPoly, eval_s0Poly, Coeffs.bdryV]
  ring

/-- **The boundary expression at the diagonal data** is `Q⁻¹` times the value of `sPoly`. -/
theorem eval_sPoly :
    eval sPoly x = certQ * tableCoeffs.boundaryExpr (diagA x) e5 (dvec x 4) := by
  have h1 : eval (mul (smul (-1) lamPoly) fPoly) x =
      certQ * (-dvec x 4 * tableCoeffs.f (diagA x, e5, 0)) := by
    rw [eval_mul, eval_smul, eval_lamPoly', eval_fPoly]; push_cast; ring
  have h2 : eval (sum5 fun j => sum5 fun k =>
      mul (merge (s0Poly j k) (mul (pPoly j) (pPoly k))) (uPoly j k)) x =
      certQ * ∑ j, ∑ k, tableCoeffs.U (diagA x, e5, 0) j k *
        (Coeffs.bdryS0 (diagA x) (dvec x 4) j k + e5 j * e5 k) := by
    rw [eval_sum5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_sum5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_merge, eval_mul, eval_s0Poly, eval_pPoly, eval_pPoly, eval_uPoly]; ring
  have h3 : eval (sum5 fun l => sum5 fun i => sum5 fun j => sum5 fun k =>
      mul (mul (pPoly l) (vPoly i j k)) (merge (kPoly l i j k) (smul (-1) (kPoly i l j k)))) x =
      certQ * ∑ l, ∑ i, ∑ j, ∑ k, tableCoeffs.C (diagA x, e5, 0) l i j k * e5 l *
        Coeffs.bdryV (diagA x) e5 (dvec x 4) i j k := by
    rw [eval_sum5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [eval_sum5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [eval_sum5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [eval_sum5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_mul, eval_mul, eval_merge, eval_smul, eval_pPoly, eval_vPoly, eval_kPoly,
      eval_kPoly, Coeffs.C]
    push_cast; ring
  have h4 : eval (sum5 fun l => mul (pPoly l) (mPoly l)) x =
      certQ * ∑ l, e5 l * tableCoeffs.M (diagA x, e5, 0) l := by
    rw [eval_sum5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [eval_mul, eval_pPoly, eval_mPoly]; ring
  simp only [sPoly, eval_sum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h1, h2,
    h3, h4, Coeffs.boundaryExpr]
  ring

end Boundary

end OnePhaseDimension.Certificate.Boundary
