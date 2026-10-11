/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Tangency
public import OnePhaseDimension.Certificate.Matching
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The polynomial coefficient maps

A list of rows `(c, k)` (integer coefficient, key) and a denominator `Q` define the polynomial
map `(A, p, g) ↦ ∑ (c/Q) eval k` (`polyMap`). With the free slots read as the indices of a
scalar, a vector, a two-tensor or a four-tensor, such lists give coefficient maps of the shapes
of `OnePhaseDimension.Coeffs` (`famScalar`, `famVec`, `famTen2`, `famTen4`, `rowsCoeffs`).

For rows without copies of `X`, `ℓ`, `w`, `z` (as in the coefficient table of the 2026-09-24
version) we prove the structural properties required by `OnePhaseDimension.CertificateHolds`:

* smoothness (`contDiff_polyMap`, …);
* parity in `p`: a key with an even number of `p` endpoints is even in `p`;
* vanishing at `g = 0` of keys with a positive power of `g`;
* orthogonal equivariance of linear keys (`Key.eval_act`, `famTen2_act`, …);
* `D_l` of a coefficient map is given by the graph derivatives of its rows (`Dl_polyMap`).

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

open Finset
open scoped Matrix ContDiff

/-! ### Parity in `p` and vanishing at `g = 0` -/

/-- The number of `p` endpoints of a key. -/
def Key.pCount (k : Key) : ℕ := (k.edges.flatMap fun e => [e.u, e.v]).count .p

/-- The data with `p` replaced by `-p`. -/
def CertData.negP (d : CertData) : CertData := { d with p := -d.p }

theorem weight_negP (d : CertData) (ι : ℕ → Fin 5) (e : Endpoint) (a : Fin 5) :
    d.negP.weight ι e a = (if e = .p then -1 else 1) * d.weight ι e a := by
  cases e <;> simp [CertData.negP, CertData.weight]

theorem Edge.val_negP (d : CertData) (ι : ℕ → Fin 5) (e : Edge) :
    e.val d.negP ι = (-1) ^ ([e.u, e.v].count .p) * e.val d ι := by
  simp only [Edge.val, weight_negP, mul_sum, show d.negP.A = d.A from rfl]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  by_cases hu : e.u = .p <;> by_cases hv : e.v = .p <;> simp [hu, hv]

theorem Key.eval_negP {k : Key} (hk : k.hasX = false) (d : CertData) (ι : ℕ → Fin 5) :
    k.eval d.negP ι = (-1) ^ k.pCount * k.eval d ι := by
  rw [eval_eq_prod_of_hasX_eq_false hk, eval_eq_prod_of_hasX_eq_false hk]
  have hpre : k.prefactor d.negP = k.prefactor d := rfl
  rw [hpre, pCount]
  induction k.edges with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.prod_cons, Edge.val_negP, List.flatMap_cons,
      List.count_append, pow_add]
    rw [mul_left_comm, ih]
    ring

theorem Key.eval_negP_of_even {k : Key} (hk : k.hasX = false) (hp : Even k.pCount)
    (d : CertData) (ι : ℕ → Fin 5) : k.eval d.negP ι = k.eval d ι := by
  rw [k.eval_negP hk, hp.neg_one_pow, one_mul]

theorem Key.eval_eq_zero_of_g_eq_zero {k : Key} (hg : k.gPow ≠ 0) {d : CertData} (hd : d.g = 0)
    (ι : ℕ → Fin 5) : k.eval d ι = 0 := by
  simp [Key.eval, Key.prefactor, hd, zero_pow hg]

/-! ### Polynomial maps of lists of rows -/

/-- The base data used for the polynomial maps: all of `X, ℓ, w, z` vanish (rows without these
factors do not depend on them). -/
def CertData.base : CertData := ⟨0, 0, 0, 0, 0, 0, 0⟩

/-- The polynomial map `(A, p, g) ↦ ∑ (c/Q) eval k` of a list of rows, with slot assignment
`ι`. -/
noncomputable def polyMap (rows : List (ℤ × Key)) (Q : ℝ) (ι : ℕ → Fin 5)
    (x : Ten2 × Ten1 × ℝ) : ℝ :=
  (rows.map fun t => (t.1 / Q) * t.2.evalFun CertData.base ι x).sum

/-- The rows are free of copies of `X`. -/
def RowsXFree (rows : List (ℤ × Key)) : Prop := ∀ t ∈ rows, t.2.hasX = false

theorem contDiff_polyMap {rows : List (ℤ × Key)} (h : RowsXFree rows) (Q : ℝ) (ι : ℕ → Fin 5)
    {n : WithTop ℕ∞} : ContDiff ℝ n (polyMap rows Q ι) := by
  unfold polyMap
  induction rows with
  | nil => simpa using contDiff_const
  | cons t rows ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (contDiff_const.mul (Key.contDiff_evalFun (h t (by simp)) _ ι)).add
      (ih fun s hs => h s (by simp [hs]))

theorem polyMap_negP {rows : List (ℤ × Key)} (h : RowsXFree rows)
    (hp : ∀ t ∈ rows, Even t.2.pCount) (Q : ℝ) (ι : ℕ → Fin 5) (A : Ten2) (p : Ten1) (g : ℝ) :
    polyMap rows Q ι (A, -p, g) = polyMap rows Q ι (A, p, g) := by
  unfold polyMap
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [Key.evalFun, Key.evalFun, show CertData.base.withAPG (A, -p, g) =
    (CertData.base.withAPG (A, p, g)).negP from rfl, Key.eval_negP_of_even (h t ht) (hp t ht)]

theorem polyMap_g_zero {rows : List (ℤ × Key)} (hg : ∀ t ∈ rows, t.2.gPow ≠ 0) (Q : ℝ)
    (ι : ℕ → Fin 5) (A : Ten2) (p : Ten1) : polyMap rows Q ι (A, p, 0) = 0 := by
  unfold polyMap
  rw [List.sum_eq_zero]
  intro y hy
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
  rw [Key.evalFun, Key.eval_eq_zero_of_g_eq_zero (hg t ht) rfl, mul_zero]

/-- A key without copies of `X`, without `ℓ` endpoints and without factors `w`, `z` (the shape
of the rows of the coefficient table). -/
structure Key.Plain (k : Key) : Prop where
  hasX : k.hasX = false
  wPow : k.wPow = 0
  zPow : k.zPow = 0
  noEll : ∀ e ∈ k.edges, e.u ≠ .ell ∧ e.v ≠ .ell

/-- All rows are plain. -/
def RowsPlain (rows : List (ℤ × Key)) : Prop := ∀ t ∈ rows, t.2.Plain

theorem RowsPlain.xFree {rows : List (ℤ × Key)} (h : RowsPlain rows) : RowsXFree rows :=
  fun t ht => (h t ht).hasX

/-- The polynomial map of a plain key does not depend on the fixed data `X, ℓ, w, z`. -/
theorem Key.Plain.evalFun_eq {k : Key} (hk : k.Plain) (d d' : CertData) (ι : ℕ → Fin 5) :
    k.evalFun d ι = k.evalFun d' ι := by
  funext x
  simp only [Key.evalFun, eval_eq_prod_of_hasX_eq_false hk.hasX, Key.prefactor, hk.wPow,
    hk.zPow, pow_zero]
  congr 2
  refine List.map_congr_left fun e he => ?_
  have h₁ : ∀ a, (d.withAPG x).weight ι e.u a = (d'.withAPG x).weight ι e.u a := fun a => by
    cases hu : e.u with
    | ell => exact absurd hu (hk.noEll e he).1
    | _ => rfl
  have h₂ : ∀ a, (d.withAPG x).weight ι e.v a = (d'.withAPG x).weight ι e.v a := fun a => by
    cases hv : e.v with
    | ell => exact absurd hv (hk.noEll e he).2
    | _ => rfl
  simp only [Edge.val, h₁, h₂]
  rfl

/-- `D_l` of a polynomial map of plain rows is given by the graph derivatives of its rows, on
admissible data, when the derivative index `l = ι r` for rows of rank `r`. -/
theorem Dl_polyMap {rows : List (ℤ × Key)} (h : RowsPlain rows) (Q : ℝ) (ι : ℕ → Fin 5)
    {d : CertData} (hd : d.Admissible) (l : Fin 5)
    (hl : ∀ t ∈ rows, ι t.2.rank = l) :
    Dl (polyMap rows Q ι) d.A d.X d.p d.g d.w d.z l =
      (rows.map fun t => (t.1 / Q) *
        (t.2.derivTerms.map fun u => (u.1 : ℝ) * u.2.eval d ι).sum).sum := by
  have hfun : polyMap rows Q ι = fun x => (rows.map fun t => (t.1 / Q) *
      t.2.evalFun d ι x).sum := by
    funext x
    unfold polyMap
    congr 1
    exact List.map_congr_left fun t ht => by rw [(h t ht).evalFun_eq CertData.base d ι]
  rw [hfun, Dl_list_sum (d.A : Ten2) d.X d.p d.g d.w d.z l rows (fun t => t.2.evalFun d ι)
    (fun t => (t.1 : ℝ) / Q) fun t ht =>
      ((Key.contDiff_evalFun (n := 1) (h t ht).hasX d ι).differentiable one_ne_zero) _]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [Key.sum_derivTerms_eq_Dl (h t ht).hasX hd ι, hl t ht]


/-! ### Orthogonal equivariance -/

/-- The weight of an endpoint with arbitrary weight vectors `W i` at the free slots. -/
def weightW (d : CertData) (W : ℕ → Fin 5 → ℝ) : Endpoint → Fin 5 → ℝ
  | .p, a => d.p a
  | .ell, a => d.ell a
  | .x _, _ => 1
  | .slot i, a => W i a

/-- The value of an edge with slot weights `W`. -/
def Edge.valW (d : CertData) (W : ℕ → Fin 5 → ℝ) (e : Edge) : ℝ :=
  ∑ a, ∑ b, weightW d W e.u a * weightW d W e.v b * (d.A ^ e.pow) a b

/-- The value of a key without `X` with slot weights `W`. -/
def Key.evalW (k : Key) (d : CertData) (W : ℕ → Fin 5 → ℝ) : ℝ :=
  k.prefactor d * (k.edges.map (Edge.valW d W)).prod

/-- The slot weights of a slot assignment. -/
def deltaW (ι : ℕ → Fin 5) (i : ℕ) (a : Fin 5) : ℝ := if a = ι i then 1 else 0

theorem Key.eval_eq_evalW {k : Key} (hk : k.hasX = false) (d : CertData) (ι : ℕ → Fin 5) :
    k.eval d ι = k.evalW d (deltaW ι) := by
  rw [eval_eq_prod_of_hasX_eq_false hk, Key.evalW]
  congr 2

theorem valW_eq_dotProduct (x y : Fin 5 → ℝ) (M : Matrix (Fin 5) (Fin 5) ℝ) :
    ∑ a, ∑ b, x a * y b * M a b = x ⬝ᵥ (M *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, mul_sum]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

/-- The matrix of a two-tensor. -/
abbrev omat (O : Ten2) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of O

theorem transpose_mul_self_of_isOrth5 {O : Ten2} (hO : IsOrth5 O) :
    (omat O)ᵀ * omat O = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
  exact (hO i j).trans rfl

theorem act2_eq (O A : Ten2) : Matrix.of (act2 O A) = omat O * Matrix.of A * (omat O)ᵀ := by
  ext i j
  simp only [act2, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_mul]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

theorem conj_pow {O N : Matrix (Fin 5) (Fin 5) ℝ} (h : Oᵀ * O = 1) (k : ℕ) :
    (O * N * Oᵀ) ^ k = O * N ^ k * Oᵀ := by
  induction k with
  | zero =>
    simp only [pow_zero, Matrix.mul_one]
    rw [← mul_eq_one_comm.1 h]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc O * N ^ k * Oᵀ * (O * N * Oᵀ) = O * N ^ k * (Oᵀ * O) * N * Oᵀ := by
          simp only [Matrix.mul_assoc]
      _ = O * (N ^ k * N) * Oᵀ := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/-- The weight vector transformed by `Oᵀ`. -/
theorem weightW_act {O : Ten2} (hO : IsOrth5 O) (d : CertData) (W : ℕ → Fin 5 → ℝ)
    (A : Ten2) (p : Ten1) (g : ℝ) {e : Endpoint} (he : e.isX = false) (hl : e ≠ .ell) :
    weightW (d.withAPG (act2 O A, act1 O p, g)) W e ᵥ* omat O =
      weightW (d.withAPG (A, p, g)) (fun i c => ∑ a, W i a * O a c) e := by
  funext c
  cases e with
  | p =>
    simp only [weightW, CertData.withAPG, Matrix.vecMul, dotProduct, act1, Matrix.of_apply]
    rw [show (∑ a, (∑ b, O a b * p b) * O a c) = ∑ b, p b * ∑ a, O a b * O a c by
      simp only [sum_mul, mul_sum]
      rw [Finset.sum_comm]
      exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring]
    simp only [show ∀ b, ∑ a, O a b * O a c = kron b c from fun b => hO b c, kron, mul_ite,
      mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  | ell => exact absurd rfl hl
  | x c' => simp [Endpoint.isX] at he
  | slot i => simp [weightW, Matrix.vecMul, dotProduct]


/-- Equivariance of slot-weighted values: acting on `(A, p)` by `O` is acting on the slot
weights by `Oᵀ`. -/
theorem Key.evalW_act {k : Key} (hk : k.hasX = false)
    (hl : ∀ e ∈ k.edges, e.u ≠ .ell ∧ e.v ≠ .ell) {O : Ten2} (hO : IsOrth5 O) (d : CertData)
    (W : ℕ → Fin 5 → ℝ) (A : Ten2) (p : Ten1) (g : ℝ) :
    k.evalW (d.withAPG (act2 O A, act1 O p, g)) W =
      k.evalW (d.withAPG (A, p, g)) (fun i c => ∑ a, W i a * O a c) := by
  have hOO := transpose_mul_self_of_isOrth5 hO
  have hpow : ∀ t, (d.withAPG (act2 O A, act1 O p, g)).A ^ t =
      omat O * (d.withAPG (A, p, g)).A ^ t * (omat O)ᵀ := fun t => by
    simp only [CertData.withAPG]
    rw [act2_eq, conj_pow hOO]
  have htr : ∀ t, ((d.withAPG (act2 O A, act1 O p, g)).A ^ t).trace =
      ((d.withAPG (A, p, g)).A ^ t).trace := fun t => by
    rw [hpow, Matrix.trace_mul_cycle, hOO, Matrix.one_mul]
  unfold Key.evalW Key.prefactor
  simp only [htr]
  congr 2
  · refine List.map_congr_left fun e he => ?_
    have hx : e.u.isX = false ∧ e.v.isX = false := by
      have := hasX_eq_false_of_mem hk he
      simpa [Edge.hasX] using this
    simp only [Edge.valW, valW_eq_dotProduct, hpow, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.mulVec_transpose,
      weightW_act hO d W A p g hx.1 (hl e he).1, weightW_act hO d W A p g hx.2 (hl e he).2]

theorem weightW_update_of_ne (d : CertData) (W : ℕ → Fin 5 → ℝ) {s : ℕ} (V : Fin 5 → ℝ)
    {x : Endpoint} (hx : x ≠ .slot s) :
    weightW d (Function.update W s V) x = weightW d W x := by
  cases x with
  | slot i =>
    have : i ≠ s := fun h => hx (by rw [h])
    exact Function.update_of_ne this V W
  | _ => rfl

theorem valW_update_of_ne (d : CertData) (W : ℕ → Fin 5 → ℝ) {s : ℕ} (V : Fin 5 → ℝ)
    {e : Edge} (hu : e.u ≠ .slot s) (hv : e.v ≠ .slot s) :
    e.valW d (Function.update W s V) = e.valW d W := by
  simp only [Edge.valW, weightW_update_of_ne d W V hu, weightW_update_of_ne d W V hv]

theorem weightW_slot (d : CertData) (W : ℕ → Fin 5 → ℝ) (i : ℕ) :
    weightW d W (.slot i) = W i := rfl

/-- The weight vector `δ_a`. -/
def unitW (a : Fin 5) (c : Fin 5) : ℝ := if c = a then 1 else 0

theorem valW_expand (d : CertData) (W : ℕ → Fin 5 → ℝ) {s : ℕ} {e : Edge}
    (h : [e.u, e.v].count (.slot s) = 1) :
    e.valW d W = ∑ a, W s a * e.valW d (Function.update W s (unitW a)) := by
  rw [count_ends] at h
  by_cases hu : e.u = .slot s <;> by_cases hv : e.v = .slot s <;> simp only [hu, hv,
    ite_true, ite_false] at h
  · omega
  · have hw : ∀ a, e.valW d (Function.update W s (unitW a)) =
        ∑ b, weightW d W e.v b * (d.A ^ e.pow) a b := fun a => by
      simp only [Edge.valW, hu, weightW_slot, Function.update_self,
        weightW_update_of_ne d W _ hv, unitW, ite_mul, one_mul, zero_mul, sum_ite_irrel,
        sum_const_zero, sum_ite_eq', mem_univ, ite_true]
    simp only [hw]
    simp only [Edge.valW, hu, weightW_slot, mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  · have hw : ∀ a, e.valW d (Function.update W s (unitW a)) =
        ∑ c, weightW d W e.u c * (d.A ^ e.pow) c a := fun a => by
      simp only [Edge.valW, hv, weightW_slot, Function.update_self,
        weightW_update_of_ne d W _ hu, unitW, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        sum_ite_eq', mem_univ, ite_true]
    simp only [hw]
    simp only [Edge.valW, hv, weightW_slot, mul_sum]
    rw [Finset.sum_comm]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  · omega

theorem prod_valW_update_of_zero (d : CertData) (W : ℕ → Fin 5 → ℝ) {s : ℕ} (V : Fin 5 → ℝ) :
    ∀ L : List Edge, slotCount (.slot s) L = 0 →
      (L.map (Edge.valW d (Function.update W s V))).prod = (L.map (Edge.valW d W)).prod
  | [], _ => rfl
  | e :: L, h => by
    rw [slotCount_cons] at h
    have he : [e.u, e.v].count (.slot s) = 0 := by omega
    rw [count_ends] at he
    have hu : e.u ≠ .slot s := fun hu => by simp [hu] at he
    have hv : e.v ≠ .slot s := fun hv => by simp [hv] at he
    simp only [List.map_cons, List.prod_cons, valW_update_of_ne d W V hu hv,
      prod_valW_update_of_zero d W V (s := s) L (by omega)]

theorem prod_valW_expand (d : CertData) (W : ℕ → Fin 5 → ℝ) {s : ℕ} :
    ∀ L : List Edge, slotCount (.slot s) L = 1 →
      (L.map (Edge.valW d W)).prod =
        ∑ a, W s a * (L.map (Edge.valW d (Function.update W s (unitW a)))).prod
  | [], h => by simp [slotCount] at h
  | e :: L, h => by
    rw [slotCount_cons] at h
    simp only [List.map_cons, List.prod_cons]
    rcases (by omega : ([e.u, e.v].count (.slot s) = 1 ∧ slotCount (.slot s) L = 0) ∨
        ([e.u, e.v].count (.slot s) = 0 ∧ slotCount (.slot s) L = 1)) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · rw [valW_expand d W h₁, sum_mul]
      refine sum_congr rfl fun a _ => ?_
      rw [prod_valW_update_of_zero d W _ (s := s) L h₂]
      ring
    · rw [count_ends] at h₁
      have hu : e.u ≠ .slot s := fun hu => by simp [hu] at h₁
      have hv : e.v ≠ .slot s := fun hv => by simp [hv] at h₁
      rw [prod_valW_expand d W (s := s) L h₂, mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [valW_update_of_ne d W _ hu hv]
      ring

/-- Multilinear expansion in a slot that occurs exactly once. -/
theorem Key.evalW_expand (k : Key) (d : CertData) (W : ℕ → Fin 5 → ℝ) {s : ℕ}
    (hs : slotCount (.slot s) k.edges = 1) :
    k.evalW d W = ∑ a, W s a * k.evalW d (Function.update W s (unitW a)) := by
  simp only [Key.evalW, prod_valW_expand d W k.edges hs, mul_sum]
  exact sum_congr rfl fun a _ => by ring

/-- The slot-weighted value only depends on the weights of the slots that occur. -/
theorem Key.evalW_congr (k : Key) (d : CertData) {W W' : ℕ → Fin 5 → ℝ}
    (h : ∀ s, slotCount (.slot s) k.edges ≠ 0 → W s = W' s) : k.evalW d W = k.evalW d W' := by
  unfold Key.evalW
  congr 2
  refine List.map_congr_left fun e he => ?_
  have hw : ∀ x : Endpoint, (x = e.u ∨ x = e.v) → weightW d W x = weightW d W' x := by
    intro x hx
    cases x with
    | slot i =>
      refine h i fun h0 => ?_
      have := List.count_eq_zero.1 h0
      exact this (List.mem_flatMap.2 ⟨e, he, by rcases hx with h | h <;> simp [h]⟩)
    | _ => rfl
  simp only [Edge.valW, hw e.u (Or.inl rfl), hw e.v (Or.inr rfl)]


/-- The slot assignment `0 ↦ l`, `1 ↦ i`, `2 ↦ j`, `3 ↦ k` (and `k` beyond). -/
def idx4 (l i j k : Fin 5) (n : ℕ) : Fin 5 :=
  if n = 0 then l else if n = 1 then i else if n = 2 then j else k

namespace Key

/-- The polynomial map of a plain key at `(O A Oᵀ, O p, g)`: the slot weights become the rows
`O_{ι s, ·}`. -/
theorem evalFun_act {k : Key} (hk : k.Plain) {O : Ten2} (hO : IsOrth5 O) (d : CertData)
    (ι : ℕ → Fin 5) (A : Ten2) (p : Ten1) (g : ℝ) :
    k.evalFun d ι (act2 O A, act1 O p, g) =
      k.evalW (d.withAPG (A, p, g)) (fun s c => O (ι s) c) := by
  rw [evalFun, eval_eq_evalW hk.hasX, evalW_act hk.hasX hk.noEll hO]
  congr 1
  funext s c
  simp [deltaW]

theorem evalW_eq_eval_of_linear {k : Key} (hk : k.Plain) (hlin : k.Linear) (d : CertData)
    {W : ℕ → Fin 5 → ℝ} {ι : ℕ → Fin 5} (h : ∀ s < k.rank, W s = deltaW ι s) :
    k.evalW d W = k.eval d ι := by
  rw [eval_eq_evalW hk.hasX]
  refine evalW_congr k d fun s hs => h s ?_
  rw [hlin s] at hs
  by_contra h'
  exact hs (ite_eq_right h')

theorem unitW_eq (a : Fin 5) : unitW a = deltaW (fun _ => a) 0 := rfl

/-- Invariance of a plain linear key of rank `0`. -/
theorem evalFun_act_rank0 {k : Key} (hk : k.Plain) (hlin : k.Linear) (h0 : k.rank = 0)
    {O : Ten2} (hO : IsOrth5 O) (d : CertData) (ι : ℕ → Fin 5) (A : Ten2) (p : Ten1) (g : ℝ) :
    k.evalFun d ι (act2 O A, act1 O p, g) = k.evalFun d ι (A, p, g) := by
  rw [evalFun_act hk hO]
  exact evalW_eq_eval_of_linear hk hlin _ fun s hs => by omega

/-- Equivariance of a plain linear key of rank `1`. -/
theorem evalFun_act_rank1 {k : Key} (hk : k.Plain) (hlin : k.Linear) (h1 : k.rank = 1)
    {O : Ten2} (hO : IsOrth5 O) (d : CertData) (l : Fin 5) (A : Ten2) (p : Ten1) (g : ℝ) :
    k.evalFun d (fun _ => l) (act2 O A, act1 O p, g) =
      ∑ a, O l a * k.evalFun d (fun _ => a) (A, p, g) := by
  rw [evalFun_act hk hO, evalW_expand k _ _ (s := 0) (by rw [hlin]; simp [h1])]
  refine sum_congr rfl fun a _ => ?_
  rw [evalFun]
  congr 1
  refine evalW_eq_eval_of_linear hk hlin _ fun s hs => ?_
  rcases (by omega : s = 0) with rfl
  funext c
  simp [unitW, deltaW]

/-- Equivariance of a plain linear key of rank `2`. -/
theorem evalFun_act_rank2 {k : Key} (hk : k.Plain) (hlin : k.Linear) (h2 : k.rank = 2)
    {O : Ten2} (hO : IsOrth5 O) (d : CertData) (i j : Fin 5) (A : Ten2) (p : Ten1) (g : ℝ) :
    k.evalFun d (idx2 i j) (act2 O A, act1 O p, g) =
      ∑ a, ∑ b, O i a * O j b * k.evalFun d (idx2 a b) (A, p, g) := by
  rw [evalFun_act hk hO, evalW_expand k _ _ (s := 0) (by rw [hlin]; simp [h2])]
  refine sum_congr rfl fun a _ => ?_
  rw [evalW_expand k _ _ (s := 1) (by rw [hlin]; simp [h2]), mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [evalFun]
  simp only [Function.update_of_ne (by norm_num : (1 : ℕ) ≠ 0), idx2]
  rw [evalW_eq_eval_of_linear hk hlin _ (ι := idx2 a b) fun s hs => ?_]
  · simp; ring
  · rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
    · funext c; simp [Function.update_of_ne, unitW, deltaW, idx2]
    · funext c; simp [unitW, deltaW, idx2]

/-- Equivariance of a plain linear key of rank `4`. -/
theorem evalFun_act_rank4 {k : Key} (hk : k.Plain) (hlin : k.Linear) (h4 : k.rank = 4)
    {O : Ten2} (hO : IsOrth5 O) (d : CertData) (l i j m : Fin 5) (A : Ten2) (p : Ten1)
    (g : ℝ) :
    k.evalFun d (idx4 l i j m) (act2 O A, act1 O p, g) =
      ∑ a, ∑ b, ∑ c, ∑ e, O l a * O i b * O j c * O m e *
        k.evalFun d (idx4 a b c e) (A, p, g) := by
  rw [evalFun_act hk hO, evalW_expand k _ _ (s := 0) (by rw [hlin]; simp [h4])]
  refine sum_congr rfl fun a _ => ?_
  rw [evalW_expand k _ _ (s := 1) (by rw [hlin]; simp [h4])]
  simp only [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [evalW_expand k _ _ (s := 2) (by rw [hlin]; simp [h4])]
  simp only [mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [evalW_expand k _ _ (s := 3) (by rw [hlin]; simp [h4])]
  simp only [mul_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [evalFun, evalW_eq_eval_of_linear hk hlin _ (ι := idx4 a b c e) fun s hs => ?_]
  · simp [idx4]; ring
  · rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl | rfl <;>
      funext c <;> simp [unitW, deltaW, idx4]

end Key


/-! ### Coefficient maps from lists of rows -/

/-- A scalar coefficient map. -/
noncomputable def famScalar (rows : List (ℤ × Key)) (Q : ℝ) : Ten2 × Ten1 × ℝ → ℝ :=
  polyMap rows Q fun _ => 0

/-- A vector coefficient map (slot `0` is the vector index). -/
noncomputable def famVec (rows : List (ℤ × Key)) (Q : ℝ) : Ten2 × Ten1 × ℝ → Ten1 :=
  fun x l => polyMap rows Q (fun _ => l) x

/-- A two-tensor coefficient map (slots `0, 1`). -/
noncomputable def famTen2 (rows : List (ℤ × Key)) (Q : ℝ) : Ten2 × Ten1 × ℝ → Ten2 :=
  fun x j k => polyMap rows Q (idx2 j k) x

/-- A four-tensor coefficient map (slots `0, 1, 2, 3`). -/
noncomputable def famTen4 (rows : List (ℤ × Key)) (Q : ℝ) : Ten2 × Ten1 × ℝ → Ten4 :=
  fun x l i j k => polyMap rows Q (idx4 l i j k) x

/-- The coefficient data defined by five lists of rows `f, U, K, M, P` and the denominator
`Q`. -/
noncomputable def rowsCoeffs (rf ru rk rm rp : List (ℤ × Key)) (Q : ℝ) : Coeffs where
  f := famScalar rf Q
  U := famTen2 ru Q
  K := famTen4 rk Q
  M := famVec rm Q
  P := famVec rp Q

/-- The rows are plain, linear, and of rank `r`. -/
structure RowsOfRank (rows : List (ℤ × Key)) (r : ℕ) : Prop where
  plain : RowsPlain rows
  linear : ∀ t ∈ rows, t.2.Linear
  rank : ∀ t ∈ rows, t.2.rank = r

theorem list_sum_finset_sum {κ : Type*} (L : List κ) (F : κ → Fin 5 → ℝ) :
    (L.map fun t => ∑ a, F t a).sum = ∑ a, (L.map fun t => F t a).sum := by
  induction L with
  | nil => simp
  | cons t L ih => simp only [List.map_cons, List.sum_cons, ih, sum_add_distrib]

section Families

variable {rows : List (ℤ × Key)} {Q : ℝ}

theorem contDiff_famScalar (h : RowsPlain rows) {n : WithTop ℕ∞} :
    ContDiff ℝ n (famScalar rows Q) :=
  contDiff_polyMap h.xFree Q _

theorem contDiff_famVec (h : RowsPlain rows) {n : WithTop ℕ∞} : ContDiff ℝ n (famVec rows Q) :=
  contDiff_pi.2 fun _ => contDiff_polyMap h.xFree Q _

theorem contDiff_famTen2 (h : RowsPlain rows) {n : WithTop ℕ∞} :
    ContDiff ℝ n (famTen2 rows Q) :=
  contDiff_pi.2 fun _ => contDiff_pi.2 fun _ => contDiff_polyMap h.xFree Q _

theorem contDiff_famTen4 (h : RowsPlain rows) {n : WithTop ℕ∞} :
    ContDiff ℝ n (famTen4 rows Q) :=
  contDiff_pi.2 fun _ => contDiff_pi.2 fun _ => contDiff_pi.2 fun _ => contDiff_pi.2 fun _ =>
    contDiff_polyMap h.xFree Q _

theorem famScalar_act (h : RowsOfRank rows 0) {O : Ten2} (hO : IsOrth5 O) (A : Ten2) (p : Ten1)
    (g : ℝ) : famScalar rows Q (act2 O A, act1 O p, g) = famScalar rows Q (A, p, g) := by
  unfold famScalar polyMap
  congr 1
  exact List.map_congr_left fun t ht => by
    rw [Key.evalFun_act_rank0 (h.plain t ht) (h.linear t ht) (h.rank t ht) hO]

theorem famVec_act (h : RowsOfRank rows 1) {O : Ten2} (hO : IsOrth5 O) (A : Ten2) (p : Ten1)
    (g : ℝ) : famVec rows Q (act2 O A, act1 O p, g) = act1 O (famVec rows Q (A, p, g)) := by
  funext l
  simp only [famVec, polyMap, act1, ← List.sum_map_mul_left]
  rw [← list_sum_finset_sum]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [Key.evalFun_act_rank1 (h.plain t ht) (h.linear t ht) (h.rank t ht) hO, mul_sum]
  exact sum_congr rfl fun a _ => by ring

theorem famTen2_act (h : RowsOfRank rows 2) {O : Ten2} (hO : IsOrth5 O) (A : Ten2) (p : Ten1)
    (g : ℝ) : famTen2 rows Q (act2 O A, act1 O p, g) = act2 O (famTen2 rows Q (A, p, g)) := by
  funext i j
  simp only [famTen2, polyMap, act2, ← List.sum_map_mul_left]
  simp only [← list_sum_finset_sum]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [Key.evalFun_act_rank2 (h.plain t ht) (h.linear t ht) (h.rank t ht) hO, mul_sum]
  exact sum_congr rfl fun a _ => by rw [mul_sum]; exact sum_congr rfl fun b _ => by ring

theorem famTen4_act (h : RowsOfRank rows 4) {O : Ten2} (hO : IsOrth5 O) (A : Ten2) (p : Ten1)
    (g : ℝ) : famTen4 rows Q (act2 O A, act1 O p, g) = act4 O (famTen4 rows Q (A, p, g)) := by
  funext l i j k
  simp only [famTen4, polyMap, act4, ← List.sum_map_mul_left]
  simp only [← list_sum_finset_sum]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  rw [Key.evalFun_act_rank4 (h.plain t ht) (h.linear t ht) (h.rank t ht) hO]
  simp only [mul_sum]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun e _ => by ring

theorem famTen2_neg (h : RowsPlain rows) (hp : ∀ t ∈ rows, Even t.2.pCount) (A : Ten2)
    (p : Ten1) (g : ℝ) : famTen2 rows Q (A, -p, g) = famTen2 rows Q (A, p, g) := by
  funext j k
  exact polyMap_negP h.xFree hp Q _ A p g

theorem famTen4_neg (h : RowsPlain rows) (hp : ∀ t ∈ rows, Even t.2.pCount) (A : Ten2)
    (p : Ten1) (g : ℝ) : famTen4 rows Q (A, -p, g) = famTen4 rows Q (A, p, g) := by
  funext l i j k
  exact polyMap_negP h.xFree hp Q _ A p g

theorem famVec_g_zero (hg : ∀ t ∈ rows, t.2.gPow ≠ 0) (A : Ten2) (p : Ten1) :
    famVec rows Q (A, p, 0) = 0 := by
  funext l
  exact polyMap_g_zero hg Q _ A p

end Families

/-! ### The structural fields of the certificate statement -/

section Structural

variable {rf ru rk rm rp : List (ℤ × Key)} {Q : ℝ}

theorem rowsCoeffs_smooth (hf : RowsPlain rf) (hu : RowsPlain ru) (hk : RowsPlain rk)
    (hm : RowsPlain rm) (hp : RowsPlain rp) :
    ContDiff ℝ ∞ (rowsCoeffs rf ru rk rm rp Q).f ∧ ContDiff ℝ ∞ (rowsCoeffs rf ru rk rm rp Q).U ∧
      ContDiff ℝ ∞ (rowsCoeffs rf ru rk rm rp Q).K ∧
      ContDiff ℝ ∞ (rowsCoeffs rf ru rk rm rp Q).M ∧
      ContDiff ℝ ∞ (rowsCoeffs rf ru rk rm rp Q).P :=
  ⟨contDiff_famScalar hf, contDiff_famTen2 hu, contDiff_famTen4 hk, contDiff_famVec hm,
    contDiff_famVec hp⟩

theorem rowsCoeffs_equiv (hf : RowsOfRank rf 0) (hu : RowsOfRank ru 2) (hk : RowsOfRank rk 4)
    (hm : RowsOfRank rm 1) (hp : RowsOfRank rp 1) (O : Ten2) (hO : IsOrth5 O) (A : Ten2)
    (p : Ten1) (g : ℝ) :
    (rowsCoeffs rf ru rk rm rp Q).f (act2 O A, act1 O p, g) =
        (rowsCoeffs rf ru rk rm rp Q).f (A, p, g) ∧
      (rowsCoeffs rf ru rk rm rp Q).U (act2 O A, act1 O p, g) =
        act2 O ((rowsCoeffs rf ru rk rm rp Q).U (A, p, g)) ∧
      (rowsCoeffs rf ru rk rm rp Q).K (act2 O A, act1 O p, g) =
        act4 O ((rowsCoeffs rf ru rk rm rp Q).K (A, p, g)) ∧
      (rowsCoeffs rf ru rk rm rp Q).M (act2 O A, act1 O p, g) =
        act1 O ((rowsCoeffs rf ru rk rm rp Q).M (A, p, g)) ∧
      (rowsCoeffs rf ru rk rm rp Q).P (act2 O A, act1 O p, g) =
        act1 O ((rowsCoeffs rf ru rk rm rp Q).P (A, p, g)) :=
  ⟨famScalar_act hf hO A p g, famTen2_act hu hO A p g, famTen4_act hk hO A p g,
    famVec_act hm hO A p g, famVec_act hp hO A p g⟩

theorem rowsCoeffs_even_U (hu : RowsPlain ru) (he : ∀ t ∈ ru, Even t.2.pCount) (A : Ten2)
    (p : Ten1) (g : ℝ) :
    (rowsCoeffs rf ru rk rm rp Q).U (A, -p, g) = (rowsCoeffs rf ru rk rm rp Q).U (A, p, g) :=
  famTen2_neg hu he A p g

theorem rowsCoeffs_even_K (hk : RowsPlain rk) (he : ∀ t ∈ rk, Even t.2.pCount) (A : Ten2)
    (p : Ten1) (g : ℝ) :
    (rowsCoeffs rf ru rk rm rp Q).K (A, -p, g) = (rowsCoeffs rf ru rk rm rp Q).K (A, p, g) :=
  famTen4_neg hk he A p g

theorem rowsCoeffs_P_g_zero (hg : ∀ t ∈ rp, t.2.gPow ≠ 0) (A : Ten2) (p : Ten1) :
    (rowsCoeffs rf ru rk rm rp Q).P (A, p, 0) = 0 :=
  famVec_g_zero hg A p

end Structural


/-! ### Decidable checks on rows -/

/-- An endpoint is not a slot at or above `r`. -/
def Endpoint.slotLt (r : ℕ) : Endpoint → Bool
  | .slot i => i < r
  | _ => true

namespace Key

/-- Boolean check of `Key.Linear`. -/
def linearB (k : Key) : Bool :=
  (List.range k.rank).all (fun m => slotCount (.slot m) k.edges == 1) &&
    k.edges.all fun e => e.u.slotLt k.rank && e.v.slotLt k.rank

/-- Boolean check of `Key.Plain`. -/
def plainB (k : Key) : Bool :=
  !k.hasX && k.wPow == 0 && k.zPow == 0 && k.edges.all fun e => e.u != .ell && e.v != .ell

theorem linear_of_linearB {k : Key} (h : k.linearB = true) : k.Linear := by
  simp only [linearB, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  intro m
  split_ifs with hm
  · exact h.1 m hm
  · rw [slotCount, List.count_eq_zero]
    intro hmem
    obtain ⟨e, he, hx⟩ := List.mem_flatMap.1 hmem
    have := h.2 e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx <;> simp [← hx, Endpoint.slotLt] at this <;> omega

theorem plain_of_plainB {k : Key} (h : k.plainB = true) : k.Plain := by
  simp only [plainB, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.all_eq_true,
    bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

end Key

/-- Boolean check of `RowsOfRank`. -/
def rowsOfRankB (rows : List (ℤ × Key)) (r : ℕ) : Bool :=
  rows.all fun t => t.2.plainB && t.2.linearB && t.2.rank == r

theorem rowsOfRank_of_check {rows : List (ℤ × Key)} {r : ℕ} (h : rowsOfRankB rows r = true) :
    RowsOfRank rows r := by
  simp only [rowsOfRankB, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨fun t ht => Key.plain_of_plainB (h t ht).1.1,
    fun t ht => Key.linear_of_linearB (h t ht).1.2, fun t ht => (h t ht).2⟩

theorem even_pCount_of_check {rows : List (ℤ × Key)}
    (h : (rows.all fun t => t.2.pCount % 2 == 0) = true) : ∀ t ∈ rows, Even t.2.pCount := by
  simp only [List.all_eq_true, beq_iff_eq] at h
  exact fun t ht => Nat.even_iff.2 (h t ht)

theorem gPow_ne_zero_of_check {rows : List (ℤ × Key)}
    (h : (rows.all fun t => t.2.gPow != 0) = true) : ∀ t ∈ rows, t.2.gPow ≠ 0 := by
  simp only [List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact h

/-! ### A stub: the row `U = A` -/

/-- The single row `U_{jk} = A_{jk}`. -/
def stubRowsU : List (ℤ × Key) := [(1, ⟨2, 0, 0, 0, [], [⟨.slot 0, .slot 1, 1⟩]⟩)]

example : RowsOfRank stubRowsU 2 := rowsOfRank_of_check (by decide)

example : ∀ t ∈ stubRowsU, Even t.2.pCount := even_pCount_of_check (by decide)

end OnePhaseDimension.Certificate
