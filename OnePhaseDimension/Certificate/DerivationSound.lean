/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Derivation
public import OnePhaseDimension.Statements.Certificate
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Soundness of the graph derivative

For a key `k` without copies of `X`, `Key.evalFun k d ι` is the polynomial map
`(A, p, g) ↦ eval k` (the other data fixed). We prove:

* `Key.contDiff_evalFun`: it is smooth;
* `Key.sum_derivTerms_eq_Dl`: on admissible data, the graph derivative `Key.derivTerms`
  evaluates to `D_l (evalFun k)`, the derivative of the polynomial map along the generator
  `(X_l - q_l A, w A_{l·} - g z δ_{l·}, z p_l)` (`OnePhaseDimension.Dl`), with `l = ι k.rank`.

The derivative is computed along the line `t ↦ (A, p, g) + t · gen` by the one-variable
product rule.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

open Finset

/-! ### Line derivatives of matrix powers and of products -/

theorem hasDerivAt_line_apply (A E : Matrix (Fin 5) (Fin 5) ℝ) (a b : Fin 5) :
    HasDerivAt (fun t : ℝ => (A + t • E) a b) (E a b) 0 := by
  have : (fun t : ℝ => (A + t • E) a b) = fun t => A a b + t * E a b := by
    funext t; simp
  rw [this]
  convert ((hasDerivAt_id (0 : ℝ)).mul_const (E a b)).const_add (A a b) using 1
  · rfl
  · rw [one_mul]

/-- The derivative of a matrix power along a line: `Σ_{h<k} A^h E A^{k-1-h}`. -/
def powDeriv (A E : Matrix (Fin 5) (Fin 5) ℝ) (k : ℕ) : Matrix (Fin 5) (Fin 5) ℝ :=
  ∑ h ∈ range k, A ^ h * E * A ^ (k - 1 - h)

theorem powDeriv_succ (A E : Matrix (Fin 5) (Fin 5) ℝ) (k : ℕ) :
    powDeriv A E (k + 1) = powDeriv A E k * A + A ^ k * E := by
  rw [powDeriv, sum_range_succ, powDeriv, Finset.sum_mul]
  congr 1
  · refine sum_congr rfl fun h hh => ?_
    rw [mem_range] at hh
    rw [show k + 1 - 1 - h = k - 1 - h + 1 by omega, pow_succ]
    simp only [Matrix.mul_assoc]
  · simp

theorem hasDerivAt_pow_apply (A E : Matrix (Fin 5) (Fin 5) ℝ) (k : ℕ) :
    ∀ a b : Fin 5, HasDerivAt (fun t : ℝ => ((A + t • E) ^ k) a b) (powDeriv A E k a b) 0 := by
  induction k with
  | zero => intro a b; simpa [powDeriv] using hasDerivAt_const (0 : ℝ) ((1 : Matrix _ _ ℝ) a b)
  | succ k ih =>
    intro a b
    have hf : (fun t : ℝ => ((A + t • E) ^ (k + 1)) a b) =
        fun t => ∑ c, ((A + t • E) ^ k) a c * (A + t • E) c b := by
      funext t; rw [pow_succ, Matrix.mul_apply]
    rw [hf]
    have := HasDerivAt.fun_sum (u := univ) fun c _ => (ih a c).mul (hasDerivAt_line_apply A E c b)
    convert this using 1
    simp only [zero_smul, add_zero, powDeriv_succ, Matrix.add_apply, Matrix.mul_apply,
      sum_add_distrib, Matrix.zero_apply]

/-- The product rule for a list of factors. -/
def listDeriv {κ : Type*} (f f' : κ → ℝ) : List κ → ℝ
  | [] => 0
  | i :: L => f' i * (L.map f).prod + f i * listDeriv f f' L

theorem hasDerivAt_list_prod {κ : Type*} (F : κ → ℝ → ℝ) (F' : κ → ℝ) :
    ∀ L : List κ, (∀ i ∈ L, HasDerivAt (F i) (F' i) 0) →
      HasDerivAt (fun t => (L.map fun i => F i t).prod) (listDeriv (fun i => F i 0) F' L) 0
  | [], _ => by simpa [listDeriv] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  | i :: L, h => by
    have := (h i (by simp)).mul (hasDerivAt_list_prod F F' L fun j hj => h j (by simp [hj]))
    convert this using 1
    · funext t; simp
    · rfl

theorem listDeriv_congr {κ : Type*} (f : κ → ℝ) {f' g' : κ → ℝ} :
    ∀ L : List κ, (∀ i ∈ L, f' i = g' i) → listDeriv f f' L = listDeriv f g' L
  | [], _ => rfl
  | i :: L, h => by
    simp only [listDeriv, h i (by simp), listDeriv_congr f L fun j hj => h j (by simp [hj])]

theorem listDeriv_sub {κ : Type*} (f f' g' : κ → ℝ) :
    ∀ L : List κ, listDeriv f (fun i => f' i - g' i) L = listDeriv f f' L - listDeriv f g' L
  | [] => by simp [listDeriv]
  | i :: L => by simp only [listDeriv, listDeriv_sub f f' g' L]; ring

theorem listDeriv_mul_self {κ : Type*} (f : κ → ℝ) (c : κ → ℝ) (q : ℝ) :
    ∀ L : List κ, listDeriv f (fun i => c i * q * f i) L = (L.map c).sum * q * (L.map f).prod
  | [] => by simp [listDeriv]
  | i :: L => by simp only [listDeriv, listDeriv_mul_self f c q L, List.map_cons,
      List.sum_cons, List.prod_cons]; ring


/-! ### The polynomial map of a key and the line along the generator -/

/-- The data with `(A, p, g)` replaced by `x`. -/
def CertData.withAPG (d : CertData) (x : Ten2 × Ten1 × ℝ) : CertData :=
  { d with A := Matrix.of x.1, p := x.2.1, g := x.2.2 }

/-- The value of a key as a function of `(A, p, g)`, the other data being fixed. -/
def Key.evalFun (k : Key) (d : CertData) (ι : ℕ → Fin 5) (x : Ten2 × Ten1 × ℝ) : ℝ :=
  k.eval (d.withAPG x) ι

section Line

variable (d : CertData) (l : Fin 5)

/-- The matrix component `X_l - q_l A` of the generator. -/
def genA : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of fun i j => d.X l i j - qVec d.X d.A l * d.A i j

/-- The vector component `w A_{l·} - g z δ_{l·}` of the generator. -/
def genP : Fin 5 → ℝ := fun i => d.w * d.A l i - d.g * d.z * kron l i

/-- The scalar component `z p_l` of the generator. -/
def genG : ℝ := d.z * d.p l

/-- The point `(A, p, g)` of the data. -/
def CertData.basePoint : Ten2 × Ten1 × ℝ := ((d.A : Ten2), d.p, d.g)

/-- The data along the line `t ↦ (A, p, g) + t · gen`. -/
def lineData (t : ℝ) : CertData :=
  d.withAPG (d.basePoint + t • gen d.A d.X d.p d.g d.w d.z l)

theorem lineData_A (t : ℝ) : (lineData d l t).A = d.A + t • genA d l := by
  ext i j
  rfl

theorem lineData_p (t : ℝ) : (lineData d l t).p = d.p + t • genP d l := by
  funext i; simp [lineData, CertData.withAPG, CertData.basePoint, gen, genP]

theorem lineData_g (t : ℝ) : (lineData d l t).g = d.g + t * genG d l := by
  simp [lineData, CertData.withAPG, CertData.basePoint, gen, genG]

@[simp] theorem lineData_ell (t : ℝ) : (lineData d l t).ell = d.ell := rfl
@[simp] theorem lineData_X (t : ℝ) : (lineData d l t).X = d.X := rfl
@[simp] theorem lineData_w (t : ℝ) : (lineData d l t).w = d.w := rfl
@[simp] theorem lineData_z (t : ℝ) : (lineData d l t).z = d.z := rfl

theorem lineData_zero : lineData d l 0 = d := by
  have hA := lineData_A d l 0
  have hp := lineData_p d l 0
  have hg := lineData_g d l 0
  simp only [zero_smul, add_zero, zero_mul] at hA hp hg
  cases d
  simp only [lineData, CertData.withAPG, CertData.mk.injEq] at hA hp hg ⊢
  simp_all

/-- The derivative of the weight of an endpoint along the line. -/
def weightDeriv (e : Endpoint) (a : Fin 5) : ℝ := if e = .p then genP d l a else 0

theorem hasDerivAt_weight (ι : ℕ → Fin 5) (e : Endpoint) (a : Fin 5) :
    HasDerivAt (fun t => (lineData d l t).weight ι e a) (weightDeriv d l e a) 0 := by
  cases e with
  | p =>
    simp only [CertData.weight, lineData_p, weightDeriv, ite_true, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    convert ((hasDerivAt_id (0 : ℝ)).mul_const (genP d l a)).const_add (d.p a) using 1
    · rfl
    · rw [one_mul]
  | ell => simpa [CertData.weight, weightDeriv] using hasDerivAt_const (0 : ℝ) (d.ell a)
  | x c => simpa [CertData.weight, weightDeriv] using hasDerivAt_const (0 : ℝ) (1 : ℝ)
  | slot i =>
    simpa [CertData.weight, weightDeriv] using
      hasDerivAt_const (0 : ℝ) (if a = ι i then (1 : ℝ) else 0)

/-- The derivative of the value of an edge along the line. -/
def valDeriv (ι : ℕ → Fin 5) (e : Edge) : ℝ :=
  ∑ a, ∑ b, ((weightDeriv d l e.u a * d.weight ι e.v b + d.weight ι e.u a * weightDeriv d l e.v b)
      * (d.A ^ e.pow) a b + d.weight ι e.u a * d.weight ι e.v b * powDeriv d.A (genA d l) e.pow a b)

theorem hasDerivAt_val (ι : ℕ → Fin 5) (e : Edge) :
    HasDerivAt (fun t => Edge.val (lineData d l t) ι e) (valDeriv d l ι e) 0 := by
  simp only [Edge.val, lineData_A]
  have := HasDerivAt.fun_sum (u := univ) fun a _ => HasDerivAt.fun_sum (u := univ) fun b _ =>
    ((hasDerivAt_weight d l ι e.u a).mul (hasDerivAt_weight d l ι e.v b)).mul
      (hasDerivAt_pow_apply d.A (genA d l) e.pow a b)
  convert this using 1
  simp only [valDeriv, Pi.mul_apply, lineData_zero, zero_smul, add_zero]

/-- The derivative of a trace factor along the line. -/
theorem hasDerivAt_trace (k : ℕ) :
    HasDerivAt (fun t => ((lineData d l t).A ^ k).trace) (powDeriv d.A (genA d l) k).trace 0 := by
  simp only [Matrix.trace, Matrix.diag, lineData_A]
  exact HasDerivAt.fun_sum fun a _ => hasDerivAt_pow_apply d.A (genA d l) k a a

end Line

/-! ### Smoothness -/

section Smooth

variable {n : WithTop ℕ∞}

theorem contDiff_list_prod {κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : κ → E → ℝ) : ∀ L : List κ, (∀ i ∈ L, ContDiff ℝ n (f i)) →
      ContDiff ℝ n (fun x => (L.map fun i => f i x).prod)
  | [], _ => by simpa using contDiff_const
  | i :: L, h => by
    simpa using (h i (by simp)).mul (contDiff_list_prod f L fun j hj => h j (by simp [hj]))

theorem contDiff_entry (a b : Fin 5) : ContDiff ℝ n fun x : Ten2 × Ten1 × ℝ => x.1 a b := by
  fun_prop

theorem contDiff_pow_apply (k : ℕ) :
    ∀ a b : Fin 5, ContDiff ℝ n fun x : Ten2 × Ten1 × ℝ => ((Matrix.of x.1) ^ k) a b := by
  induction k with
  | zero => intro a b; simpa using contDiff_const
  | succ k ih =>
    intro a b
    simp only [pow_succ, Matrix.mul_apply]
    exact ContDiff.sum fun c _ => (ih a c).mul (by simpa using contDiff_entry c b)

theorem contDiff_weight (d : CertData) (ι : ℕ → Fin 5) (e : Endpoint) (a : Fin 5) :
    ContDiff ℝ n fun x : Ten2 × Ten1 × ℝ => (d.withAPG x).weight ι e a := by
  cases e with
  | p => simp only [CertData.weight, CertData.withAPG]; fun_prop
  | _ => exact contDiff_const

theorem contDiff_val (d : CertData) (ι : ℕ → Fin 5) (e : Edge) :
    ContDiff ℝ n fun x : Ten2 × Ten1 × ℝ => Edge.val (d.withAPG x) ι e := by
  simp only [Edge.val]
  exact ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    ((contDiff_weight d ι e.u a).mul (contDiff_weight d ι e.v b)).mul
      (by simpa [CertData.withAPG] using contDiff_pow_apply e.pow a b)

theorem Key.contDiff_prefactor (k : Key) (d : CertData) :
    ContDiff ℝ n fun x : Ten2 × Ten1 × ℝ => k.prefactor (d.withAPG x) := by
  simp only [Key.prefactor]
  have h₁ : ContDiff ℝ n fun x : Ten2 × Ten1 × ℝ => (d.withAPG x).g ^ k.gPow := by
    simp only [CertData.withAPG]; fun_prop
  have h₂ : ContDiff ℝ n fun x : Ten2 × Ten1 × ℝ => (d.withAPG x).w ^ k.wPow := by
    simp only [CertData.withAPG]; exact contDiff_const
  have h₃ : ContDiff ℝ n fun x : Ten2 × Ten1 × ℝ => (d.withAPG x).z ^ k.zPow := by
    simp only [CertData.withAPG]; exact contDiff_const
  refine ((h₁.mul h₂).mul h₃).mul ?_
  exact contDiff_list_prod (fun t x => ((d.withAPG x).A ^ t).trace) _ fun t _ => by
    simp only [Matrix.trace, Matrix.diag, CertData.withAPG]
    exact ContDiff.sum fun a _ => contDiff_pow_apply t a a

/-- The polynomial map of a key without copies of `X` is smooth. -/
theorem Key.contDiff_evalFun {k : Key} (hk : k.hasX = false) (d : CertData) (ι : ℕ → Fin 5) :
    ContDiff ℝ n (k.evalFun d ι) := by
  have : k.evalFun d ι = fun x => k.prefactor (d.withAPG x) *
      (k.edges.map fun e => Edge.val (d.withAPG x) ι e).prod := by
    funext x; rw [Key.evalFun, Key.eval_eq_prod_of_hasX_eq_false hk]
  rw [this]
  exact (k.contDiff_prefactor d).mul
    (contDiff_list_prod (fun e x => Edge.val (d.withAPG x) ι e) _ fun e _ => contDiff_val d ι e)

end Smooth


/-! ### The derivative of the value of a key along the generator -/

/-- The derivative of the value of a key without `X` along the generator `gen` (index `l`),
written by the product rule over the factors `g^h`, the traces and the edges. -/
def Key.semDeriv (k : Key) (d : CertData) (ι : ℕ → Fin 5) (l : Fin 5) : ℝ :=
  ((k.gPow * d.g ^ (k.gPow - 1) * genG d l) * d.w ^ k.wPow * d.z ^ k.zPow *
      (k.traces.map fun t => (d.A ^ t).trace).prod +
    d.g ^ k.gPow * d.w ^ k.wPow * d.z ^ k.zPow *
      listDeriv (fun t => (d.A ^ t).trace) (fun t => (powDeriv d.A (genA d l) t).trace)
        k.traces) * (k.edges.map (Edge.val d ι)).prod +
  k.prefactor d * listDeriv (Edge.val d ι) (valDeriv d l ι) k.edges

theorem Key.hasDerivAt_eval {k : Key} (hk : k.hasX = false) (d : CertData) (ι : ℕ → Fin 5)
    (l : Fin 5) :
    HasDerivAt (fun t => k.eval (lineData d l t) ι) (k.semDeriv d ι l) 0 := by
  have hfun : (fun t => k.eval (lineData d l t) ι) = fun t =>
      ((lineData d l t).g ^ k.gPow * d.w ^ k.wPow * d.z ^ k.zPow *
        (k.traces.map fun i => ((lineData d l t).A ^ i).trace).prod) *
      (k.edges.map fun e => Edge.val (lineData d l t) ι e).prod := by
    funext t
    rw [Key.eval_eq_prod_of_hasX_eq_false hk, Key.prefactor]
    rfl
  rw [hfun]
  have hg : HasDerivAt (fun t => (lineData d l t).g ^ k.gPow)
      (k.gPow * d.g ^ (k.gPow - 1) * genG d l) 0 := by
    simp only [lineData_g]
    have h₁ : HasDerivAt (fun t : ℝ => d.g + t * genG d l) (genG d l) 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).mul_const (genG d l)).const_add d.g using 1
      · rfl
      · rw [one_mul]
    convert h₁.pow k.gPow using 1
    simp
  have htr := hasDerivAt_list_prod (fun i t => ((lineData d l t).A ^ i).trace)
    (fun i => (powDeriv d.A (genA d l) i).trace) k.traces fun i _ => hasDerivAt_trace d l i
  have hval := hasDerivAt_list_prod (fun e t => Edge.val (lineData d l t) ι e)
    (valDeriv d l ι) k.edges fun e _ => hasDerivAt_val d l ι e
  have := (((hg.mul_const (d.w ^ k.wPow)).mul_const (d.z ^ k.zPow)).mul htr).mul hval
  convert this using 1
  simp only [Key.semDeriv, Key.prefactor, Pi.mul_apply, lineData_zero]

/-- The directional derivative `D_l` (of the frozen statement) of the polynomial map of a key
without `X` is the product-rule expression `Key.semDeriv`. -/
theorem Key.Dl_evalFun {k : Key} (hk : k.hasX = false) (d : CertData) (ι : ℕ → Fin 5)
    (l : Fin 5) :
    Dl (k.evalFun d ι) d.A d.X d.p d.g d.w d.z l = k.semDeriv d ι l := by
  set v := gen d.A d.X d.p d.g d.w d.z l
  have hdiff : DifferentiableAt ℝ (k.evalFun d ι) d.basePoint :=
    ((k.contDiff_evalFun (n := 1) hk d ι).differentiable one_ne_zero).differentiableAt
  have hline : HasDerivAt (fun t : ℝ => d.basePoint + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add d.basePoint
  have h0 : d.basePoint + (0 : ℝ) • v = d.basePoint := by simp
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline h0.symm
  exact hcomp.unique (k.hasDerivAt_eval hk d ι l)


/-! ### The graph derivative evaluates to the product-rule expression -/

theorem list_sum_map_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_map_range f n,
      sum_range_succ]
    simp

section Graph

variable {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5)
include hd

/-- The matrix `X_l` with entries `X_{lij}`. -/
abbrev xMat (d : CertData) (l : Fin 5) : Matrix (Fin 5) (Fin 5) ℝ := Matrix.of fun i j => d.X l i j

omit hd in
theorem genA_eq (l : Fin 5) : genA d l = xMat d l - qVec d.X d.A l • d.A := by
  ext i j; simp [genA]

omit hd in
theorem powDeriv_genA (l : Fin 5) (k : ℕ) :
    powDeriv d.A (genA d l) k = powDeriv d.A (xMat d l) k - (k * qVec d.X d.A l) • d.A ^ k := by
  rw [genA_eq, powDeriv, powDeriv]
  simp only [Matrix.mul_sub, Matrix.sub_mul, sum_sub_distrib]
  congr 1
  have : ∀ h ∈ range k, d.A ^ h * (qVec d.X d.A l • d.A) * d.A ^ (k - 1 - h) =
      qVec d.X d.A l • d.A ^ k := by
    intro h hh
    rw [mem_range] at hh
    rw [Matrix.mul_smul, Matrix.smul_mul, ← pow_succ, ← pow_add,
      show h + 1 + (k - 1 - h) = k by omega]
  rw [sum_congr rfl this, sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]

/-- A path block is the matrix product `A^h X_l A^m` between its two ends. -/
theorem blockVal_pathBlock_eq {u v : Endpoint} (hu : u.isX = false) (hv : v.isX = false)
    (r h m : ℕ) :
    blockVal d ι (pathBlock r u v h m) = ∑ a, ∑ b, d.weight ι u a * d.weight ι v b *
      (d.A ^ h * xMat d (ι r) * d.A ^ m) a b := by
  rw [blockVal_pathBlock d ι hu hv]
  refine sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply, mul_sum, sum_mul]
  rw [Finset.sum_comm]
  calc _ = ∑ e, ∑ b, ∑ c, d.weight ι u a * (d.A ^ h) a c *
        (d.weight ι v b * (d.A ^ m) e b * d.X c e (ι r)) :=
        sum_congr rfl fun e _ => Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      refine sum_congr rfl fun b _ => sum_congr rfl fun e _ => sum_congr rfl fun c _ => ?_
      rw [hd.X_cycle c e (ι r)]
      ring

theorem sum_weight_powDeriv {e : Edge} (he : e.hasX = false) (r : ℕ) :
    ∑ a, ∑ b, d.weight ι e.u a * d.weight ι e.v b * powDeriv d.A (genA d (ι r)) e.pow a b =
      ∑ h ∈ range e.pow, blockVal d ι (pathBlock r e.u e.v h (e.pow - 1 - h)) -
        e.pow * qVec d.X d.A (ι r) * Edge.val d ι e := by
  simp only [Edge.hasX, Bool.or_eq_false_iff] at he
  simp only [powDeriv_genA, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, mul_sub,
    sum_sub_distrib, blockVal_pathBlock_eq hd ι he.1 he.2, Edge.val]
  congr 1
  · simp only [powDeriv, Matrix.sum_apply, mul_sum]
    exact (sum_congr rfl fun a _ => Finset.sum_comm).trans Finset.sum_comm
  · simp only [mul_sum]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

omit hd in
theorem val_slot_left (r : ℕ) (v : Endpoint) (n : ℕ) :
    Edge.val d ι ⟨.slot r, v, n⟩ = ∑ b, d.weight ι v b * (d.A ^ n) (ι r) b := by
  simp [Edge.val, CertData.weight, ite_mul, sum_ite_eq']

omit hd in
theorem val_slot_right (r : ℕ) (u : Endpoint) (n : ℕ) :
    Edge.val d ι ⟨u, .slot r, n⟩ = ∑ a, d.weight ι u a * (d.A ^ n) a (ι r) := by
  simp [Edge.val, CertData.weight, mul_ite, ite_mul, sum_ite_eq']

omit hd in
theorem sum_weightDeriv_left (r : ℕ) (v : Endpoint) (n : ℕ) :
    ∑ a, ∑ b, genP d (ι r) a * d.weight ι v b * (d.A ^ n) a b =
      d.w * Edge.val d ι ⟨.slot r, v, n + 1⟩ - d.g * d.z * Edge.val d ι ⟨.slot r, v, n⟩ := by
  rw [val_slot_left, val_slot_left, Finset.sum_comm]
  simp only [genP, kron, sub_mul, sum_sub_distrib, mul_sum, pow_succ', Matrix.mul_apply]
  congr 1
  · exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring
  · simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
    exact sum_congr rfl fun b _ => by ring

theorem sum_weightDeriv_right (r : ℕ) (u : Endpoint) (n : ℕ) :
    ∑ a, ∑ b, d.weight ι u a * genP d (ι r) b * (d.A ^ n) a b =
      d.w * Edge.val d ι ⟨u, .slot r, n + 1⟩ - d.g * d.z * Edge.val d ι ⟨u, .slot r, n⟩ := by
  rw [val_slot_right, val_slot_right]
  simp only [genP, kron, mul_sub, sub_mul, sum_sub_distrib, mul_sum, pow_succ,
    Matrix.mul_apply]
  congr 1
  · refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [hd.isSymm.apply b (ι r)]
    ring
  · simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
    exact sum_congr rfl fun a _ => by ring

end Graph


@[simp] theorem Endpoint.isX_slot (i : ℕ) : (Endpoint.slot i).isX = false := rfl
@[simp] theorem Endpoint.isX_p : Endpoint.p.isX = false := rfl

/-- The graph value of the derivative terms of one edge (without the `-q_l A` part). -/
def valPath (d : CertData) (ι : ℕ → Fin 5) (r : ℕ) (e : Edge) : ℝ :=
  ((edgeDeriv r e).map fun t => (t.1 : ℝ) * d.w ^ t.2.1 * (d.g * d.z) ^ t.2.2.1 *
    blockVal d ι t.2.2.2).sum

section Graph₂

variable {d : CertData} (hd : d.Admissible) (ι : ℕ → Fin 5)

omit hd in
theorem blockVal_single {e : Edge} (he : e.hasX = false) :
    blockVal d ι [e] = Edge.val d ι e := by
  rw [blockVal_of_hasX_eq_false d ι (by simpa using he)]
  simp

include hd in
theorem valDeriv_eq {e : Edge} (he : e.hasX = false) (r : ℕ) :
    valDeriv d (ι r) ι e = valPath d ι r e - e.pow * qVec d.X d.A (ι r) * Edge.val d ι e := by
  have he' := he
  simp only [Edge.hasX, Bool.or_eq_false_iff] at he'
  have hpath : ((List.range e.pow).map fun h => ((1 : ℤ) : ℝ) * d.w ^ 0 * (d.g * d.z) ^ 0 *
      blockVal d ι (pathBlock r e.u e.v h (e.pow - 1 - h))).sum =
      ∑ h ∈ range e.pow, blockVal d ι (pathBlock r e.u e.v h (e.pow - 1 - h)) := by
    rw [list_sum_map_range]; simp
  simp only [valDeriv, add_mul, sum_add_distrib, sum_weight_powDeriv hd ι he r]
  simp only [valPath, edgeDeriv, List.map_append, List.map_map, List.sum_append,
    Function.comp_def]
  rw [hpath]
  have h₁ : ∑ a, ∑ b, weightDeriv d (ι r) e.u a * d.weight ι e.v b * (d.A ^ e.pow) a b =
      if e.u = .p then d.w * Edge.val d ι ⟨.slot r, e.v, e.pow + 1⟩ -
        d.g * d.z * Edge.val d ι ⟨.slot r, e.v, e.pow⟩ else 0 := by
    split_ifs with h
    · simp only [weightDeriv, h, ite_true]; exact sum_weightDeriv_left ι r e.v e.pow
    · simp [weightDeriv, h]
  have h₂ : ∑ a, ∑ b, d.weight ι e.u a * weightDeriv d (ι r) e.v b * (d.A ^ e.pow) a b =
      if e.v = .p then d.w * Edge.val d ι ⟨e.u, .slot r, e.pow + 1⟩ -
        d.g * d.z * Edge.val d ι ⟨e.u, .slot r, e.pow⟩ else 0 := by
    split_ifs with h
    · simp only [weightDeriv, h, ite_true]; exact sum_weightDeriv_right hd ι r e.u e.pow
    · simp [weightDeriv, h]
  rw [h₁, h₂]
  by_cases hu : e.u = .p <;> by_cases hv : e.v = .p <;>
    simp [hu, hv, blockVal_single, Edge.hasX, he'.1, he'.2] <;> ring

include hd in
theorem trace_powDeriv_genA (r k : ℕ) :
    (powDeriv d.A (genA d (ι r)) k).trace =
      k * blockVal d ι (traceBlock r k) - k * qVec d.X d.A (ι r) * (d.A ^ k).trace := by
  rw [powDeriv_genA, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, blockVal_traceBlock]
  congr 1
  rw [powDeriv, Matrix.trace_sum]
  have : ∀ h ∈ range k, (d.A ^ h * xMat d (ι r) * d.A ^ (k - 1 - h)).trace =
      (d.A ^ (k - 1) * xMat d (ι r)).trace := by
    intro h hh
    rw [mem_range] at hh
    rw [Matrix.trace_mul_cycle, ← pow_add, show k - 1 - h + h = k - 1 by omega]
  rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [hd.X_cycle a b (ι r), hd.X_swap₂₃]

/-- The product rule over the edges, on the graph side. -/
theorem sum_edgesDeriv (r : ℕ) : ∀ L : List Edge,
    ((edgesDeriv r L).map fun t => (t.c : ℝ) * d.w ^ t.dw * (d.g * d.z) ^ t.dgz *
      ((t.free.map (Edge.val d ι)).prod * blockVal d ι t.block)).sum =
      listDeriv (Edge.val d ι) (valPath d ι r) L
  | [] => rfl
  | e :: es => by
    simp only [edgesDeriv, List.map_append, List.map_map, List.sum_append, Function.comp_def,
      List.map_cons, List.prod_cons, listDeriv]
    congr 1
    · rw [valPath, ← List.sum_map_mul_right]
      congr 1
      exact List.map_congr_left fun t _ => by ring
    · rw [← sum_edgesDeriv r es, ← List.sum_map_mul_left]
      congr 1
      exact List.map_congr_left fun t _ => by ring

/-- The product rule over the traces, on the graph side. -/
theorem sum_tracesDeriv (r : ℕ) : ∀ ts : List ℕ,
    ((tracesDeriv r ts).map fun t => (t.1 : ℝ) *
      ((t.2.1.map fun s => (d.A ^ s).trace).prod * blockVal d ι t.2.2)).sum =
      listDeriv (fun s => (d.A ^ s).trace) (fun s => s * blockVal d ι (traceBlock r s)) ts
  | [] => rfl
  | t :: ts => by
    simp only [tracesDeriv, List.map_cons, List.map_map, List.sum_cons, Function.comp_def,
      List.prod_cons, listDeriv, Int.cast_natCast]
    rw [← sum_tracesDeriv r ts, ← List.sum_map_mul_left]
    congr 1
    · ring
    · congr 1
      exact List.map_congr_left fun u _ => by ring

end Graph₂


/-! ### The keys of the derivative terms -/

theorem xCopiesIn_zero_iff (B : List Edge) :
    XCopiesIn {0} B ↔ ∀ f ∈ B, ∀ c, (f.u = .x c ∨ f.v = .x c) → c = 0 := by
  simp [XCopiesIn]

theorem ne_x_of_isX {e : Endpoint} (h : e.isX = false) (c : ℕ) : e ≠ .x c := by
  rintro rfl; simp [Endpoint.isX] at h

theorem xCopiesIn_edgeDeriv {r : ℕ} {e : Edge} (he : e.hasX = false)
    {s : ℤ × ℕ × ℕ × List Edge} (hs : s ∈ edgeDeriv r e) : XCopiesIn {0} s.2.2.2 := by
  simp only [Edge.hasX, Bool.or_eq_false_iff] at he
  have hu := ne_x_of_isX he.1
  have hv := ne_x_of_isX he.2
  rw [xCopiesIn_zero_iff]
  simp only [edgeDeriv, List.mem_append, List.mem_map, List.mem_range] at hs
  rcases hs with ⟨h, _, rfl⟩ | hs | hs
  · intro f hf c hc
    simp only [pathBlock, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;> simp_all
  · split_ifs at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> intro f hf c hc <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf <;> subst hf <;> simp_all
    · simp at hs
  · split_ifs at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> intro f hf c hc <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf <;> subst hf <;> simp_all
    · simp at hs

theorem mem_edgesDeriv (r : ℕ) : ∀ (L : List Edge) (t : DTerm), t ∈ edgesDeriv r L →
    (∀ f ∈ t.free, f ∈ L) ∧ ∃ e ∈ L, ∃ s ∈ edgeDeriv r e, t.block = s.2.2.2
  | [], _, h => by simp [edgesDeriv] at h
  | e :: es, t, h => by
    simp only [edgesDeriv, List.mem_append, List.mem_map] at h
    rcases h with ⟨s, hs, rfl⟩ | ⟨t', ht', rfl⟩
    · exact ⟨fun f hf => List.mem_cons_of_mem e hf, e, List.mem_cons_self, s, hs, rfl⟩
    · obtain ⟨h₁, e', he', s, hs, hb⟩ := mem_edgesDeriv r es t' ht'
      refine ⟨fun f hf => ?_, e', List.mem_cons_of_mem e he', s, hs, hb⟩
      rcases List.mem_cons.1 hf with rfl | hf
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem e (h₁ f hf)

theorem mem_tracesDeriv (r : ℕ) : ∀ (ts : List ℕ) (t : ℤ × List ℕ × List Edge),
    t ∈ tracesDeriv r ts → ∃ s, t.2.2 = traceBlock r s
  | [], _, h => by simp [tracesDeriv] at h
  | a :: ts, t, h => by
    simp only [tracesDeriv, List.mem_cons, List.mem_map] at h
    rcases h with rfl | ⟨u, hu, rfl⟩
    · exact ⟨a, rfl⟩
    · exact mem_tracesDeriv r ts u hu

theorem xCopiesIn_traceBlock (r s : ℕ) : XCopiesIn {0} (traceBlock r s) := by
  rw [xCopiesIn_zero_iff]
  intro f hf c hc
  simp only [traceBlock, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl <;> simp_all

theorem hasX_eq_false_of_mem {k : Key} (hk : k.hasX = false) {e : Edge} (he : e ∈ k.edges) :
    e.hasX = false := by
  simp only [Key.hasX, List.any_eq_false] at hk
  simpa using hk e he

section Terms

variable {k : Key} (hk : k.hasX = false) (d : CertData) (ι : ℕ → Fin 5)
include hk

theorem Key.eval_edgeTermKey {t : DTerm} (ht : t ∈ edgesDeriv k.rank k.edges) :
    (k.edgeTermKey t).eval d ι = k.prefactor d * d.w ^ t.dw * (d.g * d.z) ^ t.dgz *
      ((t.free.map (Edge.val d ι)).prod * blockVal d ι t.block) := by
  obtain ⟨h₁, e, he, s, hs, hb⟩ := mem_edgesDeriv k.rank k.edges t ht
  rw [Key.eval_free_append_block _ rfl (fun f hf => hasX_eq_false_of_mem hk (h₁ f hf))
    (hb ▸ xCopiesIn_edgeDeriv (hasX_eq_false_of_mem hk he) hs)]
  simp only [Key.edgeTermKey, Key.prefactor, pow_add, mul_pow]
  ring

theorem Key.eval_traceTermKey {t : ℤ × List ℕ × List Edge}
    (ht : t ∈ tracesDeriv k.rank k.traces) :
    (k.traceTermKey t).eval d ι = d.g ^ k.gPow * d.w ^ k.wPow * d.z ^ k.zPow *
      (t.2.1.map fun s => (d.A ^ s).trace).prod *
      ((k.edges.map (Edge.val d ι)).prod * blockVal d ι t.2.2) := by
  obtain ⟨s, hs⟩ := mem_tracesDeriv k.rank k.traces t ht
  rw [Key.eval_free_append_block _ rfl (fun f hf => hasX_eq_false_of_mem hk hf)
    (hs ▸ xCopiesIn_traceBlock k.rank s)]
  rfl

theorem Key.eval_gTermKey :
    k.gTermKey.eval d ι = d.g ^ (k.gPow - 1) * d.w ^ k.wPow * d.z ^ (k.zPow + 1) *
      (k.traces.map fun s => (d.A ^ s).trace).prod *
      ((k.edges.map (Edge.val d ι)).prod * d.p (ι k.rank)) := by
  rw [Key.eval_free_append_block _ rfl (fun f hf => hasX_eq_false_of_mem hk hf)
    (by
      rw [xCopiesIn_zero_iff]; intro f hf c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf; subst hf; simp at hc),
    blockVal_single ι rfl]
  simp [Key.gTermKey, Key.prefactor, Edge.val, CertData.weight, Matrix.one_apply]

theorem Key.eval_qTermKey (hd : d.Admissible) :
    k.qTermKey.eval d ι = k.prefactor d *
      ((k.edges.map (Edge.val d ι)).prod * qVec d.X d.A (ι k.rank)) := by
  rw [Key.eval_free_append_block _
    (show k.qTermKey.edges = k.edges ++ traceBlock k.rank 2 from rfl)
    (fun f hf => hasX_eq_false_of_mem hk hf) (xCopiesIn_traceBlock k.rank 2),
    blockVal_traceBlock]
  simp only [Key.qTermKey, Key.prefactor, qVec, pow_one, show 2 - 1 = 1 from rfl]
  congr 2
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [hd.X_cycle, mul_comm]

end Terms

theorem Key.degA_cast (k : Key) : (k.degA : ℝ) =
    (k.edges.map fun e => (e.pow : ℝ)).sum + (k.traces.map fun s : ℕ => (s : ℝ)).sum := by
  simp [Key.degA, Nat.cast_list_sum, List.map_map, Function.comp_def]

/-- **The graph derivative is sound.** For a key without copies of `X`, on admissible data, the
terms of `Key.derivTerms` evaluate to `D_l (evalFun k)` with `l = ι k.rank`. -/
theorem Key.sum_derivTerms_eq_Dl {k : Key} (hk : k.hasX = false) {d : CertData}
    (hd : d.Admissible) (ι : ℕ → Fin 5) :
    (k.derivTerms.map fun t => (t.1 : ℝ) * t.2.eval d ι).sum =
      Dl (k.evalFun d ι) d.A d.X d.p d.g d.w d.z (ι k.rank) := by
  rw [Key.Dl_evalFun hk d ι]
  have hS1 : ((edgesDeriv k.rank k.edges).map fun t => (t.c : ℝ) * (k.edgeTermKey t).eval d ι).sum =
      k.prefactor d * listDeriv (Edge.val d ι) (valPath d ι k.rank) k.edges := by
    rw [← sum_edgesDeriv ι k.rank k.edges, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [Key.eval_edgeTermKey hk d ι ht]
    ring
  have hS2 : ((tracesDeriv k.rank k.traces).map fun t =>
      (t.1 : ℝ) * (k.traceTermKey t).eval d ι).sum =
      d.g ^ k.gPow * d.w ^ k.wPow * d.z ^ k.zPow * (k.edges.map (Edge.val d ι)).prod *
        listDeriv (fun s => (d.A ^ s).trace) (fun s => s * blockVal d ι (traceBlock k.rank s))
          k.traces := by
    rw [← sum_tracesDeriv ι k.rank k.traces, ← List.sum_map_mul_left]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [Key.eval_traceTermKey hk d ι ht]
    ring
  have hval : listDeriv (Edge.val d ι) (valDeriv d (ι k.rank) ι) k.edges =
      listDeriv (Edge.val d ι) (valPath d ι k.rank) k.edges -
        (k.edges.map fun e => (e.pow : ℝ)).sum * qVec d.X d.A (ι k.rank) *
          (k.edges.map (Edge.val d ι)).prod := by
    rw [listDeriv_congr _ _ fun e he => valDeriv_eq hd ι (hasX_eq_false_of_mem hk he) k.rank,
      listDeriv_sub, listDeriv_mul_self]
  have htr : listDeriv (fun s => (d.A ^ s).trace)
      (fun s => (powDeriv d.A (genA d (ι k.rank)) s).trace) k.traces =
      listDeriv (fun s => (d.A ^ s).trace) (fun s => s * blockVal d ι (traceBlock k.rank s))
        k.traces - (k.traces.map fun s : ℕ => (s : ℝ)).sum * qVec d.X d.A (ι k.rank) *
          (k.traces.map fun s => (d.A ^ s).trace).prod := by
    rw [listDeriv_congr _ _ fun s _ => trace_powDeriv_genA hd ι k.rank s, listDeriv_sub,
      listDeriv_mul_self]
  simp only [Key.derivTerms, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hS1, hS2, Key.eval_gTermKey hk d ι,
    Key.eval_qTermKey hk d ι hd, Key.semDeriv, hval, htr, genG, Int.cast_natCast,
    Int.cast_neg, Key.degA_cast, List.map_map, Function.comp_def, Key.prefactor]
  rcases Nat.eq_zero_or_pos k.gPow with h0 | hpos
  · simp only [h0]; ring
  · obtain ⟨m, hm⟩ : ∃ m, k.gPow = m + 1 := ⟨k.gPow - 1, by omega⟩
    simp only [hm, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring


/-- The collected graph derivative `Key.deriv` evaluates to `D_l (evalFun k)`, provided every
reduced derivative term fits the packing. -/
theorem Key.eval_deriv {k : Key} (hk : k.hasX = false) {d : CertData} (hd : d.Admissible)
    (ι : ℕ → Fin 5) (hb : ∀ t ∈ k.derivTerms, t.2.reduce.2.boundedB = true) :
    k.deriv.eval d ι = Dl (k.evalFun d ι) d.A d.X d.p d.g d.w d.z (ι k.rank) := by
  rw [← Key.sum_derivTerms_eq_Dl hk hd ι, Key.deriv, Poly.eval_mergeAll, List.map_map]
  congr 1
  exact List.map_congr_left fun t ht => Key.eval_term t.1 t.2 (hb t ht) hd ι

/-! ### Linearity of `D_l` -/

section Linear

variable {F G : Ten2 × Ten1 × ℝ → ℝ} (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) (l : Fin 5)

theorem Dl_add (hF : DifferentiableAt ℝ F (A, p, g)) (hG : DifferentiableAt ℝ G (A, p, g)) :
    Dl (fun x => F x + G x) A X p g w z l = Dl F A X p g w z l + Dl G A X p g w z l := by
  simp only [Dl, fderiv_fun_add hF hG]
  rfl

theorem Dl_const_mul (c : ℝ) (hF : DifferentiableAt ℝ F (A, p, g)) :
    Dl (fun x => c * F x) A X p g w z l = c * Dl F A X p g w z l := by
  simp only [Dl, fderiv_const_mul hF c]
  rfl

theorem differentiableAt_list_sum {κ : Type*} (L : List κ) (f : κ → Ten2 × Ten1 × ℝ → ℝ)
    (c : κ → ℝ) (hf : ∀ i ∈ L, DifferentiableAt ℝ (f i) (A, p, g)) :
    DifferentiableAt ℝ (fun x => (L.map fun i => c i * f i x).sum) (A, p, g) := by
  induction L with
  | nil => simp
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hf i (by simp)).const_mul _).add (ih fun j hj => hf j (by simp [hj]))

theorem Dl_list_sum {κ : Type*} (L : List κ) (f : κ → Ten2 × Ten1 × ℝ → ℝ) (c : κ → ℝ)
    (hf : ∀ i ∈ L, DifferentiableAt ℝ (f i) (A, p, g)) :
    Dl (fun x => (L.map fun i => c i * f i x).sum) A X p g w z l =
      (L.map fun i => c i * Dl (f i) A X p g w z l).sum := by
  induction L with
  | nil => simp [Dl]
  | cons i L ih =>
    simp only [List.map_cons, List.sum_cons]
    have hi : DifferentiableAt ℝ (fun x => c i * f i x) (A, p, g) :=
      (hf i (by simp)).const_mul _
    have hL := differentiableAt_list_sum A p g L f c fun j hj => hf j (by simp [hj])
    rw [Dl_add A X p g w z l hi hL, Dl_const_mul A X p g w z l _ (hf i (by simp)),
      ih fun j hj => hf j (by simp [hj])]

end Linear

end OnePhaseDimension.Certificate
