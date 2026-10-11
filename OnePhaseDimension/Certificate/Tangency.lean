/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.DerivationSound

/-!
# Tangency of the generator to the constraint set

On the constraint set (`A` symmetric, trace-free, `|A|² = 1`; `X` symmetric and trace-free) the
matrix component `X_l - q_l A` of the generator is trace-free and orthogonal to `A`, so
`D_l tr A = 0` and `D_l |A|² = 2 q_l - 2 q_l |A|² = 0` (the 2026-09-24 version, Section "Exact
contraction and differentiation rules"). Consequently the trace reductions
`tr A⁰ = 5`, `tr A = 0`, `tr A² = 1` may be applied before differentiating:
`Key.Dl_evalFun_reduceTraces`.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate

open Finset

/-- `D_l F` is the derivative of `F` along the line through `(A, p, g)` in the direction of the
generator. -/
theorem Dl_eq_of_hasDerivAt {F : Ten2 × Ten1 × ℝ → ℝ} {A : Ten2} {X : Ten3} {p : Ten1}
    {g w z : ℝ} {l : Fin 5} {D : ℝ} (hF : DifferentiableAt ℝ F (A, p, g))
    (hD : HasDerivAt (fun t : ℝ => F ((A, p, g) + t • gen A X p g w z l)) D 0) :
    Dl F A X p g w z l = D := by
  have hline : HasDerivAt (fun t : ℝ => (A, p, g) + t • gen A X p g w z l)
      (gen A X p g w z l) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (gen A X p g w z l)).const_add (A, p, g)
  exact (hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)).unique hD

section Frozen

variable {A : Ten2} {X : Ten3} {p : Ten1} {g w z : ℝ} (l : Fin 5)

theorem sum_X_self (hX : IsSTF3 X) : ∑ i, X l i i = 0 := by
  rw [← hX.2.2 l]
  exact sum_congr rfl fun i _ => by rw [hX.1, hX.2.1]

/-- The matrix component of the generator is trace-free. -/
theorem trace_gen (hA : IsSTF2 A) (hX : IsSTF3 X) :
    ∑ i, (gen A X p g w z l).1 i i = 0 := by
  simp only [gen, sum_sub_distrib, ← mul_sum, hA.2, mul_zero, sub_zero, sum_X_self l hX]

/-- The matrix component of the generator is orthogonal to `A`. -/
theorem inner_gen (hA1 : sq2 A = 1) :
    ∑ i, ∑ j, (gen A X p g w z l).1 i j * A i j = 0 := by
  simp only [gen, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum, ← sq]
  rw [show (∑ i, ∑ j, A i j ^ 2) = sq2 A from rfl, hA1, mul_one]
  simp [qVec]

/-- The trace as a function of `(A, p, g)`. -/
def trFun (x : Ten2 × Ten1 × ℝ) : ℝ := ∑ i, x.1 i i

/-- The squared norm `|A|²` as a function of `(A, p, g)`. -/
def sqFun (x : Ten2 × Ten1 × ℝ) : ℝ := sq2 x.1

/-- `D_l tr A = 0` on the constraint set. -/
theorem Dl_trFun (hA : IsSTF2 A) (hX : IsSTF3 X) : Dl trFun A X p g w z l = 0 := by
  rw [← trace_gen (p := p) (g := g) (w := w) (z := z) l hA hX]
  refine Dl_eq_of_hasDerivAt (by unfold trFun; fun_prop) ?_
  simp only [trFun, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  refine HasDerivAt.fun_sum fun i _ => ?_
  convert ((hasDerivAt_id (0 : ℝ)).mul_const ((gen A X p g w z l).1 i i)).const_add (A i i)
    using 1
  · rfl
  · rw [one_mul]

/-- `D_l |A|² = 2 q_l - 2 q_l |A|² = 0` on the constraint set. -/
theorem Dl_sqFun (hA1 : sq2 A = 1) : Dl sqFun A X p g w z l = 0 := by
  have h := inner_gen (X := X) (p := p) (g := g) (w := w) (z := z) l hA1
  refine Dl_eq_of_hasDerivAt (D := ∑ i, ∑ j, 2 * (A i j * (gen A X p g w z l).1 i j))
    (by unfold sqFun sq2; fun_prop) ?_ |>.trans ?_
  · simp only [sqFun, sq2, Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    have hl : HasDerivAt (fun t : ℝ => A i j + t * (gen A X p g w z l).1 i j)
        ((gen A X p g w z l).1 i j) 0 := by
      convert ((hasDerivAt_id (0 : ℝ)).mul_const ((gen A X p g w z l).1 i j)).const_add
        (A i j) using 1
      · rfl
      · rw [one_mul]
    convert hl.pow 2 using 1
    simp
    ring
  · simp only [← mul_sum, mul_comm (A _ _)]
    rw [h, mul_zero]

end Frozen

/-! ### The trace reductions commute with differentiation -/

section Reduce

variable {d : CertData} (hd : d.Admissible) (l : Fin 5)
include hd

theorem trace_powDeriv_genA_eq_zero {t : ℕ} (ht : t ≤ 2) :
    (powDeriv d.A (genA d l) t).trace = 0 := by
  rw [trace_powDeriv_genA hd (fun _ => l) 0 t, blockVal_traceBlock]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
  · simp
  · simp only [Nat.sub_self, pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      sum_ite_eq, mem_univ, ite_true, pow_one, hd.trace_eq_zero, mul_zero, sub_zero]
    rw [show (∑ a, d.X a a l) = 0 from hd.X_trace l]
    simp
  · simp only [show 2 - 1 = 1 from rfl, pow_one, hd.trace_sq_eq_one, mul_one, qVec]
    rw [sub_eq_zero]
    congr 1
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [hd.X_cycle, mul_comm]

theorem listDeriv_reduceTraces : ∀ ts : List ℕ,
    listDeriv (fun t => (d.A ^ t).trace) (fun t => (powDeriv d.A (genA d l) t).trace) ts =
      ((Key.reduceTraces ts).1 : ℝ) * listDeriv (fun t => (d.A ^ t).trace)
        (fun t => (powDeriv d.A (genA d l) t).trace) (Key.reduceTraces ts).2
  | [] => by simp [Key.reduceTraces, listDeriv]
  | t :: ts => by
    have ih := listDeriv_reduceTraces ts
    have hp := reduceTraces_spec hd ts
    simp only [Key.reduceTraces, listDeriv]
    split_ifs with h0 h1 h2
    · subst h0
      rw [trace_powDeriv_genA_eq_zero hd l (by omega), ih]
      simp [Matrix.trace_one]; ring
    · subst h1
      rw [trace_powDeriv_genA_eq_zero hd l (by omega)]
      simp [hd.trace_eq_zero]
    · subst h2
      rw [trace_powDeriv_genA_eq_zero hd l (by omega), ih, hd.trace_sq_eq_one]
      ring
    · simp only [listDeriv, ih, hp]
      ring

end Reduce

/-- **Reducing traces before differentiating is sound.** On admissible data, `D_l` of a key
without `X` is the reduction factor times `D_l` of the key with its trace factors
`tr A⁰, tr A, tr A²` reduced. -/
theorem Key.Dl_evalFun_reduceTraces {k : Key} (hk : k.hasX = false) {d : CertData}
    (hd : d.Admissible) (ι : ℕ → Fin 5) (l : Fin 5) :
    Dl (k.evalFun d ι) d.A d.X d.p d.g d.w d.z l =
      (Key.reduceTraces k.traces).1 *
        Dl ({ k with traces := (Key.reduceTraces k.traces).2 }.evalFun d ι)
          d.A d.X d.p d.g d.w d.z l := by
  have hk' : ({ k with traces := (Key.reduceTraces k.traces).2 } : Key).hasX = false := hk
  rw [Key.Dl_evalFun hk d ι l, Key.Dl_evalFun hk' d ι l]
  simp only [Key.semDeriv, Key.prefactor, listDeriv_reduceTraces hd l k.traces,
    reduceTraces_spec hd k.traces]
  ring

end OnePhaseDimension.Certificate
