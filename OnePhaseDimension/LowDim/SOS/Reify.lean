/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.SOS.Poly
public import OnePhaseDimension.LowDim.CertificateThree.Explicit

/-!
# The interior polynomial of the certificate in `ℝ³` as a sparse polynomial

We mirror the tensor operations of the certificate in `ℝ³` (matrix–vector and matrix products,
outer products, inner products, the coefficients `U`, `M` and their directional derivatives) on
tensors whose entries are sparse polynomials (`Poly`). Each operation commutes with evaluation,
so that the polynomial `interiorP` built from polynomial inputs evaluates to `25000` times
`Gen.interiorPolyThree` at the evaluated inputs (`eval_interiorP`). The factor `25000` clears
all denominators: `1000 U`, `1000 D_l U`, `500 M` and `500 D_l M` have integer coefficients.

## Main definitions

* `LowDim.SOS.interiorP`: `25000 𝓘` as a polynomial in polynomial inputs.

## Main statements

* `LowDim.SOS.eval_interiorP`.
-/

@[expose] public section

namespace OnePhaseDimension.LowDim.SOS

open Gen Gen.CertThree

/-- A vector of polynomials. -/
abbrev PV := Fin 3 → Poly
/-- A matrix of polynomials. -/
abbrev PM := Fin 3 → Fin 3 → Poly
/-- A three-tensor of polynomials. -/
abbrev PT := Fin 3 → Fin 3 → Fin 3 → Poly

section Ops

variable (y : ℕ → ℝ)

/-- Entrywise evaluation of a vector. -/
noncomputable def evV (u : PV) : Gen.Ten1 3 := fun i ↦ (u i).eval y
/-- Entrywise evaluation of a matrix. -/
noncomputable def evM (A : PM) : Gen.Ten2 3 := fun i j ↦ (A i j).eval y
/-- Entrywise evaluation of a three-tensor. -/
noncomputable def evT (X : PT) : Gen.Ten3 3 := fun i j k ↦ (X i j k).eval y

/-- `P - Q`. -/
noncomputable def psub (P Q : Poly) : Poly := Poly.merge P (Poly.smul (-1) Q)

/-- `∑_{i<3} f i`. -/
noncomputable def sum3 (f : Fin 3 → Poly) : Poly := Poly.merge (f 0) (Poly.merge (f 1) (f 2))

theorem eval_psub (P Q : Poly) : (psub P Q).eval y = P.eval y - Q.eval y := by
  rw [psub, Poly.eval_merge, Poly.eval_smul]; push_cast; ring

theorem eval_sum3 (f : Fin 3 → Poly) : (sum3 f).eval y = ∑ i, (f i).eval y := by
  rw [sum3, Poly.eval_merge, Poly.eval_merge, Fin.sum_univ_three]; ring

/-- `Ap`. -/
noncomputable def matVecP (A : PM) (p : PV) : PV := fun i ↦ sum3 fun a ↦ Poly.mul (A i a) (p a)

/-- `AB`. -/
noncomputable def matMulP (A B : PM) : PM := fun i j ↦ sum3 fun a ↦ Poly.mul (A i a) (B a j)

/-- `u · v`. -/
noncomputable def dotP (u v : PV) : Poly := sum3 fun i ↦ Poly.mul (u i) (v i)

/-- `Ep + Av`. -/
noncomputable def matVecDirP (A : PM) (p : PV) (E : PM) (v : PV) : PV :=
  fun i ↦ Poly.merge (matVecP E p i) (matVecP A v i)

/-- `v · Ap + p · (Ep + Av)`. -/
noncomputable def quadFormDirP (A : PM) (p : PV) (E : PM) (v : PV) : Poly :=
  Poly.merge (dotP v (matVecP A p)) (dotP p (matVecDirP A p E v))

theorem evV_matVecP (A : PM) (p : PV) : evV y (matVecP A p) = matVec (evM y A) (evV y p) := by
  funext i
  simp only [evV, matVecP, eval_sum3, Poly.eval_mul, matVec, evM]

theorem evM_matMulP (A B : PM) : evM y (matMulP A B) = matMul (evM y A) (evM y B) := by
  funext i j
  simp only [evM, matMulP, eval_sum3, Poly.eval_mul, matMul]

theorem eval_dotP (u v : PV) : (dotP u v).eval y = dot (evV y u) (evV y v) := by
  simp only [dotP, eval_sum3, Poly.eval_mul, dot, evV]

theorem eval_dotP_self (u : PV) : (dotP u u).eval y = Gen.sq1 (evV y u) := by
  rw [eval_dotP, sq1_eq_dot]

theorem eval_quadFormP (A : PM) (p : PV) :
    (dotP p (matVecP A p)).eval y = quadForm (evM y A) (evV y p) := by
  rw [eval_dotP, evV_matVecP, quadForm]

theorem evV_matVecDirP (A : PM) (p : PV) (E : PM) (v : PV) :
    evV y (matVecDirP A p E v) = matVecDir (evM y A) (evV y p) (evM y E) (evV y v) := by
  funext i
  have h1 := congrFun (evV_matVecP y E p) i
  have h2 := congrFun (evV_matVecP y A v) i
  simp only [evV] at h1 h2 ⊢
  simp only [matVecDirP, Poly.eval_merge, h1, h2, matVecDir, Pi.add_apply]

theorem eval_quadFormDirP (A : PM) (p : PV) (E : PM) (v : PV) :
    (quadFormDirP A p E v).eval y
      = quadFormDir (evM y A) (evV y p) (evM y E) (evV y v) := by
  rw [quadFormDirP, Poly.eval_merge, eval_dotP, eval_dotP, evV_matVecP, evV_matVecDirP,
    quadFormDir]

end Ops

/-! ### The coefficients -/

/-- `1000 U_{jk}`. -/
noncomputable def coeffUP (A : PM) (p : PV) (j k : Fin 3) : Poly :=
  let Ap := matVecP A p
  let s := dotP p p
  Poly.merge (Poly.smul 197 (Poly.mul (p j) (p k)))
    (Poly.merge (Poly.smul (-135) (Poly.mul (p j) (Ap k)))
      (Poly.merge (Poly.smul 429 (Poly.mul (Ap j) (Ap k)))
        (Poly.merge
          (Poly.mul (Poly.merge (Poly.const 527)
            (Poly.merge (Poly.smul (-346) (dotP p Ap)) (Poly.smul (-1) s))) (A j k))
          (Poly.mul (Poly.merge (Poly.const 196) (Poly.smul (-425) s)) (matMulP A A j k)))))

/-- `1000 (D U)_{jk}` in the direction `(E, v)`. -/
noncomputable def coeffUDirP (A : PM) (p : PV) (E : PM) (v : PV) (j k : Fin 3) : Poly :=
  let Ap := matVecP A p
  let d := matVecDirP A p E v
  let s := dotP p p
  let pv := dotP p v
  Poly.merge (Poly.smul 197 (Poly.merge (Poly.mul (v j) (p k)) (Poly.mul (p j) (v k))))
    (Poly.merge (Poly.smul (-135) (Poly.merge (Poly.mul (v j) (Ap k)) (Poly.mul (p j) (d k))))
      (Poly.merge (Poly.smul 429 (Poly.merge (Poly.mul (d j) (Ap k)) (Poly.mul (Ap j) (d k))))
        (Poly.merge
          (Poly.mul (Poly.merge (Poly.const 527)
            (Poly.merge (Poly.smul (-346) (dotP p Ap)) (Poly.smul (-1) s))) (E j k))
          (Poly.merge
            (Poly.mul (Poly.merge (Poly.smul (-346) (quadFormDirP A p E v))
              (Poly.smul (-2) pv)) (A j k))
            (Poly.merge
              (Poly.mul (Poly.merge (Poly.const 196) (Poly.smul (-425) s))
                (Poly.merge (matMulP E A j k) (matMulP A E j k)))
              (Poly.mul (Poly.smul (-850) pv) (matMulP A A j k)))))))

/-- `500 M_l`. -/
noncomputable def coeffMP (A : PM) (p : PV) (l : Fin 3) : Poly :=
  Poly.merge (Poly.smul 39 (p l)) (Poly.smul 69 (matVecP A p l))

/-- `500 (D M)_l` in the direction `(E, v)`. -/
noncomputable def coeffMDirP (A : PM) (p : PV) (E : PM) (v : PV) (l : Fin 3) : Poly :=
  Poly.merge (Poly.smul 39 (v l)) (Poly.smul 69 (matVecDirP A p E v l))

section Coeffs

variable (y : ℕ → ℝ)

theorem eval_coeffUP (A : PM) (p : PV) (j k : Fin 3) :
    (coeffUP A p j k).eval y = 1000 * coeffU (evM y A) (evV y p) j k := by
  have h1 := congrFun (evV_matVecP y A p)
  have h2 := congrFun (congrFun (evM_matMulP y A A) j) k
  simp only [evV, evM] at h1 h2
  simp only [coeffUP, Poly.eval_merge, Poly.eval_smul, Poly.eval_mul, Poly.eval_const,
    eval_dotP_self, eval_dotP, evV_matVecP, h1, h2, coeffU_apply, quadForm]
  simp only [evV, evM]
  push_cast
  ring

theorem eval_coeffUDirP (A : PM) (p : PV) (E : PM) (v : PV) (j k : Fin 3) :
    (coeffUDirP A p E v j k).eval y
      = 1000 * coeffUDir (evM y A) (evV y p) (evM y E) (evV y v) j k := by
  have h1 := congrFun (evV_matVecP y A p)
  have h2 := congrFun (congrFun (evM_matMulP y A A) j) k
  have h3 := congrFun (congrFun (evM_matMulP y E A) j) k
  have h4 := congrFun (congrFun (evM_matMulP y A E) j) k
  have h5 := congrFun (evV_matVecDirP y A p E v)
  simp only [evV, evM] at h1 h2 h3 h4 h5
  simp only [coeffUDirP, Poly.eval_merge, Poly.eval_smul, Poly.eval_mul, Poly.eval_const,
    eval_dotP_self, eval_dotP, evV_matVecP, eval_quadFormDirP, h1, h2, h3, h4, h5]
  simp only [coeffUDir, outer, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, quadForm,
    evV, evM]
  push_cast
  ring

theorem eval_coeffMP (A : PM) (p : PV) (l : Fin 3) :
    (coeffMP A p l).eval y = 500 * coeffM (evM y A) (evV y p) l := by
  have h1 := congrFun (evV_matVecP y A p) l
  simp only [evV] at h1
  simp only [coeffMP, Poly.eval_merge, Poly.eval_smul, h1, coeffM_apply, evV]
  push_cast
  ring

theorem eval_coeffMDirP (A : PM) (p : PV) (E : PM) (v : PV) (l : Fin 3) :
    (coeffMDirP A p E v l).eval y
      = 500 * coeffMDir (evM y A) (evV y p) (evM y E) (evV y v) l := by
  have h1 := congrFun (evV_matVecDirP y A p E v) l
  simp only [evV] at h1
  simp only [coeffMDirP, Poly.eval_merge, Poly.eval_smul, h1, coeffMDir, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, evV]
  push_cast
  ring

end Coeffs

/-! ### The interior polynomial -/

/-- `q_l = X_{lij} A_{ij}`. -/
noncomputable def qVecP (X : PT) (A : PM) (l : Fin 3) : Poly :=
  sum3 fun i ↦ sum3 fun j ↦ Poly.mul (X l i j) (A i j)

/-- `δ_{la}` as a polynomial. -/
noncomputable def kronP (l a : Fin 3) : Poly := Bool.rec [] (Poly.const 1) (Nat.beq l.val a.val)

/-- The direction `E = X_l − q_l A` of the generator. -/
noncomputable def dirEP (X : PT) (A : PM) (l : Fin 3) : PM :=
  fun a b ↦ psub (X l a b) (Poly.mul (qVecP X A l) (A a b))

/-- The direction `v = w A_{l·} − g z δ_{l·}` of the generator. -/
noncomputable def dirVP (A : PM) (g w z : Poly) (l : Fin 3) : PV :=
  fun a ↦ psub (Poly.mul w (A l a)) (Poly.mul (Poly.mul g z) (kronP l a))

/-- `25000 𝓘`, the interior expression of the certificate in `ℝ³` times `25000`. -/
noncomputable def interiorP (A : PM) (X : PT) (p : PV) (g w z : Poly) (ℓ : PV) : Poly :=
  Poly.merge
    (Poly.mul (Poly.mul z z)
      (psub (Poly.smul 75 (sum3 fun j ↦ sum3 fun k ↦ Poly.mul (coeffUP A p j k) (A j k)))
        (Poly.const 25000)))
    (Poly.merge
      (sum3 fun l ↦ sum3 fun j ↦ sum3 fun k ↦
        Poly.mul (Poly.merge (Poly.smul 25 (coeffUDirP A p (dirEP X A l) (dirVP A g w z l) j k))
          (Poly.smul 4 (Poly.mul (qVecP X A l) (coeffUP A p j k)))) (X l j k))
      (Poly.merge
        (Poly.mul w (sum3 fun l ↦
          Poly.merge (Poly.smul 50 (coeffMDirP A p (dirEP X A l) (dirVP A g w z l) l))
            (Poly.smul 108 (Poly.mul (qVecP X A l) (coeffMP A p l)))))
        (psub (Poly.smul 25000 (dotP ℓ ℓ))
          (Poly.smul 29000 (sum3 fun l ↦ Poly.mul (qVecP X A l) (ℓ l))))))

section Interior

variable (y : ℕ → ℝ)

theorem eval_qVecP (X : PT) (A : PM) (l : Fin 3) :
    (qVecP X A l).eval y = Gen.qVec (evT y X) (evM y A) l := by
  simp only [qVecP, eval_sum3, Poly.eval_mul, Gen.qVec, evT, evM]

theorem eval_kronP (l a : Fin 3) : (kronP l a).eval y = Gen.kron l a := by
  rw [kronP, Gen.kron]
  rcases h : Nat.beq l.val a.val <;> dsimp only
  · have : l ≠ a := fun hla => by
      subst hla
      rw [Nat.beq_refl] at h
      exact Bool.noConfusion h
    simp [this]
  · have : l = a := Fin.ext (Nat.eq_of_beq_eq_true h)
    simp [this]

theorem evM_dirEP (X : PT) (A : PM) (l : Fin 3) :
    evM y (dirEP X A l)
      = fun a b ↦ evT y X l a b - Gen.qVec (evT y X) (evM y A) l * evM y A a b := by
  funext a b
  simp only [evM, dirEP, eval_psub, Poly.eval_mul, eval_qVecP, evT]

theorem evV_dirVP (A : PM) (g w z : Poly) (l : Fin 3) :
    evV y (dirVP A g w z l)
      = fun a ↦ w.eval y * evM y A l a - g.eval y * z.eval y * Gen.kron l a := by
  funext a
  simp only [evV, dirVP, eval_psub, Poly.eval_mul, eval_kronP, evM]

/-- The polynomial `interiorP` evaluates to `25000 𝓘` at the evaluated inputs. -/
theorem eval_interiorP (A : PM) (X : PT) (p : PV) (g w z : Poly) (ℓ : PV) :
    (interiorP A X p g w z ℓ).eval y
      = 25000 * interiorPolyThree (evM y A) (evT y X) (evV y p) (g.eval y) (w.eval y)
          (z.eval y) (evV y ℓ) := by
  simp only [interiorP, Poly.eval_merge, Poly.eval_mul, Poly.eval_smul, Poly.eval_const,
    eval_psub, eval_sum3, eval_coeffUP, eval_coeffUDirP, eval_coeffMP, eval_coeffMDirP,
    eval_qVecP, evM_dirEP, evV_dirVP, eval_dotP_self]
  simp only [interiorPolyThree, Finset.sum_add_distrib,
    Fin.sum_univ_three, evM, evT, evV]
  push_cast
  ring

end Interior

end OnePhaseDimension.LowDim.SOS
