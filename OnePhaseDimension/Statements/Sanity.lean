/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Statements.Certificate
public import OnePhaseDimension.Statements.Cone

/-!
# Sanity checks on the statement vocabulary

Checks that the notation in the statements means what it should: `∇` is the gradient, `Δ` is the
trace of the Hessian in an orthonormal basis, `dropLast` keeps the first five coordinates, and
the derivative `Dl` along the generator gives `D_l g = z p_l` and `D_l p_i = w A_{li} - g z δ_{li}`.
-/

open scoped Gradient Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

example {n : ℕ} (F : E n → ℝ) (x : E n) : ∇ F x = gradient F x := rfl

/-- `Δ` is the Euclidean Laplacian: the trace of the Hessian in any orthonormal basis. -/
example {n : ℕ} (F : E n → ℝ) :
    Δ F = fun x ↦ ∑ i, iteratedFDeriv ℝ 2 F x ![EuclideanSpace.basisFun (Fin n) ℝ i,
      EuclideanSpace.basisFun (Fin n) ℝ i] :=
  InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis F _

/-- `dropLast` keeps the coordinates `0, …, 4`. -/
example (x : E 6) (i : Fin 5) : dropLast x i = x (Fin.castSucc i) := rfl

/-- `D_l g = z p_l`. -/
example (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) (l : Fin 5) :
    Dl (fun x : Ten2 × Ten1 × ℝ ↦ x.2.2) A X p g w z l = z * p l := by
  have h : (fun x : Ten2 × Ten1 × ℝ ↦ x.2.2) =
      (ContinuousLinearMap.snd ℝ Ten1 ℝ).comp (ContinuousLinearMap.snd ℝ Ten2 (Ten1 × ℝ)) := rfl
  simp only [Dl, h, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', gen]

/-- `D_l p_i = w A_{li} - g z δ_{li}`. -/
example (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) (l i : Fin 5) :
    Dl (fun x : Ten2 × Ten1 × ℝ ↦ x.2.1 i) A X p g w z l = w * A l i - g * z * kron l i := by
  have h : (fun x : Ten2 × Ten1 × ℝ ↦ x.2.1 i) =
      (ContinuousLinearMap.proj i).comp ((ContinuousLinearMap.fst ℝ Ten1 ℝ).comp
        (ContinuousLinearMap.snd ℝ Ten2 (Ten1 × ℝ))) := rfl
  simp only [Dl, h, ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', ContinuousLinearMap.coe_fst', ContinuousLinearMap.proj_apply, gen]

/-- The volume coefficient `1` of the energy satisfies `Q² = 1`. -/
example {d : ℕ} (x : E d) : (fun _ : E d ↦ (1 : ℝ)) x ^ 2 = 1 := by norm_num

/-- The certificate predicate typechecks on the zero data (where it is false). -/
example : Prop := CertificateHolds ⟨0, 0, 0, 0, 0⟩

end OnePhaseDimension
