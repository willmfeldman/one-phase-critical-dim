/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.SOS.Reify
public import OnePhaseDimension.LowDim.SOS.Gram
public import OnePhaseDimension.LowDim.SOS.Data.QForm
public import OnePhaseDimension.LowDim.SOS.Data.Scale

/-!
# The interior form at diagonal `A` computed in Lean

We evaluate the polynomial `interiorP` of the interior expression at the polynomial inputs

* `A = diag(y₀, y₁, −y₀ − y₁)`, `p = (y₂, y₃, y₄)`, `g = y₅`, `w = y₆`, `z = y₇`,
  `ℓ = (y₈, y₉, y₁₀)`,
* `X = ∑_s ξ_s Ẽ_s` with `ξ_s = y_{11+s}`, in the basis of symmetric trace-free three-tensors
  in `ℝ³` given by the coordinates `ξ = (X₁₁₂, X₂₂₂, X₁₁₁, X₁₂₂, X₀₁₁, X₀₂₂, X₀₁₂)`
  (`stfOfCoords`),

and check by kernel computation that `S/25000` times it is the scaled interior form
`Data.qPoly` used in the certificate identity (`interiorP_eq_qPoly`). Hence the polynomial
identity of the certificate is about the interior expression computed in Lean from its
definition, not about exported data (`eval_qPoly`).
-/

@[expose] public section

namespace OnePhaseDimension.LowDim.SOS

open Data

/-- The entry `i` of the vector `(a, b, c)`, by the recursor. -/
noncomputable def sel3 {α : Type} (a b c : α) (i : Fin 3) : α :=
  Nat.rec (motive := fun _ => α) a (fun n _ => Nat.rec (motive := fun _ => α) b (fun _ _ => c) n)
    i.val

theorem sel3_zero {α : Type} (a b c : α) : sel3 a b c 0 = a := rfl
theorem sel3_one {α : Type} (a b c : α) : sel3 a b c 1 = b := rfl
theorem sel3_two {α : Type} (a b c : α) : sel3 a b c 2 = c := rfl

/-- `−y_a − y_b`. -/
noncomputable def negSumP (a b : ℕ) : Poly :=
  Poly.merge (Poly.smul (-1) (Poly.var a)) (Poly.smul (-1) (Poly.var b))

/-- `ξ_s = y_{11+s}`. -/
noncomputable def xiP (s : ℕ) : Poly := Poly.var (Nat.add 11 s)

/-- `A = diag(y₀, y₁, −y₀ − y₁)`. -/
noncomputable def diagAP : PM := fun i j =>
  Bool.rec [] (sel3 (Poly.var 0) (Poly.var 1) (negSumP 0 1) i) (Nat.beq i.val j.val)

/-- The symmetric trace-free three-tensor with coordinates `ξ = y₁₁, …, y₁₇`. -/
noncomputable def stfXP : PT :=
  sel3
    (sel3 (sel3 (negSumP 15 16) (negSumP 13 14) (negSumP 11 12))
      (sel3 (negSumP 13 14) (xiP 4) (xiP 6)) (sel3 (negSumP 11 12) (xiP 6) (xiP 5)))
    (sel3 (sel3 (negSumP 13 14) (xiP 4) (xiP 6))
      (sel3 (xiP 4) (xiP 2) (xiP 0)) (sel3 (xiP 6) (xiP 0) (xiP 3)))
    (sel3 (sel3 (negSumP 11 12) (xiP 6) (xiP 5))
      (sel3 (xiP 6) (xiP 0) (xiP 3)) (sel3 (xiP 5) (xiP 3) (xiP 1)))

/-- `p = (y₂, y₃, y₄)`. -/
noncomputable def pP : PV := fun i => Poly.var (Nat.add 2 i.val)

/-- `ℓ = (y₈, y₉, y₁₀)`. -/
noncomputable def ellP : PV := fun i => Poly.var (Nat.add 8 i.val)

/-- `25000 𝓘` at the polynomial inputs. -/
noncomputable def interiorDiagP : Poly :=
  interiorP diagAP stfXP pP (Poly.var 5) (Poly.var 6) (Poly.var 7) ellP

set_option maxRecDepth 100000 in
/-- `S/25000 · 25000 𝓘 − S Q = 0`, by kernel computation. -/
theorem interiorP_eq_qPoly :
    Poly.isNil (Poly.merge (Poly.smul (Int.ofNat (Nat.div scale 25000)) interiorDiagP)
      (ofData (-1) qPoly)) = true := by
  decide +kernel

end OnePhaseDimension.LowDim.SOS
