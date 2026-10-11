/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Statements.CertificateGen

/-!
# Five-dimensional certificate data as generic data

At `m = 5` the dimension-generic certificate data and expressions coincide with the
five-dimensional ones: the coefficient `m` of `U_{jk}A_{jk}` is `5` and the Hardy constant
`((m - 1)/2)²` is `4`. Hence every five-dimensional certificate with constants `ε*, δ*` is a
generic certificate with `m = 5` (`CertificateHolds.toGen`).
-/

@[expose] public section

namespace OnePhaseDimension

/-- The Hardy constant of `S⁵` is `4`. -/
theorem Gen.hardyConst_five : Gen.hardyConst 5 = 4 := by norm_num [Gen.hardyConst]

namespace Coeffs

/-- Five-dimensional certificate data, viewed as generic data with `m = 5`. -/
def toGen (c : Coeffs) : Gen.Coeffs 5 := ⟨c.f, c.U, c.K, c.M, c.P⟩

variable (c : Coeffs)

theorem termZ_toGen (A : Ten2) (p : Ten1) (g z : ℝ) :
    c.toGen.termZ A p g z = c.termZ A p g z := by
  unfold Gen.Coeffs.termZ Coeffs.termZ
  rw [Gen.hardyConst_five, show ((5 : ℕ) : ℝ) = 5 by norm_num]
  rfl

/-- The generic interior expression at `m = 5` is the five-dimensional one. -/
theorem interiorExpr_toGen (A : Ten2) (X : Ten3) (p : Ten1) (g w z : ℝ) (ℓ : Ten1) :
    c.toGen.interiorExpr A X p g w z ℓ = c.interiorExpr A X p g w z ℓ := by
  unfold Gen.Coeffs.interiorExpr Coeffs.interiorExpr
  rw [termZ_toGen]
  rfl

/-- The generic boundary expression at `m = 5` is the five-dimensional one. -/
theorem boundaryExpr_toGen (A : Ten2) (p : Ten1) (lam : ℝ) :
    c.toGen.boundaryExpr A p lam = c.boundaryExpr A p lam :=
  rfl

end Coeffs

/-- A five-dimensional certificate is a generic certificate with `m = 5`, `ε = ε*`, `δ = δ*`. -/
theorem CertificateHolds.toGen {c : Coeffs} (h : CertificateHolds c) :
    Gen.CertificateHolds 5 εStar δStar c.toGen where
  smooth_f := h.smooth_f
  smooth_U := h.smooth_U
  smooth_K := h.smooth_K
  smooth_M := h.smooth_M
  smooth_P := h.smooth_P
  equiv_f := h.equiv_f
  equiv_U := h.equiv_U
  equiv_K := h.equiv_K
  equiv_M := h.equiv_M
  equiv_P := h.equiv_P
  even_U := h.even_U
  even_K := h.even_K
  P_g_zero := h.P_g_zero
  interior A X p g w z ℓ hA hA1 hX hpg := by
    rw [Coeffs.interiorExpr_toGen]
    exact h.interior A X p g w z ℓ hA hA1 hX hpg
  f_ge := h.f_ge
  boundary := h.boundary

end OnePhaseDimension
