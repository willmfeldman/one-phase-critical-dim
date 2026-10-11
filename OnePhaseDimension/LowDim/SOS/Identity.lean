/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.SOS.Gram
public import OnePhaseDimension.LowDim.SOS.Data.Blocks0
public import OnePhaseDimension.LowDim.SOS.Data.Blocks1
public import OnePhaseDimension.LowDim.SOS.Data.Blocks2
public import OnePhaseDimension.LowDim.SOS.Data.Blocks3
public import OnePhaseDimension.LowDim.SOS.Data.Mult0
public import OnePhaseDimension.LowDim.SOS.Data.QForm
public import OnePhaseDimension.LowDim.SOS.Data.Residual
public import OnePhaseDimension.LowDim.SOS.Data.Scale

/-!
# The certificate identity

In the variables `y = (α₀, α₁, p₀, p₁, p₂, g, v)`, `v = (w, z, ℓ₀, ℓ₁, ℓ₂, ξ₀, …, ξ₆)`, the
sum-of-squares certificate of the interior inequality in `ℝ³` at diagonal `A` is the identity

  `S Q − S/50 (z² + |ℓ|²) − S/1000 |v|²`
    `= S' ∑_k m_k ∑_{r,s} (L_k L_kᵀ)_{rs} b_r b_s + R + h Mult`

of polynomials with integer coefficients, where `S Q` is the scaled interior form
(`Data.qPoly`), `m_k ∈ {1, χ}` with `χ = 1 − |p|² − g²`, `L_k` are integer lower-triangular
matrices with basis monomials `b_r`, `R` is the residual (`Data.residualPoly`),
`h = 2α₀² + 2α₀α₁ + 2α₁² − 1 = |A|² − 1` and `Mult` is the multiplier of `h`
(`Data.multPoly0`). The data were found numerically; the identity is checked here by kernel
computation (`total_isNil`). That `S Q` is the interior expression is checked separately
(`interiorP_eq_qPoly`).
-/

@[expose] public section

namespace OnePhaseDimension.LowDim.SOS

open Data

/-- `χ = 1 - p₀² - p₁² - p₂² - g²` in the variables `y₂, …, y₅`. -/
noncomputable def chiPoly : Poly :=
  [([], 1), ([0, 0, 0, 0, 0, 2], -1), ([0, 0, 0, 0, 2], -1), ([0, 0, 0, 2], -1), ([0, 0, 2], -1)]

/-- `h = 2α₀² + 2α₀α₁ + 2α₁² - 1` in the variables `y₀, y₁`. -/
noncomputable def hPoly : Poly := [([], -1), ([0, 2], 2), ([1, 1], 2), ([2], 2)]

/-- `c · ∑_{j ∈ js} y_j²`. -/
noncomputable def sqPoly (c : ℤ) (js : List ℕ) : Poly :=
  Poly.mergeAll (Poly.lmap (fun j => [(Mono.mul (Mono.var j) (Mono.var j), c)]) js)

/-- All Gram blocks. -/
def blocks : List (Bool × List (ℕ × ℕ × List ℤ)) :=
  [block00, block01, block02, block03, block04, block05, block06, block07, block08, block09,
    block10, block11, block12, block13, block14, block15, block16, block17, block18]

/-- One block, scaled by `sc`, with its multiplier. -/
noncomputable def blockWithMult (sc : ℤ) (b : Bool × List (ℕ × ℕ × List ℤ)) : Poly :=
  Bool.rec (blockPoly sc b.2) (Poly.mul chiPoly (blockPoly sc b.2)) b.1

/-- The certificate identity, all terms on one side. -/
noncomputable def total : Poly :=
  Poly.mergeAll [ofData 1 qPoly,
    sqPoly (Int.negSucc (Nat.pred (Nat.div scale 50))) [7, 8, 9, 10],
    sqPoly (Int.negSucc (Nat.pred (Nat.div scale 1000)))
      [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17],
    Poly.mergeAll (Poly.lmap (blockWithMult (Int.negSucc (Nat.pred gramScale))) blocks),
    ofData (-1) residualPoly,
    Poly.mul hPoly (ofData (-1) multPoly0)]

set_option maxRecDepth 100000 in
theorem total_isNil : Poly.isNil total = true := by
  decide +kernel

end OnePhaseDimension.LowDim.SOS
