/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Boundary.DiagEval

/-!
# The boundary remainder and its eleven coefficients

The two boundary blocks of the second table (rank `-1`) have rows `(β_t, c_{t1}, …, c_{t5})` with
`β_t` an exponent vector in four variables. With `J_c(x) = Q⁻¹ ∑_t c_{tc} x^{β_t}` and
`Av F(x) = 24⁻¹ ∑_{σ ∈ S₄} F(x ∘ σ)`, the boundary Gram term is

  `Λ(x) = ∑_blocks ρ(x) Av(∑_c J_c²)(x)`, with `ρ = 1` (mode `I`) or `ρ = ∑ xᵢ` (mode `H`).

The remainder `E_b = Λ + 1/4 - 𝓢` is computed as a polynomial (`ebPoly`, scaled by `24 Q²`),
homogenized by `x^α ↦ x^α R^{⌊(5-|α|)/2⌋}` and compared in the kernel with
`∑_β (Q² e_β) ∑_{σ ∈ S₄} x^{σ·β}` for the eleven printed coefficients (`eb_eq`).
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Certificate.Boundary

open Poly4 Data

/-- The 24 permutations of `Fin 4`. -/
def perms4 : List (Fin 4 → Fin 4) :=
  [![0, 1, 2, 3], ![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![0, 3, 2, 1],
    ![1, 0, 2, 3], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 2, 3, 0], ![1, 3, 0, 2], ![1, 3, 2, 0],
    ![2, 0, 1, 3], ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![2, 3, 1, 0],
    ![3, 0, 1, 2], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 1, 2, 0], ![3, 2, 0, 1], ![3, 2, 1, 0]]

/-- The exponent vector of a four-digit word. -/
def wordMono (len word : ℕ) : Mono :=
  match wordDigits len word with
  | [a, b, c, d] => (a, b, c, d)
  | _ => 0

/-- The polynomial `Q J_c` of column `c` of a boundary block. -/
def jPoly (b : Block) (c : ℕ) : Poly4 :=
  ofList (b.rows.map fun r => (wordMono r.1 r.2.1, r.2.2.getD c 0))

/-- The polynomial `Q² ∑_c J_c²` of a boundary block (five columns). -/
def gramPoly (b : Block) : Poly4 :=
  Poly4.sum ((List.range 5).map fun c => Poly4.pow (jPoly b c) 2)

/-- The multiplier `ρ` of a boundary block: `1` in mode `I`, `∑ xᵢ = -λ` in mode `H`. -/
def rhoPoly (b : Block) : Poly4 :=
  if b.mode = .H then Poly4.sum ((List.finRange 4).map var) else const 1

/-- The polynomial `24 Q² Λ`. -/
def lamGramPoly : Poly4 :=
  Poly4.sum (tableIIBoundary.map fun b =>
    mul (rhoPoly b) (Poly4.sum (perms4.map fun σ => subst σ (gramPoly b))))

/-- The denominator `Q = 250000` as an integer. -/
def qInt : ℤ := 250000

/-- The polynomial `24 Q² E_b = 24 Q² Λ + 6 Q² - 24 Q (Q 𝓢)`. -/
def ebPoly : Poly4 :=
  Poly4.sum [lamGramPoly, const (6 * qInt ^ 2), smul (-24 * qInt) sPoly]

/-- The eleven printed coefficients `Q² e_β`. -/
def elevenCoeffs : List (Mono × ℤ) :=
  [((0, 0, 0, 4), -13479110), ((0, 0, 0, 5), 17712712), ((0, 0, 1, 3), -93201124),
    ((0, 0, 1, 4), 151038620), ((0, 0, 2, 2), -78543848), ((0, 0, 2, 3), 244636976),
    ((0, 1, 1, 2), -139986162), ((0, 1, 1, 3), 310091962), ((0, 1, 2, 2), 445177656),
    ((1, 1, 1, 1), -4861942), ((1, 1, 1, 2), 157995170)]

/-- The orbit sum `∑_{σ ∈ S₄} x^{σ·β}` (that is, `24 m_β`). -/
def orbitPoly (β : Mono) : Poly4 := ofList (perms4.map fun σ => (β.subst σ, 1))

/-- The polynomial `∑_β (Q² e_β) ∑_σ x^{σ·β}`. -/
def elevenPoly : Poly4 :=
  Poly4.sum (elevenCoeffs.map fun t => smul t.2 (orbitPoly t.1))

/-- **The eleven coefficients.** After homogenization, `24 Q² E_b` is the orbit-sum combination
of the eleven printed coefficients. Checked by the kernel. -/
theorem eb_eq : homog ebPoly = elevenPoly := by decide +kernel

/-- `Q² ∑_β |e_β| = 1656725282`. -/
theorem elevenCoeffs_abs_sum : (elevenCoeffs.map fun t => t.2.natAbs).sum = 1656725282 := by
  decide +kernel

end OnePhaseDimension.Certificate.Boundary
