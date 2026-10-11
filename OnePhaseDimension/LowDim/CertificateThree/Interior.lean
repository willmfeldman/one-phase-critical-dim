/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.CertificateThree.Boundary
public import OnePhaseDimension.LowDim.SOS.Assembly
public import OnePhaseDimension.LowDim.SOS.InteriorCheck

/-!
# The interior inequality of the certificate in `ℝ³` at diagonal `A`

For `A = diag(α₀, α₁, −α₀ − α₁)` with `|A|² = 1`, every symmetric trace-free three-tensor `X`,
every `(p, g)` with `g² + |p|² ≤ 1` and all `w, z, ℓ`,

  `𝓘(A, X, p, g, w, z, ℓ) ≥ 1/50 · (z² + |ℓ|²)`.

The proof is a sum-of-squares certificate checked by kernel computation. Write
`X = ∑_s ξ_s Ẽ_s` in the coordinates `ξ = (X₁₁₂, X₂₂₂, X₁₁₁, X₁₂₂, X₀₁₁, X₀₂₂, X₀₁₂)` (a
symmetric trace-free three-tensor in `ℝ³` is determined by them, `stfOfCoords_coords`). With
`v = (w, z, ℓ, ξ) ∈ ℝ¹²` the expression `𝓘` is a quadratic form in `v` whose coefficients are
polynomials in `(α₀, α₁, p, g)`; it is computed in Lean (`interiorP_eq_qPoly`) and the identity

  `𝓘 − 1/50 (z² + |ℓ|²) − 1/1000 |v|² = ∑_k m_k ∑_i (L_k b_k)_i² + R + h · Mult`

(`m_k ∈ {1, χ}`, `χ = 1 − |p|² − g²`, `h = |A|² − 1`) is checked in the kernel
(`total_isNil`). The residual satisfies `|R| ≤ 1/1000 |v|²` on the domain.

## Main statements

* `Gen.certThree_interior_diag`: the interior inequality at diagonal `A`.
* `Gen.certThree_holds`, `Gen.certificateStatement_three`: with the boundary inequality at
  diagonal `A` and the reduction to diagonal `A`, the certificate in `ℝ³` holds.
-/

@[expose] public section

namespace OnePhaseDimension.LowDim.SOS

open Gen

/-- The symmetric trace-free three-tensor in `ℝ³` with coordinates
`ξ = (X₁₁₂, X₂₂₂, X₁₁₁, X₁₂₂, X₀₁₁, X₀₂₂, X₀₁₂)`. -/
noncomputable def stfOfCoords (ξ : Fin 7 → ℝ) : Gen.Ten3 3 :=
  ![![![-ξ 4 - ξ 5, -ξ 2 - ξ 3, -ξ 0 - ξ 1], ![-ξ 2 - ξ 3, ξ 4, ξ 6], ![-ξ 0 - ξ 1, ξ 6, ξ 5]],
    ![![-ξ 2 - ξ 3, ξ 4, ξ 6], ![ξ 4, ξ 2, ξ 0], ![ξ 6, ξ 0, ξ 3]],
    ![![-ξ 0 - ξ 1, ξ 6, ξ 5], ![ξ 6, ξ 0, ξ 3], ![ξ 5, ξ 3, ξ 1]]]

/-- The coordinates `(X₁₁₂, X₂₂₂, X₁₁₁, X₁₂₂, X₀₁₁, X₀₂₂, X₀₁₂)` of a three-tensor. -/
noncomputable def stfCoords (X : Gen.Ten3 3) : Fin 7 → ℝ :=
  ![X 1 1 2, X 2 2 2, X 1 1 1, X 1 2 2, X 0 1 1, X 0 2 2, X 0 1 2]

theorem stfOfCoords_coords {X : Gen.Ten3 3} (hX : Gen.IsSTF3 X) :
    stfOfCoords (stfCoords X) = X := by
  obtain ⟨h1, h2, h3⟩ := hX
  have t0 := h3 0
  have t1 := h3 1
  have t2 := h3 2
  simp only [Fin.sum_univ_three] at t0 t1 t2
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [stfOfCoords, stfCoords] <;>
    linarith [h1 0 1 0, h1 0 2 0, h1 0 1 1, h1 0 2 2, h1 0 1 2, h1 0 2 1, h1 1 2 0, h1 1 2 1,
      h1 1 2 2, h1 0 1 0, h2 0 0 1, h2 0 0 2, h2 0 1 2, h2 1 0 1, h2 1 0 2, h2 1 1 2, h2 2 0 1,
      h2 2 0 2, h2 2 1 2, h1 0 2 1]

/-- The variables `y = (α₀, α₁, p, g, w, z, ℓ, ξ)` of the certificate identity. -/
noncomputable def certVars (α₀ α₁ : ℝ) (p : Gen.Ten1 3) (g w z : ℝ) (ℓ : Gen.Ten1 3)
    (ξ : Fin 7 → ℝ) (i : ℕ) : ℝ :=
  [α₀, α₁, p 0, p 1, p 2, g, w, z, ℓ 0, ℓ 1, ℓ 2, ξ 0, ξ 1, ξ 2, ξ 3, ξ 4, ξ 5, ξ 6].getD i 0

section Inputs

variable (α₀ α₁ : ℝ) (p : Gen.Ten1 3) (g w z : ℝ) (ℓ : Gen.Ten1 3) (ξ : Fin 7 → ℝ)

theorem evM_diagAP :
    evM (certVars α₀ α₁ p g w z ℓ ξ) diagAP = Gen.CertThree.diag3 α₀ α₁ (-α₀ - α₁) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [evM, diagAP, sel3, negSumP, Gen.CertThree.diag3, certVars, Poly.eval_merge,
      Poly.eval_smul]
  ring

theorem evT_stfXP :
    evT (certVars α₀ α₁ p g w z ℓ ξ) stfXP = stfOfCoords ξ := by
  funext i j k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [evT, stfXP, sel3, negSumP, xiP, stfOfCoords, certVars, Poly.eval_merge,
      Poly.eval_smul] <;> ring

theorem evV_pP : evV (certVars α₀ α₁ p g w z ℓ ξ) pP = p := by
  funext i
  fin_cases i <;> simp [evV, pP, certVars]

theorem evV_ellP : evV (certVars α₀ α₁ p g w z ℓ ξ) ellP = ℓ := by
  funext i
  fin_cases i <;> simp [evV, ellP, certVars]

end Inputs

theorem eval_qPoly (y : ℕ → ℝ) :
    (ofData 1 Data.qPoly).eval y = (Data.scale : ℝ) / 25000 * interiorDiagP.eval y := by
  have h := congrArg (Poly.eval y) (Poly.eq_nil_of_isNil interiorP_eq_qPoly)
  rw [Poly.eval_merge, Poly.eval_smul, eval_ofData_neg, Poly.eval_nil] at h
  have hc : ((Int.ofNat (Nat.div Data.scale 25000) : ℤ) : ℝ) = (Data.scale : ℝ) / 25000 := by
    rw [Int.ofNat_eq_natCast, Int.cast_natCast, show Nat.div Data.scale 25000 = Data.scale / 25000
      from rfl, Nat.cast_div (Nat.dvd_of_mod_eq_zero (by decide +kernel)) (by norm_num)]
    norm_num
  rw [hc] at h
  linarith

end OnePhaseDimension.LowDim.SOS

namespace OnePhaseDimension.Gen

open LowDim.SOS CertThree

/-- The interior inequality of the certificate in `ℝ³` at diagonal `A = diag(α₀, α₁, −α₀ − α₁)`
with `|A|² = 1`: `𝓘 ≥ 1/50 (z² + |ℓ|²)` for symmetric trace-free `X` and `g² + |p|² ≤ 1`. -/
theorem certThree_interior_diag :
    ∀ α₀ α₁ : ℝ, α₀ ^ 2 + α₁ ^ 2 + (α₀ + α₁) ^ 2 = 1 → ∀ X p g w z ℓ, IsSTF3 X →
      g ^ 2 + sq1 p ≤ 1 →
        1 / 50 * (z ^ 2 + sq1 ℓ) ≤ interiorPolyThree (diag3 α₀ α₁ (-α₀ - α₁)) X p g w z ℓ := by
  intro α₀ α₁ hα X p g w z ℓ hX hpg
  set y := certVars α₀ α₁ p g w z ℓ (stfCoords X)
  have hI : interiorDiagP.eval y
      = 25000 * interiorPolyThree (diag3 α₀ α₁ (-α₀ - α₁)) X p g w z ℓ := by
    rw [interiorDiagP, eval_interiorP, evM_diagAP, evT_stfXP, stfOfCoords_coords hX, evV_pP,
      evV_ellP]
    simp [y, certVars]
  have hlow := qPoly_lower_bound y hα (by
    simp only [y, certVars, sq1, Fin.sum_univ_three] at hpg ⊢
    simpa [add_comm, add_left_comm, add_assoc] using hpg)
  rw [eval_qPoly, hI] at hlow
  have hS : (0 : ℝ) < Data.scale := by
    exact_mod_cast Nat.pos_of_ne_zero (by decide +kernel)
  have hℓ : y 7 ^ 2 + y 8 ^ 2 + y 9 ^ 2 + y 10 ^ 2 = z ^ 2 + sq1 ℓ := by
    simp only [y, certVars, sq1, Fin.sum_univ_three]
    simp
    ring
  rw [hℓ] at hlow
  generalize interiorPolyThree (diag3 α₀ α₁ (-α₀ - α₁)) X p g w z ℓ = I at hlow ⊢
  generalize (Data.scale : ℝ) = S at hlow hS
  have : S * (1 / 50 * (z ^ 2 + sq1 ℓ)) ≤ S * I := by nlinarith
  exact le_of_mul_le_mul_left this hS

/-- The certificate data `certThreeCoeffs` satisfies all properties with `ε = 1/50`,
`δ = 1/100`. -/
theorem certThree_holds : CertificateHolds 3 (1 / 50) (1 / 100) certThreeCoeffs :=
  certThree_holds_of_diag certThree_interior_diag certThree_boundary_diag

/-- The certificate in `ℝ³`. -/
theorem certificateStatement_three : CertificateStatement 3 :=
  ⟨1 / 50, 1 / 100, by norm_num, by norm_num, certThreeCoeffs, certThree_holds⟩

end OnePhaseDimension.Gen
