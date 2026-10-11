/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.CertificateThree.Rotation

/-!
# The boundary inequality of the certificate in `ℝ³`

After the rotation reduction, the boundary inequality of the certificate in `ℝ³` only has to be
checked for `A = diag(x₀, x₁, λ)` and `p = e₂`, where `x₀ + x₁ + λ = 0`, `x₀² + x₁² + λ² = 1`
and `λ < 0`. Writing `s = −λ > 0`, the two constraints give `x₀ + x₁ = s` and
`x₀ x₁ = s² − 1/2`, and `(x₀ − x₁)² = 2 − 3 s² ≥ 0` gives `3 s² ≤ 2`. The boundary polynomial
reduces to the quartic

  `𝓢(s) = 351/1000 s⁴ + 789/500 s³ − 267/400 s² − 211/250 s + 779/2000`,

and `𝓢(s) − 1/100 ≥ 0` on `0 ≤ s`, `3 s² ≤ 2` follows from the explicit certificate

  `𝓢(s) − 1/100 = σ₀(s) + a s (s − r)² + b (2/3 − s²)(s − r)²`

with `a = 2667/1000`, `b = 1636/1000`, `r = 534/1000` and `σ₀` a sum of squares, written as
`c (s² + α s + 1/10)² + γ (s + δ)² + ε` with `c, γ, ε > 0`.

## Main statements

* `Gen.boundaryPolyThree_diag3`: the boundary polynomial at `(diag(x₀, x₁, λ), e₂)` on the
  constraint set equals `𝓢(−λ)`.
* `Gen.boundaryQuartic_ge`: `1/100 ≤ 𝓢(s)` for `0 ≤ s`, `3 s² ≤ 2`.
* `Gen.certThree_boundary_diag`: the boundary inequality at diagonal `A` and `p = e₂`.
-/

@[expose] public noncomputable section

namespace OnePhaseDimension.Gen

open CertThree

/-- The quartic to which the boundary polynomial reduces, as a function of `s = −λ`. -/
def boundaryQuartic (s : ℝ) : ℝ :=
  351 / 1000 * s ^ 4 + 789 / 500 * s ^ 3 - 267 / 400 * s ^ 2 - 211 / 250 * s + 779 / 2000

/-- The boundary polynomial at `A = diag(x₀, x₁, λ)` and `p = e₂`, expanded. -/
theorem boundaryPolyThree_diag3_expand (x₀ x₁ lam : ℝ) :
    boundaryPolyThree (diag3 x₀ x₁ lam) e₂ lam =
      -173 / 500 * lam ^ 2 * (x₀ ^ 2 + x₁ ^ 2) - 73 / 500 * lam ^ 2
        + 117 / 1000 * lam * (x₀ ^ 3 + x₁ ^ 3) + 263 / 500 * lam * (x₀ ^ 2 + x₁ ^ 2)
        - 471 / 1000 * lam + 229 / 1000 * (x₀ ^ 4 + x₁ ^ 4) - 263 / 500 * (x₀ ^ 3 + x₁ ^ 3)
        + 11 / 40 := by
  simp [boundaryPolyThree, coeffU_apply, coeffM_apply, matVec, matMul, quadForm, dot, sq1, diag3,
    e₂, Fin.sum_univ_three]
  ring

/-- On the constraint set, the boundary polynomial at `(diag(x₀, x₁, λ), e₂)` is `𝓢(−λ)`. -/
theorem boundaryPolyThree_diag3 {x₀ x₁ lam : ℝ} (h₁ : x₀ + x₁ + lam = 0)
    (h₂ : x₀ ^ 2 + x₁ ^ 2 + lam ^ 2 = 1) :
    boundaryPolyThree (diag3 x₀ x₁ lam) e₂ lam = boundaryQuartic (-lam) := by
  rw [boundaryPolyThree_diag3_expand, boundaryQuartic]
  obtain rfl : x₁ = -x₀ - lam := by linarith
  linear_combination
    (229 / 1000 * x₀ ^ 2 + 229 / 1000 * x₀ * lam - 117 / 400 * lam ^ 2 + 263 / 200 * lam
      + 229 / 2000) * h₂

/-- `1/100 ≤ 𝓢(s)` for `0 ≤ s` and `3 s² ≤ 2`, by an explicit Positivstellensatz certificate. -/
theorem boundaryQuartic_ge {s : ℝ} (hs : 0 ≤ s) (hs2 : 3 * s ^ 2 ≤ 2) :
    1 / 100 ≤ boundaryQuartic s := by
  have h23 : 0 ≤ 2 / 3 - s ^ 2 := by linarith
  have k₁ := mul_nonneg hs (sq_nonneg (s - 534 / 1000))
  have k₂ := mul_nonneg h23 (sq_nonneg (s - 534 / 1000))
  have k₃ := sq_nonneg (s ^ 2 - 354531 / 496750 * s + 1 / 10)
  have k₄ := sq_nonneg (s - 232559849043 / 438693690224)
  rw [boundaryQuartic]
  linarith

/-- The boundary inequality of the certificate in `ℝ³` at `A = diag(x₀, x₁, λ)`, `p = e₂`. -/
theorem certThree_boundary_diag (x₀ x₁ lam : ℝ) (h₁ : x₀ + x₁ + lam = 0)
    (h₂ : x₀ ^ 2 + x₁ ^ 2 + lam ^ 2 = 1) (hlam : lam < 0) :
    1 / 100 ≤ boundaryPolyThree (diag3 x₀ x₁ lam) e₂ lam := by
  rw [boundaryPolyThree_diag3 h₁ h₂]
  refine boundaryQuartic_ge (by linarith) ?_
  have hx : x₁ = -x₀ - lam := by linarith
  subst hx
  nlinarith [sq_nonneg (2 * x₀ + lam)]

end OnePhaseDimension.Gen
