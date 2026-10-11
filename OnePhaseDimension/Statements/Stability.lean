/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Statements.Cone

/-!
# The stability statement, in volume-only form

For a cone `C : ConeData n`, a smooth compactly supported test `φ` and a `C¹` compactly supported
vector field `Y`, both supported away from the singular set: if at every regular boundary point
`x₀` of `D`, read through any chart `u = max F 0`,

  `⟨Y(x₀), N⟩ + H_E φ(x₀)² ≥ 0`, with `N = ∇F(x₀)` the inward unit normal and
  `H_E = -D²F(x₀)(N, N)`,

then `∫_D div Y ≤ ∫_D |∇φ|²`. Also defined: the flux functional `Flux_D(Q) = -∫_D div Q`.

## Differences from the source

The 2026-09-24 version states Euclidean stability as `∫_D |∇φ|² ≥ ∫_{∂D} H_E φ² dσ` for `φ` smooth
up to the regular boundary of `D`, and later combines it with the divergence theorem on the link.
We use the combined form above, which involves no surface measure: by the divergence theorem,
`∫_D div Y = -∫_{∂D} ⟨Y, N⟩ dσ ≤ ∫_{∂D} H_E φ² dσ`. Tests are smooth on the whole space.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open MeasureTheory
open scoped ContDiff Gradient

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-- The flux functional `Flux_D(Q) = -∫_D div Q`. -/
def fluxFunctional {n : ℕ} (D : Set (E n)) (Q : E n → E n) : ℝ := -∫ x in D, divergence Q x

/-- Volume-only stability: if `⟨Y, N⟩ + H_E φ² ≥ 0` at every regular boundary point of `D`,
with `N = ∇F` the inward unit normal and `H_E = -D²F(N, N)` read off any chart `u = max F 0`,
then `∫_D div Y ≤ ∫_D |∇φ|²`. -/
def StabilityStatement (n : ℕ) : Prop :=
  ∀ (C : ConeData n) (φ : E n → ℝ) (Y : E n → E n),
    ContDiff ℝ ∞ φ → ContDiff ℝ 1 Y → HasCompactSupport φ → HasCompactSupport Y →
    Disjoint (tsupport φ ∪ tsupport Y) C.Sing →
    (∀ x₀ ∈ frontier C.D \ C.Sing, ∀ (U : Set (E n)) (F : E n → ℝ), IsOpen U → x₀ ∈ U →
        ContDiffOn ℝ ∞ F U → (∀ x ∈ U, C.u x = max (F x) 0) → (∀ x ∈ U, 0 < F x → x ∈ C.D) →
        0 ≤ inner ℝ (Y x₀) (∇ F x₀)
          - fderiv ℝ (fun y ↦ fderiv ℝ F y) x₀ (∇ F x₀) (∇ F x₀) * φ x₀ ^ 2) →
    ∫ x in C.D, divergence Y x ≤ ∫ x in C.D, ‖∇ φ x‖ ^ 2

end OnePhaseDimension
