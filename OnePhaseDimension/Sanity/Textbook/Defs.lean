/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Textbook one-phase minimizers

A self-contained, textbook definition of a global minimizer of the one-phase Bernoulli energy
`J(v; B) = ∫_B |∇v|² + 1_{v > 0}` in `ℝᵈ`, written in plain Mathlib and independent of the
Sobolev vocabulary used elsewhere in the project. It follows the admissible class of Alt and
Caffarelli: on every ball `B`, `u ∈ H¹(B)` and `J(u; B) ≤ J(v; B)` for every `v ∈ H¹(B)` with
`v - u ∈ H¹₀(B)`.

* `partialDeriv i φ x`: the classical partial derivative `∂ᵢφ(x)`.
* `WeakGrad B f g`: `g` is the weak gradient of `f` on `B`, one coordinate at a time.
* `H1 B f g`: `f ∈ H¹(B)` with weak gradient `g`.
* `H10 B f g`: `f ∈ H¹₀(B)`, the `H¹(B)`-closure of `C_c^∞(B)`.
* `J B f g`: the real-valued energy `∫_B |g|² + 1_{f > 0}`.
* `TextbookMin u`: `u` is a global minimizer.

Weak gradients are carried as explicit data `g`, competitors may have any sign, and the energy is
a real Bochner integral (finite for `H¹(B)` functions on a ball). The `H¹₀` approximation is
measured coordinate by coordinate; this gives the same closure as the Euclidean norm of the
gradient, since all norms on `ℝᵈ` are equivalent.

## References

* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981), 105–144.
-/

open MeasureTheory Metric
open scoped ContDiff

@[expose] public section

noncomputable section

namespace OnePhaseDimension.Textbook

variable {d : ℕ}

/-- The classical partial derivative `∂ᵢφ(x)`: the derivative of `φ` at `x` in the direction of
the `i`-th standard basis vector. -/
def partialDeriv (i : Fin d) (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- `g` is the weak gradient of `f` on `B`, one coordinate at a time:
`∫_B f ∂ᵢφ = -∫_B gᵢ φ` for every `i` and every `φ ∈ C_c^∞(B)`. -/
def WeakGrad (B : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ i : Fin d, ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ ∞ φ →
    HasCompactSupport φ → tsupport φ ⊆ B →
      ∫ x in B, f x * partialDeriv i φ x = -∫ x in B, g x i * φ x

/-- `f ∈ H¹(B)` with weak gradient `g`: `f` and `g` are square integrable on `B` and `g` is the
weak gradient of `f` on `B`. -/
def H1 (B : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  MemLp f 2 (volume.restrict B) ∧ MemLp g 2 (volume.restrict B) ∧ WeakGrad B f g

/-- `f ∈ H¹₀(B)` with weak gradient `g`: `f ∈ H¹(B)` and `(f, g)` is an `H¹(B)` limit of
`(φ, ∇φ)` with `φ ∈ C_c^∞(B)`. -/
def H10 (B : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : Prop :=
  H1 B f g ∧ ∀ ε : ℝ, 0 < ε → ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ B ∧
      eLpNorm (fun x ↦ f x - φ x) 2 (volume.restrict B) < ENNReal.ofReal ε ∧
      ∀ i : Fin d,
        eLpNorm (fun x ↦ g x i - partialDeriv i φ x) 2 (volume.restrict B) < ENNReal.ofReal ε

/-- The one-phase energy `J(f; B) = ∫_B |g|² + 1_{f > 0}`, with the gradient supplied as `g`. -/
def J (B : Set (EuclideanSpace ℝ (Fin d))) (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ x in B, ‖g x‖ ^ 2 + (if 0 < f x then 1 else 0)

/-- `u` is a global minimizer of the one-phase energy in `ℝᵈ`: for some weak gradient `G`, on
every ball `B`, `u ∈ H¹(B)` and `J(u; B) ≤ J(v; B)` for every `v ∈ H¹(B)` (of any sign) with
`v - u ∈ H¹₀(B)`. -/
def TextbookMin (u : EuclideanSpace ℝ (Fin d) → ℝ) : Prop :=
  ∃ G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
    ∀ (c : EuclideanSpace ℝ (Fin d)) (r : ℝ), 0 < r →
      H1 (ball c r) u G ∧
        ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ)
          (V : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
          H1 (ball c r) v V → H10 (ball c r) (fun x ↦ v x - u x) (fun x ↦ V x - G x) →
            J (ball c r) u G ≤ J (ball c r) v V

end OnePhaseDimension.Textbook

end
