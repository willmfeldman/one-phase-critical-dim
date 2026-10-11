/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Topology.Connected.Basic

/-!
# The cone interface

`ConeData n` packages a one-homogeneous global minimizer `u` in `ℝⁿ` (its continuous
representative), a selected component `D` of `{u > 0}`, a closed dilation-invariant singular set
`Sing ∋ 0`, smooth one-sided charts at every point of `closure D \ Sing`, and a point of `D`
where the Hessian of `u` does not vanish.

`WorkingCone` is the six-dimensional working cone: either an original cone in `ℝ⁶` with an
isolated singularity, or the suspension `O × ℝ` of an original cone `O` in `ℝ⁵` with an isolated
singularity.

## Differences from the source

* The 2026-09-24 version works on the link `Ω = D ∩ S^{n-1}`, a compact manifold with boundary
  away from the singular points, whose positivity components are finitely many with pairwise
  disjoint closures. We use the Euclidean cone component `D` and record regularity through local
  charts: near each regular point of `closure D`, `u = max F 0` with `F` smooth, the positive side
  `{F > 0}` lies in `D`, `|∇F| = 1` on `{F = 0}`, and `ΔF = 0` on `{F > 0}`. The local
  separation of `D` from the other components is part of the chart.
* The 2026-09-24 version selects a nonflat component by `T ≢ 0` for the spherical Hessian
  `T = ∇²g + g Id` of `g = u|_{S^{n-1}}`. We use the ambient Hessian: `D²u x ≠ 0` for some
  `x ∈ D`. The two agree by the formula `D²u(ry) = r⁻¹ diag(0, T(y))`.
* All fields are pointwise (the continuous representative, one-homogeneous everywhere).

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

open Set
open scoped ContDiff Gradient Laplacian

@[expose] public noncomputable section

namespace OnePhaseDimension

open EllipticBernoulli

/-- A one-homogeneous global minimizer in `ℝⁿ` with a selected positivity component `D`, a
closed dilation-invariant singular set `Sing ∋ 0`, smooth one-sided charts at every point of
`closure D \ Sing`, and a point of `D` where the Hessian of `u` does not vanish. -/
structure ConeData (n : ℕ) where
  /-- The minimizer (its continuous representative). -/
  u : E n → ℝ
  nonneg : ∀ x, 0 ≤ u x
  continuous : Continuous u
  homog : ∀ r : ℝ, 0 < r → ∀ x, u (r • x) = r * u x
  minimizer : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u
  /-- A base point of the selected component. -/
  base : E n
  base_pos : 0 < u base
  /-- The selected component of `{u > 0}`. -/
  D : Set (E n)
  D_eq : D = connectedComponentIn {x | 0 < u x} base
  /-- The singular set: the vertex, and in the suspended case the axis. -/
  Sing : Set (E n)
  sing_closed : IsClosed Sing
  zero_mem_sing : (0 : E n) ∈ Sing
  sing_smul : ∀ r : ℝ, 0 < r → ∀ x ∈ Sing, r • x ∈ Sing
  /-- Smooth one-sided charts at the regular points of the closure of `D`: `u = max F 0` near
  `x₀` with `F` smooth, the positive side lies in `D`, `|∇F| = 1` on `{F = 0}` and `F` is
  harmonic on `{F > 0}`. -/
  chart : ∀ x₀ ∈ closure D \ Sing, ∃ U : Set (E n), IsOpen U ∧ x₀ ∈ U ∧
    ∃ F : E n → ℝ, ContDiffOn ℝ ∞ F U ∧ (∀ x ∈ U, u x = max (F x) 0) ∧
      (∀ x ∈ U, 0 < F x → x ∈ D) ∧ (∀ x ∈ U, F x = 0 → ‖∇ F x‖ = 1) ∧
      (∀ x ∈ U, 0 < F x → Δ F x = 0)
  /-- The Hessian of `u` does not vanish identically on `D`. -/
  nonflat : ∃ x ∈ D, iteratedFDeriv ℝ 2 u x ≠ 0

/-- Drop the last coordinate, `ℝ⁶ → ℝ⁵`. -/
def dropLast : E 6 →L[ℝ] E 5 :=
  LinearMap.toContinuousLinearMap
    ((WithLp.linearEquiv 2 ℝ (Fin 5 → ℝ)).symm.toLinearMap ∘ₗ
      LinearMap.funLeft ℝ ℝ (Fin.castSucc : Fin 5 → Fin 6) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).toLinearMap)

/-- `W` is the suspension `O × ℝ` of `O`: the function, the component and the singular set of
`W` are pulled back from `O` along the projection dropping the last coordinate. -/
structure IsSuspension (W : ConeData 6) (O : ConeData 5) : Prop where
  u_eq : ∀ x, W.u x = O.u (dropLast x)
  D_eq : W.D = dropLast ⁻¹' O.D
  sing_eq : W.Sing = dropLast ⁻¹' {0}

/-- The working cone in `ℝ⁶`: either an original cone with an isolated singularity, or the
suspension `W = O × ℝ` of an original cone `O` in `ℝ⁵` with an isolated singularity. -/
inductive WorkingCone : Type
  | orig (W : ConeData 6) (h : W.Sing = {0})
  | susp (O : ConeData 5) (hO : O.Sing = {0}) (W : ConeData 6) (hW : IsSuspension W O)

end OnePhaseDimension
