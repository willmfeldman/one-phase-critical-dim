/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import EllipticBernoulli.Variational.EnergyMinimizer

/-!
# Lipschitz representative of a minimizer

A nonnegative local minimizer of the one-phase energy in `ℝᵈ`, `d ≥ 2`, has a locally Lipschitz,
everywhere nonnegative representative that is smooth and harmonic in its positivity set. It is
proved in elliptic-bernoulli-foundations (`exists_regular_representative_univ`).

## References

* H. W. Alt, L. A. Caffarelli, *Existence and regularity for a minimum problem with free
  boundary*, J. Reine Angew. Math. 325 (1981).
* B. Velichkov, *Regularity of the One-phase Free Boundaries*, Lecture Notes of the Unione
  Matematica Italiana 28, Springer (2023), Theorem 3.1.
-/

open MeasureTheory
open scoped ContDiff Laplacian

@[expose] public section

namespace OnePhaseDimension.Registry

open EllipticBernoulli

/-- A nonnegative local minimizer of the one-phase energy in `ℝᵈ`, `d ≥ 2`, has a representative
that is locally Lipschitz, nonnegative everywhere, and smooth and harmonic in its positivity set
(Alt–Caffarelli 1981; Velichkov 2023, Theorem 3.1; harmonicity from the first variation and
Weyl's lemma). -/
theorem exists_continuous_representative {d : ℕ} (hd : 2 ≤ d) {u : E d → ℝ}
    (hnn : ∀ᵐ x ∂(volume : Measure (E d)), 0 ≤ u x)
    (hmin : IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u) :
    ∃ v : E d → ℝ, v =ᵐ[volume] u ∧ LocallyLipschitz v ∧ (∀ x, 0 ≤ v x) ∧
      ContDiffOn ℝ ∞ v {x | 0 < v x} ∧ (∀ x, 0 < v x → Δ v x = 0) := by
  have _ : 2 ≤ d := hd  -- the regularity theorem holds in every dimension
  exact exists_regular_representative_univ hnn hmin

end OnePhaseDimension.Registry
