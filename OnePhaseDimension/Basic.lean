/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import EllipticBernoulli.Defs.Variational
public import EllipticBernoulli.Defs.Regularity

/-!
# Basic setting

The ambient space `E d = EuclideanSpace ℝ (Fin d)`, the positivity set, the free boundary, the
divergence, the Sobolev vocabulary, the energy `energyJ` and the local energy minimizers
`IsLocalEnergyMinimizer` are those of `EllipticBernoulli`. Throughout, the one-phase energy has
volume coefficient `Q ≡ 1`, so that `energyJ B 1 u G = ∫_B |G|² + 1_{u > 0}`.

## Competitor class

The 2026-09-24 version of the source defines a global minimizer by comparison with nonnegative
competitors `v ∈ H¹(B)`, `v - u ∈ H¹₀(B)`, on every ball `B`. We use
`IsLocalEnergyMinimizer Set.univ (fun _ ↦ 1) u`: comparison on every ball with arbitrary real
competitors in `H¹_loc(ℝᵈ)` that agree with `u` almost everywhere off the ball, together with the
separate hypothesis `u ≥ 0`. For nonnegative `u` the two notions agree, because replacing a
competitor `v` by its positive part does not increase the energy.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension

open EllipticBernoulli

end OnePhaseDimension
