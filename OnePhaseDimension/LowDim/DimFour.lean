/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.DimThree
public import OnePhaseDimension.LowDim.CertificateThree.Interior

/-!
# Flatness in dimension four

Every nonzero, nonnegative, one-homogeneous global minimizer of the one-phase energy in `ℝ⁴` is
flat. As in dimension three: by flatness in `ℝ³`, a nonflat minimizer in `ℝ⁴` would produce a cone
whose singular set is `{0}`, and the exclusion of such cones in `ℝⁿ`, `n ≥ 3`, applies with the
universal certificate on `ℝ³`.

The 2026-09-24 version cites the classification in dimensions at most four; here the case `d = 4`
is proved by the paper's own method, with a new certificate on `ℝ³`.

## Main results

* `flatInDim_four`: minimizers in `ℝ⁴` are flat.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension

/-- There is no cone in `ℝ⁴` whose singular set is `{0}`. -/
theorem origConeExclusion_four : OrigConeExclusionStatement 4 :=
  Gen.origConeExclusion_of_certificate (by norm_num) Gen.certificateStatement_three

/-- **Flatness in dimension four.** Every nonzero, nonnegative, one-homogeneous global minimizer
of the one-phase energy in `ℝ⁴` is flat. -/
theorem flatInDim_four : FlatInDim 4 :=
  flatInDim_succ_of_exclusion (k := 3) (by norm_num) flatInDim_three origConeExclusion_four

end OnePhaseDimension
