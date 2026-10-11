/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.LowDim.DimTwo
public import OnePhaseDimension.LowDim.CertificateTwo
public import OnePhaseDimension.Cutoff.Original

/-!
# Flatness in dimension three

Every nonzero, nonnegative, one-homogeneous global minimizer of the one-phase energy in `ℝ³` is
flat. The proof is the argument of the six-dimensional case, run one dimension lower: by flatness
in `ℝ²`, a nonflat minimizer in `ℝ³` would produce a cone whose singular set is `{0}`, and the
exclusion of such cones in `ℝⁿ`, `n ≥ 3`, applies with the universal certificate on `ℝ²`.

The 2026-09-24 version cites the classification in dimensions at most four; here the case `d = 3`
is proved by the paper's own method.

## Main results

* `flatInDim_three`: minimizers in `ℝ³` are flat.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension

/-- There is no cone in `ℝ³` whose singular set is `{0}`. -/
theorem origConeExclusion_three : OrigConeExclusionStatement 3 :=
  Gen.origConeExclusion_of_certificate le_rfl Gen.certificateStatement_two

/-- **Flatness in dimension three.** Every nonzero, nonnegative, one-homogeneous global minimizer
of the one-phase energy in `ℝ³` is flat. -/
theorem flatInDim_three : FlatInDim 3 :=
  flatInDim_succ_of_exclusion (k := 2) (by norm_num) flatInDim_two origConeExclusion_three

end OnePhaseDimension
