/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Statements.Cone

/-!
# The exclusion statement

There is no working cone in `ℝ⁶`: neither an original nonflat minimizing cone with an isolated
singularity in `ℝ⁶`, nor the suspension of one in `ℝ⁵`. Together with the reduction to a working
cone and the classification in dimensions at most four, this excludes dimensions five and six as
the first dimension carrying a nonflat one-homogeneous global minimizer.
-/

@[expose] public section

namespace OnePhaseDimension

/-- There is no working cone. -/
def ExclusionStatement : Prop := IsEmpty WorkingCone

/-- There is no cone in `ℝⁿ` whose singular set is the origin: no nonflat minimizing cone in
`ℝⁿ` has an isolated singularity. -/
def OrigConeExclusionStatement (n : ℕ) : Prop := ∀ C : ConeData n, C.Sing = {0} → False

end OnePhaseDimension
