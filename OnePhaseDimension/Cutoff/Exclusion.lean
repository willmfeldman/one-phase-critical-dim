/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Cutoff.Suspended
public import OnePhaseDimension.Statements.Certificate
public import OnePhaseDimension.Statements.Exclusion

/-!
# The exclusion theorem

If the universal certificate holds, there is no working cone in `ℝ⁶`: neither an original cone
with an isolated singularity (`false_of_origCone6`) nor the suspension of an original cone in
`ℝ⁵` (`false_of_suspension`). In both cases the integrated comparison
`ε* ∫ ξ_j² w^{2a} ≤ ∫ (cut-off errors)` holds for every `j`, the errors tend to `0`, and the mass
tends to a positive limit.
-/

@[expose] public section

namespace OnePhaseDimension

/-- **Exclusion** (`cut:exclusion`): the certificate excludes every working cone. -/
theorem exclusion_of_certificate (hcert : CertificateStatement) : ExclusionStatement := by
  obtain ⟨c, hc⟩ := hcert
  refine ⟨fun W ↦ ?_⟩
  cases W with
  | orig W h => exact false_of_origCone6 hc W h
  | susp O hO W hW => exact false_of_suspension hc O hO W hW

end OnePhaseDimension
