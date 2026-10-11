/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.ToGen
public import OnePhaseDimension.Certificate.Main

/-!
# The certificate in a general dimension specializes to dimension five

Every five-dimensional certificate with constants `ε*, δ*` is a generic certificate with `m = 5`
(`CertificateHolds.toGen`), so the generic certificate statement holds for `m = 5`.
-/

@[expose] public section

namespace OnePhaseDimension

/-- The generic certificate statement holds in dimension five. -/
theorem certificateStatement_gen_five : Gen.CertificateStatement 5 :=
  ⟨εStar, δStar, εStar_pos, δStar_pos, _, Certificate.tableCoeffs_holds.toGen⟩

end OnePhaseDimension
