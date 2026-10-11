/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Collect.Bounds

/-!
# Graph-bound classification and rounding of the remainder keys, part A1

Kernel check of `roundingOK` on a quarter of the remainder data.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Collect

open Data

theorem roundingOK_A1 : roundingOK (remainderDataA.take 429) = true := by
  decide +kernel

end OnePhaseDimension.Certificate.Collect
