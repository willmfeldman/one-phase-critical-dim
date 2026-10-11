/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Spike.Smoke
public import OnePhaseDimension.Certificate.Spike.BlockB1
public import OnePhaseDimension.Certificate.Spike.BlockS3
public import OnePhaseDimension.Certificate.Spike.BlockH18

/-!
# Kernel checks of the certificate engine on sample blocks

Regression checks, built separately from the main library (`lake build OnePhaseDimensionChecks`):
the expansion of three coefficient blocks is compared, inside the kernel, with independently
computed reference lists.
-/
