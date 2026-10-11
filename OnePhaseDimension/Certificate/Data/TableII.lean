/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Data.TableII.Rank012
public import OnePhaseDimension.Certificate.Data.TableII.Rank3A
public import OnePhaseDimension.Certificate.Data.TableII.Rank3B
public import OnePhaseDimension.Certificate.Data.TableII.Boundary

/-!
# The second coefficient table

The 21 blocks of the second table in source order: 19 interior blocks (indices 0–18, 529 rows)
and two boundary blocks of rank `-1` (indices 19–20, 14 rows each), 557 coefficient rows in all.
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Data

/-- The blocks of the second coefficient table, in source order. -/
def tableII : List Block :=
  [block00, block01, block02, block03, block04, block05, block06, block07, block08, block09,
    block10, block11, block12, block13, block14, block15, block16, block17, block18, block19,
    block20]

/-- The 19 interior blocks (nonnegative rank). -/
def tableIIInterior : List Block := tableII.take 19

/-- The two boundary blocks (rank `-1`). -/
def tableIIBoundary : List Block := tableII.drop 19

end OnePhaseDimension.Certificate.Data
