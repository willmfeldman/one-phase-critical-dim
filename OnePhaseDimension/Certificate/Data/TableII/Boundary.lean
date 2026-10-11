/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Data.Types

/-!
# The second coefficient table: the two boundary blocks of rank -1 (indices 19–20)

Each block lists its rank, projection label, multiplier mode and rows; a row is
`(number of digits, word, coefficient column)`, with numerators over `Q = 250000`.
Transcribed mechanically from the source table.

## References

* OpenAI, *The critical dimension for one-phase Bernoulli minimizers*, preprint,
  September 24, 2026, https://github.com/openai/math (cited as "the source").
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Data

/-- Block 19 of the second table: `@ -1 none I`, 14 rows × 5 columns. -/
def block19 : Block where
  rank := -1
  proj := .none
  mode := .I
  rows := [
    (4, 1000, [-7510150, 892635, 2182767, 23202, -4016]),
    (4, 100, [-5873297, -966404, 1065127, 891160, -4153]),
    (4, 10, [-7594462, 3164488, 32982, 23257, -4265]),
    (4, 1, [-6664095, -676125, -2074840, -90371, -141368]),
    (4, 2000, [10527925, -1288669, -3350633, 0, 0]),
    (4, 1100, [13562510, -782596, -3072444, -1185008, -525859]),
    (4, 1010, [14954300, -3513649, -2045232, 175643, 711822]),
    (4, 1001, [16001742, 0, 0, 0, 0]),
    (4, 200, [7976754, 1609001, -1608780, -1353027, 0]),
    (4, 110, [15395603, -1696042, -847566, -840285, -117247]),
    (4, 101, [12758609, 1366427, 714605, -471973, 827299]),
    (4, 20, [10659228, -4829347, 0, 0, 0]),
    (4, 11, [14311972, -2973496, 1455043, -343953, -411843]),
    (4, 2, [9209493, 1156789, 3285152, 176907, 213479])]

/-- Block 20 of the second table: `@ -1 none H`, 14 rows × 5 columns. -/
def block20 : Block where
  rank := -1
  proj := .none
  mode := .H
  rows := [
    (4, 1000, [2926888, -771909, -672812, -28439, -32476]),
    (4, 100, [2472139, -1224863, -681989, -18744, 51971]),
    (4, 10, [2504046, -1123530, -477116, 133871, -30159]),
    (4, 1, [2879832, -887584, -486032, 142684, 52873]),
    (4, 2000, [-3960308, 1436663, 856832, -73562, -8956]),
    (4, 1100, [-5950295, 2321626, 989491, -2064346, 0]),
    (4, 1010, [-6842585, 3562264, 2077026, 553336, -610276]),
    (4, 1001, [-4035267, 4405894, 0, 0, 0]),
    (4, 200, [-3909355, 1486027, 856034, -75355, -19599]),
    (4, 110, [-9334809, 0, 0, 0, 0]),
    (4, 101, [-7349996, 2169698, 1941569, 669597, 456042]),
    (4, 20, [-3913415, 1476575, 835966, -92637, -12106]),
    (4, 11, [-6055392, 2242925, 3499526, 0, 0]),
    (4, 2, [-3956252, 1450146, 834863, -93150, -20809])]

end OnePhaseDimension.Certificate.Data
