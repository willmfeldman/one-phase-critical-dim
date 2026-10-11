/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import OnePhaseDimension.Certificate.Spike.BlockS3.Chunk1
public import OnePhaseDimension.Certificate.Spike.BlockS3.Chunk2
public import OnePhaseDimension.Certificate.Spike.BlockS3.Chunk3
public import OnePhaseDimension.Certificate.Spike.BlockS3.Chunk4
public import OnePhaseDimension.Certificate.Spike.BlockS3.Chunk5
public import OnePhaseDimension.Certificate.Spike.BlockS3.Chunk6
public import OnePhaseDimension.Certificate.Spike.BlockS3.ReferenceA
public import OnePhaseDimension.Certificate.Spike.BlockS3.ReferenceB

/-!
# Kernel expansion of the block `@ 3 sym I`

The block has 78 rank-3 rows and 4 coefficient columns. The 3081 unordered row pairs are split
into six chunks by the first row (`[0,7), [7,15), [15,23), [23,34), [34,47), [47,78)`); each chunk
is collected by kernel reduction in its own file. Here the six chunk results are merged and
compared with the independently computed reference (1441 keys).
-/

@[expose] public section

namespace OnePhaseDimension.Certificate.Spike

open Expand Data

set_option maxRecDepth 100000 in
/-- The collected block `@ 3 sym I`, as the merge of its six chunks, equals the reference. -/
theorem block_3_sym_I :
    Poly.mergeAll [blockChunk 1 3 0 7 (rowsSymI3.map (decodeRow 3)),
      blockChunk 1 3 7 8 (rowsSymI3.map (decodeRow 3)),
      blockChunk 1 3 15 8 (rowsSymI3.map (decodeRow 3)),
      blockChunk 1 3 23 11 (rowsSymI3.map (decodeRow 3)),
      blockChunk 1 3 34 13 (rowsSymI3.map (decodeRow 3)),
      blockChunk 1 3 47 31 (rowsSymI3.map (decodeRow 3))] =
      referenceSymI3A ++ referenceSymI3B := by
  rw [block_3_sym_I_chunk1, block_3_sym_I_chunk2, block_3_sym_I_chunk3, block_3_sym_I_chunk4,
    block_3_sym_I_chunk5, block_3_sym_I_chunk6, ← Poly.mergeAll_k_eq]
  decide +kernel

end OnePhaseDimension.Certificate.Spike
