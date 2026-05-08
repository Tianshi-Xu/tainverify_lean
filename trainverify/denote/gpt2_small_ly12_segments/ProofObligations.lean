/- Auto-generated human proof obligation index.

This is the intended entry point for human proof work.
Files imported here contain the reusable theorems whose bodies still need proofs.
Instance files such as `Instances.lean` and `SegmentInstances.lean` only project
these reusable proofs to concrete goals; they are not intended proof targets.

Segment proof obligations:
  - SegmentPattern_1.lean: prove_segment_pattern_1  -- instances=12, goals/instance=8, ops/instance: SM=8, PM=49, ops=[OpName.FW_add, OpName.AllToAllPrim, OpName.AllReducePrim, OpName.ChunkPrim, OpName.FW_layernorm, OpName.FW_linear, OpName.AllGatherPrim, OpName.FW_view, ...]
  - SegmentPattern_2.lean: prove_segment_pattern_2  -- instances=12, goals/instance=8, ops/instance: SM=8, PM=57, ops=[OpName.FW_transpose, OpName.ChunkPrim, OpName.FW_view, OpName.AllToAllPrim, OpName.FW_matmul, OpName.FW_div, OpName.FW_softmax, OpName.AllGatherPrim]
  - SegmentPattern_3.lean: prove_segment_pattern_3  -- instances=12, goals/instance=8, ops/instance: SM=8, PM=49, ops=[OpName.FW_transpose, OpName.FW_contiguous, OpName.AllToAllPrim, OpName.AllGatherPrim, OpName.FW_view, OpName.FW_linear, OpName.ChunkPrim, OpName.AllReducePrim, ...]
  - SegmentPattern_4.lean: prove_segment_pattern_4  -- instances=12, goals/instance=8, ops/instance: SM=8, PM=66, ops=[OpName.BW_add, OpName.AllToAllPrim, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim, OpName.BW_multiref, OpName.BW_layernorm, OpName.CROSS_DP_WRED, ...]
  - SegmentPattern_5.lean: prove_segment_pattern_5  -- instances=12, goals/instance=8, ops/instance: SM=8, PM=64, ops=[OpName.BW_view, OpName.BW_linear, OpName.BW_transpose, OpName.ChunkPrim, OpName.AllGatherPrim, OpName.BW_matmul, OpName.AllToAllPrim, OpName.AllReducePrim]
  - SegmentPattern_6.lean: prove_segment_pattern_6  -- instances=12, goals/instance=8, ops/instance: SM=8, PM=73, ops=[OpName.BW_matmul, OpName.AllToAllPrim, OpName.BW_div, OpName.BW_softmax, OpName.AllReducePrim, OpName.ChunkPrim, OpName.BW_transpose, OpName.BW_contiguous, ...]
  - SegmentPattern_7.lean: prove_segment_pattern_7  -- instances=12, goals/instance=8, ops/instance: SM=8, PM=54, ops=[OpName.BW_linear, OpName.ChunkPrim, OpName.AllGatherPrim, OpName.BW_add, OpName.AllReducePrim, OpName.BW_multiref, OpName.BW_layernorm, OpName.CROSS_DP_WRED]
  - SegmentPattern_8.lean: prove_segment_pattern_8  -- instances=12, goals/instance=3, ops/instance: SM=3, PM=17, ops=[OpName.BW_gelu, OpName.BW_linear, OpName.AllReducePrim, OpName.ChunkPrim]
  - SegmentPattern_9.lean: prove_segment_pattern_9  -- instances=12, goals/instance=8, ops/instance: SM=8, PM=49, ops=[OpName.FW_multiref, OpName.BW_layernorm, OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim, OpName.BW_linear]
  - SegmentPattern_10.lean: prove_segment_pattern_10  -- instances=12, goals/instance=6, ops/instance: SM=6, PM=32, ops=[OpName.FW_multiref, OpName.AllToAllPrim, OpName.BW_linear, OpName.BW_layernorm, OpName.BW_add]

Fallback pattern proof obligations:
  - Pattern_1.lean: prove_pattern_1  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_sum, OpName.AllReducePrim]; concrete goals: 1
  - Pattern_2.lean: prove_pattern_2  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.FW_embedding]; concrete goals: 2
  - Pattern_3.lean: prove_pattern_3  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_embedding, OpName.AllReducePrim]; concrete goals: 3
  - Pattern_7.lean: prove_pattern_7  -- instances=2, ops/instance: SM=1, PM=5, ops=[OpName.FW_linear, OpName.AllReducePrim]; concrete goals: 253, 303
  - Pattern_23.lean: prove_pattern_23  -- instances=2, ops/instance: SM=1, PM=4, ops=[OpName.FW_linear]; concrete goals: 28, 128
  - Pattern_36.lean: prove_pattern_36  -- instances=3, ops/instance: SM=1, PM=4, ops=[OpName.FW_linear]; concrete goals: 53, 228, 306
  - Pattern_46.lean: prove_pattern_46  -- instances=4, ops/instance: SM=1, PM=9, ops=[OpName.FW_linear, OpName.AllToAllPrim, OpName.AllReducePrim]; concrete goals: 78, 103, 203, 278
  - Pattern_47.lean: prove_pattern_47  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_add, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 304
  - Pattern_66.lean: prove_pattern_66  -- instances=2, ops/instance: SM=1, PM=8, ops=[OpName.FW_linear, OpName.AllToAllPrim]; concrete goals: 153, 178
  - Pattern_87.lean: prove_pattern_87  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_layernorm, OpName.AllToAllPrim]; concrete goals: 305
  - Pattern_88.lean: prove_pattern_88  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_embedding]; concrete goals: 307
  - Pattern_89.lean: prove_pattern_89  -- instances=1, ops/instance: SM=1, PM=17, ops=[OpName.BW_add, OpName.AllToAllPrim, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 308
  - Pattern_90.lean: prove_pattern_90  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_embedding]; concrete goals: 309
  - Pattern_134.lean: prove_pattern_134  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_linear]; concrete goals: 734
  - Pattern_135.lean: prove_pattern_135  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.BW_linear, OpName.CROSS_DP_WRED]; concrete goals: 735
  - Pattern_151.lean: prove_pattern_151  -- instances=1, ops/instance: SM=1, PM=10, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 730
  - Pattern_203.lean: prove_pattern_203  -- instances=1, ops/instance: SM=1, PM=12, ops=[OpName.BW_layernorm, OpName.AllToAllPrim]; concrete goals: 731
  - Pattern_204.lean: prove_pattern_204  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.BW_layernorm, OpName.AllToAllPrim, OpName.CROSS_DP_WRED]; concrete goals: 732
  - Pattern_205.lean: prove_pattern_205  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.BW_layernorm, OpName.AllToAllPrim, OpName.CROSS_DP_WRED]; concrete goals: 733
  - Pattern_206.lean: prove_pattern_206  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_sum]; concrete goals: 736
-/
import denote.gpt2_small_ly12_segments.SegmentPattern_1
import denote.gpt2_small_ly12_segments.SegmentPattern_2
import denote.gpt2_small_ly12_segments.SegmentPattern_3
import denote.gpt2_small_ly12_segments.SegmentPattern_4
import denote.gpt2_small_ly12_segments.SegmentPattern_5
import denote.gpt2_small_ly12_segments.SegmentPattern_6
import denote.gpt2_small_ly12_segments.SegmentPattern_7
import denote.gpt2_small_ly12_segments.SegmentPattern_8
import denote.gpt2_small_ly12_segments.SegmentPattern_9
import denote.gpt2_small_ly12_segments.SegmentPattern_10
import denote.gpt2_small_ly12_segments.Pattern_1
import denote.gpt2_small_ly12_segments.Pattern_2
import denote.gpt2_small_ly12_segments.Pattern_3
import denote.gpt2_small_ly12_segments.Pattern_7
import denote.gpt2_small_ly12_segments.Pattern_23
import denote.gpt2_small_ly12_segments.Pattern_36
import denote.gpt2_small_ly12_segments.Pattern_46
import denote.gpt2_small_ly12_segments.Pattern_47
import denote.gpt2_small_ly12_segments.Pattern_66
import denote.gpt2_small_ly12_segments.Pattern_87
import denote.gpt2_small_ly12_segments.Pattern_88
import denote.gpt2_small_ly12_segments.Pattern_89
import denote.gpt2_small_ly12_segments.Pattern_90
import denote.gpt2_small_ly12_segments.Pattern_134
import denote.gpt2_small_ly12_segments.Pattern_135
import denote.gpt2_small_ly12_segments.Pattern_151
import denote.gpt2_small_ly12_segments.Pattern_203
import denote.gpt2_small_ly12_segments.Pattern_204
import denote.gpt2_small_ly12_segments.Pattern_205
import denote.gpt2_small_ly12_segments.Pattern_206

namespace TrainVerify.Denote.GeneratedProofObligations

def humanSegmentProofCount : Nat := 10
def humanFallbackPatternProofCount : Nat := 20
def humanProofObligationCount : Nat := 30

end TrainVerify.Denote.GeneratedProofObligations

