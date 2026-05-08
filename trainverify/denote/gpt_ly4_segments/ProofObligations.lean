/- Auto-generated human proof obligation index.

This is the intended entry point for human proof work.
Files imported here contain the reusable theorems whose bodies still need proofs.
Instance files such as `Instances.lean` and `SegmentInstances.lean` only project
these reusable proofs to concrete goals; they are not intended proof targets.

Segment proof obligations:
  - SegmentPattern_1.lean: prove_segment_pattern_1  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=48, ops=[OpName.FW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim, OpName.FW_layernorm, OpName.FW_linear, OpName.AllGatherPrim, OpName.FW_view, ...]
  - SegmentPattern_2.lean: prove_segment_pattern_2  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=55, ops=[OpName.FW_transpose, OpName.ChunkPrim, OpName.FW_view, OpName.AllToAllPrim, OpName.FW_matmul, OpName.AllReducePrim, OpName.FW_div, OpName.FW_softmax, ...]
  - SegmentPattern_3.lean: prove_segment_pattern_3  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=38, ops=[OpName.FW_transpose, OpName.FW_contiguous, OpName.AllToAllPrim, OpName.AllGatherPrim, OpName.FW_view, OpName.FW_linear, OpName.FW_add, OpName.FW_layernorm, ...]
  - SegmentPattern_4.lean: prove_segment_pattern_4  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=66, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim, OpName.BW_multiref, OpName.BW_layernorm, OpName.CROSS_DP_WRED, OpName.BW_linear, ...]
  - SegmentPattern_5.lean: prove_segment_pattern_5  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=59, ops=[OpName.BW_view, OpName.BW_linear, OpName.ChunkPrim, OpName.BW_transpose, OpName.AllGatherPrim, OpName.BW_matmul, OpName.AllToAllPrim]
  - SegmentPattern_6.lean: prove_segment_pattern_6  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=63, ops=[OpName.BW_matmul, OpName.BW_div, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim, OpName.BW_softmax, OpName.AllToAllPrim, OpName.BW_transpose, ...]
  - SegmentPattern_7.lean: prove_segment_pattern_7  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=44, ops=[OpName.BW_linear, OpName.AllReducePrim, OpName.BW_add, OpName.BW_multiref, OpName.AllToAllPrim, OpName.BW_layernorm, OpName.CROSS_DP_WRED, OpName.ChunkPrim]
  - SegmentPattern_8.lean: prove_segment_pattern_8  -- instances=4, goals/instance=3, ops/instance: SM=3, PM=25, ops=[OpName.BW_gelu, OpName.BW_linear, OpName.AllToAllPrim, OpName.CROSS_DP_WRED]
  - SegmentPattern_9.lean: prove_segment_pattern_9  -- instances=4, goals/instance=8, ops/instance: SM=8, PM=44, ops=[OpName.FW_multiref, OpName.AllToAllPrim, OpName.BW_layernorm, OpName.BW_add, OpName.BW_linear, OpName.ChunkPrim]
  - SegmentPattern_10.lean: prove_segment_pattern_10  -- instances=4, goals/instance=6, ops/instance: SM=6, PM=38, ops=[OpName.FW_multiref, OpName.AllGatherPrim, OpName.BW_linear, OpName.ChunkPrim, OpName.AllReducePrim, OpName.AllToAllPrim, OpName.BW_layernorm, OpName.BW_add]

Fallback pattern proof obligations:
  - Pattern_1.lean: prove_pattern_1  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_sum, OpName.AllReducePrim]; concrete goals: 1
  - Pattern_2.lean: prove_pattern_2  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_embedding, OpName.AllReducePrim]; concrete goals: 2
  - Pattern_3.lean: prove_pattern_3  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_embedding, OpName.ChunkPrim]; concrete goals: 3
  - Pattern_19.lean: prove_pattern_19  -- instances=2, ops/instance: SM=1, PM=4, ops=[OpName.FW_linear]; concrete goals: 53, 106
  - Pattern_21.lean: prove_pattern_21  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_layernorm, OpName.AllGatherPrim]; concrete goals: 105
  - Pattern_23.lean: prove_pattern_23  -- instances=1, ops/instance: SM=1, PM=8, ops=[OpName.FW_linear, OpName.AllToAllPrim]; concrete goals: 28
  - Pattern_44.lean: prove_pattern_44  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.FW_add, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 104
  - Pattern_45.lean: prove_pattern_45  -- instances=2, ops/instance: SM=1, PM=9, ops=[OpName.FW_linear, OpName.AllToAllPrim, OpName.AllReducePrim]; concrete goals: 78, 103
  - Pattern_53.lean: prove_pattern_53  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_embedding]; concrete goals: 107
  - Pattern_54.lean: prove_pattern_54  -- instances=1, ops/instance: SM=1, PM=14, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllToAllPrim, OpName.AllGatherPrim]; concrete goals: 108
  - Pattern_55.lean: prove_pattern_55  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.BW_embedding, OpName.ChunkPrim, OpName.CROSS_DP_WRED]; concrete goals: 109
  - Pattern_58.lean: prove_pattern_58  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.BW_layernorm, OpName.CROSS_DP_WRED]; concrete goals: 252
  - Pattern_59.lean: prove_pattern_59  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.BW_layernorm, OpName.CROSS_DP_WRED]; concrete goals: 253
  - Pattern_76.lean: prove_pattern_76  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_linear]; concrete goals: 255
  - Pattern_78.lean: prove_pattern_78  -- instances=1, ops/instance: SM=1, PM=9, ops=[OpName.BW_linear, OpName.AllReducePrim, OpName.ChunkPrim]; concrete goals: 254
  - Pattern_112.lean: prove_pattern_112  -- instances=1, ops/instance: SM=1, PM=10, ops=[OpName.BW_add, OpName.AllReducePrim, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 250
  - Pattern_125.lean: prove_pattern_125  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_layernorm]; concrete goals: 251
  - Pattern_126.lean: prove_pattern_126  -- instances=1, ops/instance: SM=1, PM=4, ops=[OpName.BW_sum]; concrete goals: 256
-/
import denote.gpt_ly4_segments.SegmentPattern_1
import denote.gpt_ly4_segments.SegmentPattern_2
import denote.gpt_ly4_segments.SegmentPattern_3
import denote.gpt_ly4_segments.SegmentPattern_4
import denote.gpt_ly4_segments.SegmentPattern_5
import denote.gpt_ly4_segments.SegmentPattern_6
import denote.gpt_ly4_segments.SegmentPattern_7
import denote.gpt_ly4_segments.SegmentPattern_8
import denote.gpt_ly4_segments.SegmentPattern_9
import denote.gpt_ly4_segments.SegmentPattern_10
import denote.gpt_ly4_segments.Pattern_1
import denote.gpt_ly4_segments.Pattern_2
import denote.gpt_ly4_segments.Pattern_3
import denote.gpt_ly4_segments.Pattern_19
import denote.gpt_ly4_segments.Pattern_21
import denote.gpt_ly4_segments.Pattern_23
import denote.gpt_ly4_segments.Pattern_44
import denote.gpt_ly4_segments.Pattern_45
import denote.gpt_ly4_segments.Pattern_53
import denote.gpt_ly4_segments.Pattern_54
import denote.gpt_ly4_segments.Pattern_55
import denote.gpt_ly4_segments.Pattern_58
import denote.gpt_ly4_segments.Pattern_59
import denote.gpt_ly4_segments.Pattern_76
import denote.gpt_ly4_segments.Pattern_78
import denote.gpt_ly4_segments.Pattern_112
import denote.gpt_ly4_segments.Pattern_125
import denote.gpt_ly4_segments.Pattern_126

namespace TrainVerify.Denote.GeneratedProofObligations

def humanSegmentProofCount : Nat := 10
def humanFallbackPatternProofCount : Nat := 18
def humanProofObligationCount : Nat := 28

end TrainVerify.Denote.GeneratedProofObligations

