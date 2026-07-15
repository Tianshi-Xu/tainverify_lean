/- Auto-generated human proof obligation index.

This is the intended entry point for human proof work.
Files imported here contain the reusable theorems whose bodies still need proofs.
`Instances.lean` projects Pattern_N proofs to concrete goals, and
`MainTheorem.lean` composes those projections into `all_goals_stmt`.

Optional segment proof packages: none

Pattern proof obligations for all_goals_stmt:
  - Pattern_1.lean: prove_pattern_1  -- instances=1, ops/instance: SM=25, PM=53, ops=[OpName.FW_multiref, OpName.FW_reshape, OpName.FW_mix_precision_linear, OpName.FW_topk_routing, OpName.FW_view, OpName.FW_all2all_moe_gmm, OpName.FW_sigmoid, OpName.FW_swiglu, ...]; concrete goals: 1
  - Pattern_2.lean: prove_pattern_2  -- instances=1, ops/instance: SM=1, PM=5, ops=[OpName.FW_inner_chunk_ce, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 2
  - Pattern_3.lean: prove_pattern_3  -- instances=1, ops/instance: SM=903, PM=1866, ops=[OpName.FW_float, OpName.FW_multiref, OpName.FW_rms_norm, OpName.FW_per_head_mix_precision_linear, OpName.FW_rotary_embedding, OpName.FW_attn_sliding_window, OpName.FW_reshape, OpName.FW_mix_precision_linear, ...]; concrete goals: 3
  - Pattern_4.lean: prove_pattern_4  -- instances=1, ops/instance: SM=25, PM=55, ops=[OpName.FW_topk_routing, OpName.FW_stack, OpName.ChunkPrim, OpName.AllGatherPrim]; concrete goals: 4
  - Pattern_5.lean: prove_pattern_5  -- instances=1, ops/instance: SM=1, PM=3, ops=[OpName.FW_embedding, OpName.AllReducePrim]; concrete goals: 5
-/
import denote.Pattern_1
import denote.Pattern_2
import denote.Pattern_3
import denote.Pattern_4
import denote.Pattern_5

namespace TrainVerify.Denote.GeneratedProofObligations

def optionalSegmentProofPackageCount : Nat := 0
def humanPatternProofCount : Nat := 5
def humanProofObligationCount : Nat := 5

end TrainVerify.Denote.GeneratedProofObligations

