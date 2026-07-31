/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_920_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5909, 5922], outs := [5923] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_921_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5904, 5923], outs := [5924] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_922_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5924], outs := [5925] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_923_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8580, 5925], outs := [5926] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_924_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5926, 5927], outs := [5928], params := [1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_925_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [5928, 5929], outs := [5930] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_926_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [5930, 5931, 4678], outs := [4673, 4674], params := [1024] } := by
  intro s
  change 2 ≥ 2
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
