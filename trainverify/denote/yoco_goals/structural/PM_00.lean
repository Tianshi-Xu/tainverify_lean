/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_0_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_embedding", ins := [4677, 7389], outs := [7391], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [4691], outs := ((List.range 12).map (fun r => 11853 + r)), params := [12] } := by
  intro s
  change 12 ≥ 12
  omega

theorem pm_node_2_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4799], outs := [7803], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_3_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4853], outs := [7989], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_4_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4907], outs := [8175], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_5_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4961], outs := [8361], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_6_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [5015], outs := [8547], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_7_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [5069], outs := [8733], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_8_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [5123], outs := [8919], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_9_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [5177], outs := [9105], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_10_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [5231], outs := [9291], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_11_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [5285], outs := [9477], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_12_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4678], outs := [11835], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_13_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_embedding", ins := [4677, 7390], outs := [7392], params := [77440] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_14_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [4691], outs := ((List.range 12).map (fun r => 11853 + r)), params := [12] } := by
  intro s
  change 12 ≥ 12
  omega

theorem pm_node_15_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4799], outs := [7804], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_16_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4853], outs := [7990], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_17_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4907], outs := [8176], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_18_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4961], outs := [8362], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_19_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [5015], outs := [8548], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_20_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [5069], outs := [8734], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_21_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [5123], outs := [8920], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_22_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [5177], outs := [9106], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_23_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [5231], outs := [9292], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_24_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [5285], outs := [9478], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_25_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4678], outs := [11836], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_26_wf : IsWellFormedNode pm { rank := 0, op := "OpName.AllReducePrim", ins := [7391, 7392], outs := [4680] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_27_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_28_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [4680], outs := [4681] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_29_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [14603, 14607], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_30_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [4681], outs := [14611, 14615], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_31_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [14603, 4682], outs := [4683] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_32_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [14611, 4682], outs := [4683] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_33_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [14620, 14624, 14628], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_34_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [4683], outs := [14632, 14636, 14640], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_35_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14620, 4684], outs := [4685] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_36_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14624, 4686], outs := [4687] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_37_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14628, 4688], outs := [4689] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_38_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14632, 4684], outs := [4685] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_39_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14636, 4686], outs := [4687] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
