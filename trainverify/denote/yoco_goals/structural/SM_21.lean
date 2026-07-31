/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_840_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5814], outs := [5815], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_841_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5818], outs := [5819], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_842_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8513, 5801, 5802, 5804, 5805], outs := [5806], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_843_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5810], outs := [5811] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_844_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5815, 5819], outs := [5820] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_845_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5820], outs := [5821], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_846_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5821, 5822], outs := [5823] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_847_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5823], outs := [5824], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_848_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5811, 5824], outs := [5825] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_849_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5806, 5825], outs := [5826] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_850_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5826], outs := [5827] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_851_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8502, 5827], outs := [5828] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_852_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5828], outs := [8529, 8533], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_853_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8529, 5829], outs := [5830] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_854_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5830, 5831], outs := [5832] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_855_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5832 + r)), outs := [5837], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_856_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5837], outs := [5838], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_857_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5838], outs := [5839], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_858_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5839, 5840], outs := [5841] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_859_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5841], outs := [5842], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_860_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5842], outs := [5843] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_861_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8533, 5843], outs := [5844] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_862_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5844], outs := [8537, 8541], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_863_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8537, 5845], outs := [5846] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_864_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5846], outs := [8548, 8552, 8556, 8560, 8564], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_865_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8548], outs := [5847] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_866_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8556], outs := [5856], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_867_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8560], outs := [5861], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_868_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8564], outs := [5865], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_869_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5847, 5848], outs := [5849] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_870_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5856, 5857], outs := [5858] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_871_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5861, 5862], outs := [5863] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_872_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5865, 5866], outs := [5867] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_873_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5849], outs := [5850, 5851, 5852], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_874_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5858], outs := [5859], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_875_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5863], outs := [5864], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_876_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5867], outs := [5868], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_877_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8552, 5850, 5851, 5853, 5854], outs := [5855], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_878_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5859], outs := [5860] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_879_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5864, 5868], outs := [5869] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
