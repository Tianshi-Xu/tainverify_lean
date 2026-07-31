/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_640_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5532], outs := [5533] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_641_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8268, 5533], outs := [5534] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_642_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5534], outs := [8295, 8299], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_643_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8295, 5535], outs := [5536] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_644_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5536, 5537], outs := [5538] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_645_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5538 + r)), outs := [5543], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_646_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5543], outs := [5544], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_647_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5544], outs := [5545], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_648_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5545, 5546], outs := [5547] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_649_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5547], outs := [5548], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_650_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5548], outs := [5549] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_651_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8299, 5549], outs := [5550] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_652_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5550], outs := [8303, 8307], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_653_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8303, 5551], outs := [5552] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_654_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5552], outs := [8314, 8318, 8322, 8326, 8330], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_655_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8314], outs := [5553] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_656_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8322], outs := [5562], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_657_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8326], outs := [5567], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_658_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8330], outs := [5571], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_659_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5553, 5554], outs := [5555] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_660_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5562, 5563], outs := [5564] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_661_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5567, 5568], outs := [5569] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_662_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5571, 5572], outs := [5573] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_663_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5555], outs := [5556, 5557, 5558], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_664_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5564], outs := [5565], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_665_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5569], outs := [5570], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_666_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5573], outs := [5574], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_667_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8318, 5556, 5557, 5559, 5560], outs := [5561], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_668_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5565], outs := [5566] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_669_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5570, 5574], outs := [5575] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_670_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5575], outs := [5576], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_671_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5576, 5577], outs := [5578] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_672_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5578], outs := [5579], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_673_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5566, 5579], outs := [5580] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_674_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5561, 5580], outs := [5581] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_675_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5581], outs := [5582] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_676_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8307, 5582], outs := [5583] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_677_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5583], outs := [8334, 8338], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_678_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8334, 5584], outs := [5585] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_679_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5585, 5586], outs := [5587] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
