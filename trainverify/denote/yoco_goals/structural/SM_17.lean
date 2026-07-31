/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_680_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5587 + r)), outs := [5592], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_681_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5592], outs := [5593], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_682_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5593], outs := [5594], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_683_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5594, 5595], outs := [5596] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_684_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5596], outs := [5597], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_685_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5597], outs := [5598] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_686_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8338, 5598], outs := [5599] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_687_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5599], outs := [8342, 8346], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_688_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8342, 5600], outs := [5601] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_689_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5601], outs := [8353, 8357, 8361, 8365, 8369], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_690_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8353], outs := [5602] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_691_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8361], outs := [5611], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_692_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8365], outs := [5616], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_693_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8369], outs := [5620], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_694_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5602, 5603], outs := [5604] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_695_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5611, 5612], outs := [5613] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_696_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5616, 5617], outs := [5618] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_697_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5620, 5621], outs := [5622] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_698_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5604], outs := [5605, 5606, 5607], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_699_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5613], outs := [5614], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_700_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5618], outs := [5619], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_701_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5622], outs := [5623], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_702_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8357, 5605, 5606, 5608, 5609], outs := [5610], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_703_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5614], outs := [5615] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_704_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5619, 5623], outs := [5624] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_705_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5624], outs := [5625], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_706_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5625, 5626], outs := [5627] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_707_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5627], outs := [5628], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_708_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5615, 5628], outs := [5629] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_709_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5610, 5629], outs := [5630] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_710_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5630], outs := [5631] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_711_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8346, 5631], outs := [5632] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_712_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5632], outs := [8373, 8377], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_713_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8373, 5633], outs := [5634] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_714_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5634, 5635], outs := [5636] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_715_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5636 + r)), outs := [5641], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_716_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5641], outs := [5642], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_717_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5642], outs := [5643], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_718_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5643, 5644], outs := [5645] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_719_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5645], outs := [5646], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
