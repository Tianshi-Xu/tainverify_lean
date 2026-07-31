/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_800_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5758, 5759], outs := [5760] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_801_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5763, 5764], outs := [5765] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_802_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5767, 5768], outs := [5769] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_803_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5751], outs := [5752, 5753, 5754], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_804_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5760], outs := [5761], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_805_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5765], outs := [5766], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_806_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5769], outs := [5770], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_807_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8474, 5752, 5753, 5755, 5756], outs := [5757], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_808_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5761], outs := [5762] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_809_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5766, 5770], outs := [5771] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_810_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5771], outs := [5772], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_811_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5772, 5773], outs := [5774] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_812_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5774], outs := [5775], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_813_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5762, 5775], outs := [5776] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_814_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5757, 5776], outs := [5777] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_815_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5777], outs := [5778] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_816_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8463, 5778], outs := [5779] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_817_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5779], outs := [8490, 8494], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_818_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8490, 5780], outs := [5781] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_819_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5781, 5782], outs := [5783] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_820_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5783 + r)), outs := [5788], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_821_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5788], outs := [5789], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_822_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5789], outs := [5790], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_823_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5790, 5791], outs := [5792] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_824_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5792], outs := [5793], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_825_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5793], outs := [5794] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_826_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8494, 5794], outs := [5795] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_827_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5795], outs := [8498, 8502], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_828_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8498, 5796], outs := [5797] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_829_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5797], outs := [8509, 8513, 8517, 8521, 8525], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_830_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8509], outs := [5798] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_831_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8517], outs := [5807], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_832_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8521], outs := [5812], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_833_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8525], outs := [5816], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_834_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5798, 5799], outs := [5800] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_835_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5807, 5808], outs := [5809] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_836_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5812, 5813], outs := [5814] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_837_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5816, 5817], outs := [5818] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_838_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5800], outs := [5801, 5802, 5803], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_839_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5809], outs := [5810], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
