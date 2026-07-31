/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_120_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7539, 4845], outs := [4846] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_121_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4846], outs := [7548, 7552, 7556], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_122_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7548, 4847], outs := [4848] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_123_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7552, 4849], outs := [4850] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_124_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7556, 4851], outs := [4852] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_125_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4853, 4848, 4850], outs := [4854, 4855], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_126_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4854, 4855, 4852, 4856, 4857], outs := [4858], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_127_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4858], outs := [4859], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_128_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4859], outs := [4860], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_129_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4860, 4861], outs := [4862] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_130_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4862], outs := [4863], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_131_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4863], outs := [4864] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_132_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7543, 4864], outs := [4865] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_133_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4865], outs := [7560, 7564], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_134_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7560, 4866], outs := [4867] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_135_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4867], outs := [7571, 7575, 7579, 7583, 7587], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_136_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7571], outs := [4868] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_137_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7579], outs := [4877], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_138_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7583], outs := [4882], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_139_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7587], outs := [4886], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_140_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [4868, 4869], outs := [4870] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_141_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4877, 4878], outs := [4879] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_142_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4882, 4883], outs := [4884] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_143_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4886, 4887], outs := [4888] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_144_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [4870], outs := [4871, 4872, 4873], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_145_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4879], outs := [4880], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_146_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4884], outs := [4885], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_147_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4888], outs := [4889], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_148_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7575, 4871, 4872, 4874, 4875], outs := [4876], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_149_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [4880], outs := [4881] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_150_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [4885, 4889], outs := [4890] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_151_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4890], outs := [4891], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_152_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4891, 4892], outs := [4893] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_153_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4893], outs := [4894], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_154_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [4881, 4894], outs := [4895] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_155_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [4876, 4895], outs := [4896] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_156_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4896], outs := [4897] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_157_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7564, 4897], outs := [4898] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_158_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4898], outs := [7591, 7595], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_159_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7591, 4899], outs := [4900] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
