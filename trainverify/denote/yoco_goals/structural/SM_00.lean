/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_0_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_embedding", ins := [4677, 4679], outs := [4680] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_1_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4680], outs := [4681] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_2_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4681], outs := [7383, 7387], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_3_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7383, 4682], outs := [4683] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_4_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4683], outs := [7392, 7396, 7400], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_5_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7392, 4684], outs := [4685] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_6_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7396, 4686], outs := [4687] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_7_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7400, 4688], outs := [4689] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_8_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_9_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4692, 4693, 4689, 4694, 4695], outs := [4696], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_10_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4696], outs := [4697], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_11_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4697], outs := [4698], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_12_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_13_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_14_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4701], outs := [4702] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_15_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7387, 4702], outs := [4703] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_16_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [7404, 7408], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_17_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7404, 4704], outs := [4705] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_18_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := [7415, 7419, 7423, 7427, 7431], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_19_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7415], outs := [4706] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_20_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7423], outs := [4715], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_21_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7427], outs := [4720], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_22_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7431], outs := [4724], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_23_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_24_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4715, 4716], outs := [4717] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_25_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4720, 4721], outs := [4722] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_26_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4724, 4725], outs := [4726] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_27_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [4708], outs := [4709, 4710, 4711], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_28_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4717], outs := [4718], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_29_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4722], outs := [4723], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_30_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4726], outs := [4727], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_31_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7419, 4709, 4710, 4712, 4713], outs := [4714], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_32_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [4718], outs := [4719] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_33_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [4723, 4727], outs := [4728] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_34_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4728], outs := [4729], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_35_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_36_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4731], outs := [4732], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_37_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [4719, 4732], outs := [4733] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_38_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [4714, 4733], outs := [4734] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_39_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4734], outs := [4735] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
