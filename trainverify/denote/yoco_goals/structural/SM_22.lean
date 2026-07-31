/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_880_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5869], outs := [5870], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_881_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5870, 5871], outs := [5872] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_882_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5872], outs := [5873], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_883_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5860, 5873], outs := [5874] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_884_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5855, 5874], outs := [5875] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_885_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5875], outs := [5876] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_886_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8541, 5876], outs := [5877] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_887_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5877], outs := [8568, 8572], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_888_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8568, 5878], outs := [5879] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_889_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5879, 5880], outs := [5881] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_890_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5881 + r)), outs := [5886], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_891_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5886], outs := [5887], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_892_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5887], outs := [5888], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_893_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5888, 5889], outs := [5890] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_894_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5890], outs := [5891], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_895_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5891], outs := [5892] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_896_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8572, 5892], outs := [5893] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_897_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5893], outs := [8576, 8580], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_898_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8576, 5894], outs := [5895] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_899_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5895], outs := [8587, 8591, 8595, 8599, 8603], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_900_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8587], outs := [5896] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_901_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8595], outs := [5905], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_902_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8599], outs := [5910], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_903_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8603], outs := [5914], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_904_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5896, 5897], outs := [5898] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_905_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5905, 5906], outs := [5907] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_906_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5910, 5911], outs := [5912] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_907_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5914, 5915], outs := [5916] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_908_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5898], outs := [5899, 5900, 5901], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_909_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5907], outs := [5908], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_910_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5912], outs := [5913], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_911_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5916], outs := [5917], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_912_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8591, 5899, 5900, 5902, 5903], outs := [5904], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_913_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_stack", ins := [4710, 4764, 4818, 4872, 4926, 4980, 5034, 5088, 5142, 5196, 5250, 5304, 5361, 5410, 5459, 5508, 5557, 5606, 5655, 5704, 5753, 5802, 5851, 5900], outs := [4675] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_914_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_stack", ins := [4711, 4765, 4819, 4873, 4927, 4981, 5035, 5089, 5143, 5197, 5251, 5305, 5362, 5411, 5460, 5509, 5558, 5607, 5656, 5705, 5754, 5803, 5852, 5901], outs := [4676] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_915_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5908], outs := [5909] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_916_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5913, 5917], outs := [5918] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_917_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5918], outs := [5919], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_918_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5919, 5920], outs := [5921] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_919_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5921], outs := [5922], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
