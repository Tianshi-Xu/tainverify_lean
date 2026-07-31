/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_80_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4790], outs := [7487, 7491], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_81_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7487, 4791], outs := [4792] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_82_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4792], outs := [7496, 7500, 7504], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_83_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7496, 4793], outs := [4794] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_84_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7500, 4795], outs := [4796] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_85_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7504, 4797], outs := [4798] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_86_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4799, 4794, 4796], outs := [4800, 4801], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_87_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4800, 4801, 4798, 4802, 4803], outs := [4804], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_88_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4804], outs := [4805], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_89_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4805], outs := [4806], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_90_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4806, 4807], outs := [4808] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_91_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4808], outs := [4809], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_92_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4809], outs := [4810] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_93_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7491, 4810], outs := [4811] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_94_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4811], outs := [7508, 7512], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_95_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7508, 4812], outs := [4813] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_96_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4813], outs := [7519, 7523, 7527, 7531, 7535], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_97_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7519], outs := [4814] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_98_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7527], outs := [4823], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_99_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7531], outs := [4828], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_100_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7535], outs := [4832], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_101_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [4814, 4815], outs := [4816] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_102_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4823, 4824], outs := [4825] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_103_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4828, 4829], outs := [4830] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_104_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4832, 4833], outs := [4834] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_105_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [4816], outs := [4817, 4818, 4819], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_106_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4825], outs := [4826], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_107_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4830], outs := [4831], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_108_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4834], outs := [4835], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_109_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7523, 4817, 4818, 4820, 4821], outs := [4822], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_110_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [4826], outs := [4827] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_111_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [4831, 4835], outs := [4836] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_112_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4836], outs := [4837], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_113_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4837, 4838], outs := [4839] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_114_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4839], outs := [4840], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_115_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [4827, 4840], outs := [4841] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_116_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [4822, 4841], outs := [4842] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_117_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4842], outs := [4843] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_118_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7512, 4843], outs := [4844] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_119_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4844], outs := [7539, 7543], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
