/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_40_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7408, 4735], outs := [4736] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_41_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [7435, 7439], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_42_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7435, 4737], outs := [4738] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_43_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [7444, 7448, 7452], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_44_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7444, 4739], outs := [4740] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_45_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7448, 4741], outs := [4742] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_46_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7452, 4743], outs := [4744] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_47_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_48_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4746, 4747, 4744, 4748, 4749], outs := [4750], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_49_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4750], outs := [4751], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_50_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4751], outs := [4752], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_51_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4752, 4753], outs := [4754] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_52_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4754], outs := [4755], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_53_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4755], outs := [4756] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_54_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7439, 4756], outs := [4757] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_55_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [7456, 7460], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_56_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7456, 4758], outs := [4759] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_57_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := [7467, 7471, 7475, 7479, 7483], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_58_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7467], outs := [4760] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_59_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7475], outs := [4769], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_60_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7479], outs := [4774], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_61_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7483], outs := [4778], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_62_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [4760, 4761], outs := [4762] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_63_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_64_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_65_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_66_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [4762], outs := [4763, 4764, 4765], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_67_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_68_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_69_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_70_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7471, 4763, 4764, 4766, 4767], outs := [4768], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_71_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [4772], outs := [4773] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_72_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [4777, 4781], outs := [4782] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_73_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4782], outs := [4783], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_74_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4783, 4784], outs := [4785] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_75_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4785], outs := [4786], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_76_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [4773, 4786], outs := [4787] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_77_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [4768, 4787], outs := [4788] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_78_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4788], outs := [4789] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_79_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7460, 4789], outs := [4790] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
