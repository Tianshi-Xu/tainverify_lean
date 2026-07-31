/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1080_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9699], outs := [9709], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1081_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9700], outs := [9710], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1082_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9709], outs := [9713] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1083_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9710], outs := [9714] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1084_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15973, 9713], outs := [9717] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1085_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15981, 9714], outs := [9718] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1086_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9717], outs := [15985, 15989], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1087_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9718], outs := [15993, 15997], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1088_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15985, 5355], outs := [9721] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1089_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15993, 5355], outs := [9722] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1090_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9721], outs := [16004, 16008, 16012, 16016, 16020], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1091_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9722], outs := [16027, 16031, 16035, 16039, 16043], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1092_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16004], outs := [9723] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1093_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16012], outs := [9743], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1094_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16016], outs := [9757], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1095_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16020], outs := [9775], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1096_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16027], outs := [9724] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1097_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16035], outs := [9744], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1098_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16039], outs := [9758], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1099_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16043], outs := [9776], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1100_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [9723, 5358], outs := [9729] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1101_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9743, 5367], outs := [9747] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1102_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9757, 5372], outs := [9761] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1103_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9775, 5376], outs := [9779] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1104_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [9724, 5358], outs := [9730] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1105_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9744, 5367], outs := [9748] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1106_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9758, 5372], outs := [9762] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1107_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9776, 5376], outs := [9780] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1108_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [9729], outs := [9731, 9733, 9735], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1109_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9747], outs := [9753], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1110_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9761], outs := [9771], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1111_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9779], outs := [9789], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1112_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [9730], outs := [9732, 9734, 9736], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1113_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9748], outs := [9754], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1114_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9762], outs := [9772], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1115_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9780], outs := [9790], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1116_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16008, 9731, 9733, 9737, 9739], outs := [9741], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1117_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [9753], outs := [9755] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1118_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [9771, 9789], outs := [9793] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1119_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16031, 9732, 9734, 9738, 9740], outs := [9742], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
