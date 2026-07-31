/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1120_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [9754], outs := [9756] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1121_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [9772, 9790], outs := [9794] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1122_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9793], outs := [9795], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1123_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9794], outs := [9796], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1124_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9795, 5381], outs := [9801] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1125_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9796, 5381], outs := [9802] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1126_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9801], outs := [9811], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1127_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9802], outs := [9812], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1128_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [9755, 9811], outs := [9815] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1129_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [9756, 9812], outs := [9816] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1130_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [9741, 9815], outs := [9819] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1131_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [9742, 9816], outs := [9820] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1132_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9819], outs := [9825] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1133_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9820], outs := [9826] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1134_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15989, 9825], outs := [9829] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1135_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15997, 9826], outs := [9830] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1136_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9829], outs := [16047, 16051], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1137_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9830], outs := [16055, 16059], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1138_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16047, 5388], outs := [9833] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1139_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16055, 5388], outs := [9834] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1140_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [9833, 5390], outs := [9835] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1141_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [9834, 5390], outs := [9836] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1142_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [9835, 5392, 5393, 5394, 5395], outs := [9859], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1143_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [9836, 5392, 5393, 5394, 5395], outs := [9860], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1144_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9859], outs := [9861], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1145_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9860], outs := [9862], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1146_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9861], outs := [9867], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1147_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9862], outs := [9868], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1148_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9867, 5399], outs := [9871] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1149_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9868, 5399], outs := [9872] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1150_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9871], outs := [9881], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1151_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9872], outs := [9882], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1152_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9881], outs := [9885] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1153_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9882], outs := [9886] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1154_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16051, 9885], outs := [9889] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1155_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16059, 9886], outs := [9890] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1156_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9889], outs := [16063, 16067], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1157_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9890], outs := [16071, 16075], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1158_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16063, 5404], outs := [9893] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1159_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16071, 5404], outs := [9894] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
