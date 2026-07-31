/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1160_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9893], outs := [16082, 16086, 16090, 16094, 16098], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1161_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9894], outs := [16105, 16109, 16113, 16117, 16121], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1162_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16082], outs := [9895] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1163_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16090], outs := [9915], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1164_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16094], outs := [9929], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1165_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16098], outs := [9947], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1166_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16105], outs := [9896] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1167_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16113], outs := [9916], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1168_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16117], outs := [9930], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1169_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16121], outs := [9948], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1170_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [9895, 5407], outs := [9901] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1171_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9915, 5416], outs := [9919] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1172_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9929, 5421], outs := [9933] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1173_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9947, 5425], outs := [9951] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1174_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [9896, 5407], outs := [9902] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1175_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9916, 5416], outs := [9920] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1176_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9930, 5421], outs := [9934] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1177_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9948, 5425], outs := [9952] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1178_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [9901], outs := [9903, 9905, 9907], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1179_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9919], outs := [9925], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1180_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9933], outs := [9943], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1181_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9951], outs := [9961], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1182_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [9902], outs := [9904, 9906, 9908], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1183_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9920], outs := [9926], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1184_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9934], outs := [9944], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1185_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9952], outs := [9962], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1186_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16086, 9903, 9905, 9909, 9911], outs := [9913], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1187_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [9925], outs := [9927] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1188_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [9943, 9961], outs := [9965] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1189_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16109, 9904, 9906, 9910, 9912], outs := [9914], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1190_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [9926], outs := [9928] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1191_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [9944, 9962], outs := [9966] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1192_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9965], outs := [9967], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1193_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9966], outs := [9968], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1194_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9967, 5430], outs := [9973] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1195_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9968, 5430], outs := [9974] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1196_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9973], outs := [9983], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1197_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9974], outs := [9984], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1198_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [9927, 9983], outs := [9987] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1199_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [9928, 9984], outs := [9988] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
