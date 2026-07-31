/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1240_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [10067, 5456], outs := [10073] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1241_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10087, 5465], outs := [10091] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1242_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10101, 5470], outs := [10105] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1243_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10119, 5474], outs := [10123] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1244_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [10068, 5456], outs := [10074] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1245_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10088, 5465], outs := [10092] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1246_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10102, 5470], outs := [10106] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1247_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10120, 5474], outs := [10124] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1248_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [10073], outs := [10075, 10077, 10079], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1249_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10091], outs := [10097], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1250_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10105], outs := [10115], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1251_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10123], outs := [10133], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1252_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [10074], outs := [10076, 10078, 10080], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1253_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10092], outs := [10098], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1254_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10106], outs := [10116], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1255_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10124], outs := [10134], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1256_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16164, 10075, 10077, 10081, 10083], outs := [10085], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1257_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [10097], outs := [10099] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1258_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [10115, 10133], outs := [10137] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1259_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16187, 10076, 10078, 10082, 10084], outs := [10086], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1260_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [10098], outs := [10100] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1261_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [10116, 10134], outs := [10138] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1262_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10137], outs := [10139], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1263_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10138], outs := [10140], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1264_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10139, 5479], outs := [10145] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1265_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10140, 5479], outs := [10146] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1266_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10145], outs := [10155], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1267_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10146], outs := [10156], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1268_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [10099, 10155], outs := [10159] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1269_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [10100, 10156], outs := [10160] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1270_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [10085, 10159], outs := [10163] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1271_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [10086, 10160], outs := [10164] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1272_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10163], outs := [10169] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1273_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10164], outs := [10170] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1274_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16145, 10169], outs := [10173] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1275_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16153, 10170], outs := [10174] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1276_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10173], outs := [16203, 16207], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1277_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10174], outs := [16211, 16215], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1278_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16203, 5486], outs := [10177] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1279_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16211, 5486], outs := [10178] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
