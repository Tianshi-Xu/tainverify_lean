/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1200_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [9913, 9987], outs := [9991] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1201_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [9914, 9988], outs := [9992] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1202_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9991], outs := [9997] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1203_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9992], outs := [9998] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1204_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16067, 9997], outs := [10001] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1205_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16075, 9998], outs := [10002] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1206_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10001], outs := [16125, 16129], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1207_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10002], outs := [16133, 16137], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1208_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16125, 5437], outs := [10005] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1209_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16133, 5437], outs := [10006] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1210_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10005, 5439], outs := [10007] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1211_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10006, 5439], outs := [10008] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1212_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10007, 5441, 5442, 5443, 5444], outs := [10031], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1213_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10008, 5441, 5442, 5443, 5444], outs := [10032], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1214_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10031], outs := [10033], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1215_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10032], outs := [10034], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1216_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10033], outs := [10039], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1217_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10034], outs := [10040], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1218_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10039, 5448], outs := [10043] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1219_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10040, 5448], outs := [10044] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1220_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10043], outs := [10053], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1221_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10044], outs := [10054], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1222_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10053], outs := [10057] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1223_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10054], outs := [10058] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1224_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16129, 10057], outs := [10061] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1225_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16137, 10058], outs := [10062] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1226_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10061], outs := [16141, 16145], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1227_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10062], outs := [16149, 16153], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1228_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16141, 5453], outs := [10065] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1229_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16149, 5453], outs := [10066] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1230_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10065], outs := [16160, 16164, 16168, 16172, 16176], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1231_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10066], outs := [16183, 16187, 16191, 16195, 16199], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1232_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16160], outs := [10067] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1233_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16168], outs := [10087], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1234_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16172], outs := [10101], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1235_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16176], outs := [10119], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1236_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16183], outs := [10068] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1237_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16191], outs := [10088], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1238_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16195], outs := [10102], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1239_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16199], outs := [10120], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
