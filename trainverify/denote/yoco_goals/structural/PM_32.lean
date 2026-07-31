/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1280_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10177, 5488], outs := [10179] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1281_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10178, 5488], outs := [10180] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1282_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10179, 5490, 5491, 5492, 5493], outs := [10203], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1283_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10180, 5490, 5491, 5492, 5493], outs := [10204], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1284_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10203], outs := [10205], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1285_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10204], outs := [10206], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1286_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10205], outs := [10211], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1287_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10206], outs := [10212], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1288_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10211, 5497], outs := [10215] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1289_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10212, 5497], outs := [10216] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1290_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10215], outs := [10225], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1291_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10216], outs := [10226], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1292_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10225], outs := [10229] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1293_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10226], outs := [10230] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1294_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16207, 10229], outs := [10233] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1295_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16215, 10230], outs := [10234] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1296_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10233], outs := [16219, 16223], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1297_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10234], outs := [16227, 16231], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1298_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16219, 5502], outs := [10237] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1299_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16227, 5502], outs := [10238] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1300_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10237], outs := [16238, 16242, 16246, 16250, 16254], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1301_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10238], outs := [16261, 16265, 16269, 16273, 16277], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1302_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16238], outs := [10239] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1303_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16246], outs := [10259], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1304_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16250], outs := [10273], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1305_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16254], outs := [10291], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1306_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16261], outs := [10240] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1307_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16269], outs := [10260], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1308_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16273], outs := [10274], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1309_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16277], outs := [10292], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1310_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [10239, 5505], outs := [10245] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1311_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10259, 5514], outs := [10263] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1312_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10273, 5519], outs := [10277] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1313_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10291, 5523], outs := [10295] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1314_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [10240, 5505], outs := [10246] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1315_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10260, 5514], outs := [10264] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1316_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10274, 5519], outs := [10278] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1317_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10292, 5523], outs := [10296] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1318_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [10245], outs := [10247, 10249, 10251], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1319_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10263], outs := [10269], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
