/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1320_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10277], outs := [10287], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1321_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10295], outs := [10305], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1322_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [10246], outs := [10248, 10250, 10252], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1323_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10264], outs := [10270], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1324_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10278], outs := [10288], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1325_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10296], outs := [10306], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1326_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16242, 10247, 10249, 10253, 10255], outs := [10257], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1327_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [10269], outs := [10271] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1328_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [10287, 10305], outs := [10309] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1329_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16265, 10248, 10250, 10254, 10256], outs := [10258], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1330_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [10270], outs := [10272] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1331_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [10288, 10306], outs := [10310] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1332_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10309], outs := [10311], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1333_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10310], outs := [10312], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1334_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10311, 5528], outs := [10317] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1335_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10312, 5528], outs := [10318] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1336_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10317], outs := [10327], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1337_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10318], outs := [10328], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1338_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [10271, 10327], outs := [10331] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1339_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [10272, 10328], outs := [10332] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1340_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [10257, 10331], outs := [10335] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1341_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [10258, 10332], outs := [10336] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1342_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10335], outs := [10341] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1343_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10336], outs := [10342] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1344_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16223, 10341], outs := [10345] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1345_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16231, 10342], outs := [10346] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1346_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10345], outs := [16281, 16285], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1347_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10346], outs := [16289, 16293], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1348_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16281, 5535], outs := [10349] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1349_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16289, 5535], outs := [10350] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1350_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10349, 5537], outs := [10351] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1351_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10350, 5537], outs := [10352] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1352_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10351, 5539, 5540, 5541, 5542], outs := [10375], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1353_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10352, 5539, 5540, 5541, 5542], outs := [10376], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1354_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10375], outs := [10377], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1355_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10376], outs := [10378], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1356_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10377], outs := [10383], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1357_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10378], outs := [10384], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1358_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10383, 5546], outs := [10387] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1359_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10384, 5546], outs := [10388] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
