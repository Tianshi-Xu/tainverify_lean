/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1440_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10581], outs := [16394, 16398, 16402, 16406, 16410], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1441_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10582], outs := [16417, 16421, 16425, 16429, 16433], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1442_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16394], outs := [10583] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1443_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16402], outs := [10603], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1444_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16406], outs := [10617], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1445_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16410], outs := [10635], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1446_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16417], outs := [10584] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1447_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16425], outs := [10604], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1448_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16429], outs := [10618], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1449_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16433], outs := [10636], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1450_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [10583, 5603], outs := [10589] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1451_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10603, 5612], outs := [10607] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1452_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10617, 5617], outs := [10621] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1453_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10635, 5621], outs := [10639] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1454_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [10584, 5603], outs := [10590] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1455_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10604, 5612], outs := [10608] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1456_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10618, 5617], outs := [10622] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1457_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10636, 5621], outs := [10640] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1458_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [10589], outs := [10591, 10593, 10595], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1459_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10607], outs := [10613], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1460_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10621], outs := [10631], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1461_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10639], outs := [10649], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1462_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [10590], outs := [10592, 10594, 10596], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1463_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10608], outs := [10614], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1464_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10622], outs := [10632], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1465_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10640], outs := [10650], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1466_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16398, 10591, 10593, 10597, 10599], outs := [10601], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1467_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [10613], outs := [10615] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1468_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [10631, 10649], outs := [10653] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1469_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16421, 10592, 10594, 10598, 10600], outs := [10602], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1470_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [10614], outs := [10616] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1471_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [10632, 10650], outs := [10654] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1472_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10653], outs := [10655], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1473_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10654], outs := [10656], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1474_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10655, 5626], outs := [10661] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1475_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10656, 5626], outs := [10662] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1476_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10661], outs := [10671], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1477_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10662], outs := [10672], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1478_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [10615, 10671], outs := [10675] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1479_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [10616, 10672], outs := [10676] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
