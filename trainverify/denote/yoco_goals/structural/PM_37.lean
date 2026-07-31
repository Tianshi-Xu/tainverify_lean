/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1480_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [10601, 10675], outs := [10679] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1481_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [10602, 10676], outs := [10680] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1482_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10679], outs := [10685] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1483_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10680], outs := [10686] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1484_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16379, 10685], outs := [10689] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1485_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16387, 10686], outs := [10690] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1486_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10689], outs := [16437, 16441], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1487_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10690], outs := [16445, 16449], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1488_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16437, 5633], outs := [10693] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1489_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16445, 5633], outs := [10694] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1490_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10693, 5635], outs := [10695] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1491_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10694, 5635], outs := [10696] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1492_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10695, 5637, 5638, 5639, 5640], outs := [10719], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1493_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10696, 5637, 5638, 5639, 5640], outs := [10720], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1494_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10719], outs := [10721], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1495_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10720], outs := [10722], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1496_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10721], outs := [10727], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1497_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10722], outs := [10728], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1498_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10727, 5644], outs := [10731] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1499_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10728, 5644], outs := [10732] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1500_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10731], outs := [10741], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1501_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10732], outs := [10742], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1502_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10741], outs := [10745] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1503_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10742], outs := [10746] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1504_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16441, 10745], outs := [10749] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1505_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16449, 10746], outs := [10750] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1506_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10749], outs := [16453, 16457], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1507_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10750], outs := [16461, 16465], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1508_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16453, 5649], outs := [10753] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1509_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16461, 5649], outs := [10754] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1510_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10753], outs := [16472, 16476, 16480, 16484, 16488], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1511_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10754], outs := [16495, 16499, 16503, 16507, 16511], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1512_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16472], outs := [10755] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1513_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16480], outs := [10775], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1514_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16484], outs := [10789], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1515_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16488], outs := [10807], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1516_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16495], outs := [10756] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1517_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16503], outs := [10776], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1518_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16507], outs := [10790], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1519_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16511], outs := [10808], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
