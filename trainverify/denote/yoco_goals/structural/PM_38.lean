/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1520_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [10755, 5652], outs := [10761] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1521_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10775, 5661], outs := [10779] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1522_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10789, 5666], outs := [10793] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1523_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10807, 5670], outs := [10811] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1524_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [10756, 5652], outs := [10762] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1525_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10776, 5661], outs := [10780] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1526_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10790, 5666], outs := [10794] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1527_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10808, 5670], outs := [10812] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1528_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [10761], outs := [10763, 10765, 10767], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1529_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10779], outs := [10785], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1530_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10793], outs := [10803], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1531_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10811], outs := [10821], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1532_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [10762], outs := [10764, 10766, 10768], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1533_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10780], outs := [10786], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1534_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10794], outs := [10804], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1535_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10812], outs := [10822], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1536_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16476, 10763, 10765, 10769, 10771], outs := [10773], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1537_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [10785], outs := [10787] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1538_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [10803, 10821], outs := [10825] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1539_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16499, 10764, 10766, 10770, 10772], outs := [10774], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1540_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [10786], outs := [10788] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1541_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [10804, 10822], outs := [10826] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1542_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10825], outs := [10827], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1543_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10826], outs := [10828], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1544_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10827, 5675], outs := [10833] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1545_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10828, 5675], outs := [10834] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1546_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10833], outs := [10843], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1547_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10834], outs := [10844], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1548_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [10787, 10843], outs := [10847] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1549_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [10788, 10844], outs := [10848] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1550_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [10773, 10847], outs := [10851] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1551_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [10774, 10848], outs := [10852] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1552_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10851], outs := [10857] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1553_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10852], outs := [10858] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1554_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16457, 10857], outs := [10861] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1555_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16465, 10858], outs := [10862] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1556_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10861], outs := [16515, 16519], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1557_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10862], outs := [16523, 16527], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1558_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16515, 5682], outs := [10865] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1559_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16523, 5682], outs := [10866] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
