/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1400_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [10442], outs := [10444] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1401_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [10460, 10478], outs := [10482] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1402_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10481], outs := [10483], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1403_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10482], outs := [10484], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1404_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10483, 5577], outs := [10489] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1405_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10484, 5577], outs := [10490] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1406_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10489], outs := [10499], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1407_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10490], outs := [10500], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1408_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [10443, 10499], outs := [10503] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1409_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [10444, 10500], outs := [10504] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1410_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [10429, 10503], outs := [10507] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1411_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [10430, 10504], outs := [10508] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1412_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10507], outs := [10513] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1413_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10508], outs := [10514] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1414_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16301, 10513], outs := [10517] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1415_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16309, 10514], outs := [10518] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1416_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10517], outs := [16359, 16363], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1417_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10518], outs := [16367, 16371], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1418_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16359, 5584], outs := [10521] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1419_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16367, 5584], outs := [10522] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1420_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [10521, 5586], outs := [10523] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1421_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [10522, 5586], outs := [10524] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1422_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [10523, 5588, 5589, 5590, 5591], outs := [10547], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1423_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [10524, 5588, 5589, 5590, 5591], outs := [10548], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1424_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10547], outs := [10549], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1425_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10548], outs := [10550], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1426_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10549], outs := [10555], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1427_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10550], outs := [10556], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1428_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10555, 5595], outs := [10559] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1429_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [10556, 5595], outs := [10560] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1430_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10559], outs := [10569], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1431_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10560], outs := [10570], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1432_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [10569], outs := [10573] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1433_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [10570], outs := [10574] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1434_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16363, 10573], outs := [10577] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1435_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16371, 10574], outs := [10578] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1436_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [10577], outs := [16375, 16379], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1437_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [10578], outs := [16383, 16387], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1438_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16375, 5600], outs := [10581] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1439_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16383, 5600], outs := [10582] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
