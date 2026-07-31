/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1600_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10965], outs := [10975], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1601_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [10983], outs := [10993], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1602_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [10934], outs := [10936, 10938, 10940], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1603_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10952], outs := [10958], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1604_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10966], outs := [10976], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1605_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [10984], outs := [10994], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1606_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16554, 10935, 10937, 10941, 10943], outs := [10945], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1607_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [10957], outs := [10959] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1608_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [10975, 10993], outs := [10997] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1609_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16577, 10936, 10938, 10942, 10944], outs := [10946], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1610_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [10958], outs := [10960] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1611_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [10976, 10994], outs := [10998] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1612_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [10997], outs := [10999], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1613_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [10998], outs := [11000], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1614_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [10999, 5724], outs := [11005] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1615_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11000, 5724], outs := [11006] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1616_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11005], outs := [11015], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1617_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11006], outs := [11016], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1618_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [10959, 11015], outs := [11019] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1619_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [10960, 11016], outs := [11020] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1620_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [10945, 11019], outs := [11023] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1621_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [10946, 11020], outs := [11024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1622_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11023], outs := [11029] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1623_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11024], outs := [11030] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1624_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16535, 11029], outs := [11033] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1625_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16543, 11030], outs := [11034] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1626_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11033], outs := [16593, 16597], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1627_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11034], outs := [16601, 16605], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1628_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16593, 5731], outs := [11037] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1629_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16601, 5731], outs := [11038] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1630_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11037, 5733], outs := [11039] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1631_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11038, 5733], outs := [11040] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1632_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [11039, 5735, 5736, 5737, 5738], outs := [11063], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1633_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [11040, 5735, 5736, 5737, 5738], outs := [11064], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1634_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11063], outs := [11065], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1635_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11064], outs := [11066], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1636_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11065], outs := [11071], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1637_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11066], outs := [11072], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1638_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11071, 5742], outs := [11075] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1639_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11072, 5742], outs := [11076] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
