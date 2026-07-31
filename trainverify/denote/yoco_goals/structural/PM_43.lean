/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1720_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11269], outs := [16706, 16710, 16714, 16718, 16722], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1721_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11270], outs := [16729, 16733, 16737, 16741, 16745], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1722_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16706], outs := [11271] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1723_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16714], outs := [11291], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1724_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16718], outs := [11305], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1725_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16722], outs := [11323], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1726_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16729], outs := [11272] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1727_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16737], outs := [11292], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1728_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16741], outs := [11306], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1729_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16745], outs := [11324], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1730_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [11271, 5799], outs := [11277] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1731_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11291, 5808], outs := [11295] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1732_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11305, 5813], outs := [11309] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1733_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11323, 5817], outs := [11327] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1734_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [11272, 5799], outs := [11278] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1735_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11292, 5808], outs := [11296] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1736_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11306, 5813], outs := [11310] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1737_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11324, 5817], outs := [11328] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1738_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [11277], outs := [11279, 11281, 11283], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1739_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11295], outs := [11301], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1740_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11309], outs := [11319], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1741_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11327], outs := [11337], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1742_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [11278], outs := [11280, 11282, 11284], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1743_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11296], outs := [11302], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1744_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11310], outs := [11320], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1745_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11328], outs := [11338], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1746_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16710, 11279, 11281, 11285, 11287], outs := [11289], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1747_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [11301], outs := [11303] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1748_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [11319, 11337], outs := [11341] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1749_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16733, 11280, 11282, 11286, 11288], outs := [11290], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1750_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [11302], outs := [11304] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1751_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [11320, 11338], outs := [11342] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1752_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11341], outs := [11343], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1753_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11342], outs := [11344], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1754_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11343, 5822], outs := [11349] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1755_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11344, 5822], outs := [11350] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1756_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11349], outs := [11359], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1757_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11350], outs := [11360], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1758_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [11303, 11359], outs := [11363] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1759_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [11304, 11360], outs := [11364] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
