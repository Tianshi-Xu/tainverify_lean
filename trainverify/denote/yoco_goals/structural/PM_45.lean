/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1800_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [11443, 5848], outs := [11449] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1801_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11463, 5857], outs := [11467] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1802_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11477, 5862], outs := [11481] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1803_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11495, 5866], outs := [11499] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1804_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [11444, 5848], outs := [11450] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1805_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11464, 5857], outs := [11468] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1806_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11478, 5862], outs := [11482] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1807_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11496, 5866], outs := [11500] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1808_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [11449], outs := [11451, 11453, 11455], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1809_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11467], outs := [11473], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1810_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11481], outs := [11491], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1811_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11499], outs := [11509], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1812_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [11450], outs := [11452, 11454, 11456], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1813_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11468], outs := [11474], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1814_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11482], outs := [11492], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1815_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11500], outs := [11510], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1816_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16788, 11451, 11453, 11457, 11459], outs := [11461], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1817_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [11473], outs := [11475] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1818_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [11491, 11509], outs := [11513] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1819_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16811, 11452, 11454, 11458, 11460], outs := [11462], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1820_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [11474], outs := [11476] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1821_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [11492, 11510], outs := [11514] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1822_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11513], outs := [11515], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1823_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11514], outs := [11516], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1824_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11515, 5871], outs := [11521] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1825_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11516, 5871], outs := [11522] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1826_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11521], outs := [11531], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1827_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11522], outs := [11532], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1828_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [11475, 11531], outs := [11535] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1829_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [11476, 11532], outs := [11536] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1830_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [11461, 11535], outs := [11539] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1831_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [11462, 11536], outs := [11540] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1832_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11539], outs := [11545] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1833_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11540], outs := [11546] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1834_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16769, 11545], outs := [11549] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1835_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16777, 11546], outs := [11550] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1836_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11549], outs := [16827, 16831], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1837_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11550], outs := [16835, 16839], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1838_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16827, 5878], outs := [11553] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1839_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16835, 5878], outs := [11554] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
