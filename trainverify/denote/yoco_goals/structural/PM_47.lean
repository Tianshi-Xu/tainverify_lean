/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1880_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11653], outs := [11663], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1881_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11671], outs := [11681], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1882_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [11622], outs := [11624, 11626, 11628], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1883_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11640], outs := [11646], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1884_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11654], outs := [11664], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1885_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11672], outs := [11682], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1886_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16866, 11623, 11625, 11629, 11631], outs := [11633], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1887_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_stack", ins := [7483, 7669, 7855, 8041, 8227, 8413, 8599, 8785, 8971, 9157, 9343, 9529, 9733, 9905, 10077, 10249, 10421, 10593, 10765, 10937, 11109, 11281, 11453, 11625], outs := [11729] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1888_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_stack", ins := [7485, 7671, 7857, 8043, 8229, 8415, 8601, 8787, 8973, 9159, 9345, 9531, 9735, 9907, 10079, 10251, 10423, 10595, 10767, 10939, 11111, 11283, 11455, 11627], outs := [11781] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1889_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [11645], outs := [11647] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1890_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [11663, 11681], outs := [11685] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1891_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16889, 11624, 11626, 11630, 11632], outs := [11634], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1892_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_stack", ins := [7484, 7670, 7856, 8042, 8228, 8414, 8600, 8786, 8972, 9158, 9344, 9530, 9734, 9906, 10078, 10250, 10422, 10594, 10766, 10938, 11110, 11282, 11454, 11626], outs := [11730] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1893_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_stack", ins := [7486, 7672, 7858, 8044, 8230, 8416, 8602, 8788, 8974, 9160, 9346, 9532, 9736, 9908, 10080, 10252, 10424, 10596, 10768, 10940, 11112, 11284, 11456, 11628], outs := [11782] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1894_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [11646], outs := [11648] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1895_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [11664, 11682], outs := [11686] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1896_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11685], outs := [11687], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1897_wf : IsWellFormedNode pm { rank := 0, op := "OpName.AllGatherPrim", ins := [11729, 11730], outs := [4675], params := [1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1898_wf : IsWellFormedNode pm { rank := 0, op := "OpName.AllGatherPrim", ins := [11781, 11782], outs := [4676], params := [1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1899_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11686], outs := [11688], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1900_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11687, 5920], outs := [11693] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1901_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11688, 5920], outs := [11694] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1902_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11693], outs := [11703], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1903_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11694], outs := [11704], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1904_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [11647, 11703], outs := [11707] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1905_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [11648, 11704], outs := [11708] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1906_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [11633, 11707], outs := [11711] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1907_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [11634, 11708], outs := [11712] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1908_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11711], outs := [11717] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1909_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11712], outs := [11718] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1910_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16847, 11717], outs := [11721] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1911_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16855, 11718], outs := [11722] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1912_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11721, 5927], outs := [11727], params := [2, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1913_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11722, 5927], outs := [11728], params := [2, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1914_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [11727, 5929], outs := [11833] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1915_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [11728, 5929], outs := [11834] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1916_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_inner_chunk_ce", ins := [11833, 5931, 11835], outs := [11837, 11839], params := [1024] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1917_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_inner_chunk_ce", ins := [11834, 5931, 11836], outs := [11838, 11840], params := [1024] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1918_wf : IsWellFormedNode pm { rank := 0, op := "OpName.AllGatherPrim", ins := [11837, 11838], outs := [4673], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1919_wf : IsWellFormedNode pm { rank := 0, op := "OpName.AllGatherPrim", ins := [11839, 11840], outs := [4674], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
