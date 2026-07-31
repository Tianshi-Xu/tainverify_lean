/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1840_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11553, 5880], outs := [11555] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1841_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11554, 5880], outs := [11556] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1842_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [11555, 5882, 5883, 5884, 5885], outs := [11579], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1843_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [11556, 5882, 5883, 5884, 5885], outs := [11580], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1844_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11579], outs := [11581], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1845_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11580], outs := [11582], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1846_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11581], outs := [11587], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1847_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11582], outs := [11588], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1848_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11587, 5889], outs := [11591] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1849_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11588, 5889], outs := [11592] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1850_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11591], outs := [11601], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1851_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11592], outs := [11602], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1852_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11601], outs := [11605] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1853_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11602], outs := [11606] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1854_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16831, 11605], outs := [11609] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1855_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16839, 11606], outs := [11610] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1856_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11609], outs := [16843, 16847], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1857_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11610], outs := [16851, 16855], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1858_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16843, 5894], outs := [11613] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1859_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16851, 5894], outs := [11614] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1860_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11613], outs := [16862, 16866, 16870, 16874, 16878], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1861_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11614], outs := [16885, 16889, 16893, 16897, 16901], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1862_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16862], outs := [11615] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1863_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16870], outs := [11635], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1864_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16874], outs := [11649], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1865_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16878], outs := [11667], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1866_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16885], outs := [11616] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1867_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16893], outs := [11636], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1868_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16897], outs := [11650], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1869_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16901], outs := [11668], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1870_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [11615, 5897], outs := [11621] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1871_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11635, 5906], outs := [11639] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1872_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11649, 5911], outs := [11653] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1873_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11667, 5915], outs := [11671] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1874_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [11616, 5897], outs := [11622] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1875_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11636, 5906], outs := [11640] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1876_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11650, 5911], outs := [11654] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1877_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11668, 5915], outs := [11672] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1878_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [11621], outs := [11623, 11625, 11627], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1879_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11639], outs := [11645], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
