/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1640_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11075], outs := [11085], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1641_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11076], outs := [11086], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1642_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11085], outs := [11089] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1643_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11086], outs := [11090] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1644_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16597, 11089], outs := [11093] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1645_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16605, 11090], outs := [11094] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1646_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11093], outs := [16609, 16613], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1647_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11094], outs := [16617, 16621], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1648_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16609, 5747], outs := [11097] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1649_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16617, 5747], outs := [11098] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1650_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11097], outs := [16628, 16632, 16636, 16640, 16644], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1651_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11098], outs := [16651, 16655, 16659, 16663, 16667], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1652_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16628], outs := [11099] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1653_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16636], outs := [11119], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1654_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16640], outs := [11133], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1655_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16644], outs := [11151], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1656_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16651], outs := [11100] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1657_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16659], outs := [11120], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1658_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16663], outs := [11134], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1659_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16667], outs := [11152], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1660_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [11099, 5750], outs := [11105] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1661_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11119, 5759], outs := [11123] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1662_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11133, 5764], outs := [11137] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1663_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11151, 5768], outs := [11155] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1664_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [11100, 5750], outs := [11106] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1665_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11120, 5759], outs := [11124] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1666_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11134, 5764], outs := [11138] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1667_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11152, 5768], outs := [11156] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1668_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [11105], outs := [11107, 11109, 11111], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1669_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11123], outs := [11129], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1670_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11137], outs := [11147], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1671_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11155], outs := [11165], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1672_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [11106], outs := [11108, 11110, 11112], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_1673_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11124], outs := [11130], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1674_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11138], outs := [11148], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1675_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11156], outs := [11166], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1676_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [16632, 11107, 11109, 11113, 11115], outs := [11117], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1677_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [11129], outs := [11131] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1678_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [11147, 11165], outs := [11169] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1679_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [16655, 11108, 11110, 11114, 11116], outs := [11118], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
