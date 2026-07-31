/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1680_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [11130], outs := [11132] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1681_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [11148, 11166], outs := [11170] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1682_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11169], outs := [11171], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1683_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11170], outs := [11172], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1684_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11171, 5773], outs := [11177] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1685_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11172, 5773], outs := [11178] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1686_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11177], outs := [11187], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1687_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11178], outs := [11188], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1688_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [11131, 11187], outs := [11191] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1689_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [11132, 11188], outs := [11192] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1690_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [11117, 11191], outs := [11195] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1691_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [11118, 11192], outs := [11196] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1692_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11195], outs := [11201] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1693_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11196], outs := [11202] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1694_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16613, 11201], outs := [11205] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1695_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16621, 11202], outs := [11206] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1696_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11205], outs := [16671, 16675], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1697_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11206], outs := [16679, 16683], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1698_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16671, 5780], outs := [11209] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1699_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16679, 5780], outs := [11210] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1700_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11209, 5782], outs := [11211] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1701_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11210, 5782], outs := [11212] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1702_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [11211, 5784, 5785, 5786, 5787], outs := [11235], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1703_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [11212, 5784, 5785, 5786, 5787], outs := [11236], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1704_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11235], outs := [11237], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1705_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11236], outs := [11238], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1706_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11237], outs := [11243], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1707_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11238], outs := [11244], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1708_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11243, 5791], outs := [11247] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1709_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11244, 5791], outs := [11248] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1710_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11247], outs := [11257], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1711_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11248], outs := [11258], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1712_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11257], outs := [11261] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1713_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11258], outs := [11262] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1714_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16675, 11261], outs := [11265] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1715_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16683, 11262], outs := [11266] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1716_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11265], outs := [16687, 16691], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1717_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11266], outs := [16695, 16699], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1718_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16687, 5796], outs := [11269] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1719_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16695, 5796], outs := [11270] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
