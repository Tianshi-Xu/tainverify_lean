/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_1760_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [11289, 11363], outs := [11367] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1761_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [11290, 11364], outs := [11368] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1762_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11367], outs := [11373] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1763_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11368], outs := [11374] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1764_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16691, 11373], outs := [11377] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1765_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16699, 11374], outs := [11378] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1766_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11377], outs := [16749, 16753], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1767_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11378], outs := [16757, 16761], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1768_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16749, 5829], outs := [11381] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1769_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16757, 5829], outs := [11382] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1770_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [11381, 5831], outs := [11383] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1771_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [11382, 5831], outs := [11384] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1772_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_zigzag", ins := [11383, 5833, 5834, 5835, 5836], outs := [11407], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1773_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_zigzag", ins := [11384, 5833, 5834, 5835, 5836], outs := [11408], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1774_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11407], outs := [11409], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1775_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11408], outs := [11410], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1776_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11409], outs := [11415], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1777_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11410], outs := [11416], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1778_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [11415, 5840], outs := [11419] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1779_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [11416, 5840], outs := [11420] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1780_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [11419], outs := [11429], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1781_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [11420], outs := [11430], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1782_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11429], outs := [11433] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1783_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11430], outs := [11434] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1784_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [16753, 11433], outs := [11437] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1785_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [16761, 11434], outs := [11438] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1786_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11437], outs := [16765, 16769], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1787_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11438], outs := [16773, 16777], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_1788_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [16765, 5845], outs := [11441] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1789_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [16773, 5845], outs := [11442] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1790_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [11441], outs := [16784, 16788, 16792, 16796, 16800], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1791_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [11442], outs := [16807, 16811, 16815, 16819, 16823], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_1792_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [16784], outs := [11443] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1793_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16792], outs := [11463], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1794_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16796], outs := [11477], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1795_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [16800], outs := [11495], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1796_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [16807], outs := [11444] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1797_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16815], outs := [11464], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1798_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16819], outs := [11478], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_1799_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [16823], outs := [11496], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
