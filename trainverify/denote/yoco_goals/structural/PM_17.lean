/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_680_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8854], outs := [8864], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_681_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [8807, 8863], outs := [8867] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_682_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [8808, 8864], outs := [8868] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_683_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [8793, 8867], outs := [8871] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_684_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [8794, 8868], outs := [8872] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_685_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8871], outs := [8877] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_686_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8872], outs := [8878] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_687_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15267, 8877], outs := [8881] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_688_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15275, 8878], outs := [8882] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_689_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8881], outs := [15325, 15329], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_690_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8882], outs := [15333, 15337], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_691_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15325, 5115], outs := [8885] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_692_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15333, 5115], outs := [8886] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_693_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8885], outs := [15342, 15346, 15350], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_694_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8886], outs := [15355, 15359, 15363], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_695_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15342, 5117], outs := [8887] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_696_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15346, 5119], outs := [8899] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_697_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15350, 5121], outs := [8909] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_698_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15355, 5117], outs := [8888] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_699_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15359, 5119], outs := [8900] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_700_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15363, 5121], outs := [8910] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_701_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11861, 8919, 8887, 8899], outs := [8921, 8923], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_702_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11861, 8920, 8888, 8900], outs := [8922, 8924], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_703_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8921, 8923, 8909, 5126, 5127], outs := [8925], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_704_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8922, 8924, 8910, 5126, 5127], outs := [8926], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_705_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8925], outs := [8927], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_706_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8926], outs := [8928], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_707_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8927], outs := [8933], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_708_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8928], outs := [8934], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_709_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8933, 5131], outs := [8937] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_710_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8934, 5131], outs := [8938] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_711_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8937], outs := [8947], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_712_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8938], outs := [8948], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_713_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8947], outs := [8951] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_714_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8948], outs := [8952] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_715_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15329, 8951], outs := [8955] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_716_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15337, 8952], outs := [8956] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_717_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8955], outs := [15367, 15371], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_718_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8956], outs := [15375, 15379], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_719_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15367, 5136], outs := [8959] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
