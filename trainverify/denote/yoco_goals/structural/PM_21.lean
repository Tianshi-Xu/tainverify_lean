/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_840_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [9166, 9240], outs := [9244] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_841_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9243], outs := [9249] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_842_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9244], outs := [9250] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_843_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15475, 9249], outs := [9253] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_844_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15483, 9250], outs := [9254] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_845_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9253], outs := [15533, 15537], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_846_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9254], outs := [15541, 15545], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_847_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15533, 5223], outs := [9257] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_848_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15541, 5223], outs := [9258] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_849_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9257], outs := [15550, 15554, 15558], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_850_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9258], outs := [15563, 15567, 15571], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_851_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15550, 5225], outs := [9259] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_852_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15554, 5227], outs := [9271] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_853_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15558, 5229], outs := [9281] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_854_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15563, 5225], outs := [9260] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_855_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15567, 5227], outs := [9272] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_856_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15571, 5229], outs := [9282] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_857_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11863, 9291, 9259, 9271], outs := [9293, 9295], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_858_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11863, 9292, 9260, 9272], outs := [9294, 9296], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_859_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [9293, 9295, 9281, 5234, 5235], outs := [9297], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_860_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9294, 9296, 9282, 5234, 5235], outs := [9298], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_861_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9297], outs := [9299], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_862_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9298], outs := [9300], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_863_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9299], outs := [9305], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_864_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9300], outs := [9306], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_865_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9305, 5239], outs := [9309] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_866_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9306, 5239], outs := [9310] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_867_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9309], outs := [9319], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_868_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9310], outs := [9320], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_869_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9319], outs := [9323] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_870_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9320], outs := [9324] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_871_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15537, 9323], outs := [9327] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_872_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15545, 9324], outs := [9328] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_873_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9327], outs := [15575, 15579], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_874_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9328], outs := [15583, 15587], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_875_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15575, 5244], outs := [9331] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_876_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15583, 5244], outs := [9332] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_877_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9331], outs := [15594, 15598, 15602, 15606, 15610], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_878_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9332], outs := [15617, 15621, 15625, 15629, 15633], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_879_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [15594], outs := [9333] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
