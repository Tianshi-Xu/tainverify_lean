/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_760_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [8994, 9050], outs := [9054] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_761_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [8979, 9053], outs := [9057] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_762_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [8980, 9054], outs := [9058] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_763_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9057], outs := [9063] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_764_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9058], outs := [9064] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_765_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15371, 9063], outs := [9067] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_766_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15379, 9064], outs := [9068] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_767_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9067], outs := [15429, 15433], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_768_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9068], outs := [15437, 15441], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_769_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15429, 5169], outs := [9071] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_770_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15437, 5169], outs := [9072] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_771_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9071], outs := [15446, 15450, 15454], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_772_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9072], outs := [15459, 15463, 15467], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_773_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15446, 5171], outs := [9073] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_774_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15450, 5173], outs := [9085] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_775_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15454, 5175], outs := [9095] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_776_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15459, 5171], outs := [9074] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_777_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15463, 5173], outs := [9086] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_778_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15467, 5175], outs := [9096] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_779_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11862, 9105, 9073, 9085], outs := [9107, 9109], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_780_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11862, 9106, 9074, 9086], outs := [9108, 9110], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_781_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [9107, 9109, 9095, 5180, 5181], outs := [9111], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_782_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [9108, 9110, 9096, 5180, 5181], outs := [9112], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_783_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9111], outs := [9113], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_784_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9112], outs := [9114], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_785_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9113], outs := [9119], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_786_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9114], outs := [9120], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_787_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9119, 5185], outs := [9123] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_788_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9120, 5185], outs := [9124] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_789_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9123], outs := [9133], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_790_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9124], outs := [9134], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_791_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9133], outs := [9137] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_792_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9134], outs := [9138] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_793_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15433, 9137], outs := [9141] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_794_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15441, 9138], outs := [9142] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_795_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9141], outs := [15471, 15475], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_796_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9142], outs := [15479, 15483], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_797_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15471, 5190], outs := [9145] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_798_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15479, 5190], outs := [9146] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_799_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [9145], outs := [15490, 15494, 15498, 15502, 15506], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
