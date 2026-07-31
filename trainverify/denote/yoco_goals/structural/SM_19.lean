/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_760_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8431], outs := [5700] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_761_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8439], outs := [5709], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_762_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8443], outs := [5714], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_763_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8447], outs := [5718], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_764_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5700, 5701], outs := [5702] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_765_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5709, 5710], outs := [5711] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_766_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5714, 5715], outs := [5716] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_767_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5718, 5719], outs := [5720] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_768_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5702], outs := [5703, 5704, 5705], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_769_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5711], outs := [5712], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_770_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5716], outs := [5717], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_771_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5720], outs := [5721], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_772_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8435, 5703, 5704, 5706, 5707], outs := [5708], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_773_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5712], outs := [5713] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_774_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5717, 5721], outs := [5722] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_775_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5722], outs := [5723], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_776_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5723, 5724], outs := [5725] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_777_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5725], outs := [5726], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_778_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5713, 5726], outs := [5727] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_779_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5708, 5727], outs := [5728] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_780_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5728], outs := [5729] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_781_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8424, 5729], outs := [5730] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_782_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5730], outs := [8451, 8455], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_783_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8451, 5731], outs := [5732] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_784_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5732, 5733], outs := [5734] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_785_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5734 + r)), outs := [5739], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_786_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5739], outs := [5740], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_787_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5740], outs := [5741], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_788_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5741, 5742], outs := [5743] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_789_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5743], outs := [5744], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_790_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5744], outs := [5745] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_791_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8455, 5745], outs := [5746] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_792_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5746], outs := [8459, 8463], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_793_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8459, 5747], outs := [5748] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_794_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5748], outs := [8470, 8474, 8478, 8482, 8486], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_795_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8470], outs := [5749] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_796_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8478], outs := [5758], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_797_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8482], outs := [5763], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_798_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8486], outs := [5767], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_799_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5749, 5750], outs := [5751] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
