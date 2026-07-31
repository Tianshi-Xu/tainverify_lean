/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_720_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5646], outs := [5647] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_721_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8377, 5647], outs := [5648] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_722_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5648], outs := [8381, 8385], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_723_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8381, 5649], outs := [5650] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_724_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5650], outs := [8392, 8396, 8400, 8404, 8408], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_725_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8392], outs := [5651] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_726_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8400], outs := [5660], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_727_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8404], outs := [5665], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_728_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8408], outs := [5669], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_729_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5651, 5652], outs := [5653] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_730_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5660, 5661], outs := [5662] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_731_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5665, 5666], outs := [5667] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_732_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5669, 5670], outs := [5671] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_733_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5653], outs := [5654, 5655, 5656], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_734_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5662], outs := [5663], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_735_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5667], outs := [5668], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_736_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5671], outs := [5672], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_737_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8396, 5654, 5655, 5657, 5658], outs := [5659], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_738_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5663], outs := [5664] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_739_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5668, 5672], outs := [5673] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_740_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5673], outs := [5674], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_741_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5674, 5675], outs := [5676] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_742_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5676], outs := [5677], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_743_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5664, 5677], outs := [5678] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_744_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5659, 5678], outs := [5679] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_745_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5679], outs := [5680] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_746_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8385, 5680], outs := [5681] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_747_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5681], outs := [8412, 8416], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_748_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8412, 5682], outs := [5683] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_749_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5683, 5684], outs := [5685] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_750_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5685 + r)), outs := [5690], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_751_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5690], outs := [5691], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_752_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5691], outs := [5692], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_753_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5692, 5693], outs := [5694] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_754_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5694], outs := [5695], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_755_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5695], outs := [5696] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_756_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8416, 5696], outs := [5697] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_757_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5697], outs := [8420, 8424], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_758_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8420, 5698], outs := [5699] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_759_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5699], outs := [8431, 8435, 8439, 8443, 8447], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
