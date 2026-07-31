/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_520_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5366, 5367], outs := [5368] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_521_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5371, 5372], outs := [5373] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_522_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5375, 5376], outs := [5377] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_523_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5359], outs := [5360, 5361, 5362], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_524_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5368], outs := [5369], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_525_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5373], outs := [5374], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_526_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5377], outs := [5378], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_527_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8162, 5360, 5361, 5363, 5364], outs := [5365], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_528_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5369], outs := [5370] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_529_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5374, 5378], outs := [5379] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_530_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5379], outs := [5380], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_531_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5380, 5381], outs := [5382] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_532_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5382], outs := [5383], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_533_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5370, 5383], outs := [5384] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_534_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5365, 5384], outs := [5385] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_535_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5385], outs := [5386] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_536_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8151, 5386], outs := [5387] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_537_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5387], outs := [8178, 8182], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_538_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8178, 5388], outs := [5389] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_539_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5389, 5390], outs := [5391] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_540_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5391 + r)), outs := [5396], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_541_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5396], outs := [5397], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_542_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5397], outs := [5398], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_543_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5398, 5399], outs := [5400] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_544_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5400], outs := [5401], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_545_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5401], outs := [5402] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_546_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8182, 5402], outs := [5403] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_547_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5403], outs := [8186, 8190], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_548_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8186, 5404], outs := [5405] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_549_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5405], outs := [8197, 8201, 8205, 8209, 8213], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_550_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8197], outs := [5406] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_551_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8205], outs := [5415], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_552_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8209], outs := [5420], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_553_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8213], outs := [5424], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_554_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5406, 5407], outs := [5408] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_555_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5415, 5416], outs := [5417] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_556_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5420, 5421], outs := [5422] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_557_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5424, 5425], outs := [5426] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_558_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5408], outs := [5409, 5410, 5411], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_559_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5417], outs := [5418], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
