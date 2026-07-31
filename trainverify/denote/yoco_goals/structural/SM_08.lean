/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_320_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5123, 5118, 5120], outs := [5124, 5125], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_321_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5124, 5125, 5122, 5126, 5127], outs := [5128], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_322_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5128], outs := [5129], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_323_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5129], outs := [5130], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_324_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5130, 5131], outs := [5132] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_325_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5132], outs := [5133], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_326_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5133], outs := [5134] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_327_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7803, 5134], outs := [5135] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_328_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5135], outs := [7820, 7824], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_329_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7820, 5136], outs := [5137] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_330_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5137], outs := [7831, 7835, 7839, 7843, 7847], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_331_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7831], outs := [5138] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_332_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7839], outs := [5147], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_333_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7843], outs := [5152], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_334_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7847], outs := [5156], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_335_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5138, 5139], outs := [5140] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_336_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5147, 5148], outs := [5149] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_337_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5152, 5153], outs := [5154] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_338_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5156, 5157], outs := [5158] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_339_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5140], outs := [5141, 5142, 5143], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_340_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5149], outs := [5150], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_341_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5154], outs := [5155], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_342_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5158], outs := [5159], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_343_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7835, 5141, 5142, 5144, 5145], outs := [5146], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_344_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5150], outs := [5151] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_345_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5155, 5159], outs := [5160] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_346_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5160], outs := [5161], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_347_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5161, 5162], outs := [5163] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_348_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5163], outs := [5164], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_349_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5151, 5164], outs := [5165] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_350_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5146, 5165], outs := [5166] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_351_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5166], outs := [5167] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_352_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7824, 5167], outs := [5168] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_353_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5168], outs := [7851, 7855], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_354_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7851, 5169], outs := [5170] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_355_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5170], outs := [7860, 7864, 7868], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_356_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7860, 5171], outs := [5172] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_357_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7864, 5173], outs := [5174] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_358_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7868, 5175], outs := [5176] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_359_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5177, 5172, 5174], outs := [5178, 5179], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
