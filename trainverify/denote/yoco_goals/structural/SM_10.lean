/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_400_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5236], outs := [5237], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_401_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5237], outs := [5238], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_402_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5238, 5239], outs := [5240] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_403_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5240], outs := [5241], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_404_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5241], outs := [5242] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_405_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7907, 5242], outs := [5243] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_406_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5243], outs := [7924, 7928], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_407_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7924, 5244], outs := [5245] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_408_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5245], outs := [7935, 7939, 7943, 7947, 7951], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_409_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7935], outs := [5246] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_410_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7943], outs := [5255], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_411_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7947], outs := [5260], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_412_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7951], outs := [5264], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_413_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5246, 5247], outs := [5248] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_414_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5255, 5256], outs := [5257] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_415_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5260, 5261], outs := [5262] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_416_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5264, 5265], outs := [5266] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_417_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5248], outs := [5249, 5250, 5251], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_418_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5257], outs := [5258], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_419_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5262], outs := [5263], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_420_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5266], outs := [5267], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_421_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7939, 5249, 5250, 5252, 5253], outs := [5254], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_422_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5258], outs := [5259] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_423_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5263, 5267], outs := [5268] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_424_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5268], outs := [5269], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_425_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5269, 5270], outs := [5271] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_426_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5271], outs := [5272], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_427_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5259, 5272], outs := [5273] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_428_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5254, 5273], outs := [5274] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_429_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5274], outs := [5275] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_430_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7928, 5275], outs := [5276] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_431_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5276], outs := [7955, 7959], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_432_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7955, 5277], outs := [5278] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_433_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5278], outs := [7964, 7968, 7972], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_434_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7964, 5279], outs := [5280] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_435_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7968, 5281], outs := [5282] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_436_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7972, 5283], outs := [5284] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_437_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5285, 5280, 5282], outs := [5286, 5287], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_438_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5286, 5287, 5284, 5288, 5289], outs := [5290], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_439_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5290], outs := [5291], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
