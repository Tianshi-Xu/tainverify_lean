/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_360_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5178, 5179, 5176, 5180, 5181], outs := [5182], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_361_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5182], outs := [5183], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_362_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5183], outs := [5184], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_363_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5184, 5185], outs := [5186] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_364_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5186], outs := [5187], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_365_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5187], outs := [5188] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_366_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7855, 5188], outs := [5189] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_367_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5189], outs := [7872, 7876], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_368_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7872, 5190], outs := [5191] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_369_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5191], outs := [7883, 7887, 7891, 7895, 7899], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_370_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7883], outs := [5192] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_371_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7891], outs := [5201], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_372_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7895], outs := [5206], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_373_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7899], outs := [5210], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_374_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5192, 5193], outs := [5194] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_375_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5201, 5202], outs := [5203] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_376_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5206, 5207], outs := [5208] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_377_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5210, 5211], outs := [5212] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_378_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5194], outs := [5195, 5196, 5197], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_379_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5203], outs := [5204], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_380_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5208], outs := [5209], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_381_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5212], outs := [5213], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_382_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7887, 5195, 5196, 5198, 5199], outs := [5200], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_383_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5204], outs := [5205] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_384_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5209, 5213], outs := [5214] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_385_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5214], outs := [5215], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_386_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5215, 5216], outs := [5217] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_387_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5217], outs := [5218], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_388_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5205, 5218], outs := [5219] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_389_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5200, 5219], outs := [5220] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_390_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5220], outs := [5221] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_391_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7876, 5221], outs := [5222] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_392_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5222], outs := [7903, 7907], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_393_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7903, 5223], outs := [5224] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_394_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5224], outs := [7912, 7916, 7920], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_395_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7912, 5225], outs := [5226] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_396_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7916, 5227], outs := [5228] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_397_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7920, 5229], outs := [5230] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_398_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5231, 5226, 5228], outs := [5232, 5233], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_399_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5232, 5233, 5230, 5234, 5235], outs := [5236], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
