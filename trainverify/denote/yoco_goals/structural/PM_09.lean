/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_360_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [14893, 8040, 8042, 8046, 8048], outs := [8050], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_361_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [8062], outs := [8064] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_362_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [8080, 8098], outs := [8102] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_363_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8101], outs := [8103], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_364_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8102], outs := [8104], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_365_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8103, 4892], outs := [8109] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_366_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8104, 4892], outs := [8110] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_367_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8109], outs := [8119], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_368_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8110], outs := [8120], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_369_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [8063, 8119], outs := [8123] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_370_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [8064, 8120], outs := [8124] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_371_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [8049, 8123], outs := [8127] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_372_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [8050, 8124], outs := [8128] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_373_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8127], outs := [8133] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_374_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8128], outs := [8134] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_375_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [14851, 8133], outs := [8137] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_376_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [14859, 8134], outs := [8138] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_377_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8137], outs := [14909, 14913], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_378_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8138], outs := [14917, 14921], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_379_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [14909, 4899], outs := [8141] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_380_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [14917, 4899], outs := [8142] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_381_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8141], outs := [14926, 14930, 14934], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_382_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8142], outs := [14939, 14943, 14947], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_383_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14926, 4901], outs := [8143] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_384_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14930, 4903], outs := [8155] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_385_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14934, 4905], outs := [8165] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_386_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14939, 4901], outs := [8144] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_387_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14943, 4903], outs := [8156] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_388_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14947, 4905], outs := [8166] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_389_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11857, 8175, 8143, 8155], outs := [8177, 8179], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_390_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11857, 8176, 8144, 8156], outs := [8178, 8180], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_391_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8177, 8179, 8165, 4910, 4911], outs := [8181], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_392_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8178, 8180, 8166, 4910, 4911], outs := [8182], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_393_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8181], outs := [8183], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_394_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8182], outs := [8184], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_395_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8183], outs := [8189], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_396_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8184], outs := [8190], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_397_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8189, 4915], outs := [8193] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_398_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8190, 4915], outs := [8194] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_399_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8193], outs := [8203], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
