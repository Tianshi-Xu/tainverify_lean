/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_280_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [7875], outs := [7877] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_281_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [7893, 7911], outs := [7915] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_282_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [14789, 7854, 7856, 7860, 7862], outs := [7864], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_283_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [7876], outs := [7878] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_284_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [7894, 7912], outs := [7916] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_285_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7915], outs := [7917], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_286_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7916], outs := [7918], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_287_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7917, 4838], outs := [7923] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_288_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7918, 4838], outs := [7924] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_289_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [7923], outs := [7933], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_290_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [7924], outs := [7934], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_291_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [7877, 7933], outs := [7937] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_292_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [7878, 7934], outs := [7938] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_293_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [7863, 7937], outs := [7941] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_294_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [7864, 7938], outs := [7942] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_295_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [7941], outs := [7947] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_296_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [7942], outs := [7948] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_297_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [14747, 7947], outs := [7951] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_298_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [14755, 7948], outs := [7952] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_299_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [7951], outs := [14805, 14809], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_300_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [7952], outs := [14813, 14817], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_301_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [14805, 4845], outs := [7955] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_302_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [14813, 4845], outs := [7956] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_303_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [7955], outs := [14822, 14826, 14830], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_304_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [7956], outs := [14835, 14839, 14843], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_305_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14822, 4847], outs := [7957] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_306_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14826, 4849], outs := [7969] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_307_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14830, 4851], outs := [7979] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_308_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14835, 4847], outs := [7958] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_309_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14839, 4849], outs := [7970] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_310_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14843, 4851], outs := [7980] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_311_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11856, 7989, 7957, 7969], outs := [7991, 7993], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_312_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11856, 7990, 7958, 7970], outs := [7992, 7994], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_313_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7991, 7993, 7979, 4856, 4857], outs := [7995], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_314_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7992, 7994, 7980, 4856, 4857], outs := [7996], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_315_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7995], outs := [7997], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_316_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7996], outs := [7998], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_317_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7997], outs := [8003], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_318_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7998], outs := [8004], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_319_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8003, 4861], outs := [8007] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
