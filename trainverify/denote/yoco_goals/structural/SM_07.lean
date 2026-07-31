/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_280_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7764, 5067], outs := [5068] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_281_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5069, 5064, 5066], outs := [5070, 5071], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_282_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5070, 5071, 5068, 5072, 5073], outs := [5074], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_283_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5074], outs := [5075], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_284_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5075], outs := [5076], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_285_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5076, 5077], outs := [5078] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_286_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5078], outs := [5079], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_287_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5079], outs := [5080] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_288_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7751, 5080], outs := [5081] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_289_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5081], outs := [7768, 7772], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_290_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7768, 5082], outs := [5083] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_291_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5083], outs := [7779, 7783, 7787, 7791, 7795], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_292_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7779], outs := [5084] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_293_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7787], outs := [5093], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_294_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7791], outs := [5098], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_295_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7795], outs := [5102], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_296_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5084, 5085], outs := [5086] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_297_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5093, 5094], outs := [5095] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_298_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5098, 5099], outs := [5100] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_299_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5102, 5103], outs := [5104] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_300_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5086], outs := [5087, 5088, 5089], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_301_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5095], outs := [5096], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_302_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5100], outs := [5101], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_303_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5104], outs := [5105], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_304_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7783, 5087, 5088, 5090, 5091], outs := [5092], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_305_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5096], outs := [5097] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_306_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5101, 5105], outs := [5106] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_307_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5106], outs := [5107], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_308_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5107, 5108], outs := [5109] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_309_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5109], outs := [5110], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_310_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5097, 5110], outs := [5111] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_311_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5092, 5111], outs := [5112] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_312_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5112], outs := [5113] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_313_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7772, 5113], outs := [5114] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_314_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5114], outs := [7799, 7803], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_315_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7799, 5115], outs := [5116] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_316_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5116], outs := [7808, 7812, 7816], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_317_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7808, 5117], outs := [5118] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_318_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7812, 5119], outs := [5120] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_319_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7816, 5121], outs := [5122] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
