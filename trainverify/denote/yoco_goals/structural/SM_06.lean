/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_240_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7708, 5011], outs := [5012] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_241_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7712, 5013], outs := [5014] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_242_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 5015, 5010, 5012], outs := [5016, 5017], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_243_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [5016, 5017, 5014, 5018, 5019], outs := [5020], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_244_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5020], outs := [5021], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_245_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5021], outs := [5022], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_246_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5022, 5023], outs := [5024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_247_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5024], outs := [5025], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_248_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5025], outs := [5026] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_249_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7699, 5026], outs := [5027] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_250_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5027], outs := [7716, 7720], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_251_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7716, 5028], outs := [5029] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_252_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5029], outs := [7727, 7731, 7735, 7739, 7743], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_253_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7727], outs := [5030] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_254_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7735], outs := [5039], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_255_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7739], outs := [5044], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_256_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7743], outs := [5048], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_257_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5030, 5031], outs := [5032] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_258_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5039, 5040], outs := [5041] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_259_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5044, 5045], outs := [5046] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_260_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5048, 5049], outs := [5050] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_261_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5032], outs := [5033, 5034, 5035], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_262_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5041], outs := [5042], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_263_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5046], outs := [5047], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_264_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5050], outs := [5051], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_265_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7731, 5033, 5034, 5036, 5037], outs := [5038], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_266_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5042], outs := [5043] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_267_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5047, 5051], outs := [5052] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_268_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5052], outs := [5053], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_269_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5053, 5054], outs := [5055] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_270_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5055], outs := [5056], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_271_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5043, 5056], outs := [5057] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_272_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5038, 5057], outs := [5058] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_273_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5058], outs := [5059] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_274_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7720, 5059], outs := [5060] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_275_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5060], outs := [7747, 7751], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_276_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7747, 5061], outs := [5062] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_277_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5062], outs := [7756, 7760, 7764], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_278_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7756, 5063], outs := [5064] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_279_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7760, 5065], outs := [5066] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
