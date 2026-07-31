/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_240_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7812], outs := [7818], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_241_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7817, 4807], outs := [7821] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_242_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7818, 4807], outs := [7822] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_243_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [7821], outs := [7831], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_244_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [7822], outs := [7832], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_245_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [7831], outs := [7835] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_246_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [7832], outs := [7836] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_247_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [14705, 7835], outs := [7839] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_248_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [14713, 7836], outs := [7840] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_249_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [7839], outs := [14743, 14747], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_250_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [7840], outs := [14751, 14755], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_251_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [14743, 4812], outs := [7843] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_252_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [14751, 4812], outs := [7844] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_253_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [7843], outs := [14762, 14766, 14770, 14774, 14778], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_254_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [7844], outs := [14785, 14789, 14793, 14797, 14801], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_255_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [14762], outs := [7845] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_256_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [14770], outs := [7865], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_257_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [14774], outs := [7879], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_258_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [14778], outs := [7897], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_259_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [14785], outs := [7846] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_260_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [14793], outs := [7866], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_261_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [14797], outs := [7880], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_262_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [14801], outs := [7898], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_263_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [7845, 4815], outs := [7851] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_264_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7865, 4824], outs := [7869] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_265_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7879, 4829], outs := [7883] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_266_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7897, 4833], outs := [7901] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_267_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [7846, 4815], outs := [7852] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_268_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7866, 4824], outs := [7870] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_269_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7880, 4829], outs := [7884] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_270_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7898, 4833], outs := [7902] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_271_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [7851], outs := [7853, 7855, 7857], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_272_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [7869], outs := [7875], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_273_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [7883], outs := [7893], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_274_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [7901], outs := [7911], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_275_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [7852], outs := [7854, 7856, 7858], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_276_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [7870], outs := [7876], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_277_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [7884], outs := [7894], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_278_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [7902], outs := [7912], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_279_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [14766, 7853, 7855, 7859, 7861], outs := [7863], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
