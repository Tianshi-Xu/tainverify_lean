/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_440_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5291], outs := [5292], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_441_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5292, 5293], outs := [5294] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_442_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5294], outs := [5295], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_443_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5295], outs := [5296] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_444_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7959, 5296], outs := [5297] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_445_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5297], outs := [7976, 7980], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_446_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7976, 5298], outs := [5299] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_447_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5299], outs := [7987, 7991, 7995, 7999, 8003], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_448_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7987], outs := [5300] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_449_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7995], outs := [5309], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_450_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7999], outs := [5314], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_451_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8003], outs := [5318], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_452_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5300, 5301], outs := [5302] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_453_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5309, 5310], outs := [5311] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_454_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5314, 5315], outs := [5316] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_455_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5318, 5319], outs := [5320] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_456_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5302], outs := [5303, 5304, 5305], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_457_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5311], outs := [5312], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_458_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5316], outs := [5317], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_459_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5320], outs := [5321], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_460_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7991, 5303, 5304, 5306, 5307], outs := [5308], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_461_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5312], outs := [5313] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_462_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5317, 5321], outs := [5322] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_463_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5322], outs := [5323], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_464_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5323, 5324], outs := [5325] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_465_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5325], outs := [5326], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_466_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5313, 5326], outs := [5327] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_467_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5308, 5327], outs := [5328] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_468_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5328], outs := [5329] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_469_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7980, 5329], outs := [5330] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_470_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5330], outs := [8007, 8011], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_471_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8007, 5331], outs := [5332] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_472_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_maybe_shuffle", ins := [8011, 5337], outs := [5338], params := [1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_473_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5332], outs := [8015, 8019], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_474_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5338], outs := [8139, 8143], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_475_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [8015, 5333], outs := [5334] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_476_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [8019, 5335], outs := [5336] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_477_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8139, 5339], outs := [5340] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_478_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5334], outs := [8033, 8037, 8041, 8045, 8049, 8053, 8057, 8061, 8065, 8069, 8073, 8077], params := [12] } := by
  intro s
  change 12 ≥ 12
  omega

theorem sm_node_479_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5336], outs := [8091, 8095, 8099, 8103, 8107, 8111, 8115, 8119, 8123, 8127, 8131, 8135], params := [12] } := by
  intro s
  change 12 ≥ 12
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
