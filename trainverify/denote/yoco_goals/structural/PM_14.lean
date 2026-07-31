/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_560_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15129, 8580], outs := [8584] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_561_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8583], outs := [15159, 15163], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_562_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8584], outs := [15167, 15171], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_563_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15159, 5028], outs := [8587] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_564_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15167, 5028], outs := [8588] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_565_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8587], outs := [15178, 15182, 15186, 15190, 15194], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_566_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8588], outs := [15201, 15205, 15209, 15213, 15217], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_567_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [15178], outs := [8589] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_568_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15186], outs := [8609], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_569_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15190], outs := [8623], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_570_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15194], outs := [8641], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_571_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [15201], outs := [8590] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_572_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15209], outs := [8610], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_573_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15213], outs := [8624], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_574_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15217], outs := [8642], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_575_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [8589, 5031], outs := [8595] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_576_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8609, 5040], outs := [8613] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_577_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8623, 5045], outs := [8627] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_578_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8641, 5049], outs := [8645] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_579_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [8590, 5031], outs := [8596] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_580_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8610, 5040], outs := [8614] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_581_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8624, 5045], outs := [8628] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_582_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8642, 5049], outs := [8646] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_583_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [8595], outs := [8597, 8599, 8601], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_584_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8613], outs := [8619], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_585_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8627], outs := [8637], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_586_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8645], outs := [8655], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_587_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [8596], outs := [8598, 8600, 8602], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_588_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8614], outs := [8620], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_589_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8628], outs := [8638], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_590_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8646], outs := [8656], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_591_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15182, 8597, 8599, 8603, 8605], outs := [8607], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_592_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [8619], outs := [8621] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_593_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [8637, 8655], outs := [8659] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_594_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15205, 8598, 8600, 8604, 8606], outs := [8608], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_595_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [8620], outs := [8622] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_596_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [8638, 8656], outs := [8660] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_597_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8659], outs := [8661], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_598_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8660], outs := [8662], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_599_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8661, 5054], outs := [8667] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
