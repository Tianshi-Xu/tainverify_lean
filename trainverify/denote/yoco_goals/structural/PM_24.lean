/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_960_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15714], outs := [9571], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_961_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [15721], outs := [9520] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_962_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15729], outs := [9540], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_963_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15733], outs := [9554], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_964_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15737], outs := [9572], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_965_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [9519, 5301], outs := [9525] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_966_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9539, 5310], outs := [9543] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_967_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9553, 5315], outs := [9557] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_968_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9571, 5319], outs := [9575] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_969_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [9520, 5301], outs := [9526] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_970_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9540, 5310], outs := [9544] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_971_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9554, 5315], outs := [9558] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_972_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9572, 5319], outs := [9576] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_973_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [9525], outs := [9527, 9529, 9531], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_974_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9543], outs := [9549], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_975_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9557], outs := [9567], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_976_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9575], outs := [9585], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_977_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [9526], outs := [9528, 9530, 9532], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_978_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9544], outs := [9550], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_979_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9558], outs := [9568], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_980_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9576], outs := [9586], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_981_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15702, 9527, 9529, 9533, 9535], outs := [9537], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_982_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [9549], outs := [9551] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_983_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [9567, 9585], outs := [9589] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_984_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15725, 9528, 9530, 9534, 9536], outs := [9538], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_985_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [9550], outs := [9552] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_986_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [9568, 9586], outs := [9590] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_987_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9589], outs := [9591], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_988_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9590], outs := [9592], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_989_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9591, 5324], outs := [9597] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_990_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9592, 5324], outs := [9598] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_991_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9597], outs := [9607], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_992_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9598], outs := [9608], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_993_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [9551, 9607], outs := [9611] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_994_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [9552, 9608], outs := [9612] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_995_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [9537, 9611], outs := [9615] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_996_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [9538, 9612], outs := [9616] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_997_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9615], outs := [9621] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_998_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [9616], outs := [9622] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_999_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15683, 9621], outs := [9625] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
