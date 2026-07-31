/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_880_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15602], outs := [9353], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_881_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15606], outs := [9367], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_882_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15610], outs := [9385], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_883_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [15617], outs := [9334] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_884_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15625], outs := [9354], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_885_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15629], outs := [9368], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_886_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15633], outs := [9386], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_887_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [9333, 5247], outs := [9339] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_888_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9353, 5256], outs := [9357] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_889_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9367, 5261], outs := [9371] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_890_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9385, 5265], outs := [9389] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_891_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [9334, 5247], outs := [9340] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_892_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9354, 5256], outs := [9358] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_893_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9368, 5261], outs := [9372] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_894_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9386, 5265], outs := [9390] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_895_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [9339], outs := [9341, 9343, 9345], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_896_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9357], outs := [9363], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_897_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9371], outs := [9381], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_898_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9389], outs := [9399], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_899_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [9340], outs := [9342, 9344, 9346], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_900_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9358], outs := [9364], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_901_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9372], outs := [9382], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_902_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9390], outs := [9400], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_903_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15598, 9341, 9343, 9347, 9349], outs := [9351], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_904_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [9363], outs := [9365] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_905_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [9381, 9399], outs := [9403] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_906_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15621, 9342, 9344, 9348, 9350], outs := [9352], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_907_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [9364], outs := [9366] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_908_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [9382, 9400], outs := [9404] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_909_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9403], outs := [9405], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_910_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9404], outs := [9406], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_911_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9405, 5270], outs := [9411] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_912_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9406, 5270], outs := [9412] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_913_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9411], outs := [9421], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_914_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9412], outs := [9422], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_915_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [9365, 9421], outs := [9425] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_916_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [9366, 9422], outs := [9426] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_917_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [9351, 9425], outs := [9429] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_918_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [9352, 9426], outs := [9430] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_919_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [9429], outs := [9435] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
