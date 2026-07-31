/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_720_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15375, 5136], outs := [8960] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_721_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8959], outs := [15386, 15390, 15394, 15398, 15402], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_722_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8960], outs := [15409, 15413, 15417, 15421, 15425], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_723_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [15386], outs := [8961] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_724_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15394], outs := [8981], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_725_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15398], outs := [8995], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_726_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15402], outs := [9013], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_727_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [15409], outs := [8962] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_728_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15417], outs := [8982], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_729_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15421], outs := [8996], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_730_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15425], outs := [9014], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_731_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [8961, 5139], outs := [8967] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_732_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8981, 5148], outs := [8985] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_733_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8995, 5153], outs := [8999] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_734_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9013, 5157], outs := [9017] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_735_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [8962, 5139], outs := [8968] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_736_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8982, 5148], outs := [8986] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_737_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8996, 5153], outs := [9000] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_738_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9014, 5157], outs := [9018] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_739_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [8967], outs := [8969, 8971, 8973], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_740_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8985], outs := [8991], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_741_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8999], outs := [9009], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_742_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9017], outs := [9027], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_743_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [8968], outs := [8970, 8972, 8974], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_744_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8986], outs := [8992], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_745_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9000], outs := [9010], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_746_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9018], outs := [9028], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_747_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15390, 8969, 8971, 8975, 8977], outs := [8979], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_748_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [8991], outs := [8993] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_749_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [9009, 9027], outs := [9031] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_750_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15413, 8970, 8972, 8976, 8978], outs := [8980], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_751_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [8992], outs := [8994] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_752_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [9010, 9028], outs := [9032] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_753_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9031], outs := [9033], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_754_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9032], outs := [9034], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_755_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9033, 5162], outs := [9039] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_756_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9034, 5162], outs := [9040] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_757_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9039], outs := [9049], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_758_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9040], outs := [9050], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_759_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [8993, 9049], outs := [9053] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
