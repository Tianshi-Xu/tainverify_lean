/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_640_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8770], outs := [15271, 15275], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_641_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15263, 5082], outs := [8773] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_642_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15271, 5082], outs := [8774] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_643_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8773], outs := [15282, 15286, 15290, 15294, 15298], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_644_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8774], outs := [15305, 15309, 15313, 15317, 15321], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_645_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [15282], outs := [8775] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_646_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15290], outs := [8795], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_647_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15294], outs := [8809], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_648_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15298], outs := [8827], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_649_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [15305], outs := [8776] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_650_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15313], outs := [8796], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_651_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15317], outs := [8810], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_652_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15321], outs := [8828], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_653_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [8775, 5085], outs := [8781] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_654_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8795, 5094], outs := [8799] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_655_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8809, 5099], outs := [8813] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_656_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8827, 5103], outs := [8831] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_657_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [8776, 5085], outs := [8782] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_658_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8796, 5094], outs := [8800] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_659_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8810, 5099], outs := [8814] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_660_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8828, 5103], outs := [8832] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_661_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [8781], outs := [8783, 8785, 8787], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_662_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8799], outs := [8805], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_663_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8813], outs := [8823], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_664_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8831], outs := [8841], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_665_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [8782], outs := [8784, 8786, 8788], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_666_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8800], outs := [8806], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_667_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8814], outs := [8824], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_668_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8832], outs := [8842], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_669_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15286, 8783, 8785, 8789, 8791], outs := [8793], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_670_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [8805], outs := [8807] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_671_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [8823, 8841], outs := [8845] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_672_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15309, 8784, 8786, 8790, 8792], outs := [8794], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_673_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [8806], outs := [8808] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_674_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [8824, 8842], outs := [8846] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_675_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8845], outs := [8847], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_676_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8846], outs := [8848], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_677_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8847, 5108], outs := [8853] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_678_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8848, 5108], outs := [8854] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_679_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8853], outs := [8863], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
