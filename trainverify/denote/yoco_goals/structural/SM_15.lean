/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_600_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5477], outs := [5478], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_601_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5478, 5479], outs := [5480] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_602_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5480], outs := [5481], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_603_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5468, 5481], outs := [5482] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_604_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5463, 5482], outs := [5483] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_605_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5483], outs := [5484] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_606_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8229, 5484], outs := [5485] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_607_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5485], outs := [8256, 8260], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_608_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8256, 5486], outs := [5487] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_609_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5487, 5488], outs := [5489] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_610_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5489 + r)), outs := [5494], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_611_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5494], outs := [5495], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_612_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5495], outs := [5496], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_613_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5496, 5497], outs := [5498] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_614_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5498], outs := [5499], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_615_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5499], outs := [5500] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_616_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8260, 5500], outs := [5501] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_617_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5501], outs := [8264, 8268], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_618_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8264, 5502], outs := [5503] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_619_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5503], outs := [8275, 8279, 8283, 8287, 8291], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_620_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8275], outs := [5504] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_621_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8283], outs := [5513], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_622_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8287], outs := [5518], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_623_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8291], outs := [5522], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_624_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5504, 5505], outs := [5506] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_625_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5513, 5514], outs := [5515] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_626_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5518, 5519], outs := [5520] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_627_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5522, 5523], outs := [5524] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_628_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5506], outs := [5507, 5508, 5509], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_629_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5515], outs := [5516], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_630_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5520], outs := [5521], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_631_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5524], outs := [5525], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_632_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8279, 5507, 5508, 5510, 5511], outs := [5512], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_633_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5516], outs := [5517] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_634_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5521, 5525], outs := [5526] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_635_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5526], outs := [5527], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_636_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5527, 5528], outs := [5529] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_637_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5529], outs := [5530], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_638_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5517, 5530], outs := [5531] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_639_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5512, 5531], outs := [5532] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
