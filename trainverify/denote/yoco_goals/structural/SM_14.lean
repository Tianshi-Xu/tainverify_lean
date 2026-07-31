/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_560_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5422], outs := [5423], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_561_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5426], outs := [5427], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_562_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8201, 5409, 5410, 5412, 5413], outs := [5414], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_563_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5418], outs := [5419] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_564_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5423, 5427], outs := [5428] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_565_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5428], outs := [5429], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_566_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5429, 5430], outs := [5431] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_567_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5431], outs := [5432], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_568_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [5419, 5432], outs := [5433] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_569_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [5414, 5433], outs := [5434] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_570_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5434], outs := [5435] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_571_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8190, 5435], outs := [5436] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_572_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5436], outs := [8217, 8221], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_573_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8217, 5437], outs := [5438] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_574_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [5438, 5439], outs := [5440] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_575_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_zigzag", ins := ((List.range 5).map (fun r => 5440 + r)), outs := [5445], params := [16, 4, 64, 64, 1, 0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_576_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5445], outs := [5446], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_577_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [5446], outs := [5447], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_578_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5447, 5448], outs := [5449] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_579_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5449], outs := [5450], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_580_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5450], outs := [5451] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_581_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [8221, 5451], outs := [5452] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_582_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5452], outs := [8225, 8229], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_583_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [8225, 5453], outs := [5454] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_584_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5454], outs := [8236, 8240, 8244, 8248, 8252], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_585_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [8236], outs := [5455] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_586_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8244], outs := [5464], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_587_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8248], outs := [5469], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_588_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [8252], outs := [5473], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_589_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [5455, 5456], outs := [5457] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_590_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5464, 5465], outs := [5466] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_591_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5469, 5470], outs := [5471] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_592_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [5473, 5474], outs := [5475] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_593_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [5457], outs := [5458, 5459, 5460], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_594_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5466], outs := [5467], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_595_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5471], outs := [5472], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_596_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5475], outs := [5476], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_597_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [8240, 5458, 5459, 5461, 5462], outs := [5463], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_598_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [5467], outs := [5468] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_599_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [5472, 5476], outs := [5477] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
