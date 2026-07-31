/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_800_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [9146], outs := [15513, 15517, 15521, 15525, 15529], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_801_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [15490], outs := [9147] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_802_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15498], outs := [9167], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_803_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15502], outs := [9181], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_804_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [15506], outs := [9199], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_805_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [15513], outs := [9148] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_806_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15521], outs := [9168], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_807_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15525], outs := [9182], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_808_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [15529], outs := [9200], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_809_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [9147, 5193], outs := [9153] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_810_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9167, 5202], outs := [9171] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_811_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9181, 5207], outs := [9185] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_812_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9199, 5211], outs := [9203] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_813_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [9148, 5193], outs := [9154] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_814_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9168, 5202], outs := [9172] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_815_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9182, 5207], outs := [9186] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_816_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9200, 5211], outs := [9204] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_817_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [9153], outs := [9155, 9157, 9159], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_818_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9171], outs := [9177], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_819_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9185], outs := [9195], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_820_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9203], outs := [9213], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_821_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [9154], outs := [9156, 9158, 9160], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_822_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9172], outs := [9178], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_823_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9186], outs := [9196], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_824_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9204], outs := [9214], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_825_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [15494, 9155, 9157, 9161, 9163], outs := [9165], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_826_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [9177], outs := [9179] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_827_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [9195, 9213], outs := [9217] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_828_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [15517, 9156, 9158, 9162, 9164], outs := [9166], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_829_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [9178], outs := [9180] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_830_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [9196, 9214], outs := [9218] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_831_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [9217], outs := [9219], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_832_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [9218], outs := [9220], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_833_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [9219, 5216], outs := [9225] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_834_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [9220, 5216], outs := [9226] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_835_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [9225], outs := [9235], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_836_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [9226], outs := [9236], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_837_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [9179, 9235], outs := [9239] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_838_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [9180, 9236], outs := [9240] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_839_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [9165, 9239], outs := [9243] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
