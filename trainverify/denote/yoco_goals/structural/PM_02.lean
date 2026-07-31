/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_80_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_81_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [4706, 4707], outs := [4708] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_82_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4715, 4716], outs := [4717] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_83_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4715, 4716], outs := [4717] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_84_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4720, 4721], outs := [4722] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_85_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4720, 4721], outs := [4722] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_86_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4724, 4725], outs := [4726] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_87_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4724, 4725], outs := [4726] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_88_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4708], outs := [7479], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_89_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4708], outs := [7480], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_90_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [4717], outs := [4718], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_91_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [4717], outs := [4718], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_92_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [4722], outs := [4723], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_93_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [4722], outs := [4723], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_94_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [4726], outs := [4727], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_95_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [4726], outs := [4727], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_96_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [7479], outs := [7481, 7483, 7485], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_97_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [7480], outs := [7482, 7484, 7486], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_98_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [4718], outs := [4719] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_99_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [4718], outs := [4719] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_100_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4723], outs := [7521], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_101_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4723], outs := [7522], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_102_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4727], outs := [7539], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_103_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4727], outs := [7540], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_104_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [11941, 7481, 7483, 7487, 7489], outs := [7491], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_105_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [11942, 7482, 7484, 7488, 7490], outs := [7492], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_106_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [7521, 7539], outs := [7543] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_107_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [7522, 7540], outs := [7544] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_108_wf : IsWellFormedNode pm { rank := 0, op := "OpName.AllGatherPrim", ins := [7491, 7492], outs := [4714], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_109_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7543], outs := [7545], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_110_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7544], outs := [7546], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_111_wf : IsWellFormedNode pm { rank := 0, op := "OpName.AllGatherPrim", ins := [7545, 7546], outs := [4729], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_112_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_113_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4729, 4730], outs := [4731] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_114_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [4731], outs := [4732], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_115_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [4731], outs := [4732], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_116_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [4719, 4732], outs := [4733] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_117_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [4719, 4732], outs := [4733] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_118_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [4714, 4733], outs := [4734] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_119_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [4714, 4733], outs := [4734] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
