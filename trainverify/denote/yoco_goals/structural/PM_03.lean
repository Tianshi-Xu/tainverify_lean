/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_120_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [4734], outs := [4735] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_121_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [4734], outs := [4735] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_122_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [14648, 4735], outs := [4736] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_123_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [14656, 4735], outs := [4736] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_124_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [4736], outs := [14660, 14664], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_125_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [4736], outs := [14668, 14672], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_126_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [14660, 4737], outs := [4738] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_127_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [14668, 4737], outs := [4738] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_128_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [4738], outs := [14677, 14681, 14685], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_129_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [4738], outs := [14689, 14693, 14697], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_130_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14677, 4739], outs := [4740] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_131_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14681, 4741], outs := [4742] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_132_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14685, 4743], outs := [4744] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_133_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14689, 4739], outs := [4740] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_134_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14693, 4741], outs := [4742] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_135_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14697, 4743], outs := [4744] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_136_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11854, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_137_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11854, 4745, 4740, 4742], outs := [4746, 4747], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_138_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4744], outs := [7607], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_139_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4744], outs := [7608], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_140_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4746], outs := [7619], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_141_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4747], outs := [7621], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_142_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4746], outs := [7620], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_143_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4747], outs := [7622], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_144_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7619, 7621, 7607, 4748, 4749], outs := [7623], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_145_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7620, 7622, 7608, 4748, 4749], outs := [7624], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_146_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7623], outs := [7625], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_147_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7624], outs := [7626], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_148_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7625], outs := [7631], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_149_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7626], outs := [7632], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_150_wf : IsWellFormedNode pm { rank := 0, op := "OpName.AllGatherPrim", ins := [7631, 7632], outs := [4752], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_151_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4752, 4753], outs := [4754] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_152_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4752, 4753], outs := [4754] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_153_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [4754], outs := [4755], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_154_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [4754], outs := [4755], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_155_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [4755], outs := [4756] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_156_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [4755], outs := [4756] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_157_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [14664, 4756], outs := [4757] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_158_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [14672, 4756], outs := [4757] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_159_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
