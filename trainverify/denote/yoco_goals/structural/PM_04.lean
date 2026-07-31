/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_160_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [4757], outs := [11889, 11890], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_161_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_162_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [11890], outs := [12011], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_163_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [11889, 4758], outs := [4759] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_164_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [11890], outs := [12012], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_165_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [4759], outs := ((List.range 5).map (fun r => 11903 + r)), params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_166_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [4759], outs := ((List.range 5).map (fun r => 11903 + r)), params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_167_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11903], outs := [4760] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_168_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [11904], outs := [11977], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_169_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11905], outs := [4769], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_170_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11906], outs := [4774], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_171_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11907], outs := [4778], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_172_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11903], outs := [4760] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_173_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [11904], outs := [11978], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_174_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11905], outs := [4769], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_175_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11906], outs := [4774], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_176_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11907], outs := [4778], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_177_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [4760, 4761], outs := [4762] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_178_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [4760, 4761], outs := [4762] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_179_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_180_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4769, 4770], outs := [4771] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_181_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_182_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4774, 4775], outs := [4776] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_183_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_184_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4778, 4779], outs := [4780] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_185_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4762], outs := [7665], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_186_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4762], outs := [7666], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_187_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_188_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [4771], outs := [4772], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_189_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_190_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [4776], outs := [4777], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_191_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_192_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [4780], outs := [4781], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_193_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [7665], outs := [7667, 7669, 7671], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_194_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [7666], outs := [7668, 7670, 7672], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_195_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4772], outs := [7689], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_196_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4772], outs := [7690], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_197_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4777], outs := [7707], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_198_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4777], outs := [7708], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_199_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4781], outs := [7725], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
