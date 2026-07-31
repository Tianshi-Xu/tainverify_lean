/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_40_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14640, 4688], outs := [4689] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_41_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_42_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11853, 4690, 4685, 4687], outs := [4692, 4693], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_43_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4689], outs := [7421], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_44_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4689], outs := [7422], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_45_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4692], outs := [7433], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_46_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [4693], outs := [7435], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_47_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4692], outs := [7434], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_48_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4693], outs := [7436], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_49_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7433, 7435, 7421, 4694, 4695], outs := [7437], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_50_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7434, 7436, 7422, 4694, 4695], outs := [7438], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_51_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7437], outs := [7439], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_52_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7438], outs := [7440], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_53_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7439], outs := [7445], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_54_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7440], outs := [7446], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_55_wf : IsWellFormedNode pm { rank := 0, op := "OpName.AllGatherPrim", ins := [7445, 7446], outs := [4698], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_56_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_57_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [4698, 4699], outs := [4700] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_58_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_59_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [4700], outs := [4701], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_60_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [4701], outs := [4702] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_61_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [4701], outs := [4702] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_62_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [14607, 4702], outs := [4703] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_63_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [14615, 4702], outs := [4703] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_64_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [4703], outs := [14644, 14648], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_65_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [4703], outs := [14652, 14656], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_66_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [14644, 4704], outs := [4705] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_67_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [14652, 4704], outs := [4705] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_68_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [4705], outs := ((List.range 5).map (fun r => 11875 + r)), params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_69_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [4705], outs := ((List.range 5).map (fun r => 11875 + r)), params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_70_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [11875], outs := [4706] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_71_wf : IsWellFormedNode pm { rank := 0, op := "OpName.ChunkPrim", ins := [11876], outs := [11941], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_72_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11877], outs := [4715], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_73_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11878], outs := [4720], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_74_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [11879], outs := [4724], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_75_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [11875], outs := [4706] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_76_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [11876], outs := [11942], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_77_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11877], outs := [4715], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_78_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11878], outs := [4720], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_79_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [11879], outs := [4724], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
