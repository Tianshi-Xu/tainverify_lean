/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_160_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4900], outs := [7600, 7604, 7608], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_161_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7600, 4901], outs := [4902] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_162_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7604, 4903], outs := [4904] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_163_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7608, 4905], outs := [4906] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_164_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4907, 4902, 4904], outs := [4908, 4909], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_165_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4908, 4909, 4906, 4910, 4911], outs := [4912], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_166_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4912], outs := [4913], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_167_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4913], outs := [4914], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_168_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4914, 4915], outs := [4916] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_169_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4916], outs := [4917], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_170_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4917], outs := [4918] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_171_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7595, 4918], outs := [4919] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_172_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4919], outs := [7612, 7616], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_173_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7612, 4920], outs := [4921] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_174_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4921], outs := [7623, 7627, 7631, 7635, 7639], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_175_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7623], outs := [4922] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_176_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7631], outs := [4931], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_177_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7635], outs := [4936], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_178_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7639], outs := [4940], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_179_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [4922, 4923], outs := [4924] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_180_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4931, 4932], outs := [4933] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_181_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4936, 4937], outs := [4938] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_182_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4940, 4941], outs := [4942] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_183_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [4924], outs := [4925, 4926, 4927], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_184_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4933], outs := [4934], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_185_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4938], outs := [4939], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_186_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4942], outs := [4943], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_187_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7627, 4925, 4926, 4928, 4929], outs := [4930], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_188_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [4934], outs := [4935] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_189_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [4939, 4943], outs := [4944] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_190_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4944], outs := [4945], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_191_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4945, 4946], outs := [4947] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_192_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4947], outs := [4948], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_193_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [4935, 4948], outs := [4949] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_194_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [4930, 4949], outs := [4950] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_195_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4950], outs := [4951] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_196_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7616, 4951], outs := [4952] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_197_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4952], outs := [7643, 7647], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_198_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7643, 4953], outs := [4954] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_199_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4954], outs := [7652, 7656, 7660], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
