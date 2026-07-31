/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem sm_node_200_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7652, 4955], outs := [4956] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_201_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7656, 4957], outs := [4958] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_202_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7660, 4959], outs := [4960] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_203_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [4691, 4961, 4956, 4958], outs := [4962, 4963], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_204_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [4962, 4963, 4960, 4964, 4965], outs := [4966], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_205_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4966], outs := [4967], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_206_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4967], outs := [4968], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_207_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4968, 4969], outs := [4970] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_208_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4970], outs := [4971], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_209_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [4971], outs := [4972] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_210_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7647, 4972], outs := [4973] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_211_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4973], outs := [7664, 7668], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_212_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7664, 4974], outs := [4975] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_213_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [4975], outs := [7675, 7679, 7683, 7687, 7691], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem sm_node_214_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [7675], outs := [4976] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_215_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7683], outs := [4985], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_216_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7687], outs := [4990], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_217_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [7691], outs := [4994], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_218_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_norm_linear", ins := [4976, 4977], outs := [4978] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_219_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4985, 4986], outs := [4987] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_220_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4990, 4991], outs := [4992] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_221_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4994, 4995], outs := [4996] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_222_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_topk_routing", ins := [4978], outs := [4979, 4980, 4981], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_223_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4987], outs := [4988], params := [4096, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_224_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4992], outs := [4993], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_225_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [4996], outs := [4997], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_226_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [7679, 4979, 4980, 4982, 4983], outs := [4984], params := [64, 0, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_227_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_sigmoid", ins := [4988], outs := [4989] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_228_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_swiglu", ins := [4993, 4997], outs := [4998] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_229_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_reshape", ins := [4998], outs := [4999], params := [4096, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_230_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [4999, 5000], outs := [5001] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_231_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_view", ins := [5001], outs := [5002], params := [4096, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_232_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_mul", ins := [4989, 5002], outs := [5003] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_233_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [4984, 5003], outs := [5004] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_234_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_float", ins := [5004], outs := [5005] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_235_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_add", ins := [7668, 5005], outs := [5006] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_236_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5006], outs := [7695, 7699], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem sm_node_237_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_rms_norm", ins := [7695, 5007], outs := [5008] } := by
  intro s
  change 1 ≥ 1
  omega

theorem sm_node_238_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_multiref", ins := [5008], outs := [7704, 7708, 7712], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem sm_node_239_wf : IsWellFormedNode sm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [7704, 5009], outs := [5010] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
