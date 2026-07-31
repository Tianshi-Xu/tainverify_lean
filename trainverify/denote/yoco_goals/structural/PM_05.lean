/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_200_wf : IsWellFormedNode pm { rank := 1, op := "OpName.ChunkPrim", ins := [4781], outs := [7726], params := [0] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_201_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [11977, 7667, 7669, 7673, 7675], outs := [7677], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_202_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_all2all_moe_gmm", ins := [11978, 7668, 7670, 7674, 7676], outs := [7678], params := [64, 32, 64, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_203_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [7689], outs := [7691] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_204_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_sigmoid", ins := [7690], outs := [7692] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_205_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [7707, 7725], outs := [7729] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_206_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_swiglu", ins := [7708, 7726], outs := [7730] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_207_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7729], outs := [7731], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_208_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7730], outs := [7732], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_209_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [7731, 4784], outs := [7737] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_210_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [7732, 4784], outs := [7738] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_211_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [7737], outs := [7747], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_212_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [7738], outs := [7748], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_213_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [7691, 7747], outs := [7751] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_214_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [7692, 7748], outs := [7752] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_215_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [7677, 7751], outs := [7755] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_216_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [7678, 7752], outs := [7756] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_217_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [7755], outs := [7761] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_218_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [7756], outs := [7762] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_219_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [12011, 7761], outs := [7765] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_220_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [12012, 7762], outs := [7766] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_221_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [7765], outs := [14701, 14705], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_222_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [7766], outs := [14709, 14713], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_223_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [14701, 4791], outs := [7769] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_224_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [14709, 4791], outs := [7770] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_225_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [7769], outs := [14718, 14722, 14726], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_226_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [7770], outs := [14731, 14735, 14739], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_227_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14718, 4793], outs := [7771] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_228_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14722, 4795], outs := [7783] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_229_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [14726, 4797], outs := [7793] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_230_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14731, 4793], outs := [7772] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_231_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14735, 4795], outs := [7784] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_232_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [14739, 4797], outs := [7794] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_233_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11855, 7803, 7771, 7783], outs := [7805, 7807], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_234_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11855, 7804, 7772, 7784], outs := [7806, 7808], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_235_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [7805, 7807, 7793, 4802, 4803], outs := [7809], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_236_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [7806, 7808, 7794, 4802, 4803], outs := [7810], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_237_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7809], outs := [7811], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_238_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [7810], outs := [7812], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_239_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [7811], outs := [7817], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
