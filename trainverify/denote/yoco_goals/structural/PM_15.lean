/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_600_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8662, 5054], outs := [8668] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_601_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8667], outs := [8677], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_602_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8668], outs := [8678], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_603_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mul", ins := [8621, 8677], outs := [8681] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_604_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mul", ins := [8622, 8678], outs := [8682] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_605_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [8607, 8681], outs := [8685] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_606_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [8608, 8682], outs := [8686] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_607_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8685], outs := [8691] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_608_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8686], outs := [8692] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_609_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15163, 8691], outs := [8695] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_610_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15171, 8692], outs := [8696] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_611_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8695], outs := [15221, 15225], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_612_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8696], outs := [15229, 15233], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_613_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [15221, 5061], outs := [8699] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_614_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [15229, 5061], outs := [8700] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_615_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8699], outs := [15238, 15242, 15246], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_616_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8700], outs := [15251, 15255, 15259], params := [3] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_617_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15238, 5063], outs := [8701] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_618_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15242, 5065], outs := [8713] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_619_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_per_head_mix_precision_linear", ins := [15246, 5067], outs := [8723] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_620_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15251, 5063], outs := [8702] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_621_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15255, 5065], outs := [8714] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_622_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_per_head_mix_precision_linear", ins := [15259, 5067], outs := [8724] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_623_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rotary_embedding", ins := [11860, 8733, 8701, 8713], outs := [8735, 8737], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_624_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rotary_embedding", ins := [11860, 8734, 8702, 8714], outs := [8736, 8738], params := [16, 4] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_625_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_attn_sliding_window", ins := [8735, 8737, 8723, 5072, 5073], outs := [8739], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_626_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_attn_sliding_window", ins := [8736, 8738, 8724, 5072, 5073], outs := [8740], params := [16, 4, 64, 64, 1, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_627_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8739], outs := [8741], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_628_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8740], outs := [8742], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_629_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [8741], outs := [8747], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_630_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [8742], outs := [8748], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_631_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8747, 5077], outs := [8751] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_632_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8748, 5077], outs := [8752] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_633_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8751], outs := [8761], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_634_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8752], outs := [8762], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_635_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8761], outs := [8765] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_636_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8762], outs := [8766] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_637_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [15225, 8765], outs := [8769] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_638_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [15233, 8766], outs := [8770] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_639_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8769], outs := [15263, 15267], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
