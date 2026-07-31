/- Auto-generated concrete well-formedness facts. -/
import denote.GeneratedYOCOMoE
import denote.GraphSlicing

set_option linter.style.longLine false
set_option maxRecDepth 100000

namespace TrainVerify.Denote.GeneratedStructuralFacts
open TrainVerify.Denote TrainVerify.Denote.Generated

theorem pm_node_320_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8004, 4861], outs := [8008] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_321_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8007], outs := [8017], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_322_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8008], outs := [8018], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_323_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [8017], outs := [8021] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_324_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [8018], outs := [8022] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_325_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_add", ins := [14809, 8021], outs := [8025] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_326_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_add", ins := [14817, 8022], outs := [8026] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_327_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8025], outs := [14847, 14851], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_328_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8026], outs := [14855, 14859], params := [2] } := by
  intro s
  change 2 ≥ 2
  omega

theorem pm_node_329_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_rms_norm", ins := [14847, 4866], outs := [8029] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_330_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_rms_norm", ins := [14855, 4866], outs := [8030] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_331_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_multiref", ins := [8029], outs := [14866, 14870, 14874, 14878, 14882], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_332_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_multiref", ins := [8030], outs := [14889, 14893, 14897, 14901, 14905], params := [5] } := by
  intro s
  change 5 ≥ 5
  omega

theorem pm_node_333_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_float", ins := [14866], outs := [8031] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_334_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [14874], outs := [8051], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_335_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [14878], outs := [8065], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_336_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_reshape", ins := [14882], outs := [8083], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_337_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_float", ins := [14889], outs := [8032] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_338_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [14897], outs := [8052], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_339_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [14901], outs := [8066], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_340_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_reshape", ins := [14905], outs := [8084], params := [2048, 1024] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_341_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_norm_linear", ins := [8031, 4869], outs := [8037] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_342_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8051, 4878], outs := [8055] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_343_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8065, 4883], outs := [8069] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_344_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_mix_precision_linear", ins := [8083, 4887], outs := [8087] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_345_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_norm_linear", ins := [8032, 4869], outs := [8038] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_346_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8052, 4878], outs := [8056] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_347_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8066, 4883], outs := [8070] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_348_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_mix_precision_linear", ins := [8084, 4887], outs := [8088] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_349_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_topk_routing", ins := [8037], outs := [8039, 8041, 8043], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_350_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8055], outs := [8061], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_351_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8069], outs := [8079], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_352_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_view", ins := [8087], outs := [8097], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_353_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_topk_routing", ins := [8038], outs := [8040, 8042, 8044], params := [8, 1] } := by
  intro s
  change 3 ≥ 3
  omega

theorem pm_node_354_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8056], outs := [8062], params := [2048, 1] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_355_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8070], outs := [8080], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_356_wf : IsWellFormedNode pm { rank := 1, op := "OpName.FW_view", ins := [8088], outs := [8098], params := [2048, 512] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_357_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_all2all_moe_gmm", ins := [14870, 8039, 8041, 8045, 8047], outs := [8049], params := [64, 0, 32, 8] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_358_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_sigmoid", ins := [8061], outs := [8063] } := by
  intro s
  change 1 ≥ 1
  omega

theorem pm_node_359_wf : IsWellFormedNode pm { rank := 0, op := "OpName.FW_swiglu", ins := [8079, 8097], outs := [8101] } := by
  intro s
  change 1 ≥ 1
  omega

end TrainVerify.Denote.GeneratedStructuralFacts
