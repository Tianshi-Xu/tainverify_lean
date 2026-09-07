import denote.gpt_ly4_regen.GeneratedData
import denote.KRankBWLinearDxRow
import denote.KRankBWLinearDwRowGeneral
/- AUTO-GENERATED closed relation state universe. -/
import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.DwRowReconstructionConsumer

set_option maxRecDepth 100000
set_option maxHeartbeats 500000
noncomputable section

private def fact_000056 : RelationFact :=
  .joined 744 744 [1, 4, 8, 8]

private def fact_000059 : RelationFact :=
  .joined 927 926 [1, 8, 32]

private def fact_000078 : RelationFact :=
  .joined 926 917 [1, 8, 32]

private def fact_000119 : RelationFact :=
  .reduction 927 [1254, 1251, 1248, 1245] [1, 8, 32]

private def fact_000128 : RelationFact :=
  .sharded 563 [1065, 1066, 1067, 1068] 0 [128, 32] [32, 32]

private def fact_000129 : RelationFact :=
  .sharded 568 [568] 0 [32] [32]

private def fact_000130 : RelationFact :=
  .sharded 569 [569] 0 [32] [32]

private def fact_000131 : RelationFact :=
  .sharded 571 [571] 0 [32, 32] [32, 32]

private def fact_000132 : RelationFact :=
  .sharded 573 [573] 0 [32, 32] [32, 32]

private def fact_000133 : RelationFact :=
  .sharded 575 [1229, 1230, 1231, 1232] 0 [32, 32] [8, 32]

private def fact_000172 : RelationFact :=
  .sharded 714 [714] 0 [1, 8] [1, 8]

private def fact_000173 : RelationFact :=
  .sharded 564 [1109, 1110, 1111, 1112] 2 [1, 8, 32] [1, 8, 8]

private def fact_000216 : RelationFact :=
  .sharded 578 [1261, 1262, 1263, 1264] 3 [1, 4, 8, 8] [1, 4, 8, 2]

private def fact_000265 : RelationFact :=
  .sharded 583 [1333, 1334, 1335, 1336] 2 [1, 4, 8, 8] [1, 4, 2, 8]

private def fact_000353 : RelationFact :=
  .sharded 908 [1517, 1519, 1521, 1523] 2 [1, 8, 32] [1, 8, 8]

private def fact_000364 : RelationFact :=
  .sharded 744 [1381, 1383, 1385, 1387] 1 [1, 4, 8, 8] [1, 1, 8, 8]

private def fact_000366 : RelationFact :=
  .sharded 736 [1247, 1250, 1253, 1256] 2 [1, 8, 32] [1, 8, 8]

private def fact_000367 : RelationFact :=
  .sharded 738 [1274, 1276, 1278, 1280] 3 [1, 4, 8, 8] [1, 4, 8, 2]

private def fact_000368 : RelationFact :=
  .sharded 743 [1346, 1348, 1350, 1352] 2 [1, 4, 8, 8] [1, 4, 2, 8]

private def fact_000411 : RelationFact :=
  .sharded 903 [1141, 1142, 1143, 1144] 1 [1, 8, 32] [1, 2, 32]

private def fact_000448 : RelationFact :=
  .sharded 918 [1173, 1174, 1175, 1176] 1 [1, 8, 32] [1, 2, 32]

private def fact_000449 : RelationFact :=
  .sharded 922 [1201, 1202, 1203, 1204] 1 [1, 8, 32] [1, 2, 32]

private def fact_dw_row_consumer : RelationFact :=
  .sharded 735 [1246, 1249, 1252, 1255] 0 [32, 32] [8, 32]

private def authority_transition_eq_sm_565_pm_565 : RelationFact :=
  .tensorEq .sm 565 .pm 565

private def authority_transition_eq_sm_568_pm_568 : RelationFact :=
  .tensorEq .sm 568 .pm 568

private def authority_transition_eq_sm_569_pm_569 : RelationFact :=
  .tensorEq .sm 569 .pm 569

private def authority_transition_eq_sm_571_pm_571 : RelationFact :=
  .tensorEq .sm 571 .pm 571

private def authority_transition_eq_sm_573_pm_573 : RelationFact :=
  .tensorEq .sm 573 .pm 573

private def authority_transition_eq_sm_714_pm_714 : RelationFact :=
  .tensorEq .sm 714 .pm 714

private def authority_transition_eq_sm_716_pm_716 : RelationFact :=
  .tensorEq .sm 716 .pm 716

private def authority_transition_shape_pm_565 : RelationFact :=
  .tensorShape .pm 565 [8, 32]

private def authority_transition_shape_pm_568 : RelationFact :=
  .tensorShape .pm 568 [32]

private def authority_transition_shape_pm_569 : RelationFact :=
  .tensorShape .pm 569 [32]

private def authority_transition_shape_pm_571 : RelationFact :=
  .tensorShape .pm 571 [32, 32]

private def authority_transition_shape_pm_573 : RelationFact :=
  .tensorShape .pm 573 [32, 32]

private def authority_transition_shape_pm_714 : RelationFact :=
  .tensorShape .pm 714 [1, 8]

private def anchor_sm_shape_563 : RelationFact :=
  .tensorShape .sm 563 [128, 32]

private def state_000350 : RelationState where
  facts := [anchor_sm_shape_563, authority_transition_eq_sm_565_pm_565, authority_transition_eq_sm_568_pm_568, authority_transition_eq_sm_569_pm_569, authority_transition_eq_sm_571_pm_571, authority_transition_eq_sm_573_pm_573, authority_transition_eq_sm_714_pm_714, authority_transition_eq_sm_716_pm_716, authority_transition_shape_pm_565, authority_transition_shape_pm_568, authority_transition_shape_pm_569, authority_transition_shape_pm_571, authority_transition_shape_pm_573, authority_transition_shape_pm_714, fact_000078, fact_000128, fact_000129, fact_000130, fact_000131, fact_000132, fact_000133, fact_000172, fact_000173, fact_000216, fact_000265, fact_000353, fact_000364, fact_000366, fact_000411, fact_000448, fact_000449]
  nonempty := by decide

private def state_000351 : RelationState where
  facts := [anchor_sm_shape_563, authority_transition_eq_sm_565_pm_565, authority_transition_eq_sm_568_pm_568, authority_transition_eq_sm_569_pm_569, authority_transition_eq_sm_571_pm_571, authority_transition_eq_sm_573_pm_573, authority_transition_eq_sm_714_pm_714, authority_transition_eq_sm_716_pm_716, authority_transition_shape_pm_565, authority_transition_shape_pm_568, authority_transition_shape_pm_569, authority_transition_shape_pm_571, authority_transition_shape_pm_573, authority_transition_shape_pm_714, fact_000059, fact_000128, fact_000129, fact_000130, fact_000131, fact_000132, fact_000172, fact_000173, fact_000353, fact_000367, fact_000368, fact_000411, fact_000448, fact_000449, fact_dw_row_consumer]
  nonempty := by decide

end
end TrainVerify.Denote.DwRowReconstructionConsumer

namespace TrainVerify.Denote.DwRowReconstructionConsumer
noncomputable section
private def segment_000350_sm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] }, { rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] }]
private def segment_000350_pm_nodes:List NodeDecl:=[{ rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] }, { rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] }, { rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] }, { rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] }, { rank := 0, op := "OpName.AllGatherPrim", ins := [1381, 1383, 1385, 1387], outs := [744], params := [1] }, { rank := 0, op := "OpName.AllReducePrim", ins := [1254, 1251, 1248, 1245], outs := [926] }, { rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] }, { rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] }, { rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] }, { rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] }]
@[irreducible] private def segment_000350_sm_final(s:Store):Store:=segment_000350_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) s
@[irreducible] private def segment_000350_pm_final(s:Store):Store:=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) s

private theorem segment_000350_hLinearSm(smStore:Store):(segment_000350_sm_final smStore) 927=(bw_linear ((segment_000350_sm_final smStore) 736) ((segment_000350_sm_final smStore) 926) ((segment_000350_sm_final smStore) 575)).1:=by
  have hfinal:(segment_000350_sm_final smStore)=segment_000350_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000350_sm_final;rfl
  have hout_nodes : segment_000350_sm_nodes = (segment_000350_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] }] ++ (segment_000350_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000350_sm_final smStore) 927 = (bw_linear (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 736) (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 926) (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 575)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 1) (segment_000350_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] } 927
      (fun t => (bw_linear (t 736) (t 926) (t 575)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.sm t 0 736 926 575 927 735 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 736 = (segment_000350_sm_final smStore) 736 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] } :: (segment_000350_sm_nodes.drop 2)) 736
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 926 = (segment_000350_sm_final smStore) 926 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] } :: (segment_000350_sm_nodes.drop 2)) 926
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 575 = (segment_000350_sm_final smStore) 575 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] } :: (segment_000350_sm_nodes.drop 2)) 575
      (by native_decide) (by native_decide)
  have hout : (segment_000350_sm_final smStore) 927 = (bw_linear ((segment_000350_sm_final smStore) 736) ((segment_000350_sm_final smStore) 926) ((segment_000350_sm_final smStore) 575)).1 := by
    calc
      _ = (bw_linear (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 736) (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 926) (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 575)).1 := hout_prefix
      _ = (bw_linear ((segment_000350_sm_final smStore) 736) ((segment_000350_sm_final smStore) 926) ((segment_000350_sm_final smStore) 575)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hLinearDwSm(smStore:Store):(segment_000350_sm_final smStore) 735=(bw_linear ((segment_000350_sm_final smStore) 736) ((segment_000350_sm_final smStore) 926) ((segment_000350_sm_final smStore) 575)).2:=by
  have hfinal:(segment_000350_sm_final smStore)=segment_000350_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000350_sm_final;rfl
  have hout_nodes : segment_000350_sm_nodes = (segment_000350_sm_nodes.take 1) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] }] ++ (segment_000350_sm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000350_sm_final smStore) 735 = (bw_linear (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 736) (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 926) (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 575)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 1) (segment_000350_sm_nodes.drop 2)
      { rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] } 735
      (fun t => (bw_linear (t 736) (t 926) (t 575)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.sm t 0 736 926 575 927 735 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 736 = (segment_000350_sm_final smStore) 736 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] } :: (segment_000350_sm_nodes.drop 2)) 736
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 926 = (segment_000350_sm_final smStore) 926 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] } :: (segment_000350_sm_nodes.drop 2)) 926
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 575 = (segment_000350_sm_final smStore) 575 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 1) ({ rank := 0, op := "OpName.BW_linear", ins := [736, 926, 575], outs := [927, 735] } :: (segment_000350_sm_nodes.drop 2)) 575
      (by native_decide) (by native_decide)
  have hout : (segment_000350_sm_final smStore) 735 = (bw_linear ((segment_000350_sm_final smStore) 736) ((segment_000350_sm_final smStore) 926) ((segment_000350_sm_final smStore) 575)).2 := by
    calc
      _ = (bw_linear (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 736) (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 926) (((segment_000350_sm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 575)).2 := hout_prefix
      _ = (bw_linear ((segment_000350_sm_final smStore) 736) ((segment_000350_sm_final smStore) 926) ((segment_000350_sm_final smStore) 575)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hLinearPm0(pmStore:Store):(segment_000350_pm_final pmStore) 1254=(bw_linear ((segment_000350_pm_final pmStore) 1247) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1229)).1:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] }] ++ (segment_000350_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1254 = (bw_linear (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1247) (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1229)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 0) (segment_000350_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] } 1254
      (fun t => (bw_linear (t 1247) (t 917) (t 1229)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 0 1247 917 1229 1254 1246 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1247 = (segment_000350_pm_final pmStore) 1247 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] } :: (segment_000350_pm_nodes.drop 1)) 1247
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917 = (segment_000350_pm_final pmStore) 917 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] } :: (segment_000350_pm_nodes.drop 1)) 917
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1229 = (segment_000350_pm_final pmStore) 1229 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] } :: (segment_000350_pm_nodes.drop 1)) 1229
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1254 = (bw_linear ((segment_000350_pm_final pmStore) 1247) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1229)).1 := by
    calc
      _ = (bw_linear (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1247) (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1229)).1 := hout_prefix
      _ = (bw_linear ((segment_000350_pm_final pmStore) 1247) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1229)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hLinearDwPm0(pmStore:Store):(segment_000350_pm_final pmStore) 1246=(bw_linear ((segment_000350_pm_final pmStore) 1247) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1229)).2:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] }] ++ (segment_000350_pm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1246 = (bw_linear (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1247) (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1229)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 0) (segment_000350_pm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] } 1246
      (fun t => (bw_linear (t 1247) (t 917) (t 1229)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 0 1247 917 1229 1254 1246 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1247 = (segment_000350_pm_final pmStore) 1247 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] } :: (segment_000350_pm_nodes.drop 1)) 1247
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917 = (segment_000350_pm_final pmStore) 917 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] } :: (segment_000350_pm_nodes.drop 1)) 917
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1229 = (segment_000350_pm_final pmStore) 1229 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 0) ({ rank := 0, op := "OpName.BW_linear", ins := [1247, 917, 1229], outs := [1254, 1246] } :: (segment_000350_pm_nodes.drop 1)) 1229
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1246 = (bw_linear ((segment_000350_pm_final pmStore) 1247) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1229)).2 := by
    calc
      _ = (bw_linear (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1247) (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1229)).2 := hout_prefix
      _ = (bw_linear ((segment_000350_pm_final pmStore) 1247) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1229)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hLinearPm1(pmStore:Store):(segment_000350_pm_final pmStore) 1251=(bw_linear ((segment_000350_pm_final pmStore) 1250) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1230)).1:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] }] ++ (segment_000350_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1251 = (bw_linear (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1250) (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1230)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 1) (segment_000350_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] } 1251
      (fun t => (bw_linear (t 1250) (t 917) (t 1230)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 1 1250 917 1230 1251 1249 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1250 = (segment_000350_pm_final pmStore) 1250 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] } :: (segment_000350_pm_nodes.drop 2)) 1250
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917 = (segment_000350_pm_final pmStore) 917 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] } :: (segment_000350_pm_nodes.drop 2)) 917
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1230 = (segment_000350_pm_final pmStore) 1230 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] } :: (segment_000350_pm_nodes.drop 2)) 1230
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1251 = (bw_linear ((segment_000350_pm_final pmStore) 1250) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1230)).1 := by
    calc
      _ = (bw_linear (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1250) (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1230)).1 := hout_prefix
      _ = (bw_linear ((segment_000350_pm_final pmStore) 1250) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1230)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hLinearDwPm1(pmStore:Store):(segment_000350_pm_final pmStore) 1249=(bw_linear ((segment_000350_pm_final pmStore) 1250) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1230)).2:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 1) ++ [{ rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] }] ++ (segment_000350_pm_nodes.drop 2) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1249 = (bw_linear (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1250) (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1230)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 1) (segment_000350_pm_nodes.drop 2)
      { rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] } 1249
      (fun t => (bw_linear (t 1250) (t 917) (t 1230)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 1 1250 917 1230 1251 1249 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1250 = (segment_000350_pm_final pmStore) 1250 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] } :: (segment_000350_pm_nodes.drop 2)) 1250
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917 = (segment_000350_pm_final pmStore) 917 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] } :: (segment_000350_pm_nodes.drop 2)) 917
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1230 = (segment_000350_pm_final pmStore) 1230 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 1) ({ rank := 1, op := "OpName.BW_linear", ins := [1250, 917, 1230], outs := [1251, 1249] } :: (segment_000350_pm_nodes.drop 2)) 1230
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1249 = (bw_linear ((segment_000350_pm_final pmStore) 1250) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1230)).2 := by
    calc
      _ = (bw_linear (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1250) (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 1)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1230)).2 := hout_prefix
      _ = (bw_linear ((segment_000350_pm_final pmStore) 1250) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1230)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hLinearPm2(pmStore:Store):(segment_000350_pm_final pmStore) 1248=(bw_linear ((segment_000350_pm_final pmStore) 1253) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1231)).1:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] }] ++ (segment_000350_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1248 = (bw_linear (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1253) (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1231)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 2) (segment_000350_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] } 1248
      (fun t => (bw_linear (t 1253) (t 917) (t 1231)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 2 1253 917 1231 1248 1252 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1253 = (segment_000350_pm_final pmStore) 1253 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] } :: (segment_000350_pm_nodes.drop 3)) 1253
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917 = (segment_000350_pm_final pmStore) 917 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] } :: (segment_000350_pm_nodes.drop 3)) 917
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1231 = (segment_000350_pm_final pmStore) 1231 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] } :: (segment_000350_pm_nodes.drop 3)) 1231
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1248 = (bw_linear ((segment_000350_pm_final pmStore) 1253) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1231)).1 := by
    calc
      _ = (bw_linear (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1253) (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1231)).1 := hout_prefix
      _ = (bw_linear ((segment_000350_pm_final pmStore) 1253) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1231)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hLinearDwPm2(pmStore:Store):(segment_000350_pm_final pmStore) 1252=(bw_linear ((segment_000350_pm_final pmStore) 1253) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1231)).2:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 2) ++ [{ rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] }] ++ (segment_000350_pm_nodes.drop 3) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1252 = (bw_linear (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1253) (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1231)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 2) (segment_000350_pm_nodes.drop 3)
      { rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] } 1252
      (fun t => (bw_linear (t 1253) (t 917) (t 1231)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 2 1253 917 1231 1248 1252 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1253 = (segment_000350_pm_final pmStore) 1253 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] } :: (segment_000350_pm_nodes.drop 3)) 1253
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917 = (segment_000350_pm_final pmStore) 917 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] } :: (segment_000350_pm_nodes.drop 3)) 917
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1231 = (segment_000350_pm_final pmStore) 1231 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 2) ({ rank := 2, op := "OpName.BW_linear", ins := [1253, 917, 1231], outs := [1248, 1252] } :: (segment_000350_pm_nodes.drop 3)) 1231
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1252 = (bw_linear ((segment_000350_pm_final pmStore) 1253) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1231)).2 := by
    calc
      _ = (bw_linear (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1253) (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 2)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1231)).2 := hout_prefix
      _ = (bw_linear ((segment_000350_pm_final pmStore) 1253) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1231)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hLinearPm3(pmStore:Store):(segment_000350_pm_final pmStore) 1245=(bw_linear ((segment_000350_pm_final pmStore) 1256) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1232)).1:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] }] ++ (segment_000350_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1245 = (bw_linear (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1256) (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1232)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 3) (segment_000350_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] } 1245
      (fun t => (bw_linear (t 1256) (t 917) (t 1232)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_fst_out TrainVerify.Denote.Generated.pm t 3 1256 917 1232 1245 1255 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1256 = (segment_000350_pm_final pmStore) 1256 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] } :: (segment_000350_pm_nodes.drop 4)) 1256
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917 = (segment_000350_pm_final pmStore) 917 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] } :: (segment_000350_pm_nodes.drop 4)) 917
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1232 = (segment_000350_pm_final pmStore) 1232 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] } :: (segment_000350_pm_nodes.drop 4)) 1232
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1245 = (bw_linear ((segment_000350_pm_final pmStore) 1256) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1232)).1 := by
    calc
      _ = (bw_linear (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1256) (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1232)).1 := hout_prefix
      _ = (bw_linear ((segment_000350_pm_final pmStore) 1256) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1232)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hLinearDwPm3(pmStore:Store):(segment_000350_pm_final pmStore) 1255=(bw_linear ((segment_000350_pm_final pmStore) 1256) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1232)).2:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 3) ++ [{ rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] }] ++ (segment_000350_pm_nodes.drop 4) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1255 = (bw_linear (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1256) (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1232)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 3) (segment_000350_pm_nodes.drop 4)
      { rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] } 1255
      (fun t => (bw_linear (t 1256) (t 917) (t 1232)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_linear_snd_out TrainVerify.Denote.Generated.pm t 3 1256 917 1232 1245 1255 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1256 = (segment_000350_pm_final pmStore) 1256 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] } :: (segment_000350_pm_nodes.drop 4)) 1256
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917 = (segment_000350_pm_final pmStore) 917 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] } :: (segment_000350_pm_nodes.drop 4)) 917
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1232 = (segment_000350_pm_final pmStore) 1232 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 3) ({ rank := 3, op := "OpName.BW_linear", ins := [1256, 917, 1232], outs := [1245, 1255] } :: (segment_000350_pm_nodes.drop 4)) 1232
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1255 = (bw_linear ((segment_000350_pm_final pmStore) 1256) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1232)).2 := by
    calc
      _ = (bw_linear (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1256) (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 917) (((segment_000350_pm_nodes.take 3)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1232)).2 := hout_prefix
      _ = (bw_linear ((segment_000350_pm_final pmStore) 1256) ((segment_000350_pm_final pmStore) 917) ((segment_000350_pm_final pmStore) 1232)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hAllGather(pmStore:Store):(segment_000350_pm_final pmStore) 744=allGatherPrimDimN 1 4 0 [(segment_000350_pm_final pmStore) 1381, (segment_000350_pm_final pmStore) 1383, (segment_000350_pm_final pmStore) 1385, (segment_000350_pm_final pmStore) 1387]:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 4) ++ [{ rank := 0, op := "OpName.AllGatherPrim", ins := [1381, 1383, 1385, 1387], outs := [744], params := [1] }] ++ (segment_000350_pm_nodes.drop 5) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 744 = allGatherPrimDimN 1 4 0 [((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1381, ((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1383, ((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1385, ((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1387] := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 4) (segment_000350_pm_nodes.drop 5)
      { rank := 0, op := "OpName.AllGatherPrim", ins := [1381, 1383, 1385, 1387], outs := [744], params := [1] } 744
      (fun t => allGatherPrimDimN 1 4 0 [t 1381, t 1383, t 1385, t 1387]) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_allGatherPrimDimN_out TrainVerify.Denote.Generated.pm t 0 [1381, 1383, 1385, 1387] 744 1
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1381 = (segment_000350_pm_final pmStore) 1381 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 4) ({ rank := 0, op := "OpName.AllGatherPrim", ins := [1381, 1383, 1385, 1387], outs := [744], params := [1] } :: (segment_000350_pm_nodes.drop 5)) 1381
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1383 = (segment_000350_pm_final pmStore) 1383 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 4) ({ rank := 0, op := "OpName.AllGatherPrim", ins := [1381, 1383, 1385, 1387], outs := [744], params := [1] } :: (segment_000350_pm_nodes.drop 5)) 1383
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1385 = (segment_000350_pm_final pmStore) 1385 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 4) ({ rank := 0, op := "OpName.AllGatherPrim", ins := [1381, 1383, 1385, 1387], outs := [744], params := [1] } :: (segment_000350_pm_nodes.drop 5)) 1385
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1387 = (segment_000350_pm_final pmStore) 1387 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 4) ({ rank := 0, op := "OpName.AllGatherPrim", ins := [1381, 1383, 1385, 1387], outs := [744], params := [1] } :: (segment_000350_pm_nodes.drop 5)) 1387
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 744 = allGatherPrimDimN 1 4 0 [(segment_000350_pm_final pmStore) 1381, (segment_000350_pm_final pmStore) 1383, (segment_000350_pm_final pmStore) 1385, (segment_000350_pm_final pmStore) 1387] := by
    calc
      _ = allGatherPrimDimN 1 4 0 [((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1381, ((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1383, ((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1385, ((segment_000350_pm_nodes.take 4)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1387] := hout_prefix
      _ = allGatherPrimDimN 1 4 0 [(segment_000350_pm_final pmStore) 1381, (segment_000350_pm_final pmStore) 1383, (segment_000350_pm_final pmStore) 1385, (segment_000350_pm_final pmStore) 1387] := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

private theorem segment_000350_hMatSmFst(smStore:Store):(segment_000350_sm_final smStore) 738=(bw_matmul ((segment_000350_sm_final smStore) 744) ((segment_000350_sm_final smStore) 578) ((segment_000350_sm_final smStore) 583)).1:=by
  have hfinal:(segment_000350_sm_final smStore)=segment_000350_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000350_sm_final;rfl
  have hout_nodes : segment_000350_sm_nodes = (segment_000350_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] }] ++ (segment_000350_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000350_sm_final smStore) 738 = (bw_matmul (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 744) (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 578) (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 583)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 0) (segment_000350_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] } 738
      (fun t => (bw_matmul (t 744) (t 578) (t 583)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out TrainVerify.Denote.Generated.sm t 0 744 578 583 738 743 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 744 = (segment_000350_sm_final smStore) 744 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] } :: (segment_000350_sm_nodes.drop 1)) 744
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 578 = (segment_000350_sm_final smStore) 578 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] } :: (segment_000350_sm_nodes.drop 1)) 578
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 583 = (segment_000350_sm_final smStore) 583 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] } :: (segment_000350_sm_nodes.drop 1)) 583
      (by native_decide) (by native_decide)
  have hout : (segment_000350_sm_final smStore) 738 = (bw_matmul ((segment_000350_sm_final smStore) 744) ((segment_000350_sm_final smStore) 578) ((segment_000350_sm_final smStore) 583)).1 := by
    calc
      _ = (bw_matmul (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 744) (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 578) (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 583)).1 := hout_prefix
      _ = (bw_matmul ((segment_000350_sm_final smStore) 744) ((segment_000350_sm_final smStore) 578) ((segment_000350_sm_final smStore) 583)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hMatSmSnd(smStore:Store):(segment_000350_sm_final smStore) 743=(bw_matmul ((segment_000350_sm_final smStore) 744) ((segment_000350_sm_final smStore) 578) ((segment_000350_sm_final smStore) 583)).2:=by
  have hfinal:(segment_000350_sm_final smStore)=segment_000350_sm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore:=by unfold segment_000350_sm_final;rfl
  have hout_nodes : segment_000350_sm_nodes = (segment_000350_sm_nodes.take 0) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] }] ++ (segment_000350_sm_nodes.drop 1) := by
    native_decide
  have hout_prefix : (segment_000350_sm_final smStore) 743 = (bw_matmul (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 744) (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 578) (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 583)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 0) (segment_000350_sm_nodes.drop 1)
      { rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] } 743
      (fun t => (bw_matmul (t 744) (t 578) (t 583)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out TrainVerify.Denote.Generated.sm t 0 744 578 583 738 743 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 744 = (segment_000350_sm_final smStore) 744 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] } :: (segment_000350_sm_nodes.drop 1)) 744
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 578 = (segment_000350_sm_final smStore) 578 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] } :: (segment_000350_sm_nodes.drop 1)) 578
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 583 = (segment_000350_sm_final smStore) 583 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.sm smStore
      (segment_000350_sm_nodes.take 0) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 578, 583], outs := [738, 743] } :: (segment_000350_sm_nodes.drop 1)) 583
      (by native_decide) (by native_decide)
  have hout : (segment_000350_sm_final smStore) 743 = (bw_matmul ((segment_000350_sm_final smStore) 744) ((segment_000350_sm_final smStore) 578) ((segment_000350_sm_final smStore) 583)).2 := by
    calc
      _ = (bw_matmul (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 744) (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 578) (((segment_000350_sm_nodes.take 0)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.sm) smStore 583)).2 := hout_prefix
      _ = (bw_matmul ((segment_000350_sm_final smStore) 744) ((segment_000350_sm_final smStore) 578) ((segment_000350_sm_final smStore) 583)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hMatPmFst0(pmStore:Store):(segment_000350_pm_final pmStore) 1274=(bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1261) ((segment_000350_pm_final pmStore) 1333)).1:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 6) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] }] ++ (segment_000350_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1274 = (bw_matmul (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1261) (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1333)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 6) (segment_000350_pm_nodes.drop 7)
      { rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] } 1274
      (fun t => (bw_matmul (t 744) (t 1261) (t 1333)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out TrainVerify.Denote.Generated.pm t 0 744 1261 1333 1274 1346 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744 = (segment_000350_pm_final pmStore) 744 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 6) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] } :: (segment_000350_pm_nodes.drop 7)) 744
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1261 = (segment_000350_pm_final pmStore) 1261 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 6) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] } :: (segment_000350_pm_nodes.drop 7)) 1261
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1333 = (segment_000350_pm_final pmStore) 1333 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 6) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] } :: (segment_000350_pm_nodes.drop 7)) 1333
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1274 = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1261) ((segment_000350_pm_final pmStore) 1333)).1 := by
    calc
      _ = (bw_matmul (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1261) (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1333)).1 := hout_prefix
      _ = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1261) ((segment_000350_pm_final pmStore) 1333)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hMatPmSnd0(pmStore:Store):(segment_000350_pm_final pmStore) 1346=(bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1261) ((segment_000350_pm_final pmStore) 1333)).2:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 6) ++ [{ rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] }] ++ (segment_000350_pm_nodes.drop 7) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1346 = (bw_matmul (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1261) (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1333)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 6) (segment_000350_pm_nodes.drop 7)
      { rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] } 1346
      (fun t => (bw_matmul (t 744) (t 1261) (t 1333)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out TrainVerify.Denote.Generated.pm t 0 744 1261 1333 1274 1346 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744 = (segment_000350_pm_final pmStore) 744 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 6) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] } :: (segment_000350_pm_nodes.drop 7)) 744
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1261 = (segment_000350_pm_final pmStore) 1261 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 6) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] } :: (segment_000350_pm_nodes.drop 7)) 1261
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1333 = (segment_000350_pm_final pmStore) 1333 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 6) ({ rank := 0, op := "OpName.BW_matmul", ins := [744, 1261, 1333], outs := [1274, 1346] } :: (segment_000350_pm_nodes.drop 7)) 1333
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1346 = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1261) ((segment_000350_pm_final pmStore) 1333)).2 := by
    calc
      _ = (bw_matmul (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1261) (((segment_000350_pm_nodes.take 6)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1333)).2 := hout_prefix
      _ = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1261) ((segment_000350_pm_final pmStore) 1333)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hMatPmFst1(pmStore:Store):(segment_000350_pm_final pmStore) 1276=(bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1262) ((segment_000350_pm_final pmStore) 1334)).1:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 7) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] }] ++ (segment_000350_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1276 = (bw_matmul (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1262) (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1334)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 7) (segment_000350_pm_nodes.drop 8)
      { rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] } 1276
      (fun t => (bw_matmul (t 744) (t 1262) (t 1334)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out TrainVerify.Denote.Generated.pm t 1 744 1262 1334 1276 1348 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744 = (segment_000350_pm_final pmStore) 744 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 7) ({ rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] } :: (segment_000350_pm_nodes.drop 8)) 744
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1262 = (segment_000350_pm_final pmStore) 1262 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 7) ({ rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] } :: (segment_000350_pm_nodes.drop 8)) 1262
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1334 = (segment_000350_pm_final pmStore) 1334 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 7) ({ rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] } :: (segment_000350_pm_nodes.drop 8)) 1334
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1276 = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1262) ((segment_000350_pm_final pmStore) 1334)).1 := by
    calc
      _ = (bw_matmul (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1262) (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1334)).1 := hout_prefix
      _ = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1262) ((segment_000350_pm_final pmStore) 1334)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hMatPmSnd1(pmStore:Store):(segment_000350_pm_final pmStore) 1348=(bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1262) ((segment_000350_pm_final pmStore) 1334)).2:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 7) ++ [{ rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] }] ++ (segment_000350_pm_nodes.drop 8) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1348 = (bw_matmul (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1262) (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1334)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 7) (segment_000350_pm_nodes.drop 8)
      { rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] } 1348
      (fun t => (bw_matmul (t 744) (t 1262) (t 1334)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out TrainVerify.Denote.Generated.pm t 1 744 1262 1334 1276 1348 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744 = (segment_000350_pm_final pmStore) 744 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 7) ({ rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] } :: (segment_000350_pm_nodes.drop 8)) 744
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1262 = (segment_000350_pm_final pmStore) 1262 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 7) ({ rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] } :: (segment_000350_pm_nodes.drop 8)) 1262
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1334 = (segment_000350_pm_final pmStore) 1334 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 7) ({ rank := 1, op := "OpName.BW_matmul", ins := [744, 1262, 1334], outs := [1276, 1348] } :: (segment_000350_pm_nodes.drop 8)) 1334
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1348 = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1262) ((segment_000350_pm_final pmStore) 1334)).2 := by
    calc
      _ = (bw_matmul (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1262) (((segment_000350_pm_nodes.take 7)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1334)).2 := hout_prefix
      _ = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1262) ((segment_000350_pm_final pmStore) 1334)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hMatPmFst2(pmStore:Store):(segment_000350_pm_final pmStore) 1278=(bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1263) ((segment_000350_pm_final pmStore) 1335)).1:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 8) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] }] ++ (segment_000350_pm_nodes.drop 9) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1278 = (bw_matmul (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1263) (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1335)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 8) (segment_000350_pm_nodes.drop 9)
      { rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] } 1278
      (fun t => (bw_matmul (t 744) (t 1263) (t 1335)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out TrainVerify.Denote.Generated.pm t 2 744 1263 1335 1278 1350 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744 = (segment_000350_pm_final pmStore) 744 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 8) ({ rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] } :: (segment_000350_pm_nodes.drop 9)) 744
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1263 = (segment_000350_pm_final pmStore) 1263 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 8) ({ rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] } :: (segment_000350_pm_nodes.drop 9)) 1263
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1335 = (segment_000350_pm_final pmStore) 1335 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 8) ({ rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] } :: (segment_000350_pm_nodes.drop 9)) 1335
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1278 = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1263) ((segment_000350_pm_final pmStore) 1335)).1 := by
    calc
      _ = (bw_matmul (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1263) (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1335)).1 := hout_prefix
      _ = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1263) ((segment_000350_pm_final pmStore) 1335)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hMatPmSnd2(pmStore:Store):(segment_000350_pm_final pmStore) 1350=(bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1263) ((segment_000350_pm_final pmStore) 1335)).2:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 8) ++ [{ rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] }] ++ (segment_000350_pm_nodes.drop 9) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1350 = (bw_matmul (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1263) (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1335)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 8) (segment_000350_pm_nodes.drop 9)
      { rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] } 1350
      (fun t => (bw_matmul (t 744) (t 1263) (t 1335)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out TrainVerify.Denote.Generated.pm t 2 744 1263 1335 1278 1350 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744 = (segment_000350_pm_final pmStore) 744 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 8) ({ rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] } :: (segment_000350_pm_nodes.drop 9)) 744
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1263 = (segment_000350_pm_final pmStore) 1263 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 8) ({ rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] } :: (segment_000350_pm_nodes.drop 9)) 1263
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1335 = (segment_000350_pm_final pmStore) 1335 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 8) ({ rank := 2, op := "OpName.BW_matmul", ins := [744, 1263, 1335], outs := [1278, 1350] } :: (segment_000350_pm_nodes.drop 9)) 1335
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1350 = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1263) ((segment_000350_pm_final pmStore) 1335)).2 := by
    calc
      _ = (bw_matmul (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1263) (((segment_000350_pm_nodes.take 8)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1335)).2 := hout_prefix
      _ = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1263) ((segment_000350_pm_final pmStore) 1335)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hMatPmFst3(pmStore:Store):(segment_000350_pm_final pmStore) 1280=(bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1264) ((segment_000350_pm_final pmStore) 1336)).1:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 9) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] }] ++ (segment_000350_pm_nodes.drop 10) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1280 = (bw_matmul (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1264) (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1336)).1 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 9) (segment_000350_pm_nodes.drop 10)
      { rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] } 1280
      (fun t => (bw_matmul (t 744) (t 1264) (t 1336)).1) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_fst_out TrainVerify.Denote.Generated.pm t 3 744 1264 1336 1280 1352 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744 = (segment_000350_pm_final pmStore) 744 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 9) ({ rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] } :: (segment_000350_pm_nodes.drop 10)) 744
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1264 = (segment_000350_pm_final pmStore) 1264 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 9) ({ rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] } :: (segment_000350_pm_nodes.drop 10)) 1264
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1336 = (segment_000350_pm_final pmStore) 1336 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 9) ({ rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] } :: (segment_000350_pm_nodes.drop 10)) 1336
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1280 = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1264) ((segment_000350_pm_final pmStore) 1336)).1 := by
    calc
      _ = (bw_matmul (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1264) (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1336)).1 := hout_prefix
      _ = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1264) ((segment_000350_pm_final pmStore) 1336)).1 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hMatPmSnd3(pmStore:Store):(segment_000350_pm_final pmStore) 1352=(bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1264) ((segment_000350_pm_final pmStore) 1336)).2:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 9) ++ [{ rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] }] ++ (segment_000350_pm_nodes.drop 10) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 1352 = (bw_matmul (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1264) (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1336)).2 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 9) (segment_000350_pm_nodes.drop 10)
      { rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] } 1352
      (fun t => (bw_matmul (t 744) (t 1264) (t 1336)).2) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_bw_matmul_snd_out TrainVerify.Denote.Generated.pm t 3 744 1264 1336 1280 1352 (by native_decide)
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744 = (segment_000350_pm_final pmStore) 744 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 9) ({ rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] } :: (segment_000350_pm_nodes.drop 10)) 744
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1264 = (segment_000350_pm_final pmStore) 1264 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 9) ({ rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] } :: (segment_000350_pm_nodes.drop 10)) 1264
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1336 = (segment_000350_pm_final pmStore) 1336 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 9) ({ rank := 3, op := "OpName.BW_matmul", ins := [744, 1264, 1336], outs := [1280, 1352] } :: (segment_000350_pm_nodes.drop 10)) 1336
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 1352 = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1264) ((segment_000350_pm_final pmStore) 1336)).2 := by
    calc
      _ = (bw_matmul (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 744) (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1264) (((segment_000350_pm_nodes.take 9)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1336)).2 := hout_prefix
      _ = (bw_matmul ((segment_000350_pm_final pmStore) 744) ((segment_000350_pm_final pmStore) 1264) ((segment_000350_pm_final pmStore) 1336)).2 := by rw [hout_read_0, hout_read_1, hout_read_2]
  exact hout

private theorem segment_000350_hAllReduce(pmStore:Store):(segment_000350_pm_final pmStore) 926=allReducePrim 4 0 [(segment_000350_pm_final pmStore) 1254, (segment_000350_pm_final pmStore) 1251, (segment_000350_pm_final pmStore) 1248, (segment_000350_pm_final pmStore) 1245]:=by
  have hfinal:(segment_000350_pm_final pmStore)=segment_000350_pm_nodes.foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore:=by unfold segment_000350_pm_final;rfl
  have hout_nodes : segment_000350_pm_nodes = (segment_000350_pm_nodes.take 5) ++ [{ rank := 0, op := "OpName.AllReducePrim", ins := [1254, 1251, 1248, 1245], outs := [926] }] ++ (segment_000350_pm_nodes.drop 6) := by
    native_decide
  have hout_prefix : (segment_000350_pm_final pmStore) 926 = allReducePrim 4 0 [((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1254, ((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1251, ((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1248, ((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1245] := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_middle_writer TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 5) (segment_000350_pm_nodes.drop 6)
      { rank := 0, op := "OpName.AllReducePrim", ins := [1254, 1251, 1248, 1245], outs := [926] } 926
      (fun t => allReducePrim 4 0 [t 1254, t 1251, t 1248, t 1245]) (by
        intro t
        rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective (hshuffle:=by native_decide) (hunshuffle:=by native_decide) (hattn:=by native_decide)]
        simp [applyNodeDistributed,applyNodeRingAttn]
        exact applyNode_allReducePrim_out TrainVerify.Denote.Generated.pm t 0 [1254, 1251, 1248, 1245] 926
      ) (by native_decide) (by native_decide)
  have hout_read_0 : ((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1254 = (segment_000350_pm_final pmStore) 1254 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 5) ({ rank := 0, op := "OpName.AllReducePrim", ins := [1254, 1251, 1248, 1245], outs := [926] } :: (segment_000350_pm_nodes.drop 6)) 1254
      (by native_decide) (by native_decide)
  have hout_read_1 : ((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1251 = (segment_000350_pm_final pmStore) 1251 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 5) ({ rank := 0, op := "OpName.AllReducePrim", ins := [1254, 1251, 1248, 1245], outs := [926] } :: (segment_000350_pm_nodes.drop 6)) 1251
      (by native_decide) (by native_decide)
  have hout_read_2 : ((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1248 = (segment_000350_pm_final pmStore) 1248 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 5) ({ rank := 0, op := "OpName.AllReducePrim", ins := [1254, 1251, 1248, 1245], outs := [926] } :: (segment_000350_pm_nodes.drop 6)) 1248
      (by native_decide) (by native_decide)
  have hout_read_3 : ((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1245 = (segment_000350_pm_final pmStore) 1245 := by
    rw [hfinal, hout_nodes]
    exact foldl_faithful_prefix_read_eq_final TrainVerify.Denote.Generated.pm pmStore
      (segment_000350_pm_nodes.take 5) ({ rank := 0, op := "OpName.AllReducePrim", ins := [1254, 1251, 1248, 1245], outs := [926] } :: (segment_000350_pm_nodes.drop 6)) 1245
      (by native_decide) (by native_decide)
  have hout : (segment_000350_pm_final pmStore) 926 = allReducePrim 4 0 [(segment_000350_pm_final pmStore) 1254, (segment_000350_pm_final pmStore) 1251, (segment_000350_pm_final pmStore) 1248, (segment_000350_pm_final pmStore) 1245] := by
    calc
      _ = allReducePrim 4 0 [((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1254, ((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1251, ((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1248, ((segment_000350_pm_nodes.take 5)).foldl (applyNodeDistributedFaithful TrainVerify.Denote.Generated.pm) pmStore 1245] := hout_prefix
      _ = allReducePrim 4 0 [(segment_000350_pm_final pmStore) 1254, (segment_000350_pm_final pmStore) 1251, (segment_000350_pm_final pmStore) 1248, (segment_000350_pm_final pmStore) 1245] := by rw [hout_read_0, hout_read_1, hout_read_2, hout_read_3]
  exact hout

set_option maxHeartbeats 500000 in
private theorem segment_000350_sound(smStore pmStore:Store)(hstate:state_000350.Holds smStore pmStore):state_000351.Holds (segment_000350_sm_final smStore) (segment_000350_pm_final pmStore):=by
 let smFinal:=segment_000350_sm_final smStore
 let pmFinal:=segment_000350_pm_final pmStore
 have hframe:state_000350.Holds smFinal pmFinal:=by unfold smFinal pmFinal segment_000350_sm_final segment_000350_pm_final;apply RelationState.Holds.fold_frame segment_000350_sm_nodes segment_000350_pm_nodes smStore pmStore hstate <;> native_decide
 have hlg:fact_000366.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 736) [pmFinal 1247, pmFinal 1250, pmFinal 1253, pmFinal 1256] 2 [1,8,32] [1,8,8] at hlg
 have hlx:fact_000078.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change smFinal 926=pmFinal 917∧(smFinal 926).shape=[1,8,32]∧(pmFinal 917).shape=[1,8,32] at hlx
 have hlw:fact_000133.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 575) [pmFinal 1229, pmFinal 1230, pmFinal 1231, pmFinal 1232] 0 [32,32] [8,32] at hlw
 have hls:=segment_000350_hLinearSm smStore
 change smFinal 927=(bw_linear (smFinal 736) (smFinal 926) (smFinal 575)).1 at hls
 have hds:=segment_000350_hLinearDwSm smStore
 change smFinal 735=(bw_linear (smFinal 736) (smFinal 926) (smFinal 575)).2 at hds
 have hlp0:=segment_000350_hLinearPm0 pmStore
 change pmFinal 1254=(bw_linear (pmFinal 1247) (pmFinal 917) (pmFinal 1229)).1 at hlp0
 have lgs0:=hlg.shard_shapes (pmFinal 1247) (by simp)
 have lws0:=hlw.shard_shapes (pmFinal 1229) (by simp)
 have los0:(pmFinal 1254).shape=[1,8,32]:=by rw [hlp0];exact bw_linear_3d_fst_shape 1 8 8 32 _ _ _ lgs0 hlx.2.2 lws0
 have hdp0:=segment_000350_hLinearDwPm0 pmStore
 change pmFinal 1246=(bw_linear (pmFinal 1247) (pmFinal 917) (pmFinal 1229)).2 at hdp0
 have lds0:(pmFinal 1246).shape=[8,32]:=by rw [hdp0];exact bw_linear_3d_snd_shape 1 8 8 32 _ _ _ lgs0 hlx.2.2 lws0
 have hlp1:=segment_000350_hLinearPm1 pmStore
 change pmFinal 1251=(bw_linear (pmFinal 1250) (pmFinal 917) (pmFinal 1230)).1 at hlp1
 have lgs1:=hlg.shard_shapes (pmFinal 1250) (by simp)
 have lws1:=hlw.shard_shapes (pmFinal 1230) (by simp)
 have los1:(pmFinal 1251).shape=[1,8,32]:=by rw [hlp1];exact bw_linear_3d_fst_shape 1 8 8 32 _ _ _ lgs1 hlx.2.2 lws1
 have hdp1:=segment_000350_hLinearDwPm1 pmStore
 change pmFinal 1249=(bw_linear (pmFinal 1250) (pmFinal 917) (pmFinal 1230)).2 at hdp1
 have lds1:(pmFinal 1249).shape=[8,32]:=by rw [hdp1];exact bw_linear_3d_snd_shape 1 8 8 32 _ _ _ lgs1 hlx.2.2 lws1
 have hlp2:=segment_000350_hLinearPm2 pmStore
 change pmFinal 1248=(bw_linear (pmFinal 1253) (pmFinal 917) (pmFinal 1231)).1 at hlp2
 have lgs2:=hlg.shard_shapes (pmFinal 1253) (by simp)
 have lws2:=hlw.shard_shapes (pmFinal 1231) (by simp)
 have los2:(pmFinal 1248).shape=[1,8,32]:=by rw [hlp2];exact bw_linear_3d_fst_shape 1 8 8 32 _ _ _ lgs2 hlx.2.2 lws2
 have hdp2:=segment_000350_hLinearDwPm2 pmStore
 change pmFinal 1252=(bw_linear (pmFinal 1253) (pmFinal 917) (pmFinal 1231)).2 at hdp2
 have lds2:(pmFinal 1252).shape=[8,32]:=by rw [hdp2];exact bw_linear_3d_snd_shape 1 8 8 32 _ _ _ lgs2 hlx.2.2 lws2
 have hlp3:=segment_000350_hLinearPm3 pmStore
 change pmFinal 1245=(bw_linear (pmFinal 1256) (pmFinal 917) (pmFinal 1232)).1 at hlp3
 have lgs3:=hlg.shard_shapes (pmFinal 1256) (by simp)
 have lws3:=hlw.shard_shapes (pmFinal 1232) (by simp)
 have los3:(pmFinal 1245).shape=[1,8,32]:=by rw [hlp3];exact bw_linear_3d_fst_shape 1 8 8 32 _ _ _ lgs3 hlx.2.2 lws3
 have hdp3:=segment_000350_hLinearDwPm3 pmStore
 change pmFinal 1255=(bw_linear (pmFinal 1256) (pmFinal 917) (pmFinal 1232)).2 at hdp3
 have lds3:(pmFinal 1255).shape=[8,32]:=by rw [hdp3];exact bw_linear_3d_snd_shape 1 8 8 32 _ _ _ lgs3 hlx.2.2 lws3
 have lgV:smFinal 736=allGatherPrimDimN 2 4 0 [pmFinal 1247, pmFinal 1250, pmFinal 1253, pmFinal 1256]:=by simpa only [List.length_cons,List.length_nil] using hlg.full_value
 have lwV:smFinal 575=allGatherPrimDimN 0 4 0 [pmFinal 1229, pmFinal 1230, pmFinal 1231, pmFinal 1232]:=by simpa only [List.length_cons,List.length_nil] using hlw.full_value
 have lc_raw := TrainVerify.Denote.bw_linear_dx_row_reduction_rank3 4 1 8 8 32
   [pmFinal 1247, pmFinal 1250, pmFinal 1253, pmFinal 1256] [pmFinal 1229, pmFinal 1230, pmFinal 1231, pmFinal 1232] (pmFinal 917)
   (by decide) (by decide) (by decide) (by decide) (by decide) rfl rfl
   hlg.shard_shapes hlw.shard_shapes hlx.2.2
 have lc : (bw_linear (allGatherPrimDimN 2 4 0 [pmFinal 1247, pmFinal 1250, pmFinal 1253, pmFinal 1256])
   (pmFinal 917) (allGatherPrimDimN 0 4 0 [pmFinal 1229, pmFinal 1230, pmFinal 1231, pmFinal 1232])).1 =
   allReducePrim 4 0 [(bw_linear (pmFinal 1247) (pmFinal 917) (pmFinal 1229)).1, (bw_linear (pmFinal 1250) (pmFinal 917) (pmFinal 1230)).1, (bw_linear (pmFinal 1253) (pmFinal 917) (pmFinal 1231)).1, (bw_linear (pmFinal 1256) (pmFinal 917) (pmFinal 1232)).1] := by
   simpa only [List.zipWith, tensorSum, allReducePrim, List.head?_cons, Option.map_some, Option.getD_some] using lc_raw
 have lov:smFinal 927=allReducePrim 4 0 [pmFinal 1254, pmFinal 1251, pmFinal 1248, pmFinal 1245]:=by rw [hls,lgV,hlx.1,lwV,lc];rw [←hlp0, ←hlp1, ←hlp2, ←hlp3]
 have lovl:smFinal 927=allReducePrim [pmFinal 1254, pmFinal 1251, pmFinal 1248, pmFinal 1245].length 0 [pmFinal 1254, pmFinal 1251, pmFinal 1248, pmFinal 1245]:=by simpa only [List.length_cons,List.length_nil] using lov
 have lofull:(smFinal 927).shape=[1,8,32]:=by rw [hls];exact bw_linear_3d_fst_shape 1 8 32 32 _ _ _ hlg.full_shape hlx.2.1 hlw.full_shape
 have hLin:fact_000119.Holds smFinal pmFinal:=by change ReductionRel (smFinal 927) [pmFinal 1254, pmFinal 1251, pmFinal 1248, pmFinal 1245] [1,8,32];exact {full_value:=lovl,full_shape:=lofull,contributions_nonempty:=by simp,contribution_shapes:=by intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with h0|h1|h2|h3 <;> subst z;exact los0;exact los1;exact los2;exact los3,reduced_shape:=by rw [←lovl];exact lofull}
 have hrw:=segment_000350_hAllReduce pmStore
 change pmFinal 926=allReducePrim 4 0 [pmFinal 1254, pmFinal 1251, pmFinal 1248, pmFinal 1245] at hrw
 have hrEq:smFinal 927=pmFinal 926:=(ReductionRel.to_joined_allReduce hLin).trans hrw.symm
 have houtR:fact_000059.Holds smFinal pmFinal:=by change smFinal 927=pmFinal 926∧_∧_;refine ⟨hrEq,hLin.full_shape,?_⟩;rw [←hrEq];exact hLin.full_shape
 have hgi:fact_000364.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 744) [pmFinal 1381, pmFinal 1383, pmFinal 1385, pmFinal 1387] 1 [1,4,8,8] [1,1,8,8] at hgi
 have hgw:=segment_000350_hAllGather pmStore
 change pmFinal 744=allGatherPrimDimN 1 4 0 [pmFinal 1381, pmFinal 1383, pmFinal 1385, pmFinal 1387] at hgw
 have hgEq:smFinal 744=pmFinal 744:=(ShardedRel.to_joined_allGather hgi).trans hgw.symm
 have hGJoin:fact_000056.Holds smFinal pmFinal:=by change smFinal 744=pmFinal 744∧_∧_;refine ⟨hgEq,hgi.full_shape,?_⟩;rw [←hgEq];exact hgi.full_shape
 have hx:fact_000216.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 578) [pmFinal 1261, pmFinal 1262, pmFinal 1263, pmFinal 1264] 3 [1,4,8,8] [1,4,8,2] at hx
 have hy:fact_000265.Holds smFinal pmFinal:=hframe _ (by native_decide)
 change ShardedRel (smFinal 583) [pmFinal 1333, pmFinal 1334, pmFinal 1335, pmFinal 1336] 2 [1,4,8,8] [1,4,2,8] at hy
 have hxV:smFinal 578=allGatherPrimDimN 3 4 0 [pmFinal 1261, pmFinal 1262, pmFinal 1263, pmFinal 1264]:=by simpa only [List.map,List.length_cons,List.length_nil] using hx.full_value
 have hyV:smFinal 583=allGatherPrimDimN 2 4 0 [pmFinal 1333, pmFinal 1334, pmFinal 1335, pmFinal 1336]:=by simpa only [List.map,List.length_cons,List.length_nil] using hy.full_value
 have hmf:=segment_000350_hMatSmFst smStore
 have hms:=segment_000350_hMatSmSnd smStore
 change smFinal 738=batchedMatmul (smFinal 744) (transpose2d (smFinal 583)) at hmf
 change smFinal 743=batchedMatmul (transpose2d (smFinal 578)) (smFinal 744) at hms
 have hDwComm:=TrainVerify.Denote.bw_linear_dw_row_allGather_rank3 4 1 8 8 32 [pmFinal 1247, pmFinal 1250, pmFinal 1253, pmFinal 1256] [pmFinal 1229, pmFinal 1230, pmFinal 1231, pmFinal 1232] (pmFinal 917) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by simp) (by simp) hlg.shard_shapes hlw.shard_shapes hlx.2.2
 have hDwValue:smFinal 735=allGatherPrimDimN 0 4 0 [pmFinal 1246, pmFinal 1249, pmFinal 1252, pmFinal 1255]:=by
  rw [hds,lgV,hlx.1,lwV,hDwComm]
  simp only [List.zipWith]
  rw [←hdp0, ←hdp1, ←hdp2, ←hdp3]
 have hDwValueList:smFinal 735=allGatherPrimDimN 0 [pmFinal 1246, pmFinal 1249, pmFinal 1252, pmFinal 1255].length 0 [pmFinal 1246, pmFinal 1249, pmFinal 1252, pmFinal 1255]:=by simpa only [List.length_cons,List.length_nil] using hDwValue
 have hDwFull:(smFinal 735).shape=[32,32]:=by rw [hds];exact bw_linear_3d_snd_shape 1 8 32 32 _ _ _ hlg.full_shape hlx.2.1 hlw.full_shape
 have houtD:fact_dw_row_consumer.Holds smFinal pmFinal:=by change ShardedRel (smFinal 735) [pmFinal 1246, pmFinal 1249, pmFinal 1252, pmFinal 1255] 0 [32,32] [8,32];exact {full_value:=hDwValueList,full_shape:=hDwFull,shards_nonempty:=by simp,gather_dim_lt:=by native_decide,shard_shapes:=by intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with h0|h1|h2|h3 <;> subst z;exact lds0;exact lds1;exact lds2;exact lds3,shape_contract:=by simp only [List.length_cons,List.length_nil];native_decide}
 have hpf0:=segment_000350_hMatPmFst0 pmStore
 have hps0:=segment_000350_hMatPmSnd0 pmStore
 change pmFinal 1274=batchedMatmul (pmFinal 744) (transpose2d (pmFinal 1333)) at hpf0
 change pmFinal 1346=batchedMatmul (transpose2d (pmFinal 1261)) (pmFinal 744) at hps0
 have xs0:=hx.shard_shapes (pmFinal 1261) (by simp)
 have ys0:=hy.shard_shapes (pmFinal 1333) (by simp)
 have ofs0:(pmFinal 1274).shape=[1,4,8,2]:=by rw [hpf0];exact batchedMatmul_shape_1_4_8_8_1_4_8_2 _ _ hGJoin.2.2 (transpose2d_shape_1_4_2_8 _ ys0)
 have oss0:(pmFinal 1346).shape=[1,4,2,8]:=by rw [hps0];exact batchedMatmul_shape_1_4_2_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_2 _ xs0) hGJoin.2.2
 have hpf1:=segment_000350_hMatPmFst1 pmStore
 have hps1:=segment_000350_hMatPmSnd1 pmStore
 change pmFinal 1276=batchedMatmul (pmFinal 744) (transpose2d (pmFinal 1334)) at hpf1
 change pmFinal 1348=batchedMatmul (transpose2d (pmFinal 1262)) (pmFinal 744) at hps1
 have xs1:=hx.shard_shapes (pmFinal 1262) (by simp)
 have ys1:=hy.shard_shapes (pmFinal 1334) (by simp)
 have ofs1:(pmFinal 1276).shape=[1,4,8,2]:=by rw [hpf1];exact batchedMatmul_shape_1_4_8_8_1_4_8_2 _ _ hGJoin.2.2 (transpose2d_shape_1_4_2_8 _ ys1)
 have oss1:(pmFinal 1348).shape=[1,4,2,8]:=by rw [hps1];exact batchedMatmul_shape_1_4_2_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_2 _ xs1) hGJoin.2.2
 have hpf2:=segment_000350_hMatPmFst2 pmStore
 have hps2:=segment_000350_hMatPmSnd2 pmStore
 change pmFinal 1278=batchedMatmul (pmFinal 744) (transpose2d (pmFinal 1335)) at hpf2
 change pmFinal 1350=batchedMatmul (transpose2d (pmFinal 1263)) (pmFinal 744) at hps2
 have xs2:=hx.shard_shapes (pmFinal 1263) (by simp)
 have ys2:=hy.shard_shapes (pmFinal 1335) (by simp)
 have ofs2:(pmFinal 1278).shape=[1,4,8,2]:=by rw [hpf2];exact batchedMatmul_shape_1_4_8_8_1_4_8_2 _ _ hGJoin.2.2 (transpose2d_shape_1_4_2_8 _ ys2)
 have oss2:(pmFinal 1350).shape=[1,4,2,8]:=by rw [hps2];exact batchedMatmul_shape_1_4_2_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_2 _ xs2) hGJoin.2.2
 have hpf3:=segment_000350_hMatPmFst3 pmStore
 have hps3:=segment_000350_hMatPmSnd3 pmStore
 change pmFinal 1280=batchedMatmul (pmFinal 744) (transpose2d (pmFinal 1336)) at hpf3
 change pmFinal 1352=batchedMatmul (transpose2d (pmFinal 1264)) (pmFinal 744) at hps3
 have xs3:=hx.shard_shapes (pmFinal 1264) (by simp)
 have ys3:=hy.shard_shapes (pmFinal 1336) (by simp)
 have ofs3:(pmFinal 1280).shape=[1,4,8,2]:=by rw [hpf3];exact batchedMatmul_shape_1_4_8_8_1_4_8_2 _ _ hGJoin.2.2 (transpose2d_shape_1_4_2_8 _ ys3)
 have oss3:(pmFinal 1352).shape=[1,4,2,8]:=by rw [hps3];exact batchedMatmul_shape_1_4_2_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_2 _ xs3) hGJoin.2.2
 have fcomm:=TrainVerify.Denote.bw_matmul_fst_split_1_4_8_8 (pmFinal 744) (pmFinal 1333) (pmFinal 1334) (pmFinal 1335) (pmFinal 1336) hGJoin.2.2 ys0 ys1 ys2 ys3
 have fval:smFinal 738=allGatherPrimDimN 3 4 0 [pmFinal 1274, pmFinal 1276, pmFinal 1278, pmFinal 1280]:=by rw [hmf,hGJoin.1,hyV,fcomm];rw [←hpf0, ←hpf1, ←hpf2, ←hpf3]
 have scomm:=TrainVerify.Denote.bw_matmul_snd_split_dX_1_4_8_8 (pmFinal 744) (pmFinal 1261) (pmFinal 1262) (pmFinal 1263) (pmFinal 1264) hGJoin.2.2 xs0 xs1 xs2 xs3
 have sval:smFinal 743=allGatherPrimDimN 2 4 0 [pmFinal 1346, pmFinal 1348, pmFinal 1350, pmFinal 1352]:=by rw [hms,hGJoin.1,hxV,scomm];rw [←hps0, ←hps1, ←hps2, ←hps3]
 have houtFv:smFinal 738=allGatherPrimDimN 3 [pmFinal 1274, pmFinal 1276, pmFinal 1278, pmFinal 1280].length 0 [pmFinal 1274, pmFinal 1276, pmFinal 1278, pmFinal 1280]:=by simpa only [List.length_cons,List.length_nil] using fval
 have houtFfull:(smFinal 738).shape=[1,4,8,8]:=by rw [hmf];exact batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ hGJoin.2.1 (transpose2d_shape_1_4_8_8 _ hy.full_shape)
 have houtF:fact_000367.Holds smFinal pmFinal:=by change ShardedRel (smFinal 738) [pmFinal 1274, pmFinal 1276, pmFinal 1278, pmFinal 1280] 3 [1,4,8,8] [1,4,8,2];exact {full_value:=houtFv,full_shape:=houtFfull,shards_nonempty:=by simp,gather_dim_lt:=by native_decide,shard_shapes:=by intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with h0|h1|h2|h3 <;> subst z;exact ofs0;exact ofs1;exact ofs2;exact ofs3,shape_contract:=by simp only [List.length_cons,List.length_nil];native_decide}
 have houtSv:smFinal 743=allGatherPrimDimN 2 [pmFinal 1346, pmFinal 1348, pmFinal 1350, pmFinal 1352].length 0 [pmFinal 1346, pmFinal 1348, pmFinal 1350, pmFinal 1352]:=by simpa only [List.length_cons,List.length_nil] using sval
 have houtSfull:(smFinal 743).shape=[1,4,8,8]:=by rw [hms];exact batchedMatmul_shape_1_4_8_8_1_4_8_8 _ _ (transpose2d_shape_1_4_8_8 _ hx.full_shape) hGJoin.2.1
 have houtS:fact_000368.Holds smFinal pmFinal:=by change ShardedRel (smFinal 743) [pmFinal 1346, pmFinal 1348, pmFinal 1350, pmFinal 1352] 2 [1,4,8,8] [1,4,2,8];exact {full_value:=houtSv,full_shape:=houtSfull,shards_nonempty:=by simp,gather_dim_lt:=by native_decide,shard_shapes:=by intro z hz;simp only [List.mem_cons,List.not_mem_nil,or_false] at hz;rcases hz with h0|h1|h2|h3 <;> subst z;exact oss0;exact oss1;exact oss2;exact oss3,shape_contract:=by simp only [List.length_cons,List.length_nil];native_decide}
 intro fact hfact
 have hc:fact∈[fact_000119,fact_000056,fact_000059,fact_000367,fact_000368,fact_dw_row_consumer]++state_000350.facts:=by exact (show state_000351.facts⊆[fact_000119,fact_000056,fact_000059,fact_000367,fact_000368,fact_dw_row_consumer]++state_000350.facts by native_decide) hfact
 simp only [List.mem_append] at hc
 rcases hc with fresh|old
 · simp only [List.mem_cons,List.not_mem_nil,or_false] at fresh;rcases fresh with rfl|rfl|rfl|rfl|rfl|rfl
   · exact hLin
   · exact hGJoin
   · exact houtR
   · exact houtF
   · exact houtS
   · exact houtD
 · exact hframe fact old

private def segment_000350:ClosedDepSegmentCertificate TrainVerify.Denote.Generated.sm TrainVerify.Denote.Generated.pm state_000350 state_000351 where
 smNodes:=segment_000350_sm_nodes
 pmNodes:=segment_000350_pm_nodes
 sound:=by intro a b h;have z:=segment_000350_sound a b h;unfold segment_000350_sm_final segment_000350_pm_final at z;exact z

#print axioms segment_000350
end
end TrainVerify.Denote.DwRowReconstructionConsumer
