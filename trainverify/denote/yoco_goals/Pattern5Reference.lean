/- Pattern_5 spike: FW_embedding vocab-parallel proof

   Continued from initial spike. Now uses pm_val_prefix to reduce the inner
   store lookups at pm.nodes[0] (7391) and pm.nodes[13] (7392).
-/
import denote.yoco_goals.BridgeKit

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

-- SM: full embedding
theorem denote_sm_4680 (initSM : Store) :
    denoteGraph sm initSM 4680 = fw_embedding (initSM 4677) (initSM 4679) := by
  have h := sm_val initSM 0 4680 (by native_decide) (by native_decide)
  rw [h]
  simp only [sm, List.take, List.getElem_cons_zero, denoteGraph_nodes_nil]
  rw [applyNode_fw_embedding_out]

-- PM at 7391: written at pm.nodes[0] (rank 0 embedding, offset 0)
theorem denote_pm_prefix_7391 (initPM : Store) :
    denoteGraph {pm with nodes := pm.nodes.take 26} initPM 7391 =
      fw_embedding_offset 0 (initPM 4677) (initPM 7389) := by
  have h := pm_val_prefix initPM 26 0 (by native_decide) (by native_decide) 7391 (by native_decide)
  rw [h]
  have hnode : (pm.nodes.take 26)[0]'(by native_decide) =
      { rank := 0, op := "OpName.FW_embedding", ins := [4677, 7389], outs := [7391], params := [0] } := by
    native_decide
  simp only [hnode, List.take, denoteGraph_nodes_nil]
  rw [applyNode_fw_embedding_offset_out]

-- PM at 7392: written at pm.nodes[13] (rank 1 embedding, offset 77440)
theorem denote_pm_prefix_7392 (initPM : Store) :
    denoteGraph {pm with nodes := pm.nodes.take 26} initPM 7392 =
      fw_embedding_offset 77440 (initPM 4677) (initPM 7390) := by
  have h := pm_val_prefix initPM 26 13 (by native_decide) (by native_decide) 7392 (by native_decide)
  rw [h]
  have hnode : (pm.nodes.take 26)[13]'(by native_decide) =
      { rank := 1, op := "OpName.FW_embedding", ins := [4677, 7390], outs := [7392], params := [77440] } := by
    native_decide
  simp only [hnode]
  rw [applyNode_fw_embedding_offset_out]
  -- Now need: fw_embedding_offset 77440 (denoteGraph {pm with nodes := take 13 (take 26 pm.nodes)} initPM 4677) (...7390)
  --        = fw_embedding_offset 77440 (initPM 4677) (initPM 7390)
  -- Reduce inner denoteGraph 4677 and 7390 via not-written check
  have h4677 : denoteGraph {pm with nodes := (pm.nodes.take 26).take 13} initPM 4677 = initPM 4677 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs
    native_decide
  have h7390 : denoteGraph {pm with nodes := (pm.nodes.take 26).take 13} initPM 7390 = initPM 7390 := by
    apply denoteGraph_tid_eq_of_forall_not_mem_outs
    native_decide
  rw [h4677, h7390]

-- PM at 4680: allReducePrim of the two shards
theorem denote_pm_4680 (initPM : Store) :
    denoteGraph pm initPM 4680 =
    allReducePrim 2 0
      [fw_embedding_offset 0 (initPM 4677) (initPM 7389),
       fw_embedding_offset 77440 (initPM 4677) (initPM 7390)] := by
  have h := pm_val initPM 26 4680 (by native_decide) (by native_decide)
  rw [h]
  have hnode : pm.nodes[26]'(by native_decide) =
      { rank := 0, op := "OpName.AllReducePrim", ins := [7391, 7392], outs := [4680] } := by
    native_decide
  simp only [hnode]
  rw [applyNode_allReducePrim_out]
  have hR : pm.numRanks = 2 := by native_decide
  change allReducePrim pm.numRanks 0 ([7391, 7392].map _) = _
  rw [hR]
  -- Reduce inner store lookups via the two prefix theorems
  have h7391 := denote_pm_prefix_7391 initPM
  have h7392 := denote_pm_prefix_7392 initPM
  -- The inner store is `{pm with nodes := take 26}` = `{numRanks:=2, nodes := take 26 pm.nodes}` (by hR)
  -- but the LHS from hnode is already reduced to `{numRanks:=2, nodes := ...}` form
  show allReducePrim 2 0
      [denoteGraph {numRanks := 2, nodes := pm.nodes.take 26} initPM 7391,
       denoteGraph {numRanks := 2, nodes := pm.nodes.take 26} initPM 7392] = _
  -- These match the {pm with ...} form up to numRanks unfolding.
  have hpm_form : ({numRanks := 2, nodes := pm.nodes.take 26} : GraphDecl) =
                  ({pm with nodes := pm.nodes.take 26} : GraphDecl) := by
    show ({numRanks := 2, nodes := pm.nodes.take 26} : GraphDecl) =
         ({numRanks := pm.numRanks, nodes := pm.nodes.take 26} : GraphDecl)
    rw [hR]
  rw [hpm_form, h7391, h7392]

-- Assemble Pattern_5: goal_5_stmt.
-- goal_5 : LineageGoal := { ts:=4680, tsShape:=[4096,1024], tps:=[{rank:=0,tid:=4680}], tpShapes:=[[4096,1024]], gatherDim:=0 }
-- goal_5_stmt = ∀ initSM initPM, shapes_hold → InitGoalsHold → 3-way conj
theorem prove_goal_5 : goal_5_stmt := by
  intro initSM initPM hSM hPM _hInit
  simp only [goal_5]
  refine ⟨?shape_sm, ?shape_pm, ?value⟩
  case shape_sm =>
    -- (denoteGraph sm initSM 4680).shape = [4096, 1024]
    rw [denote_sm_4680 initSM]
    sorry
  case shape_pm =>
    sorry
  case value =>
    sorry

end TrainVerify.Denote.GeneratedPatterns
