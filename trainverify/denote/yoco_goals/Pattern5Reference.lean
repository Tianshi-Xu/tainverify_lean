/- Reference / spike proofs for Pattern_5 (FW_embedding vocab-parallel).

   Status: partial. `denote_sm_4680` and `denote_pm_4680` (in terms of inner
   store lookups at 7391/7392) are proven. Missing:
     1. Reduce `denoteGraph {pm with nodes := pm.nodes.take 26} initPM 7391`
        to `fw_embedding_offset 0 (initPM 4677) (initPM 7389)` (peel to pm.nodes[0])
     2. Reduce `denoteGraph {pm with nodes := pm.nodes.take 26} initPM 7392`
        to `fw_embedding_offset 77440 (initPM 4677) (initPM 7390)` (peel to pm.nodes[13])
     3. Assemble via `fw_embedding_eq_allReduce_offset_shards` to link SM and PM sides
     4. Prove shape parts of `goal_5_stmt` (tsShape / tpShapes checks)
     5. Prove reconstructWithDim equation (single_tp: reduces to LHS = PM_val)

   Time so far on spike: ~2h. Estimated remaining for full pattern_5 proof: 3-4h.
-/
import denote.yoco_goals.BridgeKit

set_option maxRecDepth 100000

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

-- SM: full embedding computes the fw_embedding call.
theorem denote_sm_4680 (initSM : Store) :
    denoteGraph sm initSM 4680 = fw_embedding (initSM 4677) (initSM 4679) := by
  have h := sm_val initSM 0 4680 (by native_decide) (by native_decide)
  rw [h]
  simp only [sm, List.take, List.getElem_cons_zero, denoteGraph_nodes_nil]
  rw [applyNode_fw_embedding_out]

-- PM: allReducePrim of shard embeddings computed at pm.nodes[26].
theorem denote_pm_4680 (initPM : Store) :
    denoteGraph pm initPM 4680 =
    allReducePrim 2 0
      [denoteGraph {pm with nodes := pm.nodes.take 26} initPM 7391,
       denoteGraph {pm with nodes := pm.nodes.take 26} initPM 7392] := by
  have h := pm_val initPM 26 4680 (by native_decide) (by native_decide)
  rw [h]
  have hnode : pm.nodes[26]'(by native_decide) =
      { rank := 0, op := "OpName.AllReducePrim", ins := [7391, 7392], outs := [4680] } := by
    native_decide
  simp only [hnode]
  rw [applyNode_allReducePrim_out]
  have : pm.numRanks = 2 := by native_decide
  change allReducePrim pm.numRanks 0 ([7391, 7392].map _) = _
  rw [this]
  rfl

-- TODO: continue the proof — link inner store lookups to fw_embedding_offset,
-- then invoke fw_embedding_eq_allReduce_offset_shards to close SM = PM.

end TrainVerify.Denote.GeneratedPatterns
