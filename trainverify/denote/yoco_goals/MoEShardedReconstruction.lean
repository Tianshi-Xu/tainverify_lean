/- Worker #14 — MoE sharding-commute reconstruction gears over `denoteGraph_ringAttn`.

   Proves the token-sharded (2-tp) and gathered (1-tp) MoE-block intermediate
   goals that the residual/MoE frontend (Worker #12) left gated:

   - `recon_intermediateGoal_4709_ringAttn` — FW_topk_routing routing_probs (2-tp)
   - `recon_intermediateGoal_4710_ringAttn` — FW_topk_routing routing_map (2-tp)
   - `recon_intermediateGoal_4728_ringAttn` — FW_swiglu (2-tp)
   - `recon_intermediateGoal_4729_ringAttn` — FW_reshape ∘ AllGather (1-tp)

   Each transfers the token-dim (dim-0) sharding across a row-wise MoE op via the
   corresponding Pattern_1 `_allGather0_commute_2` tensor-algebra lemma, using the
   already-proven replicated router-input goal `4708` and the swiglu-input goals
   `4723`/`4727`.

   All theorems named `recon_intermediateGoal_<tid>_ringAttn`, zero sorry, zero
   user axiom (kernel + native_decide baseline only). Imports the residual/MoE
   cascade (`ResidualMoEReconstruction`, for the sm/pm graphs, goal defs, wrappers
   and the proven `4708`/`4723`/`4727` goals), the shared ring gears
   (`RingAttnGears`), and Pattern_1/Pattern_3 (commute + chunk-reconstruction
   tensor lemmas — transitively via `IntermediateReconstruction`). -/
import denote.yoco_goals.ResidualMoEReconstruction

set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.nativeDecide false
set_option linter.style.maxHeartbeats false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals

/-! ### Store-specific single-input ring node reduction

    `ringAttn_reduce1` (in `RingAttnGears`) requires the `applyNode` reduction to
    hold for *every* store. Ops like `FW_topk_routing` whose `applyNode` lemma
    needs a shape hypothesis on the folded input only satisfy the reduction at the
    *specific* prefix store. This variant takes exactly that specialized
    hypothesis. -/
theorem ringAttn_reduce1_at (g : GraphDecl) (init : Store) (k : Nat)
    (node : NodeDecl) (inTid outTid : Tid) (opfun : Tensor → Tensor)
    (hk : k < g.nodes.length)
    (hnode : g.nodes[k]'hk = node)
    (hnr1 : node.op ≠ "OpName.FW_attn_zigzag")
    (hnr2 : node.op ≠ "OpName.FW_attn_sliding_window")
    (happly : applyNode g ((g.nodes.take k).foldl (applyNodeRingAttn g) init) node outTid
      = opfun ((g.nodes.take k).foldl (applyNodeRingAttn g) init inTid))
    (hdrop_nil : ∀ n ∈ g.nodes.drop (k + 1), n.outs ≠ [])
    (hdrop : ∀ n ∈ g.nodes.drop (k + 1), outTid ∉ n.outs)
    (hpre_nil : ∀ n ∈ g.nodes.drop k, n.outs ≠ [])
    (hpre : ∀ n ∈ g.nodes.drop k, inTid ∉ n.outs) :
    denoteGraph_ringAttn g init outTid = opfun (denoteGraph_ringAttn g init inTid) := by
  have hstep := congrFun (foldl_take_succ (applyNodeRingAttn g) g.nodes init k hk) outTid
  rw [denoteGraph_ringAttn,
      foldl_prefix_ring_g12 g g.nodes init outTid (k + 1) hdrop_nil hdrop, hstep, hnode,
      applyNodeRingAttn_eq_applyNode_of_not_ring g _ _ hnr1 hnr2, happly]
  congr 1
  exact (foldl_prefix_ring_g12 g g.nodes init inTid k hpre_nil hpre).symm

/-! ### params-`[8,1]` topk applyNode lemmas (numExperts read from logits shape) -/

/-- `evalOp` on the generated `FW_topk_routing` node whose params are `[8, 1]`:
    `numExperts` is read off the logits' trailing dim (here `64`), the params
    entry `1` is only the (overridden) fallback. -/
theorem evalOp_topk_81 (numParts rank : Nat) (logits : Tensor)
    (hlast : logits.shape.reverse.head? = some 64) :
    evalOp numParts rank "OpName.FW_topk_routing" [8, 1] [logits] =
      [ (fw_topk_routing logits 8 64).1,
        (fw_topk_routing logits 8 64).2.1,
        (fw_topk_routing logits 8 64).2.2 ] := by
  have h : evalOp numParts rank "OpName.FW_topk_routing" [8, 1] [logits] =
      [ (fw_topk_routing logits 8 ((logits.shape.reverse.head?).getD 1)).1,
        (fw_topk_routing logits 8 ((logits.shape.reverse.head?).getD 1)).2.1,
        (fw_topk_routing logits 8 ((logits.shape.reverse.head?).getD 1)).2.2 ] := rfl
  rw [h, hlast]; rfl

/-- `applyNode` for the params-`[8,1]` topk node, 1st output (`routing_probs`). -/
theorem applyNode_topk81_fst (g : GraphDecl) (s : Store) (rank : Nat)
    (logitsTid t1 t2 t3 : Tid)
    (hlast : (s logitsTid).shape.reverse.head? = some 64) :
    applyNode g s { rank := rank, op := "OpName.FW_topk_routing",
                    ins := [logitsTid], outs := [t1, t2, t3], params := [8, 1] } t1 =
      (fw_topk_routing (s logitsTid) 8 64).1 := by
  unfold applyNode
  rw [show ([logitsTid] : List Tid).map s = [s logitsTid] from rfl, evalOp_topk_81 _ _ _ hlast]
  change storeSet s
    [(t1, (fw_topk_routing (s logitsTid) 8 64).1),
     (t2, (fw_topk_routing (s logitsTid) 8 64).2.1),
     (t3, (fw_topk_routing (s logitsTid) 8 64).2.2)] t1 = _
  unfold storeSet
  simp [List.find?]

/-- `applyNode` for the params-`[8,1]` topk node, 2nd output (`routing_map`). -/
theorem applyNode_topk81_snd (g : GraphDecl) (s : Store) (rank : Nat)
    (logitsTid t1 t2 t3 : Tid) (hne12 : t1 ≠ t2)
    (hlast : (s logitsTid).shape.reverse.head? = some 64) :
    applyNode g s { rank := rank, op := "OpName.FW_topk_routing",
                    ins := [logitsTid], outs := [t1, t2, t3], params := [8, 1] } t2 =
      (fw_topk_routing (s logitsTid) 8 64).2.1 := by
  unfold applyNode
  rw [show ([logitsTid] : List Tid).map s = [s logitsTid] from rfl, evalOp_topk_81 _ _ _ hlast]
  change storeSet s
    [(t1, (fw_topk_routing (s logitsTid) 8 64).1),
     (t2, (fw_topk_routing (s logitsTid) 8 64).2.1),
     (t3, (fw_topk_routing (s logitsTid) 8 64).2.2)] t2 = _
  unfold storeSet
  simp [List.find?, show ¬ (t1 = t2) from hne12]

/-! ### 4728 — FW_swiglu (token-sharded, 2-tp)

    SM `4728 = swiglu(4723, 4727)` reconstructs as the dim-0 gather of the two
    PM per-rank swiglu shards `7543`/`7544`, each computed on the chunked inputs
    `chunk_r(4723)`/`chunk_r(4727)`. Row-wise op ⇒ commutes with the token gather
    via `fw_swiglu_allGather0_commute_2`. -/
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4728_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4728
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  -- replicated swiglu inputs (1-tp, proven)
  have h4723 := recon_intermediateGoal_4723_ringAttn initSM initPM hSM hPM hInit
  have h4727 := recon_intermediateGoal_4727_ringAttn initSM initPM hSM hPM hInit
  have hv4723 : denoteGraph_ringAttn sm initSM 4723 = denoteGraph_ringAttn pm initPM 4723 :=
    oneTp_valeq intermediateGoal_4723 _ _ 4723 rfl rfl rfl rfl h4723
  have hv4727 : denoteGraph_ringAttn sm initSM 4727 = denoteGraph_ringAttn pm initPM 4727 :=
    oneTp_valeq intermediateGoal_4727 _ _ 4727 rfl rfl rfl rfl h4727
  have hs4723 : (denoteGraph_ringAttn sm initSM 4723).shape = [4096, 512] := by
    have := h4723.1; simpa [intermediateGoal_4723] using this
  have hs4727 : (denoteGraph_ringAttn sm initSM 4727).shape = [4096, 512] := by
    have := h4727.1; simpa [intermediateGoal_4727] using this
  have hp4723 : (denoteGraph_ringAttn pm initPM 4723).shape = [4096, 512] := by
    rw [← hv4723]; exact hs4723
  have hp4727 : (denoteGraph_ringAttn pm initPM 4727).shape = [4096, 512] := by
    rw [← hv4727]; exact hs4727
  -- SM swiglu node reduction (index 33)
  have rSM : denoteGraph_ringAttn sm initSM 4728
      = fw_swiglu (denoteGraph_ringAttn sm initSM 4723) (denoteGraph_ringAttn sm initSM 4727) :=
    ringAttn_reduce2 sm initSM 33
      { rank := 0, op := "OpName.FW_swiglu", ins := [4723, 4727], outs := [4728] }
      4723 4727 4728 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out sm s 0 4723 4727 4728 [])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- PM chunk node reductions (indices 100/101 for 4723, 102/103 for 4727)
  have hc7521 : denoteGraph_ringAttn pm initPM 7521 = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4723) :=
    ringAttn_reduce1 pm initPM 100
      { rank := 0, op := "OpName.ChunkPrim", ins := [4723], outs := [7521], params := [0] }
      4723 7521 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4723 7521 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7522 : denoteGraph_ringAttn pm initPM 7522 = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4723) :=
    ringAttn_reduce1 pm initPM 101
      { rank := 1, op := "OpName.ChunkPrim", ins := [4723], outs := [7522], params := [0] }
      4723 7522 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4723 7522 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7539 : denoteGraph_ringAttn pm initPM 7539 = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4727) :=
    ringAttn_reduce1 pm initPM 102
      { rank := 0, op := "OpName.ChunkPrim", ins := [4727], outs := [7539], params := [0] }
      4727 7539 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4727 7539 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7540 : denoteGraph_ringAttn pm initPM 7540 = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4727) :=
    ringAttn_reduce1 pm initPM 103
      { rank := 1, op := "OpName.ChunkPrim", ins := [4727], outs := [7540], params := [0] }
      4727 7540 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4727 7540 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM swiglu node reductions (indices 106/107)
  have rP0 : denoteGraph_ringAttn pm initPM 7543
      = fw_swiglu (denoteGraph_ringAttn pm initPM 7521) (denoteGraph_ringAttn pm initPM 7539) :=
    ringAttn_reduce2 pm initPM 106
      { rank := 0, op := "OpName.FW_swiglu", ins := [7521, 7539], outs := [7543] }
      7521 7539 7543 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 0 7521 7539 7543 [])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7544
      = fw_swiglu (denoteGraph_ringAttn pm initPM 7522) (denoteGraph_ringAttn pm initPM 7540) :=
    ringAttn_reduce2 pm initPM 107
      { rank := 1, op := "OpName.FW_swiglu", ins := [7522, 7540], outs := [7544] }
      7522 7540 7544 fw_swiglu (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_fw_swiglu_out pm s 1 7522 7540 7544 [])
      (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide)
  -- numRanks normalization
  have hnr : pm.numRanks = 2 := rfl
  -- chunk shapes
  have hs7521 : (denoteGraph_ringAttn pm initPM 7521).shape = [2048, 512] := by
    rw [hc7521, chunkPrimDimN_shape 0 pm.numRanks 0 _ [4096, 512] hp4723 (by native_decide)]; rfl
  have hs7522 : (denoteGraph_ringAttn pm initPM 7522).shape = [2048, 512] := by
    rw [hc7522, chunkPrimDimN_shape 0 pm.numRanks 1 _ [4096, 512] hp4723 (by native_decide)]; rfl
  have hs7539 : (denoteGraph_ringAttn pm initPM 7539).shape = [2048, 512] := by
    rw [hc7539, chunkPrimDimN_shape 0 pm.numRanks 0 _ [4096, 512] hp4727 (by native_decide)]; rfl
  have hs7540 : (denoteGraph_ringAttn pm initPM 7540).shape = [2048, 512] := by
    rw [hc7540, chunkPrimDimN_shape 0 pm.numRanks 1 _ [4096, 512] hp4727 (by native_decide)]; rfl
  -- reconstruct the replicated inputs as gather-of-chunks
  have hrec4723 : denoteGraph_ringAttn pm initPM 4723
      = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7521, denoteGraph_ringAttn pm initPM 7522] := by
    rw [hc7521, hc7522, hnr]
    exact (allGather0_reconstruct_chunks_2d 2048 512 (by omega) (by omega) _ hp4723).symm
  have hrec4727 : denoteGraph_ringAttn pm initPM 4727
      = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7539, denoteGraph_ringAttn pm initPM 7540] := by
    rw [hc7539, hc7540, hnr]
    exact (allGather0_reconstruct_chunks_2d 2048 512 (by omega) (by omega) _ hp4727).symm
  -- value reconstruction
  have hval : denoteGraph_ringAttn sm initSM 4728
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7543, denoteGraph_ringAttn pm initPM 7544] := by
    rw [rSM, hv4723, hv4727, hrec4723, hrec4727, hnr,
        fw_swiglu_allGather0_commute_2 _ _ _ _ 2048 512 (by omega) (by omega)
          hs7521 hs7522 hs7539 hs7540, rP0, rP1]
  -- shapes
  have hshape : (denoteGraph_ringAttn sm initSM 4728).shape = [4096, 512] := by
    rw [rSM]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs4727
  have hsp0 : (denoteGraph_ringAttn pm initPM 7543).shape = [2048, 512] := by
    rw [rP0]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs7539
  have hsp1 : (denoteGraph_ringAttn pm initPM 7544).shape = [2048, 512] := by
    rw [rP1]; unfold fw_swiglu Tensor.mkShape; simp only []; exact hs7540
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4728 4728 7543 7544 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
