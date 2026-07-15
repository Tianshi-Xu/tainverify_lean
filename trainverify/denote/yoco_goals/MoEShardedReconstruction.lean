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
/-- Shared core: SM `4728` (full swiglu) reconstructs as the dim-0 gather of the
    two PM per-rank swiglu shards `7543`/`7544`, plus the shard/full shape facts.
    Reused by both the `4728` (2-tp swiglu) and `4729` (reshape∘gather) goals. -/
theorem moe_swiglu_gather_4728 (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4728
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 7543, denoteGraph_ringAttn pm initPM 7544]
      ∧ (denoteGraph_ringAttn pm initPM 7543).shape = [2048, 512]
      ∧ (denoteGraph_ringAttn pm initPM 7544).shape = [2048, 512]
      ∧ (denoteGraph_ringAttn sm initSM 4728).shape = [4096, 512] := by
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
  refine ⟨hval, hsp0, hsp1, hshape⟩

/-! ### 4728 — FW_swiglu (token-sharded, 2-tp) -/
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4728_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4728
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hval, hsp0, hsp1, hshape⟩ := moe_swiglu_gather_4728 initSM initPM hSM hPM hInit
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4728 4728 7543 7544 [4096, 512] [2048, 512]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

/-! ### 4729 — FW_reshape ∘ AllGather (gathered, 1-tp)

    SM `4729 = view[4096,512](4728)` is an identity reshape of the full swiglu
    output, hence `= 4728 = allGather0[7543,7544]`. PM `4729 =
    allGather0[view[2048,512](7543), view[2048,512](7544)] = allGather0[7543,7544]`
    (each per-rank reshape is identity on its `[2048,512]` shard). Both sides
    therefore equal the same dim-0 gather, giving the 1-tp reconstruction. -/
set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4729_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4729
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hval28, hsp0, hsp1, hshape28⟩ := moe_swiglu_gather_4728 initSM initPM hSM hPM hInit
  -- SM reshape reduction (index 34): 4729 = view[4096,512](4728)
  have rSMv : denoteGraph_ringAttn sm initSM 4729
      = fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4728) :=
    ringAttn_reshape_reduce_g12 sm initSM 34 0 4728 4729 [4096, 512]
      (by native_decide) (by native_decide) (by decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM per-rank reshape reductions (indices 109/110)
  have rP0v : denoteGraph_ringAttn pm initPM 7545
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 7543) :=
    ringAttn_reshape_reduce_g12 pm initPM 109 0 7543 7545 [2048, 512]
      (by native_decide) (by native_decide) (by decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1v : denoteGraph_ringAttn pm initPM 7546
      = fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 7544) :=
    ringAttn_reshape_reduce_g12 pm initPM 110 1 7544 7546 [2048, 512]
      (by native_decide) (by native_decide) (by decide)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- PM allGather reduction (index 111): 4729 = allGather0[7545,7546]
  have rPMg : denoteGraph_ringAttn pm initPM 4729
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7545, denoteGraph_ringAttn pm initPM 7546] :=
    ringAttn_reduce2 pm initPM 111
      { rank := 0, op := "OpName.AllGatherPrim", ins := [7545, 7546], outs := [4729], params := [0] }
      7545 7546 4729 (fun a b => allGatherPrimDimN 0 pm.numRanks 0 [a, b])
      (by native_decide) (by native_decide) (by decide) (by decide)
      (fun s => applyNode_allGatherPrimDimN_out_thm pm s 0 [7545, 7546] 4729 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  -- identity-reshape collapses
  have hidSM : fw_view [4096, 512] (denoteGraph_ringAttn sm initSM 4728)
      = denoteGraph_ringAttn sm initSM 4728 := fw_view_id_shape [4096, 512] _ hshape28
  have hidP0 : fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 7543)
      = denoteGraph_ringAttn pm initPM 7543 := fw_view_id_shape [2048, 512] _ hsp0
  have hidP1 : fw_view [2048, 512] (denoteGraph_ringAttn pm initPM 7544)
      = denoteGraph_ringAttn pm initPM 7544 := fw_view_id_shape [2048, 512] _ hsp1
  -- both sides reduce to allGather0[7543,7544]
  have hval : denoteGraph_ringAttn sm initSM 4729 = denoteGraph_ringAttn pm initPM 4729 := by
    rw [rSMv, hidSM, hval28, rPMg, rP0v, rP1v, hidP0, hidP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4729).shape = [4096, 512] := by
    rw [rSMv, hidSM]; exact hshape28
  exact wrap_1tp_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4729 4729 [4096, 512]
    rfl rfl rfl rfl rfl rfl hval hshape

/-! ### 4709 / 4710 — FW_topk_routing routing_probs / routing_map (token-sharded, 2-tp)

    The router logits `4708` are replicated (1-tp). Each rank runs `topk` on its
    token chunk `chunk_r(4708)`; the full `topk(4708)` reconstructs as the dim-0
    gather of the per-rank `topk` outputs. `routing_probs` (`.fst`) and
    `routing_map` (`.snd.fst`) are both row-wise in the token dim, so they commute
    with the gather via Pattern_1's `fw_topk_routing_{fst,snd_fst}_allGather0_commute_2_of`.
    `numExperts = 64` is read off the logits' trailing dim (the node's params entry
    `1` is the overridden fallback), handled by the store-specific
    `ringAttn_reduce1_at` + `applyNode_topk81_*` gears. -/
set_option maxHeartbeats 4000000 in
/-- Shared core for the two `topk` goals: the replicated logits `4708` reconstruct
    as the dim-0 gather of the per-rank chunks `7479`/`7480`, plus the chunk/logits
    shape facts and the prefix-store trailing-dim (`= some 64`) hypotheses the
    `topk` `applyNode` reductions need. -/
theorem moe_topk_common (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    denoteGraph_ringAttn sm initSM 4708
        = allGatherPrimDimN 0 pm.numRanks 0
            [denoteGraph_ringAttn pm initPM 7479, denoteGraph_ringAttn pm initPM 7480]
      ∧ (denoteGraph_ringAttn sm initSM 4708).shape = [4096, 64]
      ∧ (denoteGraph_ringAttn pm initPM 7479).shape = [2048, 64]
      ∧ (denoteGraph_ringAttn pm initPM 7480).shape = [2048, 64]
      ∧ ((sm.nodes.take 27).foldl (applyNodeRingAttn sm) initSM 4708).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 96).foldl (applyNodeRingAttn pm) initPM 7479).shape.reverse.head? = some 64
      ∧ ((pm.nodes.take 97).foldl (applyNodeRingAttn pm) initPM 7480).shape.reverse.head? = some 64 := by
  have h4708 := recon_intermediateGoal_4708_ringAttn initSM initPM hSM hPM hInit
  have hv4708 : denoteGraph_ringAttn sm initSM 4708 = denoteGraph_ringAttn pm initPM 4708 :=
    oneTp_valeq intermediateGoal_4708 _ _ 4708 rfl rfl rfl rfl h4708
  have hs4708sm : (denoteGraph_ringAttn sm initSM 4708).shape = [4096, 64] := by
    have := h4708.1; simpa [intermediateGoal_4708] using this
  have hp4708 : (denoteGraph_ringAttn pm initPM 4708).shape = [4096, 64] := by
    rw [← hv4708]; exact hs4708sm
  have hnr : pm.numRanks = 2 := rfl
  have hc7479 : denoteGraph_ringAttn pm initPM 7479 = chunkPrimDimN 0 pm.numRanks 0 (denoteGraph_ringAttn pm initPM 4708) :=
    ringAttn_reduce1 pm initPM 88
      { rank := 0, op := "OpName.ChunkPrim", ins := [4708], outs := [7479], params := [0] }
      4708 7479 (fun t => chunkPrimDimN 0 pm.numRanks 0 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 0 4708 7479 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hc7480 : denoteGraph_ringAttn pm initPM 7480 = chunkPrimDimN 0 pm.numRanks 1 (denoteGraph_ringAttn pm initPM 4708) :=
    ringAttn_reduce1 pm initPM 89
      { rank := 1, op := "OpName.ChunkPrim", ins := [4708], outs := [7480], params := [0] }
      4708 7480 (fun t => chunkPrimDimN 0 pm.numRanks 1 t) (by native_decide) (by native_decide)
      (by decide) (by decide) (fun s => applyNode_chunkPrimDimN_out pm s 1 4708 7480 0)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hs7479 : (denoteGraph_ringAttn pm initPM 7479).shape = [2048, 64] := by
    rw [hc7479, chunkPrimDimN_shape 0 pm.numRanks 0 _ [4096, 64] hp4708 (by native_decide)]; rfl
  have hs7480 : (denoteGraph_ringAttn pm initPM 7480).shape = [2048, 64] := by
    rw [hc7480, chunkPrimDimN_shape 0 pm.numRanks 1 _ [4096, 64] hp4708 (by native_decide)]; rfl
  have hrec4708 : denoteGraph_ringAttn pm initPM 4708
      = allGatherPrimDimN 0 2 0 [denoteGraph_ringAttn pm initPM 7479, denoteGraph_ringAttn pm initPM 7480] := by
    rw [hc7479, hc7480, hnr]
    exact (allGather0_reconstruct_chunks_2d 2048 64 (by omega) (by omega) _ hp4708).symm
  have hSMeq : denoteGraph_ringAttn sm initSM 4708
      = allGatherPrimDimN 0 pm.numRanks 0 [denoteGraph_ringAttn pm initPM 7479, denoteGraph_ringAttn pm initPM 7480] := by
    rw [hv4708, hrec4708, hnr]
  have hpre4708sm : denoteGraph_ringAttn sm initSM 4708
      = (sm.nodes.take 27).foldl (applyNodeRingAttn sm) initSM 4708 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 sm sm.nodes initSM 4708 27 (by native_decide) (by native_decide)
  have hlastSM : ((sm.nodes.take 27).foldl (applyNodeRingAttn sm) initSM 4708).shape.reverse.head? = some 64 := by
    rw [← hpre4708sm, hs4708sm]; rfl
  have hpre7479 : denoteGraph_ringAttn pm initPM 7479
      = (pm.nodes.take 96).foldl (applyNodeRingAttn pm) initPM 7479 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 7479 96 (by native_decide) (by native_decide)
  have hlast96 : ((pm.nodes.take 96).foldl (applyNodeRingAttn pm) initPM 7479).shape.reverse.head? = some 64 := by
    rw [← hpre7479, hs7479]; rfl
  have hpre7480 : denoteGraph_ringAttn pm initPM 7480
      = (pm.nodes.take 97).foldl (applyNodeRingAttn pm) initPM 7480 := by
    rw [denoteGraph_ringAttn]
    exact foldl_prefix_ring_g12 pm pm.nodes initPM 7480 97 (by native_decide) (by native_decide)
  have hlast97 : ((pm.nodes.take 97).foldl (applyNodeRingAttn pm) initPM 7480).shape.reverse.head? = some 64 := by
    rw [← hpre7480, hs7480]; rfl
  exact ⟨hSMeq, hs4708sm, hs7479, hs7480, hlastSM, hlast96, hlast97⟩

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4709_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4709
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4708sm, hs7479, hs7480, hlastSM, hlast96, hlast97⟩ :=
    moe_topk_common initSM initPM hSM hPM hInit
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4709
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4708) 8 64).1 :=
    ringAttn_reduce1_at sm initSM 27
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4708], outs := [4709, 4710, 4711], params := [8, 1] }
      4708 4709 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst sm ((sm.nodes.take 27).foldl (applyNodeRingAttn sm) initSM) 0 4708 4709 4710 4711 hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7481
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7479) 8 64).1 :=
    ringAttn_reduce1_at pm initPM 96
      { rank := 0, op := "OpName.FW_topk_routing", ins := [7479], outs := [7481, 7483, 7485], params := [8, 1] }
      7479 7481 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 96).foldl (applyNodeRingAttn pm) initPM) 0 7479 7481 7483 7485 hlast96)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7482
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7480) 8 64).1 :=
    ringAttn_reduce1_at pm initPM 97
      { rank := 1, op := "OpName.FW_topk_routing", ins := [7480], outs := [7482, 7484, 7486], params := [8, 1] }
      7480 7482 (fun t => (fw_topk_routing t 8 64).1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_fst pm ((pm.nodes.take 97).foldl (applyNodeRingAttn pm) initPM) 0 7480 7482 7484 7486 hlast97)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4709
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7481, denoteGraph_ringAttn pm initPM 7482] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs7479 hs7480,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4709).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_fst_shape _ 8 64 4096 (by rw [hs4708sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 7481).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs7479]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 7482).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_fst_shape _ 8 64 2048 (by rw [hs7480]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4709 4709 7481 7482 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

set_option maxHeartbeats 4000000 in
theorem recon_intermediateGoal_4710_ringAttn (initSM initPM : Store)
    (hSM : StoreShapesHold initSM smInitEnv) (hPM : StoreShapesHold initPM pmInitEnv)
    (hInit : InitGoalsHold pm.numRanks initGoals initSM initPM) :
    InitGoalHolds pm.numRanks intermediateGoal_4710
      (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM) := by
  obtain ⟨hSMeq, hs4708sm, hs7479, hs7480, hlastSM, hlast96, hlast97⟩ :=
    moe_topk_common initSM initPM hSM hPM hInit
  have hnr : pm.numRanks = 2 := rfl
  have rSM : denoteGraph_ringAttn sm initSM 4710
      = (fw_topk_routing (denoteGraph_ringAttn sm initSM 4708) 8 64).2.1 :=
    ringAttn_reduce1_at sm initSM 27
      { rank := 0, op := "OpName.FW_topk_routing", ins := [4708], outs := [4709, 4710, 4711], params := [8, 1] }
      4708 4710 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd sm ((sm.nodes.take 27).foldl (applyNodeRingAttn sm) initSM) 0 4708 4709 4710 4711 (by decide) hlastSM)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP0 : denoteGraph_ringAttn pm initPM 7483
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7479) 8 64).2.1 :=
    ringAttn_reduce1_at pm initPM 96
      { rank := 0, op := "OpName.FW_topk_routing", ins := [7479], outs := [7481, 7483, 7485], params := [8, 1] }
      7479 7483 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 96).foldl (applyNodeRingAttn pm) initPM) 0 7479 7481 7483 7485 (by decide) hlast96)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have rP1 : denoteGraph_ringAttn pm initPM 7484
      = (fw_topk_routing (denoteGraph_ringAttn pm initPM 7480) 8 64).2.1 :=
    ringAttn_reduce1_at pm initPM 97
      { rank := 1, op := "OpName.FW_topk_routing", ins := [7480], outs := [7482, 7484, 7486], params := [8, 1] }
      7480 7484 (fun t => (fw_topk_routing t 8 64).2.1) (by native_decide) (by native_decide)
      (by decide) (by decide)
      (applyNode_topk81_snd pm ((pm.nodes.take 97).foldl (applyNodeRingAttn pm) initPM) 0 7480 7482 7484 7486 (by decide) hlast97)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
  have hval : denoteGraph_ringAttn sm initSM 4710
      = allGatherPrimDimN 0 pm.numRanks 0
          [denoteGraph_ringAttn pm initPM 7483, denoteGraph_ringAttn pm initPM 7484] := by
    rw [rSM, hSMeq, hnr,
        fw_topk_routing_snd_fst_allGather0_commute_2_of _ _ 2048 8 64 (by omega) (by omega) hs7479 hs7480,
        rP0, rP1]
  have hshape : (denoteGraph_ringAttn sm initSM 4710).shape = [4096, 64] := by
    rw [rSM]; exact fw_topk_routing_snd_shape _ 8 64 4096 (by rw [hs4708sm]; rfl)
  have hsp0 : (denoteGraph_ringAttn pm initPM 7483).shape = [2048, 64] := by
    rw [rP0]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs7479]; rfl)
  have hsp1 : (denoteGraph_ringAttn pm initPM 7484).shape = [2048, 64] := by
    rw [rP1]; exact fw_topk_routing_snd_shape _ 8 64 2048 (by rw [hs7480]; rfl)
  exact wrap_2tp_allGather_gen (denoteGraph_ringAttn sm initSM) (denoteGraph_ringAttn pm initPM)
    intermediateGoal_4710 4710 7483 7484 [4096, 64] [2048, 64]
    rfl rfl rfl rfl rfl rfl (by decide) hval hshape hsp0 hsp1

end TrainVerify.Denote.GeneratedPatterns
