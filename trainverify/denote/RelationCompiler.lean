/- Generic relation-composition lemmas used by generated proof certificates. -/
import denote.KRankLinearGather
import denote.KRankLinearReduction
import denote.KRankSwiGLUGather
import denote.KRankInitValue
import denote.KRankAddGather
import denote.KRankTranspose
import denote.KRankLayernormGather
import denote.KRankAllToAll
import denote.InnerChunkCELossShard
import denote.InnerChunkCEShard
import denote.SlidingWindowReconstruction
import denote.yoco_goals.ZigzagRouterRel
import denote.yoco_goals.ZigzagMoEGmmRel
import denote.yoco_goals.ZigzagAttentionRel
import denote.yoco_goals.ZigzagLinearRel
import denote.yoco_goals.ZigzagPointwiseRel
import denote.yoco_goals.ZigzagBroadcastMul
import denote.yoco_goals.ZigzagViewRel
import denote.yoco_goals.ZigzagElemwiseRel
import denote.yoco_goals.FaithfulStackGather
import denote.ZigzagCollective
import denote.MultirefGeneral
import denote.ChunkGatherDim0
import denote.PointwiseGather
import denote.MoEFullSplitCommute
import denote.RotaryGather1D
import denote.EmbeddingHiddenShard
import denote.EmbeddingSequenceShard

set_option maxRecDepth 100000

open TrainVerify.Denote

namespace TrainVerify.Denote.RelationCompiler

/-- A faithful sliding-window attention node writes its ring-attention value at
its first output. -/
theorem applyNodeDistributedFaithful_sliding_attn_out
    (g : GraphDecl) (s : Store) (rank : Nat)
    (qTid kTid vTid cuQTid cuKVTid outTid auxTid : Tid) (params : List Nat) :
    applyNodeDistributedFaithful g s
      { rank := rank, op := "OpName.FW_attn_sliding_window",
        ins := [qTid, kTid, vTid, cuQTid, cuKVTid],
        outs := [outTid, auxTid], params := params } outTid =
      applyNodeRingAttn_sliding_window g s
        { rank := rank, op := "OpName.FW_attn_sliding_window",
          ins := [qTid, kTid, vTid, cuQTid, cuKVTid],
          outs := [outTid, auxTid], params := params } := by
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
    (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
  unfold applyNodeDistributed applyNodeRingAttn
  rw [if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (by simp)]
  unfold storeSet
  simp [List.find?]

/-- Singleton-output sibling for authorities that omit the historical auxiliary
sliding-attention output. -/
theorem applyNodeDistributedFaithful_sliding_attn_out_single
    (g : GraphDecl) (s : Store) (rank : Nat)
    (qTid kTid vTid cuQTid cuKVTid outTid : Tid) (params : List Nat) :
    applyNodeDistributedFaithful g s
      { rank := rank, op := "OpName.FW_attn_sliding_window",
        ins := [qTid, kTid, vTid, cuQTid, cuKVTid],
        outs := [outTid], params := params } outTid =
      applyNodeRingAttn_sliding_window g s
        { rank := rank, op := "OpName.FW_attn_sliding_window",
          ins := [qTid, kTid, vTid, cuQTid, cuKVTid],
          outs := [outTid], params := params } := by
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
    (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
  unfold applyNodeDistributed applyNodeRingAttn
  rw [if_neg (by simp), if_neg (by simp), if_neg (by simp),
    if_neg (by simp), if_neg (by simp), if_neg (by simp), if_pos (by simp)]
  unfold storeSet
  simp [List.find?]

/-- Batch the initial-store preservation proof for several reads through one
ordered faithful prefix. Generated mixed-SCC writers instantiate the two finite
side conditions once, then project individual TIDs by membership. -/
theorem foldl_faithful_prefix_reads_eq_initial
    (g : GraphDecl) (s : Store) (before : List NodeDecl) (tids : List Tid)
    (hnil : ∀ n ∈ before, n.outs ≠ [])
    (hwrite : ∀ n ∈ before, ∀ tid ∈ tids, tid ∉ n.outs) :
    ∀ tid ∈ tids,
      (before.foldl (applyNodeDistributedFaithful g) s) tid = s tid := by
  intro tid htid
  exact foldl_applyNodeDistributedFaithful_at_not_written g before s tid hnil
    (fun n hn => hwrite n hn tid htid)

/-- A cross-store equal full tensor and its two exact dim-0 chunks form the
ordinary two-rank relation. -/
theorem Ordinary2Rel.of_eq_chunk2_dim0
    (full source : Tensor) (tokens hidden : Nat)
    (hEq : full = source) (hShape : source.shape = [2 * tokens, hidden])
    (hTokens : 0 < tokens) (hHidden : 0 < hidden) :
    GeneratedPatterns.Ordinary2Rel full (chunkPrimDimN 0 2 0 source)
      (chunkPrimDimN 0 2 1 source) [2 * tokens, hidden] [tokens, hidden] := by
  constructor
  · rw [hEq]
    exact (allGatherPrimDimN_chunkPrimDimN_id_dim0_2 source (2 * tokens) hidden
      hShape (by omega) hHidden (by omega)).symm
  · rw [hEq]
    exact hShape
  · rw [chunkPrimDimN_shape 0 2 0 source [2 * tokens, hidden] hShape (by decide)]
    simp [List.set, List.getD]
  · rw [chunkPrimDimN_shape 0 2 1 source [2 * tokens, hidden] hShape (by decide)]
    simp [List.set, List.getD]

theorem fw_view_id_of_shape (x : Tensor) (target : Shape)
    (hx : x.shape = target) : fw_view target x = x := by
  apply Tensor.ext
  · exact hx.symm
  · intro idx hidx
    change idx < prodShape target at hidx
    unfold fw_view
    rw [valAt_of_lt _ _ (by simpa only [Tensor.mkShape] using hidx)]
    rfl

/-- Recover the generic gather package from an ordinary relation when the
shard shape is known to be nonscalar.  This is a structural projection only:
no model- or graph-specific semantics are introduced. -/
theorem Ordinary2Rel.toGather2Rel
    {full rank0 rank1 : Tensor} {fullShape shardShape : Shape}
    (h : GeneratedPatterns.Ordinary2Rel full rank0 rank1 fullShape shardShape)
    (hnonscalar : shardShape ≠ [1]) :
    GeneratedPatterns.Gather2Rel full rank0 rank1 fullShape shardShape := by
  exact {
    value := h.full_value
    full_shape := h.full_shape
    shard0_shape := h.rank0_shape
    shard1_shape := h.rank1_shape
    nonscalar := hnonscalar
  }

/-- Faithful maybe-shuffle converts ordinary source shards to a zigzag relation. -/
theorem Ordinary2Rel.to_zigzag_shuffle
    (gSM gPM : GraphDecl) (sSM sPM : Store)
    (nSM n0 n1 : NodeDecl) (cu : Tensor)
    {full source0 source1 : Tensor} {fullShape shardShape : Shape}
    (h : GeneratedPatterns.Ordinary2Rel full source0 source1 fullShape shardShape)
    (hcu : ZigzagCollective.PackedCuSeqlensWF cu (shardShape.getD 0 0 * 2) 2)
    (hbuddySM : gSM.replicaBuddies nSM = [nSM])
    (hbuddy0 : gPM.replicaBuddies n0 = [n0, n1])
    (hbuddy1 : gPM.replicaBuddies n1 = [n0, n1])
    (hsmData : sSM (nSM.ins.getD 0 0) = full)
    (hp0Data : sPM (n0.ins.getD 0 0) = source0)
    (hp1Data : sPM (n1.ins.getD 0 0) = source1)
    (hp0Cu : sPM (n0.ins.getD 1 0) = cu)
    (hp1Cu : sPM (n1.ins.getD 1 0) = cu)
    (hshard : shardShape ≠ [])
    (hsmParams : nSM.params = [1, 0])
    (hp0Params : n0.params = [2, 0])
    (hp1Params : n1.params = [2, 1]) :
    GeneratedPatterns.Zigzag2Rel
      (applyNodeFaithfulShuffleValue gSM sSM nSM)
      (applyNodeFaithfulShuffleValue gPM sPM n0)
      (applyNodeFaithfulShuffleValue gPM sPM n1)
      cu fullShape shardShape := by
  apply GeneratedPatterns.Zigzag2Rel.of_sources source0 source1
  · rw [applyNodeFaithfulShuffleValue_cpSize_one gSM sSM nSM hbuddySM]
    · rw [hsmData]
      exact h.full_value
    · rw [hsmParams]
      decide
    · rw [hsmParams]
      decide
  · have hp0Data' := hp0Data
    have hp1Data' := hp1Data
    have hp0Cu' := hp0Cu
    simp only [List.getD] at hp0Data' hp1Data' hp0Cu'
    unfold applyNodeFaithfulShuffleValue
    rw [hbuddy0, hp0Params]
    simp only [List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    rw [hp0Data', hp1Data', hp0Cu']
  · have hp0Data' := hp0Data
    have hp1Data' := hp1Data
    have hp1Cu' := hp1Cu
    simp only [List.getD] at hp0Data' hp1Data' hp1Cu'
    unfold applyNodeFaithfulShuffleValue
    rw [hbuddy1, hp1Params]
    simp only [List.map, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    rw [hp0Data', hp1Data', hp1Cu']
  · rw [applyNodeFaithfulShuffleValue_cpSize_one gSM sSM nSM hbuddySM]
    · rw [hsmData]
      exact h.full_shape
    · rw [hsmParams]
      decide
    · rw [hsmParams]
      decide
  · exact h.rank0_shape
  · exact h.rank1_shape
  · apply hcu.toZigzagCuWF
    · rfl
    · intro x hx
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with hx | hx
      · rw [hx, h.rank0_shape]
        exact hshard
      · rw [hx, h.rank1_shape]
        exact hshard
    · intro x hx
      have hhead : ([source0, source1].getD 0 (zeroTensor [])) = source0 := rfl
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with hx | hx
      · rw [hx, hhead]
      · rw [hx, hhead]
        rw [h.rank1_shape, h.rank0_shape]
    · change source0.shape.getD 0 0 * 2 = shardShape.getD 0 0 * 2
      rw [h.rank0_shape]

/-- Sliding-window buddy reconstruction packaged as an ordinary relation. -/
theorem Ordinary2Rel.sliding_attention
    (gSM gPM : GraphDecl) (sSM sPM : Store)
    (nSM n0 n1 : NodeDecl)
    (L qh kvh qDim vDim causalNat window : Nat)
    (hq : GeneratedPatterns.Ordinary2Rel
      (sSM (nSM.ins.getD 0 0)) (sPM (n0.ins.getD 0 0)) (sPM (n1.ins.getD 0 0))
      [2 * L, qh, qDim] [L, qh, qDim])
    (hk : GeneratedPatterns.Ordinary2Rel
      (sSM (nSM.ins.getD 1 0)) (sPM (n0.ins.getD 1 0)) (sPM (n1.ins.getD 1 0))
      [2 * L, kvh, qDim] [L, kvh, qDim])
    (hv : GeneratedPatterns.Ordinary2Rel
      (sSM (nSM.ins.getD 2 0)) (sPM (n0.ins.getD 2 0)) (sPM (n1.ins.getD 2 0))
      [2 * L, kvh, vDim] [L, kvh, vDim])
    (hcuQ : sSM (nSM.ins.getD 3 0) = sPM (n0.ins.getD 3 0))
    (hcuK : sSM (nSM.ins.getD 4 0) = sPM (n0.ins.getD 4 0))
    (hcuQsame : sPM (n0.ins.getD 3 0) = sPM (n1.ins.getD 3 0))
    (hcuKsame : sPM (n0.ins.getD 4 0) = sPM (n1.ins.getD 4 0))
    (hparamsSM : nSM.params = n0.params) (hparamsSame : n0.params = n1.params)
    (hparams : n0.params = [qh, kvh, qDim, vDim, causalNat, window])
    (hbuddySM : ringAttnBuddies gSM nSM = [nSM])
    (hbuddy0 : ringAttnBuddies gPM n0 = [n0, n1])
    (hbuddy1 : ringAttnBuddies gPM n1 = [n0, n1])
    (hidx0 : (([n0, n1].findIdx? (fun m => m.rank = n0.rank)).getD 0) = 0)
    (hidx1 : (([n0, n1].findIdx? (fun m => m.rank = n1.rank)).getD 0) = 1)
    (hL : 0 < L) (hqh : 0 < qh) (hvDim : 0 < vDim) :
    GeneratedPatterns.Ordinary2Rel
      (applyNodeRingAttn_sliding_window gSM sSM nSM)
      (applyNodeRingAttn_sliding_window gPM sPM n0)
      (applyNodeRingAttn_sliding_window gPM sPM n1)
      [2 * L, qh, vDim] [L, qh, vDim] := by
  have hqSM : 0 < (sSM (nSM.ins.getD 0 0)).shape.length := by
    rw [hq.full_shape]
    simp
  have hkSM : 0 < (sSM (nSM.ins.getD 1 0)).shape.length := by
    rw [hk.full_shape]
    simp
  have hvSM : 0 < (sSM (nSM.ins.getD 2 0)).shape.length := by
    rw [hv.full_shape]
    simp
  have hfull :
      (fw_attn_varlen
        (allGatherPrimDimN 0 2 0 [sPM (n0.ins.getD 0 0), sPM (n1.ins.getD 0 0)])
        (allGatherPrimDimN 0 2 0 [sPM (n0.ins.getD 1 0), sPM (n1.ins.getD 1 0)])
        (allGatherPrimDimN 0 2 0 [sPM (n0.ins.getD 2 0), sPM (n1.ins.getD 2 0)])
        (sPM (n0.ins.getD 3 0)) (sPM (n0.ins.getD 4 0))
        (n0.params.getD 0 1) (n0.params.getD 1 1)
        (n0.params.getD 2 1) (n0.params.getD 3 1)
        (decide (n0.params.getD 4 0 ≠ 0)) (n0.params.getD 5 0)).shape =
        [2 * L, qh, vDim] := by
    rw [fw_attn_varlen_shape _ _ _ _ _ _ _ _ _ _ _ (2 * L)]
    · rw [hparams]
      rfl
    · rw [← hq.full_value, hq.full_shape]
      rfl
  have hrec := GeneratedPatterns.applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair
    gSM gPM sSM sPM nSM n0 n1 L qh vDim hL hqh hvDim
    hbuddySM hbuddy0 hbuddy1 hidx0 hidx1 hqSM hkSM hvSM
    hq.full_value hk.full_value hv.full_value hcuQ hcuK hcuQsame hcuKsame
    hparamsSM hparamsSame hfull
  refine ⟨hrec, ?_, ?_, ?_⟩
  · rw [applyNodeRingAttn_sliding_window_singleton
      gSM sSM nSM hbuddySM hqSM hkSM hvSM]
    · rw [hcuQ, hcuK, hparamsSM, hq.full_value, hk.full_value, hv.full_value]
      exact hfull
    · rw [hcuQ, hcuK, hparamsSM, hq.full_value, hk.full_value, hv.full_value, hfull]
      simp
  · rw [GeneratedPatterns.applyNodeRingAttn_sliding_window_pair_eq_chunk
      gPM sPM n0 n0 n1 0 hbuddy0 hidx0]
    rw [chunkPrimDimN_shape 0 2 0 _ [2 * L, qh, vDim] hfull (by omega)]
    simp [List.set, List.getD]
  · rw [GeneratedPatterns.applyNodeRingAttn_sliding_window_pair_eq_chunk
      gPM sPM n1 n0 n1 1 hbuddy1 hidx1]
    rw [← hcuQsame, ← hcuKsame, ← hparamsSame]
    rw [chunkPrimDimN_shape 0 2 1 _ [2 * L, qh, vDim] hfull (by omega)]
    simp [List.set, List.getD]

/-- Two-output RoPE preserves ordinary dim-0 sharding with one-dimensional
position shards. -/
theorem Ordinary2Rel.rotary_embedding_1d
    {positions pos0 pos1 q q0 q1 k k0 k1 csSM csPM : Tensor}
    {L qh kh d : Nat}
    (hpositions : GeneratedPatterns.Ordinary2Rel positions pos0 pos1 [2 * L] [L])
    (hq : GeneratedPatterns.Ordinary2Rel q q0 q1 [2 * L, qh, d] [L, qh, d])
    (hk : GeneratedPatterns.Ordinary2Rel k k0 k1 [2 * L, kh, d] [L, kh, d])
    (hcs : csSM = csPM)
    (hL : 0 < L) (hqh : 0 < qh) (hkh : 0 < kh) (hd : 0 < d) :
    GeneratedPatterns.Ordinary2Rel
        (fw_rotary_embedding csSM positions q k qh kh).1
        (fw_rotary_embedding csPM pos0 q0 k0 qh kh).1
        (fw_rotary_embedding csPM pos1 q1 k1 qh kh).1
        [2 * L, qh, d] [L, qh, d] ∧
      GeneratedPatterns.Ordinary2Rel
        (fw_rotary_embedding csSM positions q k qh kh).2
        (fw_rotary_embedding csPM pos0 q0 k0 qh kh).2
        (fw_rotary_embedding csPM pos1 q1 k1 qh kh).2
        [2 * L, kh, d] [L, kh, d] := by
  have hcomm := fw_rotary_embedding_allGather0_commute_2_1d_shards
    csPM pos0 pos1 q0 q1 k0 k1 L qh kh d hL hqh hkh hd
    hpositions.rank0_shape hpositions.rank1_shape
    hq.rank0_shape hq.rank1_shape hk.rank0_shape hk.rank1_shape
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcs, hpositions.full_value, hq.full_value, hk.full_value]
      simpa [fw_rotary_embedding] using congrArg Prod.fst hcomm
    · rw [fw_rotary_embedding_fst_shape, hq.full_shape]
    · rw [fw_rotary_embedding_fst_shape, hq.rank0_shape]
    · rw [fw_rotary_embedding_fst_shape, hq.rank1_shape]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hcs, hpositions.full_value, hq.full_value, hk.full_value]
      simpa [fw_rotary_embedding] using congrArg Prod.snd hcomm
    · rw [fw_rotary_embedding_snd_shape, hk.full_shape]
    · rw [fw_rotary_embedding_snd_shape, hk.rank0_shape]
    · rw [fw_rotary_embedding_snd_shape, hk.rank1_shape]

/-- Elementwise addition of two ordinary two-rank relations. -/
theorem Ordinary2Rel.add
    {fullA a0 a1 fullB b0 b1 : Tensor} (lDim d : Nat)
    (hA : GeneratedPatterns.Ordinary2Rel fullA a0 a1 [lDim * 2, d] [lDim, d])
    (hB : GeneratedPatterns.Ordinary2Rel fullB b0 b1 [lDim * 2, d] [lDim, d])
    (hl : 0 < lDim) (hd : 0 < d) :
    GeneratedPatterns.Ordinary2Rel (elemwiseAdd fullA fullB)
      (elemwiseAdd a0 b0) (elemwiseAdd a1 b1) [lDim * 2, d] [lDim, d] := by
  constructor
  · rw [hA.full_value, hB.full_value]
    exact GeneratedPatterns.elemwiseAdd_allGather0_commute_cp2
      a0 a1 b0 b1 lDim d hl hd hA.rank0_shape hA.rank1_shape
      hB.rank0_shape hB.rank1_shape
  · exact elemwiseAdd_shape_of_shapes fullA fullB [lDim * 2, d]
      hA.full_shape hB.full_shape
  · exact elemwiseAdd_shape_of_shapes a0 b0 [lDim, d]
      hA.rank0_shape hB.rank0_shape
  · exact elemwiseAdd_shape_of_shapes a1 b1 [lDim, d]
      hA.rank1_shape hB.rank1_shape

/-- Broadcast multiplication of a single-column gate by a wide payload
preserves an ordinary dim-0 two-rank relation. -/
theorem Ordinary2Rel.mul_broadcast_col1
    {fullA a0 a1 fullB b0 b1 : Tensor} (lDim d : Nat)
    (hA : GeneratedPatterns.Ordinary2Rel fullA a0 a1 [lDim * 2, 1] [lDim, 1])
    (hB : GeneratedPatterns.Ordinary2Rel fullB b0 b1 [lDim * 2, d] [lDim, d])
    (hl : 0 < lDim) (hd : 0 < d) :
    GeneratedPatterns.Ordinary2Rel (elemwiseMul fullA fullB)
      (elemwiseMul a0 b0) (elemwiseMul a1 b1) [lDim * 2, d] [lDim, d] := by
  constructor
  · rw [hA.full_value, hB.full_value]
    exact GeneratedPatterns.ZigzagBroadcastMul.mulBC_allGather0_commute_cp2
      a0 a1 b0 b1 lDim d hl hd hA.rank0_shape hA.rank1_shape
      hB.rank0_shape hB.rank1_shape
  · exact GeneratedPatterns.ZigzagBroadcastMul.elemwiseMul_shape_col1
      fullA fullB (lDim * 2) d hA.full_shape hB.full_shape hd
  · exact GeneratedPatterns.ZigzagBroadcastMul.elemwiseMul_shape_col1
      a0 b0 lDim d hA.rank0_shape hB.rank0_shape hd
  · exact GeneratedPatterns.ZigzagBroadcastMul.elemwiseMul_shape_col1
      a1 b1 lDim d hA.rank1_shape hB.rank1_shape hd

/-- Sigmoid preserves an ordinary dim-0 two-rank relation. -/
theorem Ordinary2Rel.sigmoid
    {full rank0 rank1 : Tensor} (rows hidden : Nat)
    (hrel : GeneratedPatterns.Ordinary2Rel full rank0 rank1
      [rows * 2, hidden] [rows, hidden])
    (hrows : 0 < rows) (hhidden : 0 < hidden) :
    GeneratedPatterns.Ordinary2Rel (fw_sigmoid full)
      (fw_sigmoid rank0) (fw_sigmoid rank1)
      [rows * 2, hidden] [rows, hidden] := by
  constructor
  · rw [hrel.full_value]
    exact PointwiseGather.fw_sigmoid_allGather0_commute_2
      rank0 rank1 rows hidden hrows hhidden hrel.rank0_shape hrel.rank1_shape
  · rw [fw_sigmoid_shape]; exact hrel.full_shape
  · rw [fw_sigmoid_shape]; exact hrel.rank0_shape
  · rw [fw_sigmoid_shape]; exact hrel.rank1_shape

/-- SwiGLU preserves two ordinary dim-0 relations with the same shape. -/
theorem Ordinary2Rel.swiglu
    {fullA a0 a1 fullB b0 b1 : Tensor} (rows hidden : Nat)
    (hA : GeneratedPatterns.Ordinary2Rel fullA a0 a1
      [rows * 2, hidden] [rows, hidden])
    (hB : GeneratedPatterns.Ordinary2Rel fullB b0 b1
      [rows * 2, hidden] [rows, hidden])
    (hrows : 0 < rows) (hhidden : 0 < hidden) :
    GeneratedPatterns.Ordinary2Rel (fw_swiglu fullA fullB)
      (fw_swiglu a0 b0) (fw_swiglu a1 b1)
      [rows * 2, hidden] [rows, hidden] := by
  constructor
  · rw [hA.full_value, hB.full_value]
    exact PointwiseGather.fw_swiglu_allGather0_commute_2
      a0 a1 b0 b1 rows hidden hrows hhidden
      hA.rank0_shape hA.rank1_shape hB.rank0_shape hB.rank1_shape
  · rw [fw_swiglu_shape]; exact hB.full_shape
  · rw [fw_swiglu_shape]; exact hB.rank0_shape
  · rw [fw_swiglu_shape]; exact hB.rank1_shape

/-- GLU preserves two ordinary dim-0 relations with the same shape. -/
theorem Ordinary2Rel.glu
    {fullX x0 x1 fullG g0 g1 : Tensor} (rows hidden : Nat)
    (hX : GeneratedPatterns.Ordinary2Rel fullX x0 x1
      [rows * 2, hidden] [rows, hidden])
    (hG : GeneratedPatterns.Ordinary2Rel fullG g0 g1
      [rows * 2, hidden] [rows, hidden])
    (hrows : 0 < rows) (hhidden : 0 < hidden) :
    GeneratedPatterns.Ordinary2Rel (fw_glu fullX fullG)
      (fw_glu x0 g0) (fw_glu x1 g1)
      [rows * 2, hidden] [rows, hidden] := by
  constructor
  · rw [hX.full_value, hG.full_value]
    exact GeneratedPatterns.ZigzagElemwise.binary_allGather0_commute_cp2
      fw_glu (fun a b => a * sigmoidScalar b)
      GeneratedPatterns.ZigzagElemwise.fw_glu_shape_of_shapes
      (by
        intro x y a b idx hx _hy hidx
        exact GeneratedPatterns.ZigzagElemwise.fw_glu_valAt x y idx
          (by rw [hx, GeneratedPatterns.ZigzagElemwise.prodShape_2d']; exact hidx))
      x0 x1 g0 g1 rows hidden hrows hhidden
      hX.rank0_shape hX.rank1_shape hG.rank0_shape hG.rank1_shape
  · exact GeneratedPatterns.ZigzagElemwise.fw_glu_shape_of_shapes
      fullX fullG [rows * 2, hidden] hX.full_shape hG.full_shape
  · exact GeneratedPatterns.ZigzagElemwise.fw_glu_shape_of_shapes
      x0 g0 [rows, hidden] hX.rank0_shape hG.rank0_shape
  · exact GeneratedPatterns.ZigzagElemwise.fw_glu_shape_of_shapes
      x1 g1 [rows, hidden] hX.rank1_shape hG.rank1_shape

/-- A shape-identity view preserves the ordinary two-rank relation. -/
theorem Ordinary2Rel.view_id
    {full x0 x1 : Tensor} {fullShape shardShape : Shape}
    (hrel : GeneratedPatterns.Ordinary2Rel full x0 x1 fullShape shardShape) :
    GeneratedPatterns.Ordinary2Rel (fw_view fullShape full)
      (fw_view shardShape x0) (fw_view shardShape x1) fullShape shardShape := by
  rw [fw_view_id_of_shape full fullShape hrel.full_shape,
    fw_view_id_of_shape x0 shardShape hrel.rank0_shape,
    fw_view_id_of_shape x1 shardShape hrel.rank1_shape]
  exact hrel

/-- Replicated 2-D linear preserves an ordinary two-rank relation. -/
theorem Ordinary2Rel.mix_precision_linear
    {full x0 x1 wSM wPM : Tensor} (lDim inDim outDim : Nat)
    (hrel : GeneratedPatterns.Ordinary2Rel full x0 x1
      [lDim * 2, inDim] [lDim, inDim])
    (hw : wPM.shape = [outDim, inDim]) (hwEq : wSM = wPM)
    (hl : 0 < lDim) (hin : 0 < inDim) (hout : 0 < outDim) :
    GeneratedPatterns.Ordinary2Rel (fw_linear full wSM)
      (fw_linear x0 wPM) (fw_linear x1 wPM)
      [lDim * 2, outDim] [lDim, outDim] := by
  constructor
  · rw [hwEq, hrel.full_value]
    exact fw_mix_precision_linear_allGather0_commute_2 x0 x1 wPM
      lDim inDim outDim hl hin hout hrel.rank0_shape hrel.rank1_shape hw
  · rw [hwEq]
    exact TrainVerify.Denote.GeneratedPatterns.fw_linear_shape_2d'
      (lDim * 2) inDim outDim full wPM hrel.full_shape hw
  · exact TrainVerify.Denote.GeneratedPatterns.fw_linear_shape_2d'
      lDim inDim outDim x0 wPM hrel.rank0_shape hw
  · exact TrainVerify.Denote.GeneratedPatterns.fw_linear_shape_2d'
      lDim inDim outDim x1 wPM hrel.rank1_shape hw

/-- Replicated per-head linear preserves an ordinary two-rank relation. -/
theorem Ordinary2Rel.per_head_linear
    {full x0 x1 wSM wPM : Tensor} (lDim k hW dW : Nat)
    (hrel : GeneratedPatterns.Ordinary2Rel full x0 x1 [lDim * 2, k] [lDim, k])
    (hw : wPM.shape = [hW, dW, k]) (hwEq : wSM = wPM)
    (hl : 0 < lDim) (hk : 0 < k) (hhW : 0 < hW) (hdW : 0 < dW) :
    GeneratedPatterns.Ordinary2Rel (fw_per_head_linear full wSM)
      (fw_per_head_linear x0 wPM) (fw_per_head_linear x1 wPM)
      [lDim * 2, hW, dW] [lDim, hW, dW] := by
  constructor
  · rw [hwEq, hrel.full_value]
    exact fw_per_head_mix_precision_linear_allGather0_commute_2
      x0 x1 wPM lDim k hW dW hl hk hhW hdW hrel.rank0_shape hrel.rank1_shape hw
  · rw [hwEq]
    exact TrainVerify.Denote.ZigzagCollective.fw_per_head_linear_shape_2d full wPM (lDim * 2) k hW dW hrel.full_shape hw
  · exact TrainVerify.Denote.ZigzagCollective.fw_per_head_linear_shape_2d x0 wPM lDim k hW dW hrel.rank0_shape hw
  · exact TrainVerify.Denote.ZigzagCollective.fw_per_head_linear_shape_2d x1 wPM lDim k hW dW hrel.rank1_shape hw

/-- Replicated norm-linear preserves an ordinary two-rank relation. -/
theorem Ordinary2Rel.norm_linear
    {full x0 x1 wSM wPM : Tensor} (lDim k n : Nat)
    (hrel : GeneratedPatterns.Ordinary2Rel full x0 x1 [lDim * 2, k] [lDim, k])
    (hw : wPM.shape = [n, k]) (hwEq : wSM = wPM)
    (hl : 0 < lDim) (hk : 0 < k) (hn : 0 < n) :
    GeneratedPatterns.Ordinary2Rel (fw_norm_linear full wSM)
      (fw_norm_linear x0 wPM) (fw_norm_linear x1 wPM)
      [lDim * 2, n] [lDim, n] := by
  constructor
  · rw [hwEq, hrel.full_value]
    exact fw_norm_linear_allGather0_commute_2 x0 x1 wPM lDim k n
      hl hk hn hrel.rank0_shape hrel.rank1_shape hw
  · rw [hwEq]
    simpa using fw_norm_linear_shape full wPM n k [lDim * 2]
      (by rw [hrel.full_shape]; rfl) hw
  · simpa using fw_norm_linear_shape x0 wPM n k [lDim]
      (by rw [hrel.rank0_shape]; rfl) hw
  · simpa using fw_norm_linear_shape x1 wPM n k [lDim]
      (by rw [hrel.rank1_shape]; rfl) hw

/-- Ordinary per-head linear whose PM side materializes one full producer and
then chunks it back into rank-local outputs. -/
theorem Ordinary2Rel.per_head_linear_fullProducer_chunks
    {full x0 x1 wSM wPM smOut gathered producer out0 out1 : Tensor}
    (lDim k hW dW : Nat)
    (hrel : GeneratedPatterns.Ordinary2Rel full x0 x1 [lDim * 2, k] [lDim, k])
    (hw : wPM.shape = [hW, dW, k]) (hwEq : wSM = wPM)
    (hsm : smOut = fw_per_head_linear full wSM)
    (hgather : gathered = allGatherPrimDimN 0 2 0 [x0, x1])
    (hproducer : producer = fw_per_head_linear gathered wPM)
    (hchunk0 : out0 = chunkPrimDimN 0 2 0 producer)
    (hchunk1 : out1 = chunkPrimDimN 0 2 1 producer)
    (hl : 0 < lDim) (hk : 0 < k) (hhW : 0 < hW) (hdW : 0 < dW) :
    GeneratedPatterns.Ordinary2Rel smOut out0 out1
      [lDim * 2, hW, dW] [lDim, hW, dW] := by
  have hProjected := Ordinary2Rel.per_head_linear lDim k hW dW hrel hw hwEq hl hk hhW hdW
  have hCommute := fw_per_head_mix_precision_linear_allGather0_commute_2
    x0 x1 wPM lDim k hW dW hl hk hhW hdW hrel.rank0_shape hrel.rank1_shape hw
  have hProducerGather : producer = allGatherPrimDimN 0 2 0
      [fw_per_head_linear x0 wPM, fw_per_head_linear x1 wPM] := by
    rw [hproducer, hgather]; exact hCommute
  have hout0 : out0 = fw_per_head_linear x0 wPM := by
    rw [hchunk0, hProducerGather]
    simpa only [List.getD_cons_zero] using
      (TrainVerify.Denote.GeneratedPatterns.chunk_allGather_cp2_dim0_3d
        (fw_per_head_linear x0 wPM) (fw_per_head_linear x1 wPM)
        lDim hW dW 0 hProjected.rank0_shape hProjected.rank1_shape
        hl hhW hdW (by decide))
  have hout1 : out1 = fw_per_head_linear x1 wPM := by
    rw [hchunk1, hProducerGather]
    simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      (TrainVerify.Denote.GeneratedPatterns.chunk_allGather_cp2_dim0_3d
        (fw_per_head_linear x0 wPM) (fw_per_head_linear x1 wPM)
        lDim hW dW 1 hProjected.rank0_shape hProjected.rank1_shape
        hl hhW hdW (by decide))
  rw [hsm, hout0, hout1]
  exact hProjected

/-- Ordinary replicated-linear full-producer/chunks form. -/
theorem Ordinary2Rel.mix_precision_linear_fullProducer_chunks
    {full x0 x1 wSM wPM smOut gathered producer out0 out1 : Tensor}
    (lDim inDim outDim : Nat)
    (hrel : GeneratedPatterns.Ordinary2Rel full x0 x1
      [lDim * 2, inDim] [lDim, inDim])
    (hw : wPM.shape = [outDim, inDim]) (hwEq : wSM = wPM)
    (hsm : smOut = fw_linear full wSM)
    (hgather : gathered = allGatherPrimDimN 0 2 0 [x0, x1])
    (hproducer : producer = fw_linear gathered wPM)
    (hchunk0 : out0 = chunkPrimDimN 0 2 0 producer)
    (hchunk1 : out1 = chunkPrimDimN 0 2 1 producer)
    (hl : 0 < lDim) (hin : 0 < inDim) (hout : 0 < outDim) :
    GeneratedPatterns.Ordinary2Rel smOut out0 out1
      [lDim * 2, outDim] [lDim, outDim] := by
  have hProjected := Ordinary2Rel.mix_precision_linear
    lDim inDim outDim hrel hw hwEq hl hin hout
  have hCommute := fw_mix_precision_linear_allGather0_commute_2
    x0 x1 wPM lDim inDim outDim hl hin hout
    hrel.rank0_shape hrel.rank1_shape hw
  have hProducerGather : producer = allGatherPrimDimN 0 2 0
      [fw_linear x0 wPM, fw_linear x1 wPM] := by
    rw [hproducer, hgather]; exact hCommute
  have hout0 : out0 = fw_linear x0 wPM := by
    rw [hchunk0, hProducerGather]
    simpa only [List.getD_cons_zero] using
      (GeneratedPatterns.chunk_allGather_cp2_dim0_2d
        (fw_linear x0 wPM) (fw_linear x1 wPM)
        lDim outDim 0 hProjected.rank0_shape hProjected.rank1_shape
        hl hout (by decide))
  have hout1 : out1 = fw_linear x1 wPM := by
    rw [hchunk1, hProducerGather]
    simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      (GeneratedPatterns.chunk_allGather_cp2_dim0_2d
        (fw_linear x0 wPM) (fw_linear x1 wPM)
        lDim outDim 1 hProjected.rank0_shape hProjected.rank1_shape
        hl hout (by decide))
  rw [hsm, hout0, hout1]
  exact hProjected

/-- Ordinary norm-linear full-producer/chunks form. -/
theorem Ordinary2Rel.norm_linear_fullProducer_chunks
    {full x0 x1 wSM wPM smOut gathered producer out0 out1 : Tensor}
    (lDim k n : Nat)
    (hrel : GeneratedPatterns.Ordinary2Rel full x0 x1 [lDim * 2, k] [lDim, k])
    (hw : wPM.shape = [n, k]) (hwEq : wSM = wPM)
    (hsm : smOut = fw_norm_linear full wSM)
    (hgather : gathered = allGatherPrimDimN 0 2 0 [x0, x1])
    (hproducer : producer = fw_norm_linear gathered wPM)
    (hchunk0 : out0 = chunkPrimDimN 0 2 0 producer)
    (hchunk1 : out1 = chunkPrimDimN 0 2 1 producer)
    (hl : 0 < lDim) (hk : 0 < k) (hn : 0 < n) :
    GeneratedPatterns.Ordinary2Rel smOut out0 out1 [lDim * 2, n] [lDim, n] := by
  have hProjected := Ordinary2Rel.norm_linear lDim k n hrel hw hwEq hl hk hn
  have hCommute := fw_norm_linear_allGather0_commute_2 x0 x1 wPM lDim k n
    hl hk hn hrel.rank0_shape hrel.rank1_shape hw
  have hProducerGather : producer = allGatherPrimDimN 0 2 0
      [fw_norm_linear x0 wPM, fw_norm_linear x1 wPM] := by
    rw [hproducer, hgather]; exact hCommute
  have hout0 : out0 = fw_norm_linear x0 wPM := by
    rw [hchunk0, hProducerGather]
    simpa only [List.getD_cons_zero] using
      (TrainVerify.Denote.GeneratedPatterns.chunk_allGather_cp2_dim0_2d
        (fw_norm_linear x0 wPM) (fw_norm_linear x1 wPM)
        lDim n 0 hProjected.rank0_shape hProjected.rank1_shape hl hn (by decide))
  have hout1 : out1 = fw_norm_linear x1 wPM := by
    rw [hchunk1, hProducerGather]
    simpa only [List.getD_cons_succ, List.getD_cons_zero] using
      (TrainVerify.Denote.GeneratedPatterns.chunk_allGather_cp2_dim0_2d
        (fw_norm_linear x0 wPM) (fw_norm_linear x1 wPM)
        lDim n 1 hProjected.rank0_shape hProjected.rank1_shape hl hn (by decide))
  rw [hsm, hout0, hout1]
  exact hProjected

/-- Hidden-dimension sharded embedding followed by two-rank AllToAll yields
an ordinary dim-0 relation. -/
theorem Ordinary2Rel.embedding_hidden_shards_allToAll_two
    (tokens vocab hidden : Nat) (idsSM idsPM Wfull W0 W1 : Tensor)
    (hTokens : 0 < tokens) (hVocab : 0 < vocab) (hHidden : 0 < hidden)
    (hIdsEq : idsSM = idsPM) (hIds : idsPM.shape = [2 * tokens])
    (hWeight : Wfull = allGatherPrimDimN 1 2 0 [W0, W1])
    (hWfull : Wfull.shape = [vocab, hidden * 2])
    (hW0 : W0.shape = [vocab, hidden])
    (hW1 : W1.shape = [vocab, hidden]) :
    GeneratedPatterns.Ordinary2Rel
      (fw_embedding idsSM Wfull)
      (allToAllPrimWithDims 2 0 [fw_embedding idsPM W0, fw_embedding idsPM W1] 1 0)
      (allToAllPrimWithDims 2 1 [fw_embedding idsPM W0, fw_embedding idsPM W1] 1 0)
      [2 * tokens, hidden * 2] [tokens, hidden * 2] := by
  have hAlg := fw_embedding_hidden_shards_allToAll_two tokens vocab hidden
    idsPM W0 W1 hTokens hVocab hHidden hIds hW0 hW1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hIdsEq, hWeight]
    exact hAlg
  · rw [fw_embedding_shape, hIdsEq, hIds, hWfull]
    simp [lastD]
  · have hhead : (([fw_embedding idsPM W0, fw_embedding idsPM W1].head?.map
        (fun t => t.shape)).getD []) = [2 * tokens, hidden] := by
      simp only [List.head?, Option.map, Option.getD]
      rw [fw_embedding_shape, hIds, hW0]
      simp [lastD]
    rw [allToAllPrimWithDims_shape 2 0 _ 1 0 [2 * tokens, hidden] hhead (by decide)]
    simp [List.set, List.getD]
  · have hhead : (([fw_embedding idsPM W0, fw_embedding idsPM W1].head?.map
        (fun t => t.shape)).getD []) = [2 * tokens, hidden] := by
      simp only [List.head?, Option.map, Option.getD]
      rw [fw_embedding_shape, hIds, hW0]
      simp [lastD]
    rw [allToAllPrimWithDims_shape 2 1 _ 1 0 [2 * tokens, hidden] hhead (by decide)]
    simp [List.set, List.getD]

/-- One-dimensional form used by positional/rotary InitChunk boundaries. -/
theorem Ordinary2Rel.of_eq_chunk2_dim0_1d
    (full source : Tensor) (tokens : Nat)
    (hEq : full = source) (hShape : source.shape = [2 * tokens])
    (hTokens : 0 < tokens) :
    GeneratedPatterns.Ordinary2Rel full (chunkPrimDimN 0 2 0 source)
      (chunkPrimDimN 0 2 1 source) [2 * tokens] [tokens] := by
  constructor
  · rw [hEq]
    exact (allGatherPrimDimN_chunkPrimDimN_id_dim0_2_1d source tokens
      hShape hTokens).symm
  · rw [hEq]
    exact hShape
  · rw [chunkPrimDimN_shape 0 2 0 source [2 * tokens] hShape (by decide)]
    simp [List.set, List.getD]
  · rw [chunkPrimDimN_shape 0 2 1 source [2 * tokens] hShape (by decide)]
    simp [List.set, List.getD]

/-- RMSNorm preserves an ordinary dim-0 two-rank relation when the replicated
weight has the same value in the full and sharded stores. -/
theorem GeneratedPatterns.Ordinary2Rel.rms_norm_2d
    {full rank0 rank1 fullWeight shardWeight : Tensor}
    {shard hidden : Nat}
    (h : GeneratedPatterns.Ordinary2Rel full rank0 rank1
      [shard * 2, hidden] [shard, hidden])
    (hWeight : fullWeight = shardWeight)
    (hShard : 0 < shard) (hHidden : 0 < hidden) :
    GeneratedPatterns.Ordinary2Rel
      (fw_rms_norm full fullWeight)
      (fw_rms_norm rank0 shardWeight)
      (fw_rms_norm rank1 shardWeight)
      [shard * 2, hidden] [shard, hidden] := by
  constructor
  · rw [h.full_value, hWeight]
    exact ZigzagCollective.fw_rms_norm_allGather0_commute_2_core
      rank0 rank1 shardWeight shard hidden hShard hHidden h.rank0_shape h.rank1_shape
  · unfold fw_rms_norm
    rw [h.full_shape]
    simp [Tensor.mkShape]
  · unfold fw_rms_norm
    rw [h.rank0_shape]
    simp [Tensor.mkShape]
  · unfold fw_rms_norm
    rw [h.rank1_shape]
    simp [Tensor.mkShape]

/-- Rank-3 sibling: RMSNorm still reduces only the final axis, so an
independent middle axis is preserved across dim-0 CP2 gathering. -/
theorem GeneratedPatterns.Ordinary2Rel.rms_norm_3d
    {full rank0 rank1 fullWeight shardWeight : Tensor}
    {shard middle hidden : Nat}
    (h : GeneratedPatterns.Ordinary2Rel full rank0 rank1
      [shard * 2, middle, hidden] [shard, middle, hidden])
    (hWeight : fullWeight = shardWeight)
    (hShard : 0 < shard) (hMiddle : 0 < middle) (hHidden : 0 < hidden) :
    GeneratedPatterns.Ordinary2Rel
      (fw_rms_norm full fullWeight)
      (fw_rms_norm rank0 shardWeight)
      (fw_rms_norm rank1 shardWeight)
      [shard * 2, middle, hidden] [shard, middle, hidden] := by
  constructor
  · rw [h.full_value, hWeight]
    exact ZigzagCollective.fw_rms_norm_allGather0_commute_2_core_3d
      rank0 rank1 shardWeight shard middle hidden hShard hMiddle hHidden
      h.rank0_shape h.rank1_shape
  · unfold fw_rms_norm
    rw [h.full_shape]
    simp [Tensor.mkShape]
  · unfold fw_rms_norm
    rw [h.rank0_shape]
    simp [Tensor.mkShape]
  · unfold fw_rms_norm
    rw [h.rank1_shape]
    simp [Tensor.mkShape]

/-- A graph-independent simulation certificate for unequal SM/PM node segments. -/
structure SegmentCertificate
    {S P NS NP : Type}
    (stepS : S → NS → S) (stepP : P → NP → P)
    (R : S → P → Prop) where
  smNodes : List NS
  pmNodes : List NP
  sound : ∀ sm pm, R sm pm →
    R (smNodes.foldl stepS sm) (pmNodes.foldl stepP pm)

/-- Sequentially composing sound segments preserves the relation. -/
theorem foldl_flatMap_certificates
    {S P NS NP : Type}
    (stepS : S → NS → S) (stepP : P → NP → P)
    (R : S → P → Prop)
    (cs : List (SegmentCertificate stepS stepP R))
    (sm : S) (pm : P) (h : R sm pm) :
    R ((cs.flatMap (·.smNodes)).foldl stepS sm)
      ((cs.flatMap (·.pmNodes)).foldl stepP pm) := by
  induction cs generalizing sm pm with
  | nil => simpa using h
  | cons c cs ih =>
      simp only [List.flatMap_cons, List.foldl_append]
      exact ih _ _ (c.sound sm pm h)


abbrev FaithfulSegmentCertificate
    (smGraph pmGraph : GraphDecl) (R : Store → Store → Prop) :=
  SegmentCertificate
    (applyNodeDistributedFaithful smGraph)
    (applyNodeDistributedFaithful pmGraph) R

/-- Exact node-list coverage turns segment simulation into whole-graph simulation. -/
theorem faithful_segments_cover_graphs
    (smGraph pmGraph : GraphDecl) (R : Store → Store → Prop)
    (cs : List (FaithfulSegmentCertificate smGraph pmGraph R))
    (initSM initPM : Store) (hInit : R initSM initPM)
    (hSM : cs.flatMap (·.smNodes) = smGraph.nodes)
    (hPM : cs.flatMap (·.pmNodes) = pmGraph.nodes) :
    R (denoteGraphDistributedFaithful smGraph initSM)
      (denoteGraphDistributedFaithful pmGraph initPM) := by
  unfold denoteGraphDistributedFaithful
  rw [← hSM, ← hPM]
  exact foldl_flatMap_certificates
    (applyNodeDistributedFaithful smGraph)
    (applyNodeDistributedFaithful pmGraph) R cs initSM initPM hInit

/-- One heterogeneous simulation segment, with distinct pre/post invariants. -/
structure DepSegmentCertificate
    {S P NS NP I : Type}
    (stepS : S → NS → S) (stepP : P → NP → P)
    (Inv : I → S → P → Prop) (pre post : I) where
  smNodes : List NS
  pmNodes : List NP
  sound : ∀ sm pm, Inv pre sm pm →
    Inv post (smNodes.foldl stepS sm) (pmNodes.foldl stepP pm)

/-- A dependent chain enforces exact adjacency of heterogeneous invariants. -/
inductive DepCertificateChain
    {S P NS NP I : Type}
    (stepS : S → NS → S) (stepP : P → NP → P)
    (Inv : I → S → P → Prop) : I → I → Type
  | nil (i : I) : DepCertificateChain stepS stepP Inv i i
  | cons {i j k : I}
      (head : DepSegmentCertificate stepS stepP Inv i j)
      (tail : DepCertificateChain stepS stepP Inv j k) :
      DepCertificateChain stepS stepP Inv i k

namespace DepCertificateChain

def smNodes {S P NS NP I : Type}
    {stepS : S → NS → S} {stepP : P → NP → P}
    {Inv : I → S → P → Prop} {i j : I} :
    DepCertificateChain stepS stepP Inv i j → List NS
  | .nil _ => []
  | .cons head tail => head.smNodes ++ smNodes tail

def pmNodes {S P NS NP I : Type}
    {stepS : S → NS → S} {stepP : P → NP → P}
    {Inv : I → S → P → Prop} {i j : I} :
    DepCertificateChain stepS stepP Inv i j → List NP
  | .nil _ => []
  | .cons head tail => head.pmNodes ++ pmNodes tail

theorem sound {S P NS NP I : Type}
    {stepS : S → NS → S} {stepP : P → NP → P}
    {Inv : I → S → P → Prop} {i j : I}
    (c : DepCertificateChain stepS stepP Inv i j)
    (sm : S) (pm : P) (h : Inv i sm pm) :
    Inv j (c.smNodes.foldl stepS sm) (c.pmNodes.foldl stepP pm) := by
  induction c generalizing sm pm with
  | nil => simpa [smNodes, pmNodes] using h
  | cons head tail ih =>
      simp only [smNodes, pmNodes, List.foldl_append]
      exact ih _ _ (head.sound sm pm h)

end DepCertificateChain

abbrev FaithfulDepSegmentCertificate
    {I : Type} (smGraph pmGraph : GraphDecl)
    (Inv : I → Store → Store → Prop) (pre post : I) :=
  DepSegmentCertificate
    (applyNodeDistributedFaithful smGraph)
    (applyNodeDistributedFaithful pmGraph) Inv pre post

abbrev FaithfulCertificateChain
    {I : Type} (smGraph pmGraph : GraphDecl)
    (Inv : I → Store → Store → Prop) :=
  DepCertificateChain
    (applyNodeDistributedFaithful smGraph)
    (applyNodeDistributedFaithful pmGraph) Inv

/-- Ordered list equalities, not set coverage, close a dependent chain over both graphs. -/
theorem faithful_dependent_chain_covers_graphs
    {I : Type} (smGraph pmGraph : GraphDecl)
    (Inv : I → Store → Store → Prop) {first last : I}
    (c : FaithfulCertificateChain smGraph pmGraph Inv first last)
    (initSM initPM : Store) (hInit : Inv first initSM initPM)
    (hSM : c.smNodes = smGraph.nodes)
    (hPM : c.pmNodes = pmGraph.nodes) :
    Inv last (denoteGraphDistributedFaithful smGraph initSM)
      (denoteGraphDistributedFaithful pmGraph initPM) := by
  unfold denoteGraphDistributedFaithful
  rw [← hSM, ← hPM]
  exact c.sound initSM initPM hInit


inductive StoreSide where
  | sm
  | pm
  deriving Repr, DecidableEq

def StoreSide.read (side : StoreSide) (sm pm : Store) : Store :=
  match side with
  | .sm => sm
  | .pm => pm

/-- Truthful closed relation for a stack of ordered dim-0 source relations
whose rank-local stacks reconstruct the full stack along dimension 1. -/
structure JoinedOrdinary2Rel (full rank0 rank1 joined : Tensor)
    (fullShape shardShape : Shape) : Prop extends
    GeneratedPatterns.Ordinary2Rel full rank0 rank1 fullShape shardShape where
  joined_value : joined = allGatherPrimDimN 0 2 0 [rank0, rank1]
  public_value : full = joined

structure IndexedStack2Rel (full rank0 rank1 : Tensor)
    (sources : List (Tensor × Tensor × Tensor))
    (gatherDim : Nat) (fullShape shardShape : Shape) : Prop where
  gather_dim : gatherDim = 1
  full_value : full = allGatherPrimDimN gatherDim 2 0 [rank0, rank1]
  full_shape : full.shape = fullShape
  rank0_shape : rank0.shape = shardShape
  rank1_shape : rank1.shape = shardShape
  full_stack : full = fw_stack (sources.map fun source => source.1)
  rank0_stack : rank0 = fw_stack (sources.map fun source => source.2.1)
  rank1_stack : rank1 = fw_stack (sources.map fun source => source.2.2)
  source_relations : ∀ source ∈ sources,
    GeneratedPatterns.Ordinary2Rel source.1 source.2.1 source.2.2
      fullShape.tail shardShape.tail

structure JoinedIndexedStack2Rel (full rank0 rank1 joined : Tensor)
    (sources : List (Tensor × Tensor × Tensor))
    (gatherDim : Nat) (fullShape shardShape : Shape) : Prop extends
    IndexedStack2Rel full rank0 rank1 sources gatherDim fullShape shardShape where
  joined_value : joined = allGatherPrimDimN gatherDim 2 0 [rank0, rank1]
  public_value : full = joined

/-- Rank-count-polymorphic ordinary sharding relation.  The ordered shard
list is authority: its length is the collective rank count and every shard is
shape-checked. -/
structure ShardedRel (full : Tensor) (shards : List Tensor)
    (gatherDim : Nat) (fullShape shardShape : Shape) : Prop where
  full_value : full = allGatherPrimDimN gatherDim shards.length 0 shards
  full_shape : full.shape = fullShape
  shards_nonempty : shards ≠ []
  gather_dim_lt : gatherDim < shardShape.length
  shard_shapes : ∀ shard ∈ shards, shard.shape = shardShape
  shape_contract :
    fullShape = shardShape.set gatherDim
      (shardShape.getD gatherDim 0 * shards.length)

/-- Arbitrary-rank zigzag values, retaining the actual metadata tensor and the
ordered ordinary sources. The output count is the collective rank count. -/
def ZigzagKRel (full : Tensor) (outputs : List Tensor) (cu : Tensor)
    (fullShape shardShape : Shape) : Prop :=
  ∃ sources : List Tensor,
    ShardedRel full sources 0 fullShape shardShape ∧
    sources.length = outputs.length ∧
    ZigzagCollective.ZigzagCuWF (decodeCuSeqlens cu) sources outputs.length ∧
    outputs = (List.range outputs.length).map (fun rank =>
      ZigzagCollective.fw_maybe_shuffle_collective sources
        (decodeCuSeqlens cu) outputs.length rank)

namespace ZigzagKRel

/-- Value-level list entry: shuffle every ordinary source rank in authority order.
No gather of the zigzag outputs is asserted to equal the canonical full tensor. -/
theorem of_sharded {full cu : Tensor} {sources : List Tensor}
    {fullShape shardShape : Shape}
    (hsource : ShardedRel full sources 0 fullShape shardShape)
    (hcu : ZigzagCollective.ZigzagCuWF
      (decodeCuSeqlens cu) sources sources.length) :
    ZigzagKRel full
      ((List.range sources.length).map (fun rank =>
        ZigzagCollective.fw_maybe_shuffle_collective sources
          (decodeCuSeqlens cu) sources.length rank)) cu fullShape shardShape := by
  refine ⟨sources, hsource, ?_, ?_, ?_⟩
  · rw [List.length_map, List.length_range]
  · simpa only [List.length_map, List.length_range] using hcu
  · rw [List.length_map, List.length_range]

end ZigzagKRel

/-- Canonical row order and physical zigzag row order coexist with an
independent feature-axis tensor-parallel decomposition.  The existential row
shards are semantic witnesses; `featureShards` are the ordered graph values. -/
def ZigzagFeatureRel
    (full : Tensor) (featureShards : List Tensor) (cu : Tensor)
    (fullShape rowShardShape featureShardShape : Shape) : Prop :=
  ∃ row0 row1,
    GeneratedPatterns.Zigzag2Rel full row0 row1 cu
      fullShape rowShardShape ∧
    ShardedRel (allGatherPrimDimN 0 2 0 [row0, row1]) featureShards 1
      fullShape featureShardShape

namespace ZigzagFeatureRel

/-- Eliminate a hybrid relation without conflating canonical and physical row
orders. -/
theorem sources
    {full : Tensor} {featureShards : List Tensor} {cu : Tensor}
    {fullShape rowShardShape featureShardShape : Shape}
    (h : ZigzagFeatureRel full featureShards cu
      fullShape rowShardShape featureShardShape) :
    ∃ row0 row1,
      GeneratedPatterns.Zigzag2Rel full row0 row1 cu
        fullShape rowShardShape ∧
      ShardedRel (allGatherPrimDimN 0 2 0 [row0, row1]) featureShards 1
        fullShape featureShardShape := h

/-- Shape-preserving views on the canonical full value and both feature shards
preserve the hybrid relation. -/
theorem view_id_two
    {full x0 x1 cu : Tensor} {fullShape rowShardShape featureShardShape : Shape}
    (h : ZigzagFeatureRel full [x0, x1] cu
      fullShape rowShardShape featureShardShape) :
    ZigzagFeatureRel (fw_view fullShape full)
      [fw_view featureShardShape x0, fw_view featureShardShape x1] cu
      fullShape rowShardShape featureShardShape := by
  rcases h with ⟨z0, z1, hrow, hfeature⟩
  rcases hrow with ⟨source0, source1, hrowSources⟩
  rw [fw_view_id_of_shape full fullShape hrowSources.full_shape,
      fw_view_id_of_shape x0 featureShardShape
        (hfeature.shard_shapes x0 (by simp)),
      fw_view_id_of_shape x1 featureShardShape
        (hfeature.shard_shapes x1 (by simp))]
  exact ⟨z0, z1, ⟨source0, source1, hrowSources⟩, hfeature⟩

/-- SwiGLU preserves the independent zigzag-row and feature-shard axes. -/
theorem swiglu_two
    {fullG g0 g1 fullU u0 u1 cu : Tensor}
    (rows inputDim featureDim : Nat)
    (hG : ZigzagFeatureRel fullG [g0, g1] cu
      [rows * 2, inputDim] [rows, inputDim] [rows * 2, featureDim])
    (hU : ZigzagFeatureRel fullU [u0, u1] cu
      [rows * 2, inputDim] [rows, inputDim] [rows * 2, featureDim])
    (hSplit : inputDim = 2 * featureDim)
    (hrows : 0 < rows) (hinput : 0 < inputDim) (hfeature : 0 < featureDim) :
    ZigzagFeatureRel (fw_swiglu fullG fullU)
      [fw_swiglu g0 u0, fw_swiglu g1 u1] cu
      [rows * 2, inputDim] [rows, inputDim] [rows * 2, featureDim] := by
  rcases hG with ⟨zG0, zG1, hrowG, hfeatureG⟩
  rcases hU with ⟨zU0, zU1, hrowU, hfeatureU⟩
  have hrowOut := GeneratedPatterns.Zigzag2Rel.swiglu
    rows inputDim hrowG hrowU hrows hinput
  have hfeatureOut : ShardedRel
      (fw_swiglu (allGatherPrimDimN 0 2 0 [zG0, zG1])
        (allGatherPrimDimN 0 2 0 [zU0, zU1]))
      [fw_swiglu g0 u0, fw_swiglu g1 u1] 1
      [rows * 2, inputDim] [rows * 2, featureDim] := by
    refine {
      full_value := ?_
      full_shape := ?_
      shards_nonempty := by simp
      gather_dim_lt := by norm_num
      shard_shapes := ?_
      shape_contract := by
        norm_num [List.set, List.getD]
        omega
    }
    · rw [hfeatureG.full_value, hfeatureU.full_value]
      exact fw_swiglu_allGatherDim1_two_2d g0 g1 u0 u1
        (rows * 2) featureDim (by omega) hfeature
        (hfeatureG.shard_shapes g0 (by simp))
        (hfeatureG.shard_shapes g1 (by simp))
        (hfeatureU.shard_shapes u0 (by simp))
        (hfeatureU.shard_shapes u1 (by simp))
    · unfold fw_swiglu Tensor.mkShape
      exact hfeatureU.full_shape
    · intro shardValue hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl <;> unfold fw_swiglu Tensor.mkShape
      · exact hfeatureU.shard_shapes u0 (by simp)
      · exact hfeatureU.shard_shapes u1 (by simp)
  rcases hrowG with ⟨sourceG0, sourceG1, hrowGSources⟩
  rcases hrowU with ⟨sourceU0, sourceU1, hrowUSources⟩
  have hcommute := PointwiseGather.fw_swiglu_allGather0_commute_2
    zG0 zG1 zU0 zU1 rows inputDim hrows hinput
    hrowGSources.rank0_shape hrowGSources.rank1_shape
    hrowUSources.rank0_shape hrowUSources.rank1_shape
  have hfeatureOut' : ShardedRel
      (allGatherPrimDimN 0 2 0
        [fw_swiglu zG0 zU0, fw_swiglu zG1 zU1])
      [fw_swiglu g0 u0, fw_swiglu g1 u1] 1
      [rows * 2, inputDim] [rows * 2, featureDim] := by
    rw [← hcommute]
    exact hfeatureOut
  exact ⟨fw_swiglu zG0 zU0, fw_swiglu zG1 zU1,
    hrowOut, hfeatureOut'⟩

/-- Feature-sharded row-parallel linear reduction exits back to exact CP2
zigzag row shards. Canonical row order is carried only by `Zigzag2Rel`; the
AllReduce computes the physical zigzag-order full tensor whose dim-0 chunks
are the exposed rank outputs. -/
theorem mix_precision_linear_dim1_allReduce_chunks_cp2
    {full x0 x1 cu fullWeight w0 w1 : Tensor}
    (rows inputDim featureDim outputDim : Nat)
    (hinput : ZigzagFeatureRel full [x0, x1] cu
      [rows * 2, inputDim] [rows, inputDim] [rows * 2, featureDim])
    (hweight : ShardedRel fullWeight [w0, w1] 1
      [outputDim, inputDim] [outputDim, featureDim])
    (hinputSplit : inputDim = 2 * featureDim)
    (hrows : 0 < rows) (hfeature : 0 < featureDim)
    (houtput : 0 < outputDim) :
    GeneratedPatterns.Zigzag2Rel
      (fw_linear full fullWeight)
      (chunkPrimDimN 0 2 0
        (allReducePrim 2 0 [fw_linear x0 w0, fw_linear x1 w1]))
      (chunkPrimDimN 0 2 1
        (allReducePrim 2 0 [fw_linear x0 w0, fw_linear x1 w1]))
      cu [rows * 2, outputDim] [rows, outputDim] := by
  rcases hinput with ⟨z0, z1, hrow, hfeatureRel⟩
  have hinputPos : 0 < inputDim := by omega
  have hx0 : x0.shape = [rows * 2, featureDim] :=
    hfeatureRel.shard_shapes x0 (by simp)
  have hx1 : x1.shape = [rows * 2, featureDim] :=
    hfeatureRel.shard_shapes x1 (by simp)
  have hw0 : w0.shape = [outputDim, featureDim] :=
    hweight.shard_shapes w0 (by simp)
  have hw1 : w1.shape = [outputDim, featureDim] :=
    hweight.shard_shapes w1 (by simp)
  have hreduce := fw_linear_dim1_two_allReduce_2d
    x0 x1 w0 w1 (rows * 2) featureDim outputDim
    (by omega) hfeature houtput hx0 hx1 hw0 hw1
  have hphysicalReduction :
      fw_linear (allGatherPrimDimN 0 2 0 [z0, z1]) fullWeight =
        allReducePrim 2 0 [fw_linear x0 w0, fw_linear x1 w1] := by
    rw [hfeatureRel.full_value, hweight.full_value]
    exact hreduce
  rcases hrow with ⟨source0, source1, hrowSources⟩
  have hrowRel : GeneratedPatterns.Zigzag2Rel full z0 z1 cu
      [rows * 2, inputDim] [rows, inputDim] :=
    ⟨source0, source1, hrowSources⟩
  have hrowOut := GeneratedPatterns.Zigzag2Rel.mix_precision_linear
    rows inputDim outputDim hrowRel hweight.full_shape
    hrows hinputPos houtput
  have hrowGather :
      fw_linear (allGatherPrimDimN 0 2 0 [z0, z1]) fullWeight =
        allGatherPrimDimN 0 2 0
          [fw_linear z0 fullWeight, fw_linear z1 fullWeight] :=
    fw_mix_precision_linear_allGather0_commute_2
      z0 z1 fullWeight rows inputDim outputDim
      hrows hinputPos houtput hrowSources.rank0_shape
      hrowSources.rank1_shape hweight.full_shape
  have hreducedGather :
      allReducePrim 2 0 [fw_linear x0 w0, fw_linear x1 w1] =
        allGatherPrimDimN 0 2 0
          [fw_linear z0 fullWeight, fw_linear z1 fullWeight] :=
    hphysicalReduction.symm.trans hrowGather
  rcases hrowOut with ⟨outSource0, outSource1, hrowOutSources⟩
  have houtRel : GeneratedPatterns.Zigzag2Rel
      (fw_linear full fullWeight) (fw_linear z0 fullWeight)
      (fw_linear z1 fullWeight) cu
      [rows * 2, outputDim] [rows, outputDim] :=
    ⟨outSource0, outSource1, hrowOutSources⟩
  have hchunk0 := GeneratedPatterns.chunk_allGather_cp2_dim0_2d
    (fw_linear z0 fullWeight) (fw_linear z1 fullWeight)
    rows outputDim 0 hrowOutSources.rank0_shape
    hrowOutSources.rank1_shape hrows houtput (by decide)
  have hchunk1 := GeneratedPatterns.chunk_allGather_cp2_dim0_2d
    (fw_linear z0 fullWeight) (fw_linear z1 fullWeight)
    rows outputDim 1 hrowOutSources.rank0_shape
    hrowOutSources.rank1_shape hrows houtput (by decide)
  rw [hreducedGather, hchunk0, hchunk1]
  simpa only [List.getD_cons_zero, List.getD_cons_succ] using houtRel

end ZigzagFeatureRel

/-- A graph-written full physical zigzag tensor together with its canonical
full tensor and exact rank-local zigzag shards. -/
structure JoinedZigzag2Rel
    (full row0 row1 joined cu : Tensor)
    (fullShape rowShardShape : Shape) : Prop where
  row : GeneratedPatterns.Zigzag2Rel full row0 row1 cu
    fullShape rowShardShape
  joined_value : joined = allGatherPrimDimN 0 2 0 [row0, row1]

namespace JoinedZigzag2Rel

theorem of_allGather
    {full row0 row1 joined cu : Tensor}
    {fullShape rowShardShape : Shape}
    (hrow : GeneratedPatterns.Zigzag2Rel full row0 row1 cu
      fullShape rowShardShape)
    (hjoined : joined = allGatherPrimDimN 0 2 0 [row0, row1]) :
    JoinedZigzag2Rel full row0 row1 joined cu fullShape rowShardShape :=
  { row := hrow, joined_value := hjoined }

end JoinedZigzag2Rel

/-- Existential row witnesses for a graph-written physical zigzag tensor. -/
def JoinedZigzagRel
    (full joined cu : Tensor) (fullShape rowShardShape : Shape) : Prop :=
  ∃ row0 row1,
    JoinedZigzag2Rel full row0 row1 joined cu fullShape rowShardShape

namespace JoinedZigzagRel

/-- Publish a graph-written physical joined tensor from exact live row shards. -/
theorem of_allGather
    {full row0 row1 joined cu : Tensor}
    {fullShape rowShardShape : Shape}
    (hrow : GeneratedPatterns.Zigzag2Rel full row0 row1 cu
      fullShape rowShardShape)
    (hjoined : joined = allGatherPrimDimN 0 2 0 [row0, row1]) :
    JoinedZigzagRel full joined cu fullShape rowShardShape := by
  exact ⟨row0, row1, JoinedZigzag2Rel.of_allGather hrow hjoined⟩

/-- Denotational identity writers preserve joined-zigzag authority. -/
theorem identity
    {full joined cu : Tensor} {fullShape rowShardShape : Shape}
    (h : JoinedZigzagRel full joined cu fullShape rowShardShape) :
    JoinedZigzagRel (tensorId full) (tensorId joined) cu
      fullShape rowShardShape := by
  simpa only [tensorId] using h

/-- A shape-identity 2-D view preserves joined-zigzag authority. -/
theorem view_id_2d
    {full joined cu : Tensor} {rows hidden : Nat}
    (h : JoinedZigzagRel full joined cu
      [rows * 2, hidden] [rows, hidden]) :
    JoinedZigzagRel (fw_view [rows * 2, hidden] full)
      (fw_view [rows * 2, hidden] joined) cu
      [rows * 2, hidden] [rows, hidden] := by
  rcases h with ⟨row0, row1, hjoined⟩
  have hhead : (([row0, row1] : List Tensor).head?.map
      (fun t => t.shape)).getD [] = [rows, hidden] := by
    simp [hjoined.row.rank0_shape]
  have hjoinedShape : joined.shape = [rows * 2, hidden] := by
    rw [hjoined.joined_value,
      allGatherPrimDimN_shape 0 2 _ [rows, hidden] hhead]
    simp [List.set, List.getD, Nat.mul_comm]
  rw [fw_view_id_of_shape full [rows * 2, hidden]
      hjoined.row.full_shape,
    fw_view_id_of_shape joined [rows * 2, hidden] hjoinedShape]
  exact ⟨row0, row1, hjoined⟩

/-- Replicated RMSNorm preserves canonical and physical zigzag orders. -/
theorem rms_norm
    {full joined cu wSM wPM : Tensor} (rows hidden : Nat)
    (h : JoinedZigzagRel full joined cu
      [rows * 2, hidden] [rows, hidden])
    (hwEq : wSM = wPM) (hrows : 0 < rows) (hhidden : 0 < hidden) :
    JoinedZigzagRel
      (fw_rms_norm full wSM) (fw_rms_norm joined wPM) cu
      [rows * 2, hidden] [rows, hidden] := by
  rcases h with ⟨row0, row1, hjoined⟩
  rcases hjoined.row with ⟨source0, source1, hsources⟩
  have hbase : GeneratedPatterns.Zigzag2Rel full row0 row1 cu
      [rows * 2, hidden] [rows, hidden] := ⟨source0, source1, hsources⟩
  have hrow := GeneratedPatterns.Zigzag2Rel.rms_norm
    (w := wPM) rows hidden hbase hrows hhidden rfl
  refine ⟨fw_rms_norm row0 wPM, fw_rms_norm row1 wPM, ?_⟩
  refine { row := ?_, joined_value := ?_ }
  · simpa only [hwEq] using hrow
  · rw [hjoined.joined_value]
    exact ZigzagCollective.fw_rms_norm_allGather0_commute_2_core
      row0 row1 wPM rows hidden hrows hhidden
      hsources.rank0_shape hsources.rank1_shape

/-- Replicated per-head linear preserves canonical and physical zigzag orders. -/
theorem per_head_linear
    {full joined cu wSM wPM : Tensor} (rows inputDim heads headDim : Nat)
    (h : JoinedZigzagRel full joined cu
      [rows * 2, inputDim] [rows, inputDim])
    (hw : wPM.shape = [heads, headDim, inputDim])
    (hwEq : wSM = wPM)
    (hrows : 0 < rows) (hinput : 0 < inputDim)
    (hheads : 0 < heads) (hhead : 0 < headDim) :
    JoinedZigzagRel
      (fw_per_head_linear full wSM) (fw_per_head_linear joined wPM) cu
      [rows * 2, heads, headDim] [rows, heads, headDim] := by
  rcases h with ⟨row0, row1, hjoined⟩
  rcases hjoined.row with ⟨source0, source1, hsources⟩
  have hbase : GeneratedPatterns.Zigzag2Rel full row0 row1 cu
      [rows * 2, inputDim] [rows, inputDim] := ⟨source0, source1, hsources⟩
  have hrow := GeneratedPatterns.Zigzag2Rel.per_head_linear
    rows inputDim heads headDim hbase hw
    hrows hinput hheads hhead
  refine ⟨fw_per_head_linear row0 wPM, fw_per_head_linear row1 wPM, ?_⟩
  refine { row := ?_, joined_value := ?_ }
  · simpa only [hwEq] using hrow
  · rw [hjoined.joined_value]
    exact fw_per_head_mix_precision_linear_allGather0_commute_2
      row0 row1 wPM rows inputDim heads headDim
      hrows hinput hheads hhead
      hsources.rank0_shape hsources.rank1_shape hw

end JoinedZigzagRel

/-- Shared-weight embedding transports sequence-axis sharding for any positive
rank count.  No model dimensions or tensor IDs are encoded in the theorem. -/
theorem ShardedRel.fw_embedding_shared_weight_dim1
    {ids fullWeight sharedWeight : Tensor} {idsShards : List Tensor}
    {b s hidden : Nat}
    (hids : ShardedRel ids idsShards 1
      [b, s * idsShards.length] [b, s])
    (hweightEq : fullWeight = sharedWeight)
    (hweightShape : lastD sharedWeight.shape = hidden)
    (hb : 0 < b) (hs : 0 < s) (hhidden : 0 < hidden) :
    ShardedRel (fw_embedding ids fullWeight)
      (idsShards.map (fun shard => fw_embedding shard sharedWeight)) 1
      [b, s * idsShards.length, hidden] [b, s, hidden] := by
  have hK : 0 < idsShards.length := by
    cases hlist : idsShards with
    | nil => exact (hids.shards_nonempty hlist).elim
    | cons _ _ => simp
  constructor
  · rw [hweightEq, hids.full_value]
    simpa only [List.length_map] using
      fw_embedding_allGatherPrimDimN_dim1_shared_weight
        idsShards.length b s hidden idsShards sharedWeight
        hK hb hs hhidden rfl hids.shard_shapes hweightShape
  · rw [fw_embedding_shape, hids.full_shape, hweightEq, hweightShape]
    rfl
  · cases hlist : idsShards with
    | nil => exact (hids.shards_nonempty hlist).elim
    | cons _ _ => simp
  · simp
  · intro shard hshard
    rcases List.mem_map.mp hshard with ⟨source, hsource, rfl⟩
    rw [fw_embedding_shape, hids.shard_shapes source hsource, hweightShape]
    rfl
  · simp [List.set, List.getD]

/-- `FW_contiguous` is definitionally identity, so it transports an exact
ordered sharding relation without changing its shape contract. -/
theorem ShardedRel.fw_contiguous
    {full : Tensor} {shards : List Tensor} {gatherDim : Nat}
    {fullShape shardShape : Shape}
    (h : ShardedRel full shards gatherDim fullShape shardShape) :
    ShardedRel (fw_contiguous full) (shards.map fw_contiguous)
      gatherDim fullShape shardShape := by
  have hmap : shards.map TrainVerify.Denote.fw_contiguous = shards := by
    clear h
    induction shards with
    | nil => rfl
    | cons shard rest ih =>
        change TrainVerify.Denote.tensorId shard ::
          List.map TrainVerify.Denote.tensorId rest = shard :: rest
        rw [show TrainVerify.Denote.tensorId shard = shard by rfl, ih]
  rw [hmap]
  exact h

/-- Literal shape-preserving views transport an ordered sharding relation. -/
theorem ShardedRel.fw_view_id
    {full : Tensor} {shards : List Tensor} {gatherDim : Nat}
    {fullShape shardShape : Shape}
    (h : ShardedRel full shards gatherDim fullShape shardShape) :
    ShardedRel (fw_view fullShape full)
      (shards.map (fw_view shardShape)) gatherDim fullShape shardShape := by
  have hfull : fw_view fullShape full = full :=
    fw_view_id_of_shape full fullShape h.full_shape
  have hmapAux : ∀ xs : List Tensor,
      (∀ shard ∈ xs, shard.shape = shardShape) →
      xs.map (fw_view shardShape) = xs := by
    intro xs hshapes
    induction xs with
    | nil => rfl
    | cons shard rest ih =>
        simp only [List.map]
        rw [fw_view_id_of_shape shard shardShape (hshapes shard (by simp))]
        rw [ih (by
          intro item hitem
          exact hshapes item (by simp [hitem]))]
  have hmap : shards.map (fw_view shardShape) = shards :=
    hmapAux shards h.shard_shapes
  rw [hfull, hmap]
  exact h

/-- List-indexed CP2 dim-0 rank-2 sharding projects to ordinary authority. -/
theorem ShardedRel.toOrdinary2_dim0_rank2
    {full rank0 rank1 : Tensor} {rows width : Nat}
    (h : ShardedRel full [rank0, rank1] 0 [rows * 2, width] [rows, width]) :
    GeneratedPatterns.Ordinary2Rel full rank0 rank1
      [rows * 2, width] [rows, width] := {
  full_value := by simpa only [List.length_cons, List.length_nil] using h.full_value
  full_shape := h.full_shape
  rank0_shape := h.shard_shapes rank0 (by simp)
  rank1_shape := h.shard_shapes rank1 (by simp)
}

/-- CP2 rank-2 ordinary authority embeds into list-indexed dim-0 sharding. -/
theorem ShardedRel.ofOrdinary2_dim0_rank2
    {full rank0 rank1 : Tensor} {rows width : Nat}
    (h : GeneratedPatterns.Ordinary2Rel full rank0 rank1
      [rows * 2, width] [rows, width]) :
    ShardedRel full [rank0, rank1] 0 [rows * 2, width] [rows, width] := by
  refine {
    full_value := by simpa only [List.length_cons, List.length_nil] using h.full_value
    full_shape := h.full_shape
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  intro shardValue hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact h.rank0_shape
  · exact h.rank1_shape

/-- CP2 rank-3 ordinary authority embeds into list-indexed dim-0 sharding. -/
theorem ShardedRel.ofOrdinary2_dim0_rank3
    {full rank0 rank1 : Tensor} {rows d1 d2 : Nat}
    (h : GeneratedPatterns.Ordinary2Rel full rank0 rank1
      [rows * 2, d1, d2] [rows, d1, d2]) :
    ShardedRel full [rank0, rank1] 0
      [rows * 2, d1, d2] [rows, d1, d2] := by
  refine {
    full_value := by simpa only [List.length_cons, List.length_nil] using h.full_value
    full_shape := h.full_shape
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  intro shardValue hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact h.rank0_shape
  · exact h.rank1_shape

/-- Two-rank dim-0 sharding survives a literal rank-3 to rank-2 flatten. -/
theorem ShardedRel.fw_view_3d_to_2d_dim0_two
    {full rank0 rank1 : Tensor} {rows heads headDim : Nat}
    (h : ShardedRel full [rank0, rank1] 0
      [rows * 2, heads, headDim] [rows, heads, headDim])
    (hRows : 0 < rows) (hHeads : 0 < heads) (hHeadDim : 0 < headDim) :
    ShardedRel (fw_view [rows * 2, heads * headDim] full)
      [fw_view [rows, heads * headDim] rank0,
       fw_view [rows, heads * headDim] rank1] 0
      [rows * 2, heads * headDim] [rows, heads * headDim] := by
  refine {
    full_value := ?_
    full_shape := rfl
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  · rw [h.full_value]
    exact GeneratedPatterns.fw_view_allGather0_commute_cp2
      rank0 rank1 rows heads headDim hRows hHeads hHeadDim
      (h.shard_shapes rank0 (by simp))
      (h.shard_shapes rank1 (by simp))
  · intro shardValue hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> rfl

/-- The CP2 projection of rank-3 row sharding after flattening. -/
theorem ShardedRel.fw_view_3d_to_2d_ordinary_two
    {full rank0 rank1 : Tensor} {rows heads headDim : Nat}
    (h : ShardedRel full [rank0, rank1] 0
      [rows * 2, heads, headDim] [rows, heads, headDim])
    (hRows : 0 < rows) (hHeads : 0 < heads) (hHeadDim : 0 < headDim) :
    GeneratedPatterns.Ordinary2Rel
      (fw_view [rows * 2, heads * headDim] full)
      (fw_view [rows, heads * headDim] rank0)
      (fw_view [rows, heads * headDim] rank1)
      [rows * 2, heads * headDim] [rows, heads * headDim] := by
  have hout := ShardedRel.fw_view_3d_to_2d_dim0_two h hRows hHeads hHeadDim
  exact {
    full_value := by simpa only [List.length_cons, List.length_nil] using hout.full_value
    full_shape := hout.full_shape
    rank0_shape := hout.shard_shapes _ (by simp)
    rank1_shape := hout.shard_shapes _ (by simp)
  }

/-- Two-rank row sharding is preserved by a replicated rank-2 linear. -/
theorem ShardedRel.fw_linear_dim0_two_2d
    {full rank0 rank1 weight : Tensor} {rows input output : Nat}
    (h : ShardedRel full [rank0, rank1] 0
      [rows * 2, input] [rows, input])
    (hWeight : weight.shape = [output, input])
    (hRows : 0 < rows) (hInput : 0 < input) (hOutput : 0 < output) :
    ShardedRel (fw_linear full weight)
      [fw_linear rank0 weight, fw_linear rank1 weight] 0
      [rows * 2, output] [rows, output] := by
  refine {
    full_value := ?_
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  · rw [h.full_value]
    exact GeneratedPatterns.fw_linear_allGather0_commute_2_of rank0 rank1 weight rows input output
      hRows hInput hOutput
      (h.shard_shapes rank0 (by simp))
      (h.shard_shapes rank1 (by simp)) hWeight
  · rw [fw_linear_is_matmul (rows * 2) input output full weight
      h.full_shape hWeight]
    rfl
  · intro shardValue hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [fw_linear_is_matmul rows input output rank0 weight
        (h.shard_shapes rank0 (by simp)) hWeight]
      rfl
    · rw [fw_linear_is_matmul rows input output rank1 weight
        (h.shard_shapes rank1 (by simp)) hWeight]
      rfl

/-- Two-rank row sharding is preserved by replicated per-head projection. -/
theorem ShardedRel.fw_per_head_linear_dim0_two
    {full rank0 rank1 wSM wPM : Tensor}
    {rows input heads headDim : Nat}
    (h : ShardedRel full [rank0, rank1] 0
      [rows * 2, input] [rows, input])
    (hWeight : wPM.shape = [heads, headDim, input])
    (hWeightEq : wSM = wPM)
    (hRows : 0 < rows) (hInput : 0 < input)
    (hHeads : 0 < heads) (hHeadDim : 0 < headDim) :
    ShardedRel (fw_per_head_linear full wSM)
      [fw_per_head_linear rank0 wPM, fw_per_head_linear rank1 wPM] 0
      [rows * 2, heads, headDim] [rows, heads, headDim] := by
  have hOrd : GeneratedPatterns.Ordinary2Rel full rank0 rank1
      [rows * 2, input] [rows, input] := {
    full_value := by simpa only [List.length_cons, List.length_nil] using h.full_value
    full_shape := h.full_shape
    rank0_shape := h.shard_shapes rank0 (by simp)
    rank1_shape := h.shard_shapes rank1 (by simp)
  }
  have hout := Ordinary2Rel.per_head_linear rows input heads headDim
    hOrd hWeight hWeightEq hRows hInput hHeads hHeadDim
  refine {
    full_value := by simpa only [List.length_cons, List.length_nil] using hout.full_value
    full_shape := hout.full_shape
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  intro shardValue hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact hout.rank0_shape
  · exact hout.rank1_shape

/-- Two-rank row sharding is preserved by faithful GLU. -/
theorem ShardedRel.fw_glu_dim0_two_2d
    {fullX x0 x1 fullGate gate0 gate1 : Tensor} {rows hidden : Nat}
    (hX : ShardedRel fullX [x0, x1] 0
      [rows * 2, hidden] [rows, hidden])
    (hGate : ShardedRel fullGate [gate0, gate1] 0
      [rows * 2, hidden] [rows, hidden])
    (hRows : 0 < rows) (hHidden : 0 < hidden) :
    ShardedRel (fw_glu fullX fullGate)
      [fw_glu x0 gate0, fw_glu x1 gate1] 0
      [rows * 2, hidden] [rows, hidden] := by
  have hXOrd : GeneratedPatterns.Ordinary2Rel fullX x0 x1
      [rows * 2, hidden] [rows, hidden] := {
    full_value := by simpa only [List.length_cons, List.length_nil] using hX.full_value
    full_shape := hX.full_shape
    rank0_shape := hX.shard_shapes x0 (by simp)
    rank1_shape := hX.shard_shapes x1 (by simp)
  }
  have hGateOrd : GeneratedPatterns.Ordinary2Rel fullGate gate0 gate1
      [rows * 2, hidden] [rows, hidden] := {
    full_value := by simpa only [List.length_cons, List.length_nil] using hGate.full_value
    full_shape := hGate.full_shape
    rank0_shape := hGate.shard_shapes gate0 (by simp)
    rank1_shape := hGate.shard_shapes gate1 (by simp)
  }
  have hout := Ordinary2Rel.glu rows hidden hXOrd hGateOrd hRows hHidden
  refine {
    full_value := by simpa only [List.length_cons, List.length_nil] using hout.full_value
    full_shape := hout.full_shape
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  intro shardValue hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact hout.rank0_shape
  · exact hout.rank1_shape

/-- Two-rank row sharding is preserved by SwiGLU. -/
theorem ShardedRel.fw_swiglu_dim0_two_2d
    {fullA a0 a1 fullB b0 b1 : Tensor} {rows hidden : Nat}
    (hA : ShardedRel fullA [a0, a1] 0
      [rows * 2, hidden] [rows, hidden])
    (hB : ShardedRel fullB [b0, b1] 0
      [rows * 2, hidden] [rows, hidden])
    (hRows : 0 < rows) (hHidden : 0 < hidden) :
    ShardedRel (fw_swiglu fullA fullB)
      [fw_swiglu a0 b0, fw_swiglu a1 b1] 0
      [rows * 2, hidden] [rows, hidden] := by
  have hAOrd : GeneratedPatterns.Ordinary2Rel fullA a0 a1
      [rows * 2, hidden] [rows, hidden] := {
    full_value := by simpa only [List.length_cons, List.length_nil] using hA.full_value
    full_shape := hA.full_shape
    rank0_shape := hA.shard_shapes a0 (by simp)
    rank1_shape := hA.shard_shapes a1 (by simp)
  }
  have hBOrd : GeneratedPatterns.Ordinary2Rel fullB b0 b1
      [rows * 2, hidden] [rows, hidden] := {
    full_value := by simpa only [List.length_cons, List.length_nil] using hB.full_value
    full_shape := hB.full_shape
    rank0_shape := hB.shard_shapes b0 (by simp)
    rank1_shape := hB.shard_shapes b1 (by simp)
  }
  have hout := Ordinary2Rel.swiglu rows hidden hAOrd hBOrd hRows hHidden
  refine {
    full_value := by simpa only [List.length_cons, List.length_nil] using hout.full_value
    full_shape := hout.full_shape
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  intro shardValue hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact hout.rank0_shape
  · exact hout.rank1_shape

/-- Two-rank feature-sharded SwiGLU commutes with dim-1 reconstruction. -/
theorem ShardedRel.fw_swiglu_dim1_two_2d
    {gateFull upFull gate0 gate1 up0 up1 : Tensor}
    {rows shard : Nat}
    (hGate : ShardedRel gateFull [gate0, gate1] 1
      [rows, shard * 2] [rows, shard])
    (hUp : ShardedRel upFull [up0, up1] 1
      [rows, shard * 2] [rows, shard])
    (hrows : 0 < rows) (hshard : 0 < shard) :
    ShardedRel (fw_swiglu gateFull upFull)
      [fw_swiglu gate0 up0, fw_swiglu gate1 up1] 1
      [rows, shard * 2] [rows, shard] := by
  refine {
    full_value := ?_
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  · rw [hGate.full_value, hUp.full_value]
    exact fw_swiglu_allGatherDim1_two_2d gate0 gate1 up0 up1 rows shard
      hrows hshard
      (hGate.shard_shapes gate0 (by simp))
      (hGate.shard_shapes gate1 (by simp))
      (hUp.shard_shapes up0 (by simp))
      (hUp.shard_shapes up1 (by simp))
  · unfold fw_swiglu Tensor.mkShape
    exact hUp.full_shape
  · intro shardValue hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl <;> unfold fw_swiglu Tensor.mkShape
    · exact hUp.shard_shapes up0 (by simp)
    · exact hUp.shard_shapes up1 (by simp)

/-- Two-rank dim-0 RMSNorm transport for list-indexed sharding authority. -/
theorem ShardedRel.fw_rms_norm_2d
    {full rank0 rank1 fullWeight shardWeight : Tensor}
    {rows hidden : Nat}
    (h : ShardedRel full [rank0, rank1] 0
      [rows * 2, hidden] [rows, hidden])
    (hWeight : fullWeight = shardWeight)
    (hRows : 0 < rows) (hHidden : 0 < hidden) :
    ShardedRel (fw_rms_norm full fullWeight)
      [fw_rms_norm rank0 shardWeight, fw_rms_norm rank1 shardWeight] 0
      [rows * 2, hidden] [rows, hidden] := by
  have hOrd : GeneratedPatterns.Ordinary2Rel full rank0 rank1
      [rows * 2, hidden] [rows, hidden] := {
    full_value := by
      simpa only [List.length_cons, List.length_nil] using h.full_value
    full_shape := h.full_shape
    rank0_shape := h.shard_shapes rank0 (by simp)
    rank1_shape := h.shard_shapes rank1 (by simp)
  }
  have hout :=
    TrainVerify.Denote.RelationCompiler.GeneratedPatterns.Ordinary2Rel.rms_norm_2d
      hOrd hWeight hRows hHidden
  refine {
    full_value := by simpa only [List.length_cons, List.length_nil] using hout.full_value
    full_shape := hout.full_shape
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num
  }
  intro shard hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact hout.rank0_shape
  · exact hout.rank1_shape

/-- Rank-4 transpose of axes 1 and 2 preserves a dim-3 ordered sharding relation. -/
theorem ShardedRel.fw_transposeAxes_1_2_dim3_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : ShardedRel full shards 3
      [d0, d1, d2, d3 * shards.length] [d0, d1, d2, d3]) :
    ShardedRel (transposeAxes 1 2 full) (shards.map (transposeAxes 1 2)) 3
      [d0, d2, d1, d3 * shards.length] [d0, d2, d1, d3] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      transposeAxes_1_2_allGather_dim3_rank4 shards d0 d1 d2 d3
        h.shards_nonempty h.shard_shapes
  · simp [transposeAxes, Tensor.mkShape, h.full_shape, listSwapAt, List.getD, List.set]
  · intro hnil
    cases shards with
    | nil => exact h.shards_nonempty rfl
    | cons shard rest => simp at hnil
  · simp
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    simp [transposeAxes, Tensor.mkShape, h.shard_shapes source hsource,
      listSwapAt, List.getD, List.set]
  · simp [List.set, List.getD]

/-- Rank-4 transpose of axes 1 and 2 transports dim-2 sharding to dim 1. -/
theorem ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : ShardedRel full shards 2
      [d0, d1, d2 * shards.length, d3] [d0, d1, d2, d3]) :
    ShardedRel (transposeAxes 1 2 full) (shards.map (transposeAxes 1 2)) 1
      [d0, d2 * shards.length, d1, d3] [d0, d2, d1, d3] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      transposeAxes_1_2_allGather_dim2_to_dim1_rank4 shards d0 d1 d2 d3
        h.shards_nonempty h.shard_shapes
  · simp [transposeAxes, Tensor.mkShape, h.full_shape, listSwapAt, List.getD, List.set]
  · intro hnil
    cases shards with
    | nil => exact h.shards_nonempty rfl
    | cons shard rest => simp at hnil
  · simp
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    simp [transposeAxes, Tensor.mkShape, h.shard_shapes source hsource,
      listSwapAt, List.getD, List.set]
  · simp [List.set, List.getD]

/-- Rank-4 transpose of axes 2 and 3 transports dim-2 sharding to dim 3. -/
theorem ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : ShardedRel full shards 2
      [d0, d1, d2 * shards.length, d3] [d0, d1, d2, d3]) :
    ShardedRel (transposeAxes 2 3 full) (shards.map (transposeAxes 2 3)) 3
      [d0, d1, d3, d2 * shards.length] [d0, d1, d3, d2] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      transposeAxes_2_3_allGather_dim2_to_dim3_rank4 shards d0 d1 d2 d3
        h.shards_nonempty h.shard_shapes
  · simp [transposeAxes, Tensor.mkShape, h.full_shape, listSwapAt, List.getD, List.set]
  · intro hnil
    cases shards with
    | nil => exact h.shards_nonempty rfl
    | cons shard rest => simp at hnil
  · simp
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    simp [transposeAxes, Tensor.mkShape, h.shard_shapes source hsource,
      listSwapAt, List.getD, List.set]
  · simp [List.set, List.getD]

/-- Rank-4 transpose of axes 1 and 2 transports dim-1 sharding to dim 2. -/
theorem ShardedRel.fw_transposeAxes_1_2_dim1_to_dim2_rank4
    {full : Tensor} {shards : List Tensor} {d0 d1 d2 d3 : Nat}
    (h : ShardedRel full shards 1
      [d0, d1 * shards.length, d2, d3] [d0, d1, d2, d3]) :
    ShardedRel (transposeAxes 1 2 full) (shards.map (transposeAxes 1 2)) 2
      [d0, d2, d1 * shards.length, d3] [d0, d2, d1, d3] := by
  constructor
  · rw [h.full_value]
    simpa only [List.length_map] using
      transposeAxes_1_2_allGather_dim1_to_dim2_rank4 shards d0 d1 d2 d3
        h.shards_nonempty h.shard_shapes
  · simp [transposeAxes, Tensor.mkShape, h.full_shape, listSwapAt, List.getD, List.set]
  · intro hnil
    cases shards with
    | nil => exact h.shards_nonempty rfl
    | cons shard rest => simp at hnil
  · simp
  · intro shard hmem
    rcases List.mem_map.mp hmem with ⟨source, hsource, rfl⟩
    simp [transposeAxes, Tensor.mkShape, h.shard_shapes source hsource,
      listSwapAt, List.getD, List.set]
  · simp [List.set, List.getD]

/-- Exact singleton-output writer equation for the identity contiguous op. -/
theorem applyNode_fw_contiguous_out
    (g : GraphDecl) (s : Store) (rank : Nat) (inTid outTid : Tid) :
    applyNode g s
      { rank := rank, op := "OpName.FW_contiguous", ins := [inTid], outs := [outTid] }
      outTid = fw_contiguous (s inTid) := by
  unfold applyNode
  change storeSet s [(outTid, fw_contiguous (s inTid))] outTid = _
  unfold storeSet
  simp [List.find?]

/-- The value-level bridge from an ordered sharding relation to the exact
AllGather expression consumed by a joined writer.  No shape or operator
semantics are hidden here: this is precisely `ShardedRel.full_value`. -/
theorem ShardedRel.to_joined_allGather
    {full : Tensor} {shards : List Tensor} {gatherDim : Nat}
    {fullShape shardShape : Shape}
    (h : ShardedRel full shards gatherDim fullShape shardShape) :
    full = allGatherPrimDimN gatherDim shards.length 0 shards :=
  h.full_value

/-- Construct the full K-rank relation directly from immutable InitGoal
value authority plus explicit public shape contracts. -/
theorem ShardedRel.of_init_goal
    (numRanks : Nat) (g : LineageGoal) (sm pm : Store)
    (gatherDim : Nat) (fullShape shardShape : Shape)
    (hinit : InitGoalHolds numRanks g sm pm)
    (hrep : g.replicated = false)
    (hdim : g.gatherDim = gatherDim)
    (hlen : numRanks = g.tps.length)
    (hmulti : 2 ≤ g.tps.length)
    (hnonscalar :
      ((g.tps.map fun tp => pm tp.tid).head?.map fun t => t.shape).getD [] ≠ [1])
    (hfull : (sm g.ts).shape = fullShape)
    (hshards : ∀ shard ∈ (g.tps.map fun tp => pm tp.tid), shard.shape = shardShape)
    (hdimlt : gatherDim < shardShape.length)
    (hcontract :
      fullShape = shardShape.set gatherDim
        (shardShape.getD gatherDim 0 * g.tps.length)) :
    ShardedRel (sm g.ts) (g.tps.map fun tp => pm tp.tid)
      gatherDim fullShape shardShape := by
  refine {
    full_value := by
      simpa using InitGoalHolds.sharded_value numRanks g sm pm gatherDim
        hinit hrep hdim hlen hmulti hnonscalar
    full_shape := hfull
    shards_nonempty := ?_
    gather_dim_lt := hdimlt
    shard_shapes := hshards
    shape_contract := by simpa using hcontract
  }
  cases htps : g.tps with
  | nil => simp [htps] at hmulti
  | cons first rest => simp

/-- Producer-agnostic ordered reduction relation.  The contribution list is
the exact AllReduce writer input order; its length is the dynamic rank count.
Every contribution and both public/reduced values obey the same full shape. -/
structure ReductionRel (full : Tensor) (contributions : List Tensor)
    (fullShape : Shape) : Prop where
  full_value : full = allReducePrim contributions.length 0 contributions
  full_shape : full.shape = fullShape
  contributions_nonempty : contributions ≠ []
  contribution_shapes : ∀ contribution ∈ contributions, contribution.shape = fullShape
  reduced_shape :
    (allReducePrim contributions.length 0 contributions).shape = fullShape

/-- A dim-0 vocabulary-sharded embedding produces one ordered additive
contribution per weight shard. -/
theorem ShardedRel.fw_embedding_vocab_to_reduction
    {fullW ids fullOut : Tensor} {Ws contributions : List Tensor}
    {idsShape : Shape} {shard hidden : Nat}
    (hWeight : ShardedRel fullW Ws 0
      [shard * Ws.length, hidden] [shard, hidden])
    (hshard : 0 < shard) (hhidden : 0 < hidden)
    (hids : ids.shape = idsShape)
    (hFullWriter : fullOut = fw_embedding ids fullW)
    (hContributionWriters :
      contributions = List.ofFn (fun r : Fin Ws.length =>
        fw_embedding_offset (r.val * shard) ids
          (Ws.getD r.val (zeroTensor [shard, hidden])))) :
    ReductionRel fullOut contributions (idsShape ++ [hidden]) := by
  have hparts : 0 < Ws.length := by
    cases hWs : Ws with
    | nil => exact (hWeight.shards_nonempty hWs).elim
    | cons W rest => simp
  have hWsHead :
      (Ws.head?.map (fun t => t.shape)).getD [] = [shard, hidden] := by
    cases hWs : Ws with
    | nil => exact (hWeight.shards_nonempty hWs).elim
    | cons W rest =>
      simp only [List.head?, Option.map, Option.getD]
      apply hWeight.shard_shapes W
      rw [hWs]
      exact List.mem_cons_self
  have hWsShape : ∀ r (_ : r < Ws.length),
      (Ws.getD r (zeroTensor [shard, hidden])).shape = [shard, hidden] := by
    intro r hr
    rw [List.getD, List.getElem?_eq_getElem hr, Option.getD_some]
    exact hWeight.shard_shapes Ws[r] (List.getElem_mem hr)
  have hBase := TrainVerify.Denote.fw_embedding_eq_allReduce_offset_shards
    (numParts := Ws.length) (shard := shard) (hidden := hidden)
    (hparts := hparts) (hshard := hshard) (hhid := hhidden)
    (ids := ids) (Ws := Ws) (hlen := rfl)
    (hWs_head := hWsHead) (hWs_shape := hWsShape)
  have hFullValue : fullOut = allReducePrim contributions.length 0 contributions := by
    calc
      fullOut = fw_embedding ids fullW := hFullWriter
      _ = fw_embedding ids (allGatherPrimDimN 0 Ws.length 0 Ws) := by
        rw [← hWeight.full_value]
      _ = allReducePrim Ws.length 0 (List.ofFn (fun r : Fin Ws.length =>
          fw_embedding_offset (r.val * shard) ids
            (Ws.getD r.val (zeroTensor [shard, hidden])))) := hBase
      _ = allReducePrim contributions.length 0 contributions := by
        rw [hContributionWriters, List.length_ofFn]
  have hFullShape : fullOut.shape = idsShape ++ [hidden] := by
    rw [hFullWriter, fw_embedding_shape, hWeight.full_shape, hids]
    rfl
  refine {
    full_value := hFullValue
    full_shape := hFullShape
    contributions_nonempty := ?_
    contribution_shapes := ?_
    reduced_shape := ?_
  }
  · intro hnil
    have hz : contributions.length = 0 := congrArg List.length hnil
    rw [hContributionWriters, List.length_ofFn] at hz
    omega
  · intro contribution hmem
    rw [hContributionWriters] at hmem
    obtain ⟨r, hr, rfl⟩ := List.mem_iff_getElem.mp hmem
    have hrWs : r < Ws.length := by simpa only [List.length_ofFn] using hr
    rw [List.getElem_ofFn, fw_embedding_offset_shape, hWsShape r hrWs, hids]
    simp [lastD]
  · rw [← hFullValue]
    exact hFullShape

/-- The faithful CROSS_DP_WRED evaluator and the generic reduction relation use
the same pointwise sum on every nonempty ordered contribution list. -/
theorem cross_dp_wred_eq_allReducePrim (xs : List Tensor) (hne : xs ≠ []) :
    cross_dp_wred xs = allReducePrim xs.length 0 xs := by
  cases xs with
  | nil => exact (hne rfl).elim
  | cons x rest => rfl

/-- Publish the exact value consumed by the rank-0 AllReduce writer.  Producer
semantics remain outside this writer-only reconstruction theorem. -/
theorem ReductionRel.to_joined_allReduce
    {full : Tensor} {contributions : List Tensor} {fullShape : Shape}
    (h : ReductionRel full contributions fullShape) :
    full = allReducePrim contributions.length 0 contributions :=
  h.full_value

/-- A singleton reduction carries exact shared-value authority. -/
theorem ReductionRel.singleton_value
    {full x : Tensor} {fullShape : Shape}
    (h : ReductionRel full [x] fullShape) : full = x := by
  rw [h.full_value]
  apply Tensor.ext
  · rfl
  · intro idx hidx
    change idx < prodShape (allReducePrim 1 0 [x]).shape at hidx
    change valAt (allReducePrim 1 0 [x]) idx = valAt x idx
    have hshape : (allReducePrim 1 0 [x]).shape = x.shape := rfl
    rw [hshape] at hidx
    simp [allReducePrim, Tensor.mkShape, valAt, hidx]

/-- A reduced full tensor followed by exact dim-0 chunks publishes an ordinary
row-sharding relation. -/
theorem ReductionRel.to_ordinary_chunks_2d
    {full reduced out0 out1 : Tensor} {contributions : List Tensor}
    (rows hidden : Nat)
    (h : ReductionRel full contributions [rows * 2, hidden])
    (hreduced : reduced = allReducePrim contributions.length 0 contributions)
    (hout0 : out0 = chunkPrimDimN 0 2 0 reduced)
    (hout1 : out1 = chunkPrimDimN 0 2 1 reduced)
    (hrows : 0 < rows) (hhidden : 0 < hidden) :
    GeneratedPatterns.Ordinary2Rel full out0 out1
      [rows * 2, hidden] [rows, hidden] := by
  have hfullReduced : full = reduced := h.full_value.trans hreduced.symm
  have hreducedShape : reduced.shape = [rows * 2, hidden] := by
    rw [← hfullReduced]
    exact h.full_shape
  refine ⟨?_, h.full_shape, ?_, ?_⟩
  · rw [hout0, hout1, hfullReduced]
    have hreconstruct := allGatherPrimDimN_chunks_ofFn 0 2 reduced
      (by omega) (by rw [hreducedShape]; simp)
      (by rw [hreducedShape]; simp [List.getD])
    simpa only [List.ofFn_succ, List.ofFn_zero, Fin.val_zero,
      Fin.succ_zero_eq_one, Fin.val_one] using hreconstruct.symm
  · rw [hout0, chunkPrimDimN_shape 0 2 0 reduced _ hreducedShape (by omega)]
    simp
  · rw [hout1, chunkPrimDimN_shape 0 2 1 reduced _ hreducedShape (by omega)]
    simp

/-- Rank-count-polymorphic replication relation. The ordered replica list is
    authority: every PM value equals the SM value and has the same shape. -/
structure ReplicatedRel (full : Tensor) (replicas : List Tensor)
    (shape : Shape) : Prop where
  replicas_nonempty : replicas ≠ []
  full_shape : full.shape = shape
  replica_values : ∀ replica ∈ replicas, replica = full
  replica_shapes : ∀ replica ∈ replicas, replica.shape = shape

/-- A sharded relation whose ordered PM values are authenticated as the exact
chunks of the SM value. This stronger producer fact lets distant consumers use
the original chunk writers without claiming ownership of those nodes again. -/
structure ChunkedRel (full : Tensor) (chunks : List Tensor) (dim : Nat)
    (fullShape shardShape : Shape) extends
    ShardedRel full chunks dim fullShape shardShape where
  chunk_values : ∀ r, r < chunks.length →
    chunks.getD r (zeroTensor shardShape) =
      chunkPrimDimN dim chunks.length r full

/-- Build exact two-way chunk authority from two checked chunk values. -/
theorem ChunkedRel.of_chunks_two
    {full c0 c1 : Tensor} {dim : Nat} {fullShape shardShape : Shape}
    (hfullShape : full.shape = fullShape)
    (hc0Shape : c0.shape = shardShape) (hc1Shape : c1.shape = shardShape)
    (hdim : dim < shardShape.length)
    (hcontract : fullShape = shardShape.set dim (shardShape.getD dim 0 * 2))
    (hc0 : c0 = chunkPrimDimN dim 2 0 full)
    (hc1 : c1 = chunkPrimDimN dim 2 1 full) :
    ChunkedRel full [c0, c1] dim fullShape shardShape := by
  have hdimFull : dim < full.shape.length := by
    rw [hfullShape, hcontract, List.length_set]
    exact hdim
  have hdiv : full.shape.getD dim 0 % 2 = 0 := by
    rw [hfullShape, hcontract]
    simp [List.getD, List.set, hdim]
  have hreconstruct := allGatherPrimDimN_chunks_ofFn dim 2 full
    (by decide) hdimFull hdiv
  change allGatherPrimDimN dim 2 0
    [chunkPrimDimN dim 2 0 full, chunkPrimDimN dim 2 1 full] = full at hreconstruct
  refine {
    full_value := ?_
    full_shape := hfullShape
    shards_nonempty := by simp
    gather_dim_lt := hdim
    shard_shapes := ?_
    shape_contract := by simpa only [List.length_cons, List.length_nil] using hcontract
    chunk_values := ?_
  }
  · rw [hc0, hc1]
    exact hreconstruct.symm
  · intro shardValue hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · exact hc0Shape
    · exact hc1Shape
  · intro r hr
    simp only [List.length_cons, List.length_nil] at hr
    have hrCases : r = 0 ∨ r = 1 := by omega
    rcases hrCases with rfl | rfl
    · simpa only [List.length_cons, List.length_nil, List.getD_cons_zero] using hc0
    · simpa only [List.length_cons, List.length_nil, List.getD_cons_succ,
        List.getD_cons_zero] using hc1

/-- The weaker sharded projection of exact two-way chunk authority. -/
theorem ShardedRel.of_chunks_two
    {full c0 c1 : Tensor} {dim : Nat} {fullShape shardShape : Shape}
    (hfullShape : full.shape = fullShape)
    (hc0Shape : c0.shape = shardShape) (hc1Shape : c1.shape = shardShape)
    (hdim : dim < shardShape.length)
    (hcontract : fullShape = shardShape.set dim (shardShape.getD dim 0 * 2))
    (hc0 : c0 = chunkPrimDimN dim 2 0 full)
    (hc1 : c1 = chunkPrimDimN dim 2 1 full) :
    ShardedRel full [c0, c1] dim fullShape shardShape :=
  (ChunkedRel.of_chunks_two hfullShape hc0Shape hc1Shape hdim
    hcontract hc0 hc1).toShardedRel

inductive RelationFact where
  | sharded (smTid : Tid) (pmTids : List Tid) (gatherDim : Nat)
      (fullShape shardShape : Shape)
  | chunked (smTid : Tid) (pmTids : List Tid) (gatherDim : Nat)
      (fullShape shardShape : Shape)
  | reduction (smTid : Tid) (pmTids : List Tid) (fullShape : Shape)
  | replicated (smTid : Tid) (pmTids : List Tid) (shape : Shape)
  | joined (smTid pmTid : Tid) (shape : Shape)
  | ordinary (smTid pmRank0Tid pmRank1Tid : Tid) (fullShape shardShape : Shape)
  | zigzag (smTid pmRank0Tid pmRank1Tid metadataTid : Tid) (fullShape shardShape : Shape)
  | zigzagK (smTid : Tid) (pmTids : List Tid) (metadataTid : Tid)
      (fullShape shardShape : Shape)
  | zigzagFeature (smTid : Tid) (pmTids : List Tid) (metadataTid : Tid)
      (fullShape rowShardShape featureShardShape : Shape)
  | joinedZigzag (smTid joinedPmTid metadataTid : Tid)
      (fullShape rowShardShape : Shape)
  | gather (smTid pmRank0Tid pmRank1Tid dim : Tid) (fullShape shardShape : Shape)
  | joinedOrdinary (smTid pmRank0Tid pmRank1Tid joinedPmTid : Tid)
      (fullShape shardShape : Shape)
  | indexedStack (smTid pmRank0Tid pmRank1Tid : Tid)
      (sourceTids : List (Tid × Tid × Tid)) (gatherDim : Nat)
      (fullShape shardShape : Shape)
  | joinedIndexedStack (smTid pmRank0Tid pmRank1Tid joinedPmTid : Tid)
      (sourceTids : List (Tid × Tid × Tid)) (gatherDim : Nat)
      (fullShape shardShape : Shape)
  | tensorEq (leftSide : StoreSide) (leftTid : Tid) (rightSide : StoreSide) (rightTid : Tid)
  | tensorShape (side : StoreSide) (tid : Tid) (shape : Shape)
  | packedCu (side : StoreSide) (tid : Tid) (totalTokens numRanks : Nat)
  | labelBound (side : StoreSide) (tid : Tid) (length upperBound : Nat)
  | labelChunks (fullTid rank0Tid rank1Tid : Tid) (dim : Nat)
      (fullShape shardShape : Shape)
  deriving Repr, DecidableEq

def RelationFact.Holds (fact : RelationFact) (sm pm : Store) : Prop :=
  match fact with
  | .sharded smTid pmTids gatherDim fullShape shardShape =>
      ShardedRel (sm smTid) (pmTids.map pm) gatherDim fullShape shardShape
  | .chunked smTid pmTids gatherDim fullShape shardShape =>
      ChunkedRel (sm smTid) (pmTids.map pm) gatherDim fullShape shardShape
  | .reduction smTid pmTids fullShape =>
      ReductionRel (sm smTid) (pmTids.map pm) fullShape
  | .replicated smTid pmTids shape =>
      ReplicatedRel (sm smTid) (pmTids.map pm) shape
  | .joined smTid pmTid shape =>
      sm smTid = pm pmTid ∧
      (sm smTid).shape = shape ∧
      (pm pmTid).shape = shape
  | .ordinary smTid pmRank0Tid pmRank1Tid fullShape shardShape =>
      GeneratedPatterns.Ordinary2Rel (sm smTid) (pm pmRank0Tid) (pm pmRank1Tid) fullShape shardShape
  | .zigzag smTid pmRank0Tid pmRank1Tid metadataTid fullShape shardShape =>
      GeneratedPatterns.Zigzag2Rel
        (sm smTid) (pm pmRank0Tid) (pm pmRank1Tid) (pm metadataTid)
        fullShape shardShape
  | .zigzagK smTid pmTids metadataTid fullShape shardShape =>
      ZigzagKRel (sm smTid) (pmTids.map pm) (pm metadataTid) fullShape shardShape
  | .zigzagFeature smTid pmTids metadataTid fullShape rowShardShape featureShardShape =>
      ZigzagFeatureRel (sm smTid) (pmTids.map pm) (pm metadataTid)
        fullShape rowShardShape featureShardShape
  | .joinedZigzag smTid joinedPmTid metadataTid fullShape rowShardShape =>
      JoinedZigzagRel (sm smTid) (pm joinedPmTid) (pm metadataTid)
        fullShape rowShardShape
  | .gather smTid pmRank0Tid pmRank1Tid dim fullShape shardShape =>
      sm smTid = allGatherPrimDimN dim 2 0 [pm pmRank0Tid, pm pmRank1Tid] ∧
      (sm smTid).shape = fullShape ∧
      (pm pmRank0Tid).shape = shardShape ∧ (pm pmRank1Tid).shape = shardShape
  | .joinedOrdinary smTid pmRank0Tid pmRank1Tid joinedPmTid fullShape shardShape =>
      JoinedOrdinary2Rel (sm smTid) (pm pmRank0Tid) (pm pmRank1Tid)
        (pm joinedPmTid) fullShape shardShape
  | .indexedStack smTid pmRank0Tid pmRank1Tid sourceTids gatherDim fullShape shardShape =>
      IndexedStack2Rel (sm smTid) (pm pmRank0Tid) (pm pmRank1Tid)
        (sourceTids.map fun tids => (sm tids.1, pm tids.2.1, pm tids.2.2))
        gatherDim fullShape shardShape
  | .joinedIndexedStack smTid pmRank0Tid pmRank1Tid joinedPmTid sourceTids gatherDim fullShape shardShape =>
      JoinedIndexedStack2Rel (sm smTid) (pm pmRank0Tid) (pm pmRank1Tid)
        (pm joinedPmTid)
        (sourceTids.map fun tids => (sm tids.1, pm tids.2.1, pm tids.2.2))
        gatherDim fullShape shardShape
  | .tensorEq leftSide leftTid rightSide rightTid =>
      leftSide.read sm pm leftTid = rightSide.read sm pm rightTid
  | .tensorShape side tid shape =>
      (side.read sm pm tid).shape = shape
  | .packedCu side tid totalTokens numRanks =>
      ZigzagCollective.PackedCuSeqlensWF (side.read sm pm tid) totalTokens numRanks
  | .labelBound side tid length upperBound =>
      ∀ index < length, scalarToNat (valAt (side.read sm pm tid) index) < upperBound
  | .labelChunks fullTid rank0Tid rank1Tid dim fullShape shardShape =>
      pm rank0Tid = chunkPrimDimN dim 2 0 (pm fullTid) ∧
      pm rank1Tid = chunkPrimDimN dim 2 1 (pm fullTid) ∧
      (pm fullTid).shape = fullShape ∧
      (pm rank0Tid).shape = shardShape ∧ (pm rank1Tid).shape = shardShape

namespace JoinedRel

/-- Applying the same literal view to both sides of a joined equality preserves
its equality and changes both declared shapes to that literal target. -/
theorem fw_view (targetShape inputShape : Shape) {smValue pmValue : Tensor}
    (h : smValue = pmValue ∧ smValue.shape = inputShape ∧
      pmValue.shape = inputShape) :
    Denote.fw_view targetShape smValue = Denote.fw_view targetShape pmValue ∧
      (Denote.fw_view targetShape smValue).shape = targetShape ∧
      (Denote.fw_view targetShape pmValue).shape = targetShape := by
  rcases h with ⟨hValue, _, _⟩
  rw [hValue]
  exact ⟨rfl, rfl, rfl⟩

/-- Any denotational identity cast preserves a joined equality and shape. -/
theorem identity (inputShape : Shape) {smValue pmValue : Tensor}
    (h : smValue = pmValue ∧ smValue.shape = inputShape ∧
      pmValue.shape = inputShape) :
    tensorId smValue = tensorId pmValue ∧
      (tensorId smValue).shape = inputShape ∧
      (tensorId pmValue).shape = inputShape := by
  simpa only [tensorId] using h

/-- Replicated RMSNorm preserves joined equality. -/
theorem rms_norm
    {smValue pmValue wSM wPM : Tensor} (rows hidden : Nat)
    (h : smValue = pmValue ∧ smValue.shape = [rows, hidden] ∧
      pmValue.shape = [rows, hidden])
    (hwEq : wSM = wPM) :
    fw_rms_norm smValue wSM = fw_rms_norm pmValue wPM ∧
      (fw_rms_norm smValue wSM).shape = [rows, hidden] ∧
      (fw_rms_norm pmValue wPM).shape = [rows, hidden] := by
  rcases h with ⟨hValue, hSM, hPM⟩
  subst pmValue
  subst wPM
  exact ⟨rfl, ZigzagCollective.fw_rms_norm_shape_2d smValue wSM rows hidden hSM,
    ZigzagCollective.fw_rms_norm_shape_2d smValue wSM rows hidden hSM⟩

/-- Elementwise addition preserves two joined equalities. -/
theorem add
    {smA pmA smB pmB : Tensor} {shape : Shape}
    (hA : smA = pmA ∧ smA.shape = shape ∧ pmA.shape = shape)
    (hB : smB = pmB ∧ smB.shape = shape ∧ pmB.shape = shape) :
    elemwiseAdd smA smB = elemwiseAdd pmA pmB ∧
      (elemwiseAdd smA smB).shape = shape ∧
      (elemwiseAdd pmA pmB).shape = shape := by
  rcases hA with ⟨ha, hsa, hpa⟩
  rcases hB with ⟨hb, hsb, hpb⟩
  subst pmA
  subst pmB
  exact ⟨rfl, elemwiseAdd_shape_of_shapes smA smB shape hsa hsb,
    elemwiseAdd_shape_of_shapes smA smB shape hsa hsb⟩

/-- Replicated per-head linear preserves joined equality. -/
theorem per_head_linear
    {smValue pmValue wSM wPM : Tensor} (rows inputDim heads headDim : Nat)
    (h : smValue = pmValue ∧ smValue.shape = [rows, inputDim] ∧
      pmValue.shape = [rows, inputDim])
    (hw : wPM.shape = [heads, headDim, inputDim])
    (hwEq : wSM = wPM) :
    fw_per_head_linear smValue wSM = fw_per_head_linear pmValue wPM ∧
      (fw_per_head_linear smValue wSM).shape = [rows, heads, headDim] ∧
      (fw_per_head_linear pmValue wPM).shape = [rows, heads, headDim] := by
  rcases h with ⟨hValue, hSM, hPM⟩
  subst pmValue
  subst wPM
  exact ⟨rfl, ZigzagCollective.fw_per_head_linear_shape_2d smValue wSM rows inputDim heads headDim hSM hw,
    ZigzagCollective.fw_per_head_linear_shape_2d smValue wSM rows inputDim heads headDim hSM hw⟩

end JoinedRel

/-- Two-rank dim-0 weight shards produce dim-1 output shards for rank-2 linear. -/
theorem ShardedRel.fw_linear_output_dim1_two_2d
    {smActivation pmActivation fullWeight w0 w1 : Tensor}
    {rows input output : Nat}
    (hActivation : smActivation = pmActivation ∧
      smActivation.shape = [rows, input] ∧
      pmActivation.shape = [rows, input])
    (hWeight : ShardedRel fullWeight [w0, w1] 0
      [output * 2, input] [output, input])
    (hrows : 0 < rows) (hinput : 0 < input) (houtput : 0 < output) :
    ShardedRel (fw_linear smActivation fullWeight)
      [fw_linear pmActivation w0, fw_linear pmActivation w1] 1
      [rows, output * 2] [rows, output] := by
  rcases hActivation with ⟨hValue, hSmShape, hPmShape⟩
  refine {
    full_value := ?_
    full_shape := ?_
    shards_nonempty := by simp
    gather_dim_lt := by norm_num
    shard_shapes := ?_
    shape_contract := by norm_num [List.set, List.getD]
  }
  · rw [hValue, hWeight.full_value]
    exact fw_linear_2d_weight_allGather_dim0_two pmActivation w0 w1
      rows input output hrows hinput houtput hPmShape
      (hWeight.shard_shapes w0 (by simp))
      (hWeight.shard_shapes w1 (by simp))
  · rw [fw_linear_is_matmul rows input (output * 2) smActivation fullWeight
      hSmShape hWeight.full_shape]
    rfl
  · intro shardValue hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    · rw [fw_linear_is_matmul rows input output pmActivation w0
        hPmShape (hWeight.shard_shapes w0 (by simp))]
      rfl
    · rw [fw_linear_is_matmul rows input output pmActivation w1
        hPmShape (hWeight.shard_shapes w1 (by simp))]
      rfl

namespace ZigzagFeatureRel

/-- A physical joined-zigzag activation with dim-0 weight shards enters the
hybrid feature-sharded relation after rank-local output projection. -/
theorem output_sharded_linear_two
    {full joined cu fullWeight w0 w1 : Tensor}
    (rows inputDim outputFeature : Nat)
    (hinput : JoinedZigzagRel full joined cu
      [rows * 2, inputDim] [rows, inputDim])
    (hweight : ShardedRel fullWeight [w0, w1] 0
      [outputFeature * 2, inputDim] [outputFeature, inputDim])
    (hrows : 0 < rows) (hinputDim : 0 < inputDim)
    (houtput : 0 < outputFeature) :
    ZigzagFeatureRel (fw_linear full fullWeight)
      [fw_linear joined w0, fw_linear joined w1] cu
      [rows * 2, outputFeature * 2]
      [rows, outputFeature * 2]
      [rows * 2, outputFeature] := by
  rcases hinput with ⟨z0, z1, hjoined⟩
  rcases hjoined.row with ⟨source0, source1, hrowSources⟩
  have hrowRel : GeneratedPatterns.Zigzag2Rel full z0 z1 cu
      [rows * 2, inputDim] [rows, inputDim] :=
    ⟨source0, source1, hrowSources⟩
  have hrowOut := GeneratedPatterns.Zigzag2Rel.mix_precision_linear
    rows inputDim (outputFeature * 2) hrowRel hweight.full_shape
    hrows hinputDim (by omega)
  have hhead : (([z0, z1].head?.map (fun t => t.shape)).getD []) =
      [rows, inputDim] := by simp [hrowSources.rank0_shape]
  have hjoinedShape : joined.shape = [rows * 2, inputDim] := by
    rw [hjoined.joined_value,
      allGatherPrimDimN_shape 0 2 _ [rows, inputDim] hhead]
    simp [List.set, List.getD]
  have hfeature0 := ShardedRel.fw_linear_output_dim1_two_2d
    (smActivation := joined) (pmActivation := joined)
    ⟨rfl, hjoinedShape, hjoinedShape⟩ hweight
    (by omega) hinputDim houtput
  have hcommute := fw_mix_precision_linear_allGather0_commute_2
    z0 z1 fullWeight rows inputDim (outputFeature * 2)
    hrows hinputDim (by omega)
    hrowSources.rank0_shape hrowSources.rank1_shape hweight.full_shape
  have hfeature : ShardedRel
      (allGatherPrimDimN 0 2 0
        [fw_linear z0 fullWeight, fw_linear z1 fullWeight])
      [fw_linear joined w0, fw_linear joined w1] 1
      [rows * 2, outputFeature * 2] [rows * 2, outputFeature] := by
    rw [← hcommute, ← hjoined.joined_value]
    exact hfeature0
  exact ⟨fw_linear z0 fullWeight, fw_linear z1 fullWeight,
    hrowOut, hfeature⟩

end ZigzagFeatureRel

structure RelationState where
  facts : List RelationFact
  nonempty : facts ≠ []

def RelationState.Holds (state : RelationState) (sm pm : Store) : Prop :=
  ∀ fact ∈ state.facts, fact.Holds sm pm


/-- Read a binary operator result from its exact middle writer in one faithful
ordered fold; suffix nodes preserve the selected output. -/
theorem foldl_faithful_binary_writer
    (g : GraphDecl) (s : Store) (before after : List NodeDecl)
    (target : NodeDecl) (in0 in1 out : Tid) (f : Tensor → Tensor → Tensor)
    (happly : ∀ t, applyNodeDistributedFaithful g t target out = f (t in0) (t in1))
    (hAfterNil : ∀ n ∈ after, n.outs ≠ [])
    (hAfterOut : ∀ n ∈ after, out ∉ n.outs) :
    ((before ++ [target] ++ after).foldl
      (applyNodeDistributedFaithful g) s) out =
      f ((before.foldl (applyNodeDistributedFaithful g) s) in0)
        ((before.foldl (applyNodeDistributedFaithful g) s) in1) := by
  rw [List.foldl_append, List.foldl_append]
  simp only [List.foldl]
  rw [foldl_applyNodeDistributedFaithful_at_not_written
    g after _ out hAfterNil hAfterOut]
  exact happly _

/-- Binary middle-writer form whose prefix also preserves both inputs. -/
theorem foldl_faithful_binary_middle_writer
    (g : GraphDecl) (s : Store) (before after : List NodeDecl)
    (target : NodeDecl) (in0 in1 out : Tid) (f : Tensor → Tensor → Tensor)
    (happly : ∀ t, applyNodeDistributedFaithful g t target out = f (t in0) (t in1))
    (hBeforeNil : ∀ n ∈ before, n.outs ≠ [])
    (hBefore0 : ∀ n ∈ before, in0 ∉ n.outs)
    (hBefore1 : ∀ n ∈ before, in1 ∉ n.outs)
    (hAfterNil : ∀ n ∈ after, n.outs ≠ [])
    (hAfterOut : ∀ n ∈ after, out ∉ n.outs) :
    ((before ++ [target] ++ after).foldl
      (applyNodeDistributedFaithful g) s) out = f (s in0) (s in1) := by
  rw [foldl_faithful_binary_writer g s before after target
    in0 in1 out f happly hAfterNil hAfterOut]
  rw [foldl_applyNodeDistributedFaithful_at_not_written
        g before s in0 hBeforeNil hBefore0,
      foldl_applyNodeDistributedFaithful_at_not_written
        g before s in1 hBeforeNil hBefore1]

/-- Extract a target from one immutable ordered faithful fold while exposing the
exact prefix store seen by that target.  This is the base writer for mixed SCCs:
earlier nodes may legitimately produce the target's semantic inputs. -/
theorem foldl_faithful_middle_writer
    (g : GraphDecl) (s : Store) (before after : List NodeDecl)
    (target : NodeDecl) (output : Tid) (f : Store → Tensor)
    (happly : ∀ t, applyNodeDistributedFaithful g t target output = f t)
    (hAfterNil : ∀ n ∈ after, n.outs ≠ [])
    (hAfterOutput : ∀ n ∈ after, output ∉ n.outs) :
    ((before ++ [target] ++ after).foldl
      (applyNodeDistributedFaithful g) s) output =
      f (before.foldl (applyNodeDistributedFaithful g) s) := by
  rw [List.foldl_append, List.foldl_append]
  simp only [List.foldl]
  rw [foldl_applyNodeDistributedFaithful_at_not_written
    g after _ output hAfterNil hAfterOutput]
  exact happly _

/-- A value read at a target prefix agrees with the complete ordered fold when
the target and its suffix do not write that TID.  Mixed-SCC renderers combine
this with `foldl_faithful_middle_writer` to express every atomic semantic step
against one shared final store. -/
theorem foldl_faithful_prefix_read_eq_final
    (g : GraphDecl) (s : Store) (before suffix : List NodeDecl) (tid : Tid)
    (hSuffixNil : ∀ n ∈ suffix, n.outs ≠ [])
    (hSuffixTid : ∀ n ∈ suffix, tid ∉ n.outs) :
    (before.foldl (applyNodeDistributedFaithful g) s) tid =
      ((before ++ suffix).foldl (applyNodeDistributedFaithful g) s) tid := by
  rw [List.foldl_append]
  symm
  exact foldl_applyNodeDistributedFaithful_at_not_written
    g suffix _ tid hSuffixNil hSuffixTid

/-- Read a unary target from an ordered faithful fold when its prefix preserves
its input and its suffix preserves its output. -/
theorem foldl_faithful_unary_middle_writer
    (g : GraphDecl) (s : Store) (before after : List NodeDecl)
    (target : NodeDecl) (input output : Tid) (f : Tensor → Tensor)
    (happly : ∀ t, applyNodeDistributedFaithful g t target output = f (t input))
    (hBeforeNil : ∀ n ∈ before, n.outs ≠ [])
    (hBeforeInput : ∀ n ∈ before, input ∉ n.outs)
    (hAfterNil : ∀ n ∈ after, n.outs ≠ [])
    (hAfterOutput : ∀ n ∈ after, output ∉ n.outs) :
    ((before ++ [target] ++ after).foldl
      (applyNodeDistributedFaithful g) s) output = f (s input) := by
  rw [List.foldl_append, List.foldl_append]
  simp only [List.foldl]
  rw [foldl_applyNodeDistributedFaithful_at_not_written
    g after _ output hAfterNil hAfterOutput]
  rw [happly]
  congr 1
  exact foldl_applyNodeDistributedFaithful_at_not_written
    g before s input hBeforeNil hBeforeInput

/-- Read a ChunkPrim result while retaining the value produced by the ordered
prefix. Unlike `foldl_faithful_chunk_middle_writer`, the prefix may write the
chunk input; this is the form required by full-producer certificates. -/
theorem foldl_faithful_chunk_writer
    (g : GraphDecl) (s : Store) (before after : List NodeDecl)
    (rank input output dim : Nat) (hRanks : g.numRanks = 2)
    (hAfterNonempty : ∀ n ∈ after, n.outs ≠ [])
    (hAfterOutput : ∀ n ∈ after, output ∉ n.outs) :
    let target : NodeDecl :=
      { rank := rank, op := "OpName.ChunkPrim", ins := [input],
        outs := [output], params := [dim] }
    ((before ++ [target] ++ after).foldl
      (applyNodeDistributedFaithful g) s) output =
      chunkPrimDimN dim 2 rank
        (before.foldl (applyNodeDistributedFaithful g) s input) := by
  dsimp only
  rw [List.foldl_append, List.foldl_append]
  simp only [List.foldl]
  rw [foldl_applyNodeDistributedFaithful_at_not_written
    g after _ output hAfterNonempty hAfterOutput]
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
    (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
  simp [applyNodeDistributed, applyNodeRingAttn]
  rw [applyNode_chunkPrimDimN_out, hRanks]

/-- Read an exact ChunkPrim result from its middle writer in one faithful
ordered two-rank fold. -/
theorem foldl_faithful_chunk_middle_writer
    (g : GraphDecl) (s : Store) (before after : List NodeDecl)
    (rank input output dim : Nat) (hRanks : g.numRanks = 2)
    (hBeforeNonempty : ∀ n ∈ before, n.outs ≠ [])
    (hBeforeInput : ∀ n ∈ before, input ∉ n.outs)
    (hAfterNonempty : ∀ n ∈ after, n.outs ≠ [])
    (hAfterOutput : ∀ n ∈ after, output ∉ n.outs) :
    let target : NodeDecl :=
      { rank := rank, op := "OpName.ChunkPrim", ins := [input],
        outs := [output], params := [dim] }
    ((before ++ [target] ++ after).foldl
      (applyNodeDistributedFaithful g) s) output =
      chunkPrimDimN dim 2 rank (s input) := by
  dsimp only
  rw [List.foldl_append, List.foldl_append]
  simp only [List.foldl]
  rw [foldl_applyNodeDistributedFaithful_at_not_written
    g after _ output hAfterNonempty hAfterOutput]
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
    (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
  simp [applyNodeDistributed, applyNodeRingAttn]
  rw [applyNode_chunkPrimDimN_out]
  rw [hRanks]
  congr 1
  exact foldl_applyNodeDistributedFaithful_at_not_written
    g before s input hBeforeNonempty hBeforeInput

/-- Read a multiref projection from its exact middle writer in one faithful
ordered fold. Prefix nodes preserve the input and suffix nodes preserve the
selected output; no node is re-executed or reordered. -/
theorem foldl_faithful_multiref_middle_writer
    (g : GraphDecl) (s : Store) (before after : List NodeDecl)
    (rank input : Nat) (outs : List Tid) (arity output : Nat)
    (hArity : outs.length = arity) (hOutput : output ∈ outs)
    (hBeforeNonempty : ∀ n ∈ before, n.outs ≠ [])
    (hBeforeInput : ∀ n ∈ before, input ∉ n.outs)
    (hAfterNonempty : ∀ n ∈ after, n.outs ≠ [])
    (hAfterOutput : ∀ n ∈ after, output ∉ n.outs) :
    let target : NodeDecl :=
      { rank := rank, op := "OpName.FW_multiref", ins := [input],
        outs := outs, params := [arity] }
    ((before ++ [target] ++ after).foldl
      (applyNodeDistributedFaithful g) s) output = s input := by
  dsimp only
  rw [List.foldl_append, List.foldl_append]
  simp only [List.foldl]
  rw [foldl_applyNodeDistributedFaithful_at_not_written
    g after _ output hAfterNonempty hAfterOutput]
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective
    (hshuffle := by simp) (hunshuffle := by simp) (hattn := by simp)]
  simp [applyNodeDistributed, applyNodeRingAttn]
  rw [applyNode_fw_multiref_at g _ rank input outs arity hArity output hOutput]
  exact foldl_applyNodeDistributedFaithful_at_not_written
    g before s input hBeforeNonempty hBeforeInput

/-- Extend/retire a closed state with one newly proved fact.  The generated
certificate supplies only a decidable finite-list subset proof, avoiding a
large tactic case split over every retained authority fact. -/
theorem RelationState.Holds.mono_insert
    {sm pm : Store} {before after : RelationState} {fresh : RelationFact}
    (hBefore : before.Holds sm pm) (hFresh : fresh.Holds sm pm)
    (hSubset : after.facts ⊆ fresh :: before.facts) :
    after.Holds sm pm := by
  intro fact hmem
  have covered := hSubset hmem
  simp only [List.mem_cons] at covered
  rcases covered with rfl | hold
  · exact hFresh
  · exact hBefore fact hold

namespace RelationFact

def smTids : RelationFact → List Tid
  | .sharded smTid _ _ _ _ => [smTid]
  | .chunked smTid _ _ _ _ => [smTid]
  | .reduction smTid _ _ => [smTid]
  | .replicated smTid _ _ => [smTid]
  | .joined smTid _ _ => [smTid]
  | .ordinary smTid _ _ _ _ => [smTid]
  | .zigzag smTid _ _ _ _ _ => [smTid]
  | .zigzagK smTid _ _ _ _ => [smTid]
  | .zigzagFeature smTid _ _ _ _ _ => [smTid]
  | .joinedZigzag smTid _ _ _ _ => [smTid]
  | .gather smTid _ _ _ _ _ => [smTid]
  | .joinedOrdinary smTid _ _ _ _ _ => [smTid]
  | .indexedStack smTid _ _ sourceTids _ _ _ =>
      smTid :: sourceTids.map (fun tids => tids.1)
  | .joinedIndexedStack smTid _ _ _ sourceTids _ _ _ =>
      smTid :: sourceTids.map (fun tids => tids.1)
  | .tensorEq leftSide leftTid rightSide rightTid =>
      (if leftSide = .sm then [leftTid] else []) ++
      (if rightSide = .sm then [rightTid] else [])
  | .tensorShape side tid _ => if side = .sm then [tid] else []
  | .packedCu side tid _ _ => if side = .sm then [tid] else []
  | .labelBound side tid _ _ => if side = .sm then [tid] else []
  | .labelChunks _ _ _ _ _ _ => []

def pmTids : RelationFact → List Tid
  | .sharded _ pmTids _ _ _ => pmTids
  | .chunked _ pmTids _ _ _ => pmTids
  | .reduction _ pmTids _ => pmTids
  | .replicated _ pmTids _ => pmTids
  | .joined _ pmTid _ => [pmTid]
  | .ordinary _ pm0 pm1 _ _ => [pm0, pm1]
  | .zigzag _ pm0 pm1 metadataTid _ _ => [pm0, pm1, metadataTid]
  | .zigzagK _ rankTids metadataTid _ _ => rankTids ++ [metadataTid]
  | .zigzagFeature _ rankTids metadataTid _ _ _ => rankTids ++ [metadataTid]
  | .joinedZigzag _ joinedTid metadataTid _ _ => [joinedTid, metadataTid]
  | .gather _ pm0 pm1 _ _ _ => [pm0, pm1]
  | .joinedOrdinary _ pm0 pm1 joinedTid _ _ => [pm0, pm1, joinedTid]
  | .indexedStack _ pm0 pm1 sourceTids _ _ _ =>
      pm0 :: pm1 :: sourceTids.flatMap (fun tids => [tids.2.1, tids.2.2])
  | .joinedIndexedStack _ pm0 pm1 joinedTid sourceTids _ _ _ =>
      pm0 :: pm1 :: joinedTid :: sourceTids.flatMap (fun tids => [tids.2.1, tids.2.2])
  | .tensorEq leftSide leftTid rightSide rightTid =>
      (if leftSide = .pm then [leftTid] else []) ++
      (if rightSide = .pm then [rightTid] else [])
  | .tensorShape side tid _ => if side = .pm then [tid] else []
  | .packedCu side tid _ _ => if side = .pm then [tid] else []
  | .labelBound side tid _ _ => if side = .pm then [tid] else []
  | .labelChunks fullTid rank0Tid rank1Tid _ _ _ =>
      [fullTid, rank0Tid, rank1Tid]

theorem Holds.frame {fact : RelationFact} {sm pm sm' pm' : Store}
    (h : fact.Holds sm pm)
    (hsm : ∀ tid ∈ fact.smTids, sm' tid = sm tid)
    (hpm : ∀ tid ∈ fact.pmTids, pm' tid = pm tid) :
    fact.Holds sm' pm' := by
  cases fact with
  | sharded smTid rankTids gatherDim fullShape shardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp)]
      have hmap : rankTids.map pm' = rankTids.map pm := by
        apply List.map_congr_left
        exact hpm
      rw [hmap]
      exact h
  | chunked smTid rankTids gatherDim fullShape shardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp)]
      have hmap : rankTids.map pm' = rankTids.map pm := by
        apply List.map_congr_left
        exact hpm
      rw [hmap]
      exact h
  | reduction smTid contributionTids fullShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp)]
      have hmap : contributionTids.map pm' = contributionTids.map pm := by
        apply List.map_congr_left
        exact hpm
      rw [hmap]
      exact h
  | replicated smTid replicaTids shape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp)]
      have hmap : replicaTids.map pm' = replicaTids.map pm := by
        apply List.map_congr_left
        exact hpm
      rw [hmap]
      exact h
  | joined smTid pmTid shape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp), hpm _ (by simp)]
      exact h
  | ordinary smTid pm0 pm1 fullShape shardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp), hpm _ (by simp), hpm _ (by simp)]
      exact h
  | zigzag smTid pm0 pm1 metadataTid fullShape shardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp), hpm _ (by simp), hpm _ (by simp), hpm _ (by simp)]
      exact h
  | zigzagK smTid rankTids metadataTid fullShape shardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (List.mem_singleton_self _)]
      have hmap : rankTids.map pm' = rankTids.map pm := by
        apply List.map_congr_left
        intro tid htid
        exact hpm tid (List.mem_append_left _ htid)
      rw [hmap, hpm metadataTid
        (List.mem_append_right _ (List.mem_singleton_self _))]
      exact h
  | zigzagFeature smTid rankTids metadataTid fullShape rowShardShape featureShardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp)]
      have hmap : rankTids.map pm' = rankTids.map pm := by
        apply List.map_congr_left
        intro tid htid
        exact hpm tid (by simp [htid])
      rw [hmap, hpm metadataTid (by simp)]
      exact h
  | joinedZigzag smTid joinedTid metadataTid fullShape rowShardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp), hpm _ (by simp), hpm _ (by simp)]
      exact h
  | gather smTid pm0 pm1 dim fullShape shardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp), hpm _ (by simp), hpm _ (by simp)]
      exact h
  | joinedOrdinary smTid pm0 pm1 joinedTid fullShape shardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      rw [hsm _ (by simp), hpm _ (by simp), hpm _ (by simp), hpm _ (by simp)]
      exact h
  | indexedStack smTid pm0 pm1 sourceTids gatherDim fullShape shardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      have hsources :
          sourceTids.map (fun tids => (sm' tids.1, pm' tids.2.1, pm' tids.2.2)) =
            sourceTids.map (fun tids => (sm tids.1, pm tids.2.1, pm tids.2.2)) := by
        apply List.map_congr_left
        intro tids htids
        have hsmMem : tids.1 ∈ smTid :: sourceTids.map (fun item => item.1) := by
          right
          exact List.mem_map.mpr ⟨tids, htids, rfl⟩
        have hpm0Mem : tids.2.1 ∈
            pm0 :: pm1 :: sourceTids.flatMap (fun item => [item.2.1, item.2.2]) := by
          simp only [List.mem_cons, List.mem_flatMap]
          exact Or.inr (Or.inr ⟨tids, htids, by simp⟩)
        have hpm1Mem : tids.2.2 ∈
            pm0 :: pm1 :: sourceTids.flatMap (fun item => [item.2.1, item.2.2]) := by
          simp only [List.mem_cons, List.mem_flatMap]
          exact Or.inr (Or.inr ⟨tids, htids, by simp⟩)
        rw [hsm _ hsmMem, hpm _ hpm0Mem, hpm _ hpm1Mem]
      rw [hsm _ (by simp), hpm _ (by simp), hpm _ (by simp), hsources]
      exact h
  | joinedIndexedStack smTid pm0 pm1 joinedTid sourceTids gatherDim fullShape shardShape =>
      simp only [Holds, smTids, pmTids] at h hsm hpm ⊢
      have hsources :
          sourceTids.map (fun tids => (sm' tids.1, pm' tids.2.1, pm' tids.2.2)) =
            sourceTids.map (fun tids => (sm tids.1, pm tids.2.1, pm tids.2.2)) := by
        apply List.map_congr_left
        intro tids htids
        have hsmMem : tids.1 ∈ smTid :: sourceTids.map (fun item => item.1) := by
          right
          exact List.mem_map.mpr ⟨tids, htids, rfl⟩
        have hpm0Mem : tids.2.1 ∈
            pm0 :: pm1 :: joinedTid ::
              sourceTids.flatMap (fun item => [item.2.1, item.2.2]) := by
          simp only [List.mem_cons, List.mem_flatMap]
          exact Or.inr (Or.inr (Or.inr ⟨tids, htids, by simp⟩))
        have hpm1Mem : tids.2.2 ∈
            pm0 :: pm1 :: joinedTid ::
              sourceTids.flatMap (fun item => [item.2.1, item.2.2]) := by
          simp only [List.mem_cons, List.mem_flatMap]
          exact Or.inr (Or.inr (Or.inr ⟨tids, htids, by simp⟩))
        rw [hsm _ hsmMem, hpm _ hpm0Mem, hpm _ hpm1Mem]
      rw [hsm _ (by simp), hpm _ (by simp), hpm _ (by simp),
        hpm _ (by simp), hsources]
      exact h
  | tensorEq leftSide leftTid rightSide rightTid =>
      simp only [Holds, smTids, pmTids, StoreSide.read] at h hsm hpm ⊢
      split <;> split <;> simp_all
  | tensorShape side tid shape =>
      simp only [Holds, smTids, pmTids, StoreSide.read] at h hsm hpm ⊢
      split <;> simp_all
  | packedCu side tid totalTokens numRanks =>
      simp only [Holds, smTids, pmTids, StoreSide.read] at h hsm hpm ⊢
      split <;> simp_all
  | labelBound side tid length upperBound =>
      simp only [Holds, smTids, pmTids, StoreSide.read] at h hsm hpm ⊢
      split <;> simp_all
  | labelChunks fullTid rank0Tid rank1Tid dim fullShape shardShape =>
      simp only [Holds, smTids, pmTids, StoreSide.read] at h hsm hpm ⊢
      rw [hpm _ (by simp), hpm _ (by simp), hpm _ (by simp)]
      exact h

end RelationFact

namespace RelationState

theorem Holds.frame {state : RelationState} {sm pm sm' pm' : Store}
    (h : state.Holds sm pm)
    (hsm : ∀ fact ∈ state.facts, ∀ tid ∈ fact.smTids, sm' tid = sm tid)
    (hpm : ∀ fact ∈ state.facts, ∀ tid ∈ fact.pmTids, pm' tid = pm tid) :
    state.Holds sm' pm' := by
  intro fact hfact
  exact (h fact hfact).frame
    (fun tid htid => hsm fact hfact tid htid)
    (fun tid htid => hpm fact hfact tid htid)

theorem Holds.fold_frame
    {state : RelationState} {smGraph pmGraph : GraphDecl}
    (smNodes pmNodes : List NodeDecl) (sm pm : Store)
    (h : state.Holds sm pm)
    (hsmNil : ∀ node ∈ smNodes, node.outs ≠ [])
    (hpmNil : ∀ node ∈ pmNodes, node.outs ≠ [])
    (hsmWrite : ∀ fact ∈ state.facts, ∀ tid ∈ fact.smTids,
      ∀ node ∈ smNodes, tid ∉ node.outs)
    (hpmWrite : ∀ fact ∈ state.facts, ∀ tid ∈ fact.pmTids,
      ∀ node ∈ pmNodes, tid ∉ node.outs) :
    state.Holds
      (smNodes.foldl (applyNodeDistributedFaithful smGraph) sm)
      (pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pm) := by
  apply h.frame
  · intro fact hfact tid htid
    exact foldl_applyNodeDistributedFaithful_at_not_written
      smGraph smNodes sm tid hsmNil (hsmWrite fact hfact tid htid)
  · intro fact hfact tid htid
    exact foldl_applyNodeDistributedFaithful_at_not_written
      pmGraph pmNodes pm tid hpmNil (hpmWrite fact hfact tid htid)

end RelationState

structure ClosedDepSegmentCertificate
    (smGraph pmGraph : GraphDecl) (pre post : RelationState) where
  smNodes : List NodeDecl
  pmNodes : List NodeDecl
  sound : ∀ sm pm, pre.Holds sm pm → post.Holds
    (smNodes.foldl (applyNodeDistributedFaithful smGraph) sm)
    (pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pm)

/-- Equality-indexed presentation of a closed dependent segment.  Keeping the
final stores explicit prevents elaboration from repeatedly normalizing a large
literal ordered fold inside a dependent structure field. -/
structure ClosedDepSegmentCertificateEq
    (smGraph pmGraph : GraphDecl) (pre post : RelationState) where
  smNodes : List NodeDecl
  pmNodes : List NodeDecl
  sound : ∀ sm pm smFinal pmFinal,
    smFinal = smNodes.foldl (applyNodeDistributedFaithful smGraph) sm →
    pmFinal = pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pm →
    pre.Holds sm pm → post.Holds smFinal pmFinal

namespace ClosedDepSegmentCertificateEq

noncomputable def toCertificate
    {smGraph pmGraph : GraphDecl} {pre post : RelationState}
    (certificate : ClosedDepSegmentCertificateEq smGraph pmGraph pre post) :
    ClosedDepSegmentCertificate smGraph pmGraph pre post where
  smNodes := certificate.smNodes
  pmNodes := certificate.pmNodes
  sound := by
    intro sm pm hpre
    exact certificate.sound sm pm _ _ rfl rfl hpre

end ClosedDepSegmentCertificateEq

inductive ClosedDepCertificateChain (smGraph pmGraph : GraphDecl) :
    RelationState → RelationState → Type
  | nil (state : RelationState) : ClosedDepCertificateChain smGraph pmGraph state state
  | cons {pre mid post : RelationState}
      (head : ClosedDepSegmentCertificate smGraph pmGraph pre mid)
      (tail : ClosedDepCertificateChain smGraph pmGraph mid post) :
      ClosedDepCertificateChain smGraph pmGraph pre post

namespace ClosedDepCertificateChain

def smNodes {smGraph pmGraph} {pre post} :
    ClosedDepCertificateChain smGraph pmGraph pre post → List NodeDecl
  | .nil _ => []
  | .cons head tail => head.smNodes ++ tail.smNodes

def pmNodes {smGraph pmGraph} {pre post} :
    ClosedDepCertificateChain smGraph pmGraph pre post → List NodeDecl
  | .nil _ => []
  | .cons head tail => head.pmNodes ++ tail.pmNodes

theorem sound {smGraph pmGraph} {pre post}
    (chain : ClosedDepCertificateChain smGraph pmGraph pre post)
    (sm pm : Store) (h : pre.Holds sm pm) :
    post.Holds
      (chain.smNodes.foldl (applyNodeDistributedFaithful smGraph) sm)
      (chain.pmNodes.foldl (applyNodeDistributedFaithful pmGraph) pm) := by
  induction chain generalizing sm pm with
  | nil => exact h
  | cons head tail ih =>
      simp only [smNodes, pmNodes, List.foldl_append]
      exact ih _ _ (head.sound sm pm h)

end ClosedDepCertificateChain

theorem faithful_closed_dep_chain_extract
    (smGraph pmGraph : GraphDecl) {pre post : RelationState}
    (chain : ClosedDepCertificateChain smGraph pmGraph pre post)
    (initSM initPM : Store) (hInit : pre.Holds initSM initPM)
    (hSM : chain.smNodes = smGraph.nodes)
    (hPM : chain.pmNodes = pmGraph.nodes)
    (target : RelationFact) (hTarget : target ∈ post.facts) :
    target.Holds
      (denoteGraphDistributedFaithful smGraph initSM)
      (denoteGraphDistributedFaithful pmGraph initPM) := by
  unfold denoteGraphDistributedFaithful
  rw [← hSM, ← hPM]
  exact (chain.sound initSM initPM hInit) target hTarget

private theorem gather0_2d_valAt
    (numParts Lshard d1 : Nat)
    (Ws : List Tensor)
    (hparts : 0 < numParts) (hL : 0 < Lshard) (hd1 : 0 < d1)
    (hhead : (Ws.head?.map (fun t => t.shape)).getD [] = [Lshard, d1])
    (r : Nat) (hr : r < numParts)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1) :
    valAt (allGatherPrimDimN 0 numParts 0 Ws)
          ((r * Lshard + row) * d1 + col) =
      valAt (Ws.getD r (zeroTensor [Lshard, d1]))
            (row * d1 + col) := by
  have hd1_ne : d1 ≠ 0 := Nat.ne_of_gt hd1
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hE_pos : 0 < Lshard * numParts * d1 :=
    Nat.mul_pos (Nat.mul_pos hL hparts) hd1
  have hE_ne : Lshard * numParts * d1 ≠ 0 := Nat.ne_of_gt hE_pos
  have hrr : r * Lshard + row < Lshard * numParts := by
    have hsi : r * Lshard + row < (r + 1) * Lshard := by
      calc r * Lshard + row < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
    have hle : (r + 1) * Lshard ≤ numParts * Lshard := Nat.mul_le_mul_right _ hr
    calc r * Lshard + row < (r + 1) * Lshard := hsi
      _ ≤ numParts * Lshard := hle
      _ = Lshard * numParts := by ring
  have hidx_eq : (r * Lshard + row) * d1 + col
      = col + d1 * (r * Lshard + row) := by ring
  have hidx_lt_E : (r * Lshard + row) * d1 + col < Lshard * numParts * d1 := by
    rw [hidx_eq]
    calc col + d1 * (r * Lshard + row)
        < d1 + d1 * (r * Lshard + row) := by omega
      _ = d1 * (r * Lshard + row + 1) := by ring
      _ ≤ d1 * (Lshard * numParts) := Nat.mul_le_mul_left _ (by omega)
      _ = Lshard * numParts * d1 := by ring
  have hdiv_E : ((r * Lshard + row) * d1 + col) / (Lshard * numParts * d1) = 0 :=
    Nat.div_eq_of_lt hidx_lt_E
  have hmod_E : ((r * Lshard + row) * d1 + col) % (Lshard * numParts * d1)
      = (r * Lshard + row) * d1 + col := Nat.mod_eq_of_lt hidx_lt_E
  have hdiv_P : ((r * Lshard + row) * d1 + col) / d1 = r * Lshard + row := by
    rw [hidx_eq, Nat.add_mul_div_left _ _ hd1, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmod_P : ((r * Lshard + row) * d1 + col) % d1 = col := by
    rw [hidx_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  have hdiv_L : (r * Lshard + row) / Lshard = r := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hrow, Nat.zero_add]
  have hmod_L : (r * Lshard + row) % Lshard = row := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow]
  have hshape_out : (allGatherPrimDimN 0 numParts 0 Ws).shape
      = [Lshard * numParts, d1] := by
    have := allGatherPrimDimN_shape 0 numParts Ws [Lshard, d1] hhead
    simpa using this
  have hidx_lt_prod : (r * Lshard + row) * d1 + col
      < prodShape (allGatherPrimDimN 0 numParts 0 Ws).shape := by
    rw [hshape_out]
    have hpe : prodShape [Lshard * numParts, d1] = Lshard * numParts * d1 := by
      simp [prodShape, Nat.mul_assoc]
    rw [hpe]; exact hidx_lt_E
  have h0 : valAt (allGatherPrimDimN 0 numParts 0 Ws)
        ((r * Lshard + row) * d1 + col)
      = (allGatherPrimDimN 0 numParts 0 Ws).val
          ⟨(r * Lshard + row) * d1 + col, hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    hd1_ne, hL_ne, hE_ne, ite_false]
  rw [hmod_E, hdiv_E, hdiv_P, hmod_P, hdiv_L, hmod_L]
  rw [show 0 * (Lshard * d1) + row * d1 + col
        = row * d1 + col from by ring]

private theorem chunk0_2d_valAt
    (Lshard d1 : Nat) (hL : 0 < Lshard) (hd1 : 0 < d1)
    (T : Tensor) (hT : T.shape = [2 * Lshard, d1])
    (r : Nat) (hr : r < 2)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1) :
    valAt (chunkPrimDimN 0 2 r T) (row * d1 + col) =
      valAt T ((r * Lshard + row) * d1 + col) := by
  have hd1_ne : d1 ≠ 0 := Nat.ne_of_gt hd1
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hLd_pos : 0 < Lshard * d1 := Nat.mul_pos hL hd1
  have hLd_ne : Lshard * d1 ≠ 0 := Nat.ne_of_gt hLd_pos
  have hloc_eq : row * d1 + col = col + d1 * row := by ring
  have hloc_lt : row * d1 + col < Lshard * d1 := by
    rw [hloc_eq]
    calc col + d1 * row < d1 + d1 * row := by omega
      _ = d1 * (row + 1) := by ring
      _ ≤ d1 * Lshard := Nat.mul_le_mul_left _ (by omega)
      _ = Lshard * d1 := by ring
  have hdiv_S : (row * d1 + col) / (Lshard * d1) = 0 := Nat.div_eq_of_lt hloc_lt
  have hmod_S : (row * d1 + col) % (Lshard * d1) = row * d1 + col :=
    Nat.mod_eq_of_lt hloc_lt
  have hdiv_P : (row * d1 + col) / d1 = row := by
    rw [hloc_eq, Nat.add_mul_div_left _ _ hd1, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmod_P : (row * d1 + col) % d1 = col := by
    rw [hloc_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  have hrmod : r % 2 = r := Nat.mod_eq_of_lt hr
  have hsh : (2 * Lshard) / 2 = Lshard := by omega
  have hchunk_shape : (chunkPrimDimN 0 2 r T).shape = [Lshard, d1] := by
    rw [chunkPrimDimN_shape 0 2 r T [2 * Lshard, d1] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]
    rw [hsh]
  have hloc_lt_prod : row * d1 + col < prodShape (chunkPrimDimN 0 2 r T).shape := by
    rw [hchunk_shape]
    have hpe : prodShape [Lshard, d1] = Lshard * d1 := by simp [prodShape]
    rw [hpe]; exact hloc_lt
  rw [valAt_of_lt _ _ hloc_lt_prod]
  unfold chunkPrimDimN
  simp only [Tensor.mkShape, hT, List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    show ((2:Nat) = 0) = False from by decide, ite_false,
    hsh, hrmod, hd1_ne, hLd_ne]
  rw [hmod_S, hdiv_S, hdiv_P, hmod_P]
  congr 1
  ring

theorem allGather0_reconstruct_chunks_2d
    (Lshard d1 : Nat) (hL : 0 < Lshard) (hd1 : 0 < d1)
    (T : Tensor) (hT : T.shape = [2 * Lshard, d1]) :
    allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T] = T := by
  have hsh : (2 * Lshard) / 2 = Lshard := by omega
  have hc_shape : ∀ r, (chunkPrimDimN 0 2 r T).shape = [Lshard, d1] := by
    intro r
    rw [chunkPrimDimN_shape 0 2 r T [2 * Lshard, d1] hT (by omega)]
    simp only [List.set, List.getD_cons_zero]; rw [hsh]
  have hhead : (([chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].head?.map
      (fun t => t.shape)).getD []) = [Lshard, d1] := by simp [hc_shape 0]
  have hgshape : (allGatherPrimDimN 0 2 0 [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T]).shape
      = [2 * Lshard, d1] := by
    rw [allGatherPrimDimN_shape 0 2 _ [Lshard, d1] hhead]
    simp only [List.set, List.getD_cons_zero]; rw [Nat.mul_comm Lshard 2]
  apply Tensor.ext
  · rw [hgshape, hT]
  · intro idx hidx
    rw [hgshape] at hidx
    have hprod : prodShape [2 * Lshard, d1] = 2 * Lshard * d1 := by
      simp [prodShape, Nat.mul_assoc]
    rw [hprod] at hidx
    set col := idx % d1 with hcol_def
    set fullrow := idx / d1 with hfullrow_def
    have hcol : col < d1 := by rw [hcol_def]; exact Nat.mod_lt _ hd1
    have hfullrow_lt : fullrow < 2 * Lshard := by
      rw [hfullrow_def]
      apply Nat.div_lt_of_lt_mul
      calc idx < 2 * Lshard * d1 := hidx
        _ = d1 * (2 * Lshard) := by ring
    set r := fullrow / Lshard with hr_def
    set row := fullrow % Lshard with hrow_def
    have hrow : row < Lshard := by rw [hrow_def]; exact Nat.mod_lt _ hL
    have hr : r < 2 := by
      rw [hr_def]
      apply Nat.div_lt_of_lt_mul; rw [Nat.mul_comm]; exact hfullrow_lt
    have hfullrow_split : fullrow = r * Lshard + row := by
      rw [hr_def, hrow_def]; rw [Nat.mul_comm]; exact (Nat.div_add_mod fullrow Lshard).symm
    have hidx_decomp : idx = (r * Lshard + row) * d1 + col := by
      rw [← hfullrow_split]
      rw [hcol_def, hfullrow_def]
      rw [Nat.mul_comm (idx / d1) d1]
      exact (Nat.div_add_mod idx d1).symm
    rw [hidx_decomp]
    rw [gather0_2d_valAt 2 Lshard d1 _ (by omega) hL hd1 hhead r hr row hrow col hcol]
    have hgetD : [chunkPrimDimN 0 2 0 T, chunkPrimDimN 0 2 1 T].getD r (zeroTensor [Lshard, d1])
        = chunkPrimDimN 0 2 r T := by
      interval_cases r <;> rfl
    rw [hgetD]
    exact chunk0_2d_valAt Lshard d1 hL hd1 T hT r hr row hrow col hcol

private theorem allGatherPrimDimN1_of_stack_valAt_2d
    (n Lshard d1 : Nat) (as : List Tensor)
    (_hn : 0 < n) (hL : 0 < Lshard) (hd1 : 0 < d1)
    (hhead : (as.head?.map (fun t => t.shape)).getD [] = [n, Lshard, d1])
    (hshapes : ∀ r (_ : r < 2),
        (as.getD r (zeroTensor [n, Lshard, d1])).shape = [n, Lshard, d1])
    (i : Nat) (hi : i < n)
    (r : Nat) (hr : r < 2)
    (row : Nat) (hrow : row < Lshard)
    (col : Nat) (hcol : col < d1) :
    valAt (allGatherPrimDimN 1 2 0 as)
          ((i * (2 * Lshard) + (r * Lshard + row)) * d1 + col) =
      valAt (as.getD r (zeroTensor [n, Lshard, d1]))
            ((i * Lshard + row) * d1 + col) := by
  have hd1_ne : d1 ≠ 0 := Nat.ne_of_gt hd1
  have hL_ne : Lshard ≠ 0 := Nat.ne_of_gt hL
  have hE_pos : 0 < Lshard * 2 * d1 :=
    Nat.mul_pos (Nat.mul_pos hL (by omega)) hd1
  have hE_ne : Lshard * 2 * d1 ≠ 0 := Nat.ne_of_gt hE_pos
  have hR : r * Lshard + row < 2 * Lshard := by
    have hsi : r * Lshard + row < (r + 1) * Lshard := by
      calc r * Lshard + row < r * Lshard + Lshard := by omega
        _ = (r + 1) * Lshard := by ring
    have hle : (r + 1) * Lshard ≤ 2 * Lshard := Nat.mul_le_mul_right _ (by omega)
    exact lt_of_lt_of_le hsi hle
  have hmid_lt : (r * Lshard + row) * d1 + col < Lshard * 2 * d1 := by
    calc (r * Lshard + row) * d1 + col
        < (r * Lshard + row) * d1 + d1 := by omega
      _ = (r * Lshard + row + 1) * d1 := by ring
      _ ≤ (2 * Lshard) * d1 := Nat.mul_le_mul_right _ (by omega)
      _ = Lshard * 2 * d1 := by ring
  have hidx_eq_E :
      (i * (2 * Lshard) + (r * Lshard + row)) * d1 + col
      = ((r * Lshard + row) * d1 + col) + (Lshard * 2 * d1) * i := by ring
  have hdiv_E :
      ((i * (2 * Lshard) + (r * Lshard + row)) * d1 + col) / (Lshard * 2 * d1) = i := by
    rw [hidx_eq_E, Nat.add_mul_div_left _ _ hE_pos, Nat.div_eq_of_lt hmid_lt, Nat.zero_add]
  have hmod_E :
      ((i * (2 * Lshard) + (r * Lshard + row)) * d1 + col) % (Lshard * 2 * d1)
      = (r * Lshard + row) * d1 + col := by
    rw [hidx_eq_E, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmid_lt]
  have hM_eq : (r * Lshard + row) * d1 + col
      = col + d1 * (r * Lshard + row) := by ring
  have hdiv_P : ((r * Lshard + row) * d1 + col) / d1 = r * Lshard + row := by
    rw [hM_eq, Nat.add_mul_div_left _ _ hd1, Nat.div_eq_of_lt hcol, Nat.zero_add]
  have hmod_P : ((r * Lshard + row) * d1 + col) % d1 = col := by
    rw [hM_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcol]
  have hdiv_L : (r * Lshard + row) / Lshard = r := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_div_left _ _ hL, Nat.div_eq_of_lt hrow, Nat.zero_add]
  have hmod_L : (r * Lshard + row) % Lshard = row := by
    rw [show r * Lshard + row = row + Lshard * r from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrow]
  have hshape_out : (allGatherPrimDimN 1 2 0 as).shape = [n, Lshard * 2, d1] := by
    have := allGatherPrimDimN_shape 1 2 as [n, Lshard, d1] hhead
    simpa [List.set] using this
  have hidx_lt_prod :
      (i * (2 * Lshard) + (r * Lshard + row)) * d1 + col
      < prodShape (allGatherPrimDimN 1 2 0 as).shape := by
    rw [hshape_out]
    have hpe : prodShape [n, Lshard * 2, d1] = n * (Lshard * 2 * d1) := by
      simp [prodShape]; ring
    rw [hpe, hidx_eq_E]
    calc ((r * Lshard + row) * d1 + col) + (Lshard * 2 * d1) * i
        < (Lshard * 2 * d1) + (Lshard * 2 * d1) * i := by omega
      _ = (Lshard * 2 * d1) * (i + 1) := by ring
      _ ≤ (Lshard * 2 * d1) * n := Nat.mul_le_mul_left _ (by omega)
      _ = n * (Lshard * 2 * d1) := by ring
  have har_shape : (as.getD r (zeroTensor [n, Lshard, d1])).shape = [n, Lshard, d1] :=
    hshapes r hr
  have har_prod : prodShape (as.getD r (zeroTensor [n, Lshard, d1])).shape
      = n * (Lshard * d1) := by
    rw [har_shape]; simp [prodShape]; ring
  have hidx_lt_ar : (i * Lshard + row) * d1 + col
      < prodShape (as.getD r (zeroTensor [n, Lshard, d1])).shape := by
    rw [har_prod]
    have hrowlow : row * d1 + col < Lshard * d1 := by
      calc row * d1 + col < row * d1 + d1 := by omega
        _ = (row + 1) * d1 := by ring
        _ ≤ Lshard * d1 := Nat.mul_le_mul_right _ (by omega)
    calc (i * Lshard + row) * d1 + col
        = (Lshard * d1) * i + (row * d1 + col) := by ring
      _ < (Lshard * d1) * i + Lshard * d1 := by omega
      _ = (Lshard * d1) * (i + 1) := by ring
      _ ≤ (Lshard * d1) * n := Nat.mul_le_mul_left _ (by omega)
      _ = n * (Lshard * d1) := by ring
  have h0 : valAt (allGatherPrimDimN 1 2 0 as)
        ((i * (2 * Lshard) + (r * Lshard + row)) * d1 + col)
      = (allGatherPrimDimN 1 2 0 as).val
          ⟨(i * (2 * Lshard) + (r * Lshard + row)) * d1 + col, hidx_lt_prod⟩ := by
    simp [valAt, hidx_lt_prod]
  rw [h0]
  simp only [allGatherPrimDimN, Tensor.mkShape, hhead,
    List.getD_cons_succ, List.getD_cons_zero, List.drop, List.foldl, Nat.one_mul,
    hd1_ne, hL_ne, hE_ne, ite_false]
  rw [hmod_E, hdiv_E, hdiv_P, hmod_P, hdiv_L, hmod_L]
  rw [show i * (Lshard * d1) + row * d1 + col
        = (i * Lshard + row) * d1 + col from by ring]

theorem fw_stack_allGather0_dim1_commute_2d_element
    (n Lshard d1 : Nat)
    (hL : 0 < Lshard) (hd1 : 0 < d1)
    (xs ys zs : List Tensor)
    (hxlen : xs.length = n) (hylen : ys.length = n) (hzlen : zs.length = n)
    (hxhead : (xs.head?.map (fun t => t.shape)).getD [] = [Lshard, d1])
    (hyhead : (ys.head?.map (fun t => t.shape)).getD [] = [Lshard, d1])
    (hzhead : (zs.head?.map (fun t => t.shape)).getD [] = [2 * Lshard, d1])
    (hxshapes : ∀ i (_ : i < n),
      (xs.getD i (zeroTensor [Lshard, d1])).shape = [Lshard, d1])
    (hyshapes : ∀ i (_ : i < n),
      (ys.getD i (zeroTensor [Lshard, d1])).shape = [Lshard, d1])
    (hcommute : ∀ i (_ : i < n),
      zs.getD i (zeroTensor [2 * Lshard, d1]) =
      allGatherPrimDimN 0 2 0
        [xs.getD i (zeroTensor [Lshard, d1]),
         ys.getD i (zeroTensor [Lshard, d1])]) :
    fw_stack zs =
      allGatherPrimDimN 1 2 0 [fw_stack xs, fw_stack ys] := by
  have hLHS_shape : (fw_stack zs).shape = [n, 2 * Lshard, d1] := by
    have := fw_stack_shape zs [2 * Lshard, d1] hzhead; rw [hzlen] at this; exact this
  have hxstack_shape : (fw_stack xs).shape = [n, Lshard, d1] := by
    have := fw_stack_shape xs [Lshard, d1] hxhead; rw [hxlen] at this; exact this
  have hystack_shape : (fw_stack ys).shape = [n, Lshard, d1] := by
    have := fw_stack_shape ys [Lshard, d1] hyhead; rw [hylen] at this; exact this
  have hhead2 : (([fw_stack xs, fw_stack ys].head?.map (fun t => t.shape)).getD [])
      = [n, Lshard, d1] := by simp [hxstack_shape]
  have hRHS_shape : (allGatherPrimDimN 1 2 0 [fw_stack xs, fw_stack ys]).shape
      = [n, 2 * Lshard, d1] := by
    rw [allGatherPrimDimN_shape 1 2 _ [n, Lshard, d1] hhead2]
    simp only [List.set, List.getD_cons_succ, List.getD_cons_zero]
    rw [Nat.mul_comm Lshard 2]
  have hprod : prodShape [n, 2 * Lshard, d1] = n * (2 * Lshard) * d1 := by
    simp [prodShape]
  have hps3 : prodShape [2 * Lshard, d1] = 2 * Lshard * d1 := by simp [prodShape]
  have hps3xy : prodShape [Lshard, d1] = Lshard * d1 := by simp [prodShape]
  have hzshard_pos : 0 < prodShape [2 * Lshard, d1] := by rw [hps3]; positivity
  have hxyshard_pos : 0 < prodShape [Lshard, d1] := by rw [hps3xy]; positivity
  have hshapes2 : ∀ r (_ : r < 2),
      ([fw_stack xs, fw_stack ys].getD r (zeroTensor [n, Lshard, d1])).shape
        = [n, Lshard, d1] := by
    intro r hr; interval_cases r
    · simpa [List.getD] using hxstack_shape
    · simpa [List.getD] using hystack_shape
  apply Tensor.ext
  · rw [hLHS_shape, hRHS_shape]
  · intro flatIdx hflat
    rw [hLHS_shape] at hflat
    rw [hprod] at hflat
    set col := flatIdx % d1 with hcol_def
    set row := (flatIdx / d1) % (2 * Lshard) with hrow_def
    set i := flatIdx / d1 / (2 * Lshard) with hi_def
    have hcol : col < d1 := by rw [hcol_def]; exact Nat.mod_lt _ hd1
    have hrow : row < 2 * Lshard := by rw [hrow_def]; exact Nat.mod_lt _ (by omega)
    have hi : i < n := by
      rw [hi_def]
      apply Nat.div_lt_of_lt_mul
      apply Nat.div_lt_of_lt_mul
      calc flatIdx < n * (2 * Lshard) * d1 := hflat
        _ = d1 * (2 * Lshard * n) := by ring
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i) hi
    have hL1 : flatIdx = d1 * (flatIdx / d1) + col := by
      rw [hcol_def]; exact (Nat.div_add_mod flatIdx d1).symm
    have hL0 : flatIdx / d1 = (2 * Lshard) * i + row := by
      rw [hrow_def, hi_def]; exact (Nat.div_add_mod (flatIdx / d1) (2 * Lshard)).symm
    have hdecomp : flatIdx = (i * (2 * Lshard) + row) * d1 + col := by
      rw [hL1, hL0]; ring
    have hlocal : (row * d1 + col) < prodShape [2 * Lshard, d1] := by
      rw [hps3]
      calc row * d1 + col = d1 * row + col := by ring
        _ < d1 * row + d1 := by omega
        _ = d1 * (row + 1) := by ring
        _ ≤ d1 * (2 * Lshard) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 * Lshard * d1 := by ring
    have hbnd : ∀ w, w < Lshard → w * d1 + col < prodShape [Lshard, d1] := by
      intro w hw; rw [hps3xy]
      calc w * d1 + col = d1 * w + col := by ring
        _ < d1 * w + d1 := by omega
        _ = d1 * (w + 1) := by ring
        _ ≤ d1 * Lshard := Nat.mul_le_mul_left _ (by omega)
        _ = Lshard * d1 := by ring
    have hxi_shape : (xs.getD i (zeroTensor [Lshard, d1])).shape = [Lshard, d1] :=
      hxshapes i hi
    have hyi_shape : (ys.getD i (zeroTensor [Lshard, d1])).shape = [Lshard, d1] :=
      hyshapes i hi
    have hhead_inner : (([xs.getD i (zeroTensor [Lshard, d1]),
          ys.getD i (zeroTensor [Lshard, d1])].head?.map (fun t => t.shape)).getD [])
        = [Lshard, d1] := by
      simp only [List.head?, Option.map, Option.getD]; exact hxi_shape
    rw [hdecomp]
    conv_lhs => rw [show (i * (2 * Lshard) + row) * d1 + col
        = i * prodShape [2 * Lshard, d1] + (row * d1 + col)
        from by rw [hps3]; ring]
    rw [fw_stack_valAt zs [2 * Lshard, d1] hzhead hzshard_pos i
        (by rw [hzlen]; exact hi) (row * d1 + col) hlocal]
    rw [hcommute i hi]
    by_cases hrl : row < Lshard
    · conv_lhs => rw [show row * d1 + col
          = (0 * Lshard + row) * d1 + col from by ring]
      rw [gather0_2d_valAt 2 Lshard d1
          [xs.getD i (zeroTensor [Lshard, d1]), ys.getD i (zeroTensor [Lshard, d1])]
          (by omega) hL hd1 hhead_inner 0 (by omega) row hrl col hcol]
      conv_rhs => rw [show (i * (2 * Lshard) + row) * d1 + col
          = (i * (2 * Lshard) + (0 * Lshard + row)) * d1 + col from by ring]
      rw [allGatherPrimDimN1_of_stack_valAt_2d n Lshard d1 [fw_stack xs, fw_stack ys]
          hnpos hL hd1 hhead2 hshapes2 i hi 0 (by omega) row hrl col hcol]
      simp only [List.getD_cons_zero]
      rw [show (i * Lshard + row) * d1 + col
          = i * prodShape [Lshard, d1] + (row * d1 + col)
          from by rw [hps3xy]; ring]
      rw [fw_stack_valAt xs [Lshard, d1] hxhead hxyshard_pos i
          (by rw [hxlen]; exact hi) (row * d1 + col) (hbnd row hrl)]
    · have hrsub : row - Lshard < Lshard := by omega
      conv_lhs => rw [show row * d1 + col
          = (1 * Lshard + (row - Lshard)) * d1 + col
          from by rw [show 1 * Lshard + (row - Lshard) = row from by omega]]
      rw [gather0_2d_valAt 2 Lshard d1
          [xs.getD i (zeroTensor [Lshard, d1]), ys.getD i (zeroTensor [Lshard, d1])]
          (by omega) hL hd1 hhead_inner 1 (by omega) (row - Lshard) hrsub col hcol]
      conv_rhs => rw [show (i * (2 * Lshard) + row) * d1 + col
          = (i * (2 * Lshard) + (1 * Lshard + (row - Lshard))) * d1 + col
          from by rw [show 1 * Lshard + (row - Lshard) = row from by omega]]
      rw [allGatherPrimDimN1_of_stack_valAt_2d n Lshard d1 [fw_stack xs, fw_stack ys]
          hnpos hL hd1 hhead2 hshapes2 i hi 1 (by omega)
          (row - Lshard) hrsub col hcol]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [show (i * Lshard + (row - Lshard)) * d1 + col
          = i * prodShape [Lshard, d1] + ((row - Lshard) * d1 + col)
          from by rw [hps3xy]; ring]
      rw [fw_stack_valAt ys [Lshard, d1] hyhead hxyshard_pos i
          (by rw [hylen]; exact hi) ((row - Lshard) * d1 + col) (hbnd _ hrsub)]



/-- Ordinary dim-0 gather commutes with each row-local top-k routing projection. -/
theorem topk_routing_probs_allGather0_commute_two
    (a b : Tensor) (rows numExperts topK : Nat)
    (hrows : 0 < rows) (hexperts : 0 < numExperts)
    (ha : a.shape = [rows, numExperts]) (hb : b.shape = [rows, numExperts]) :
    (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) topK numExperts).1 =
      allGatherPrimDimN 0 2 0
        [(fw_topk_routing a topK numExperts).1,
         (fw_topk_routing b topK numExperts).1] :=
  GeneratedPatterns.rowLocal_allGather0_commute_2
    (fun x => (fw_topk_routing x topK numExperts).1)
    numExperts numExperts rows hexperts hexperts hrows
    (GeneratedPatterns.RowLocalShape_topk_fst numExperts topK hexperts)
    (GeneratedPatterns.RowLocalCongr_topk_fst numExperts topK hexperts)
    a b ha hb

theorem topk_routing_map_allGather0_commute_two
    (a b : Tensor) (rows numExperts topK : Nat)
    (hrows : 0 < rows) (hexperts : 0 < numExperts)
    (ha : a.shape = [rows, numExperts]) (hb : b.shape = [rows, numExperts]) :
    (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) topK numExperts).2.1 =
      allGatherPrimDimN 0 2 0
        [(fw_topk_routing a topK numExperts).2.1,
         (fw_topk_routing b topK numExperts).2.1] :=
  GeneratedPatterns.rowLocal_allGather0_commute_2
    (fun x => (fw_topk_routing x topK numExperts).2.1)
    numExperts numExperts rows hexperts hexperts hrows
    (GeneratedPatterns.RowLocalShape_topk_snd numExperts topK hexperts)
    (GeneratedPatterns.RowLocalCongr_topk_snd numExperts topK hexperts)
    a b ha hb

theorem topk_routing_gate_scores_allGather0_commute_two
    (a b : Tensor) (rows numExperts topK : Nat)
    (hrows : 0 < rows) (hexperts : 0 < numExperts)
    (ha : a.shape = [rows, numExperts]) (hb : b.shape = [rows, numExperts]) :
    (fw_topk_routing (allGatherPrimDimN 0 2 0 [a, b]) topK numExperts).2.2 =
      allGatherPrimDimN 0 2 0
        [(fw_topk_routing a topK numExperts).2.2,
         (fw_topk_routing b topK numExperts).2.2] :=
  GeneratedPatterns.rowLocal_allGather0_commute_2
    (fun x => (fw_topk_routing x topK numExperts).2.2)
    numExperts numExperts rows hexperts hexperts hrows
    (GeneratedPatterns.RowLocalShape_topk_thd numExperts topK)
    (GeneratedPatterns.RowLocalCongr_topk_thd numExperts topK hexperts)
    a b ha hb

theorem Ordinary2Rel.topk_routing_all
    {full rank0 rank1 : Tensor} (rows numExperts topK : Nat)
    (hrel : GeneratedPatterns.Ordinary2Rel full rank0 rank1
      [rows * 2, numExperts] [rows, numExperts])
    (hrows : 0 < rows) (hexperts : 0 < numExperts) :
    GeneratedPatterns.Ordinary2Rel
        (fw_topk_routing full topK numExperts).1
        (fw_topk_routing rank0 topK numExperts).1
        (fw_topk_routing rank1 topK numExperts).1
        [rows * 2, numExperts] [rows, numExperts] ∧
      GeneratedPatterns.Ordinary2Rel
        (fw_topk_routing full topK numExperts).2.1
        (fw_topk_routing rank0 topK numExperts).2.1
        (fw_topk_routing rank1 topK numExperts).2.1
        [rows * 2, numExperts] [rows, numExperts] := by
  constructor
  · constructor
    · rw [hrel.full_value]
      exact topk_routing_probs_allGather0_commute_two rank0 rank1 rows
        numExperts topK hrows hexperts hrel.rank0_shape hrel.rank1_shape
    · exact fw_topk_routing_fst_shape full topK numExperts (rows * 2)
        (by simp [hrel.full_shape])
    · exact fw_topk_routing_fst_shape rank0 topK numExperts rows
        (by simp [hrel.rank0_shape])
    · exact fw_topk_routing_fst_shape rank1 topK numExperts rows
        (by simp [hrel.rank1_shape])
  · constructor
    · rw [hrel.full_value]
      exact topk_routing_map_allGather0_commute_two rank0 rank1 rows
        numExperts topK hrows hexperts hrel.rank0_shape hrel.rank1_shape
    · exact fw_topk_routing_snd_shape full topK numExperts (rows * 2)
        (by simp [hrel.full_shape])
    · exact fw_topk_routing_snd_shape rank0 topK numExperts rows
        (by simp [hrel.rank0_shape])
    · exact fw_topk_routing_snd_shape rank1 topK numExperts rows
        (by simp [hrel.rank1_shape])

/-- Gate scores from ordinary top-k routing preserve the same two-rank row
partition as the logits. -/
theorem Ordinary2Rel.topk_routing_gate_scores
    {full rank0 rank1 : Tensor} (rows numExperts topK : Nat)
    (hrel : GeneratedPatterns.Ordinary2Rel full rank0 rank1
      [rows * 2, numExperts] [rows, numExperts])
    (hrows : 0 < rows) (hexperts : 0 < numExperts) :
    GeneratedPatterns.Ordinary2Rel
      (fw_topk_routing full topK numExperts).2.2
      (fw_topk_routing rank0 topK numExperts).2.2
      (fw_topk_routing rank1 topK numExperts).2.2
      [rows * 2, numExperts] [rows, numExperts] := by
  constructor
  · rw [hrel.full_value]
    exact topk_routing_gate_scores_allGather0_commute_two rank0 rank1 rows
      numExperts topK hrows hexperts hrel.rank0_shape hrel.rank1_shape
  · rw [fw_topk_routing_thd_shape, hrel.full_shape]
  · rw [fw_topk_routing_thd_shape, hrel.rank0_shape]
  · rw [fw_topk_routing_thd_shape, hrel.rank1_shape]

/-- The z-loss projection of inner-chunk CE is independent of labels. -/
theorem inner_chunk_ce_snd_labels_independent
    (x w y y' : Tensor) (vocab : Nat) (zScale : Scalar) :
    (fw_inner_chunk_ce x w y vocab zScale).snd =
    (fw_inner_chunk_ce x w y' vocab zScale).snd := by
  unfold fw_inner_chunk_ce
  rfl

end TrainVerify.Denote.RelationCompiler
