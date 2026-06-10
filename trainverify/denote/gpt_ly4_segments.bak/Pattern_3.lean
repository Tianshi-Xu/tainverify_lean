/- Auto-generated pattern proof file.
   Pattern: 3
   Hash: 9e00b7a1370ce822
   Goals: 3
-/
import denote.gpt_ly4_segments.GeneratedData

open TrainVerify.Denote
open TrainVerify.Denote.Generated

namespace TrainVerify.Denote.GeneratedPatterns

def pattern_3_goalIds : List Nat := [3]
inductive pattern_3_target : Prop → Prop
  | goal_3 : pattern_3_target goal_3_stmt

def pattern_3_stmt : Prop :=
  ∀ {target : Prop}, pattern_3_target target → target

set_option maxRecDepth 4096

private lemma chunk1_ids_valAt_1_8 (ids : Tensor) (r loc : Nat)
    (hids : ids.shape = [1, 8]) (hr : r < 4) (hloc : loc < 2) :
    valAt (chunkPrimDimN 1 4 r ids) loc = valAt ids (r * 2 + loc) := by
  have hchunk_shape : (chunkPrimDimN 1 4 r ids).shape = [1, 2] := by
    rw [chunkPrimDimN_shape 1 4 r _ _ hids (by omega)]
    simp [List.set, List.getD]
  have hloc_shape : loc < prodShape (chunkPrimDimN 1 4 r ids).shape := by
    rw [hchunk_shape]
    simp [prodShape]
    exact hloc
  rw [valAt_of_lt _ _ hloc_shape]
  unfold chunkPrimDimN Tensor.mkShape
  simp only [hids, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (4 : Nat) ≠ 0 by omega, show (2 : Nat) ≠ 0 by omega,
    show (1 : Nat) ≠ 0 by omega, ite_false]
  have hidx : loc / (8 / 4 * 1) * (8 * 1) +
      (r % 4 * (8 / 4) + loc % (8 / 4 * 1) / 1) * 1 +
        loc % (8 / 4 * 1) % 1 = r * 2 + loc := by
    omega
  rw [hidx]

private lemma valAt_ag1_embedding_chunks_1_2_32 (ids weight : Tensor) (idx : Nat)
    (hids : ids.shape = [1, 8]) (hw : weight.shape = [8, 32])
    (hidx : idx < 256) :
    valAt (allGatherPrimDimN 1 4 0
        [fw_embedding (chunkPrimDimN 1 4 0 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 1 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 2 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 3 ids) weight]) idx =
      valAt weight (scalarToNat (valAt ids (idx / 32)) * 32 + idx % 32) := by
  have hlast : lastD weight.shape = 32 := by rw [hw]; rfl
  have hchunk_shape : ∀ r, (chunkPrimDimN 1 4 r ids).shape = [1, 2] := by
    intro r
    rw [chunkPrimDimN_shape 1 4 r _ _ hids (by omega)]
    simp [List.set, List.getD]
  have hhead : (([fw_embedding (chunkPrimDimN 1 4 0 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 1 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 2 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 3 ids) weight].head?.map (fun t => t.shape)).getD []) =
      [1, 2, 32] := by
    simp [fw_embedding_shape, hchunk_shape 0, hlast]
  have hg_shape : (allGatherPrimDimN 1 4 0
      [fw_embedding (chunkPrimDimN 1 4 0 ids) weight,
       fw_embedding (chunkPrimDimN 1 4 1 ids) weight,
       fw_embedding (chunkPrimDimN 1 4 2 ids) weight,
       fw_embedding (chunkPrimDimN 1 4 3 ids) weight]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  have hgidx : idx < prodShape (allGatherPrimDimN 1 4 0
      [fw_embedding (chunkPrimDimN 1 4 0 ids) weight,
       fw_embedding (chunkPrimDimN 1 4 1 ids) weight,
       fw_embedding (chunkPrimDimN 1 4 2 ids) weight,
       fw_embedding (chunkPrimDimN 1 4 3 ids) weight]).shape := by
    rw [hg_shape]
    simp [prodShape]
    exact hidx
  rw [valAt_of_lt _ _ hgidx]
  unfold allGatherPrimDimN Tensor.mkShape
  simp only [hhead, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, List.drop, List.foldl,
    show (256 : Nat) ≠ 0 by omega, show (32 : Nat) ≠ 0 by omega,
    show (2 : Nat) ≠ 0 by omega, ite_false]
  simp only [show (2 : Nat) * 4 * (1 * 32) = 256 by norm_num,
    show (1 : Nat) * 32 = 32 by norm_num,
    show (2 : Nat) * (1 * 32) = 64 by norm_num]
  set r := idx % 256 / 32 / 2 with hr_def
  set locOut := idx / 256 * 64 + idx % 256 / 32 % 2 * 32 + idx % 32 with hlocOut_def
  have hr_lt : r < 4 := by omega
  have hlocOut_lt : locOut < 64 := by omega
  have hlocId_lt : locOut / 32 < 2 := by omega
  have hpiece : valAt
      ([fw_embedding (chunkPrimDimN 1 4 0 ids) weight,
        fw_embedding (chunkPrimDimN 1 4 1 ids) weight,
        fw_embedding (chunkPrimDimN 1 4 2 ids) weight,
        fw_embedding (chunkPrimDimN 1 4 3 ids) weight].getD r (zeroTensor [1, 2, 32])) locOut =
      valAt weight (scalarToNat (valAt ids (idx / 32)) * 32 + idx % 32) := by
    have hrange : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases hrange with hr0 | hr1 | hr2 | hr3
    · rw [hr0]
      simp only [List.getD, List.getElem?_cons_zero, Option.getD_some]
      rw [fw_embedding_valAt]
      have hlocCond0 : locOut < prodShape ((chunkPrimDimN 1 4 0 ids).shape ++ [32]) := by
        rw [hchunk_shape 0]
        simp [prodShape]
        exact hlocOut_lt
      rw [hlast, dif_pos hlocCond0]
      rw [chunk1_ids_valAt_1_8 ids 0 (locOut / 32) hids (by omega) hlocId_lt]
      have hid : 0 * 2 + locOut / 32 = idx / 32 := by rw [hlocOut_def]; omega
      have hmod : locOut % 32 = idx % 32 := by rw [hlocOut_def]; omega
      rw [hid, hmod]
    · rw [hr1]
      simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      rw [fw_embedding_valAt]
      have hlocCond1 : locOut < prodShape ((chunkPrimDimN 1 4 1 ids).shape ++ [32]) := by
        rw [hchunk_shape 1]
        simp [prodShape]
        exact hlocOut_lt
      rw [hlast, dif_pos hlocCond1]
      rw [chunk1_ids_valAt_1_8 ids 1 (locOut / 32) hids (by omega) hlocId_lt]
      have hid : 1 * 2 + locOut / 32 = idx / 32 := by rw [hlocOut_def]; omega
      have hmod : locOut % 32 = idx % 32 := by rw [hlocOut_def]; omega
      rw [hid, hmod]
    · rw [hr2]
      simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      rw [fw_embedding_valAt]
      have hlocCond2 : locOut < prodShape ((chunkPrimDimN 1 4 2 ids).shape ++ [32]) := by
        rw [hchunk_shape 2]
        simp [prodShape]
        exact hlocOut_lt
      rw [hlast, dif_pos hlocCond2]
      rw [chunk1_ids_valAt_1_8 ids 2 (locOut / 32) hids (by omega) hlocId_lt]
      have hid : 2 * 2 + locOut / 32 = idx / 32 := by rw [hlocOut_def]; omega
      have hmod : locOut % 32 = idx % 32 := by rw [hlocOut_def]; omega
      rw [hid, hmod]
    · rw [hr3]
      simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      rw [fw_embedding_valAt]
      have hlocCond3 : locOut < prodShape ((chunkPrimDimN 1 4 3 ids).shape ++ [32]) := by
        rw [hchunk_shape 3]
        simp [prodShape]
        exact hlocOut_lt
      rw [hlast, dif_pos hlocCond3]
      rw [chunk1_ids_valAt_1_8 ids 3 (locOut / 32) hids (by omega) hlocId_lt]
      have hid : 3 * 2 + locOut / 32 = idx / 32 := by rw [hlocOut_def]; omega
      have hmod : locOut % 32 = idx % 32 := by rw [hlocOut_def]; omega
      rw [hid, hmod]
  simpa [hlocOut_def, Nat.mod_eq_of_lt hidx] using hpiece

private theorem fw_embedding_split_dim1_4_1_8_32
    (ids weight : Tensor)
    (hids : ids.shape = [1, 8])
    (hw : weight.shape = [8, 32]) :
    fw_embedding ids weight =
      allGatherPrimDimN 1 4 0
        [fw_embedding (chunkPrimDimN 1 4 0 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 1 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 2 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 3 ids) weight] := by
  have hlast : lastD weight.shape = 32 := by rw [hw]; rfl
  have hchunk_shape : ∀ r, (chunkPrimDimN 1 4 r ids).shape = [1, 2] := by
    intro r
    rw [chunkPrimDimN_shape 1 4 r _ _ hids (by omega)]
    simp [List.set, List.getD]
  have hhead : (([fw_embedding (chunkPrimDimN 1 4 0 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 1 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 2 ids) weight,
         fw_embedding (chunkPrimDimN 1 4 3 ids) weight].head?.map (fun t => t.shape)).getD []) =
      [1, 2, 32] := by
    simp [fw_embedding_shape, hchunk_shape 0, hlast]
  have hfw_shape : (fw_embedding ids weight).shape = [1, 8, 32] := by
    rw [fw_embedding_shape, hids, hlast]
    rfl
  have hg_shape : (allGatherPrimDimN 1 4 0
      [fw_embedding (chunkPrimDimN 1 4 0 ids) weight,
       fw_embedding (chunkPrimDimN 1 4 1 ids) weight,
       fw_embedding (chunkPrimDimN 1 4 2 ids) weight,
       fw_embedding (chunkPrimDimN 1 4 3 ids) weight]).shape = [1, 8, 32] := by
    rw [allGatherPrimDimN_shape 1 4 _ _ hhead]
    simp [List.set, List.getD]
  apply Tensor.ext
  · rw [hfw_shape, hg_shape]
  · intro idx hidx
    have hidx' : idx < 256 := by
      rw [hfw_shape] at hidx
      simp [prodShape] at hidx
      exact hidx
    rw [fw_embedding_valAt, valAt_ag1_embedding_chunks_1_2_32 ids weight idx hids hw hidx']
    have hcond2 : idx < prodShape (ids.shape ++ [32]) := by
      rw [hids]
      simp [prodShape]
      exact hidx'
    simp only [hlast, dif_pos hcond2]

private theorem sm_eval_566 (initSM : Store) :
    denoteGraph sm initSM 566 = fw_embedding (initSM 716) (initSM 565) := by
  set n0 : NodeDecl := { rank := 0, op := "OpName.FW_embedding", ins := [714, 563], outs := [564] }
  set n1 : NodeDecl := { rank := 0, op := "OpName.FW_embedding", ins := [716, 565], outs := [566] }
  have hsub : (denoteGraph sm initSM) 566 =
      (denoteGraph { sm with nodes := sm.nodes.take 2 } initSM) 566 :=
    denoteGraph_tid_eq_of_suffix_no_writes sm initSM 566
      (sm.nodes.take 2) (sm.nodes.drop 2)
      (List.take_append_drop 2 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have h2 : ({ sm with nodes := sm.nodes.take 2 } : GraphDecl) =
      { numRanks := sm.numRanks, nodes := n0 :: n1 :: [] } := rfl
  rw [h2, denoteGraph_cons_eq sm n0, denoteGraph_cons_eq sm n1]
  change (applyNode sm (applyNode sm initSM n0) n1) 566 = _
  rw [applyNode_fw_embedding_out]
  have h716 : (applyNode sm initSM n0) 716 = initSM 716 := by
    rw [applyNode_eq_of_not_mem_outs sm initSM n0 716 (by decide)]
  have h565 : (applyNode sm initSM n0) 565 = initSM 565 := by
    rw [applyNode_eq_of_not_mem_outs sm initSM n0 565 (by decide)]
  rw [h716, h565]

private theorem applyNode_chunkPrimDimN_out
    (g : GraphDecl) (s : Store) (rank dim : Nat) (inTid outTid : Tid) :
    applyNode g s { rank := rank, op := "OpName.ChunkPrim", ins := [inTid], outs := [outTid], params := [dim] } outTid =
      chunkPrimDimN dim g.numRanks rank (s inTid) := by
  unfold applyNode
  change storeSet s [(outTid, chunkPrimDimN dim g.numRanks rank (s inTid))] outTid = _
  unfold storeSet
  simp [List.find?]

@[reducible] private def p0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_embedding", ins := [714, 1065], outs := [1069], params := [0] }
@[reducible] private def p1 : NodeDecl :=
  { rank := 0, op := "OpName.ChunkPrim", ins := [716], outs := [1085], params := [1] }
@[reducible] private def p2 : NodeDecl :=
  { rank := 1, op := "OpName.FW_embedding", ins := [714, 1066], outs := [1070], params := [32] }
@[reducible] private def p3 : NodeDecl :=
  { rank := 1, op := "OpName.ChunkPrim", ins := [716], outs := [1086], params := [1] }
@[reducible] private def p4 : NodeDecl :=
  { rank := 2, op := "OpName.FW_embedding", ins := [714, 1067], outs := [1071], params := [64] }
@[reducible] private def p5 : NodeDecl :=
  { rank := 2, op := "OpName.ChunkPrim", ins := [716], outs := [1087], params := [1] }
@[reducible] private def p6 : NodeDecl :=
  { rank := 3, op := "OpName.FW_embedding", ins := [714, 1068], outs := [1072], params := [96] }
@[reducible] private def p7 : NodeDecl :=
  { rank := 3, op := "OpName.ChunkPrim", ins := [716], outs := [1088], params := [1] }
@[reducible] private def p8 : NodeDecl :=
  { rank := 0, op := "OpName.FW_embedding", ins := [1085, 565], outs := [1089] }
@[reducible] private def p9 : NodeDecl :=
  { rank := 1, op := "OpName.FW_embedding", ins := [1086, 565], outs := [1090] }
@[reducible] private def p10 : NodeDecl :=
  { rank := 2, op := "OpName.FW_embedding", ins := [1087, 565], outs := [1091] }
@[reducible] private def p11 : NodeDecl :=
  { rank := 0, op := "OpName.AllReducePrim", ins := ((List.range 4).map (fun r => 1069 + r)), outs := [564] }
@[reducible] private def p12 : NodeDecl :=
  { rank := 3, op := "OpName.FW_embedding", ins := [1088, 565], outs := [1092] }

private theorem pm_eval_1089 (initPM : Store) :
    denoteGraph pm initPM 1089 = fw_embedding (chunkPrimDimN 1 4 0 (initPM 716)) (initPM 565) := by
  have hsub : (denoteGraph pm initPM) 1089 =
      (denoteGraph { pm with nodes := pm.nodes.take 9 } initPM) 1089 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1089
      (pm.nodes.take 9) (pm.nodes.drop 9)
      (List.take_append_drop 9 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 9 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 8 ++ [p8] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p8] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p8 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p8 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 8 } initPM) p8) 1089 = _
  rw [applyNode_fw_embedding_out]
  have h1085 : (denoteGraph { pm with nodes := pm.nodes.take 8 } initPM) 1085 =
      chunkPrimDimN 1 4 0 (initPM 716) := by
    have hpre : (denoteGraph { pm with nodes := pm.nodes.take 8 } initPM) 1085 =
        (denoteGraph { pm with nodes := pm.nodes.take 2 } initPM) 1085 :=
      denoteGraph_tid_eq_of_suffix_no_writes { pm with nodes := pm.nodes.take 8 } initPM 1085
        (pm.nodes.take 2) ((pm.nodes.take 8).drop 2) (by rfl)
        (by set_option maxRecDepth 20000 in decide)
    rw [hpre]
    have h2 : ({ pm with nodes := pm.nodes.take 2 } : GraphDecl) =
        { numRanks := pm.numRanks, nodes := p0 :: p1 :: [] } := rfl
    rw [h2, denoteGraph_cons_eq pm p0, denoteGraph_cons_eq pm p1]
    change (applyNode pm (applyNode pm initPM p0) p1) 1085 = _
    rw [applyNode_chunkPrimDimN_out]
    rw [applyNode_eq_of_not_mem_outs pm initPM p0 716 (by decide)]
    rfl
  have h565 : (denoteGraph { pm with nodes := pm.nodes.take 8 } initPM) 565 = initPM 565 := by
    exact denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 8) initPM 565
      (by set_option maxRecDepth 20000 in decide)
  rw [h1085, h565]

private theorem pm_eval_1090 (initPM : Store) :
    denoteGraph pm initPM 1090 = fw_embedding (chunkPrimDimN 1 4 1 (initPM 716)) (initPM 565) := by
  have hsub : (denoteGraph pm initPM) 1090 =
      (denoteGraph { pm with nodes := pm.nodes.take 10 } initPM) 1090 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1090
      (pm.nodes.take 10) (pm.nodes.drop 10)
      (List.take_append_drop 10 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 10 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 9 ++ [p9] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p9] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p9 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p9 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 9 } initPM) p9) 1090 = _
  rw [applyNode_fw_embedding_out]
  have h1086 : (denoteGraph { pm with nodes := pm.nodes.take 9 } initPM) 1086 =
      chunkPrimDimN 1 4 1 (initPM 716) := by
    have hpre : (denoteGraph { pm with nodes := pm.nodes.take 9 } initPM) 1086 =
        (denoteGraph { pm with nodes := pm.nodes.take 4 } initPM) 1086 :=
      denoteGraph_tid_eq_of_suffix_no_writes { pm with nodes := pm.nodes.take 9 } initPM 1086
        (pm.nodes.take 4) ((pm.nodes.take 9).drop 4) (by rfl)
        (by set_option maxRecDepth 20000 in decide)
    rw [hpre]
    have h4 : ({ pm with nodes := pm.nodes.take 4 } : GraphDecl) =
        { numRanks := pm.numRanks, nodes := p0 :: p1 :: p2 :: p3 :: [] } := rfl
    rw [h4, denoteGraph_cons_eq pm p0, denoteGraph_cons_eq pm p1,
      denoteGraph_cons_eq pm p2, denoteGraph_cons_eq pm p3]
    change (applyNode pm (applyNode pm (applyNode pm (applyNode pm initPM p0) p1) p2) p3) 1086 = _
    rw [applyNode_chunkPrimDimN_out]
    rw [applyNode_eq_of_not_mem_outs pm _ p2 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p1 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p0 716 (by decide)]
    rfl
  have h565 : (denoteGraph { pm with nodes := pm.nodes.take 9 } initPM) 565 = initPM 565 := by
    exact denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 9) initPM 565
      (by set_option maxRecDepth 20000 in decide)
  rw [h1086, h565]

private theorem pm_eval_1091 (initPM : Store) :
    denoteGraph pm initPM 1091 = fw_embedding (chunkPrimDimN 1 4 2 (initPM 716)) (initPM 565) := by
  have hsub : (denoteGraph pm initPM) 1091 =
      (denoteGraph { pm with nodes := pm.nodes.take 11 } initPM) 1091 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1091
      (pm.nodes.take 11) (pm.nodes.drop 11)
      (List.take_append_drop 11 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 11 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 10 ++ [p10] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p10] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p10 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p10 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 10 } initPM) p10) 1091 = _
  rw [applyNode_fw_embedding_out]
  have h1087 : (denoteGraph { pm with nodes := pm.nodes.take 10 } initPM) 1087 =
      chunkPrimDimN 1 4 2 (initPM 716) := by
    have hpre : (denoteGraph { pm with nodes := pm.nodes.take 10 } initPM) 1087 =
        (denoteGraph { pm with nodes := pm.nodes.take 6 } initPM) 1087 :=
      denoteGraph_tid_eq_of_suffix_no_writes { pm with nodes := pm.nodes.take 10 } initPM 1087
        (pm.nodes.take 6) ((pm.nodes.take 10).drop 6) (by rfl)
        (by set_option maxRecDepth 20000 in decide)
    rw [hpre]
    have h6 : ({ pm with nodes := pm.nodes.take 6 } : GraphDecl) =
        { numRanks := pm.numRanks, nodes := p0 :: p1 :: p2 :: p3 :: p4 :: p5 :: [] } := rfl
    rw [h6, denoteGraph_cons_eq pm p0, denoteGraph_cons_eq pm p1,
      denoteGraph_cons_eq pm p2, denoteGraph_cons_eq pm p3,
      denoteGraph_cons_eq pm p4, denoteGraph_cons_eq pm p5]
    change (applyNode pm (applyNode pm (applyNode pm (applyNode pm (applyNode pm
      (applyNode pm initPM p0) p1) p2) p3) p4) p5) 1087 = _
    rw [applyNode_chunkPrimDimN_out]
    rw [applyNode_eq_of_not_mem_outs pm _ p4 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p3 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p2 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p1 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p0 716 (by decide)]
    rfl
  have h565 : (denoteGraph { pm with nodes := pm.nodes.take 10 } initPM) 565 = initPM 565 := by
    exact denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 10) initPM 565
      (by set_option maxRecDepth 20000 in decide)
  rw [h1087, h565]

private theorem pm_eval_1092 (initPM : Store) :
    denoteGraph pm initPM 1092 = fw_embedding (chunkPrimDimN 1 4 3 (initPM 716)) (initPM 565) := by
  have hsub : (denoteGraph pm initPM) 1092 =
      (denoteGraph { pm with nodes := pm.nodes.take 13 } initPM) 1092 :=
    denoteGraph_tid_eq_of_suffix_no_writes pm initPM 1092
      (pm.nodes.take 13) (pm.nodes.drop 13)
      (List.take_append_drop 13 _).symm
      (by set_option maxRecDepth 20000 in decide)
  rw [hsub]
  have htake : ({ pm with nodes := pm.nodes.take 13 } : GraphDecl) =
      { pm with nodes := pm.nodes.take 12 ++ [p12] } := rfl
  rw [htake, denoteGraph_nodes_append]
  have hsing : ({ pm with nodes := [p12] } : GraphDecl) =
      { numRanks := pm.numRanks, nodes := p12 :: [] } := rfl
  rw [hsing, denoteGraph_cons_eq pm p12 []]
  change (applyNode pm (denoteGraph { pm with nodes := pm.nodes.take 12 } initPM) p12) 1092 = _
  rw [applyNode_fw_embedding_out]
  have h1088 : (denoteGraph { pm with nodes := pm.nodes.take 12 } initPM) 1088 =
      chunkPrimDimN 1 4 3 (initPM 716) := by
    have hpre : (denoteGraph { pm with nodes := pm.nodes.take 12 } initPM) 1088 =
        (denoteGraph { pm with nodes := pm.nodes.take 8 } initPM) 1088 :=
      denoteGraph_tid_eq_of_suffix_no_writes { pm with nodes := pm.nodes.take 12 } initPM 1088
        (pm.nodes.take 8) ((pm.nodes.take 12).drop 8) (by rfl)
        (by set_option maxRecDepth 20000 in decide)
    rw [hpre]
    have h8 : ({ pm with nodes := pm.nodes.take 8 } : GraphDecl) =
        { numRanks := pm.numRanks, nodes := p0 :: p1 :: p2 :: p3 :: p4 :: p5 :: p6 :: p7 :: [] } := rfl
    rw [h8, denoteGraph_cons_eq pm p0, denoteGraph_cons_eq pm p1,
      denoteGraph_cons_eq pm p2, denoteGraph_cons_eq pm p3,
      denoteGraph_cons_eq pm p4, denoteGraph_cons_eq pm p5,
      denoteGraph_cons_eq pm p6, denoteGraph_cons_eq pm p7]
    change (applyNode pm (applyNode pm (applyNode pm (applyNode pm (applyNode pm
      (applyNode pm (applyNode pm (applyNode pm initPM p0) p1) p2) p3) p4) p5) p6) p7) 1088 = _
    rw [applyNode_chunkPrimDimN_out]
    rw [applyNode_eq_of_not_mem_outs pm _ p6 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p5 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p4 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p3 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p2 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p1 716 (by decide),
      applyNode_eq_of_not_mem_outs pm _ p0 716 (by decide)]
    rfl
  have h565 : (denoteGraph { pm with nodes := pm.nodes.take 12 } initPM) 565 = initPM 565 := by
    exact denoteGraph_tid_eq_of_forall_not_mem_outs pm (pm.nodes.take 12) initPM 565
      (by set_option maxRecDepth 20000 in decide)
  rw [h1088, h565]

theorem prove_pattern_3 : pattern_3_stmt := by
  intro target h
  cases h
  intro initSM initPM _hSmInit _hPmInit hInitGoals
  have hInit565 : InitGoalHolds pm.numRanks initGoal_565 initSM initPM := by
    have hmem : initGoal_565 ∈ initGoals := by simp [initGoals]
    exact hInitGoals initGoal_565 hmem
  have hInit716 : InitGoalHolds pm.numRanks initGoal_716 initSM initPM := by
    have hmem : initGoal_716 ∈ initGoals := by simp [initGoals]
    exact hInitGoals initGoal_716 hmem
  obtain ⟨hSh565_sm, hSh565_pm, hRec565⟩ := hInit565
  obtain ⟨hSh716_sm, hSh716_pm, hRec716⟩ := hInit716
  have h565_sm_sh : (initSM 565).shape = [8, 32] := by
    have hh := hSh565_sm
    simp only [initGoal_565] at hh
    exact hh
  have h565_pm_sh : (initPM 565).shape = [8, 32] := by
    have hh := hSh565_pm
    simp only [initGoal_565, List.map_cons, List.map_nil, List.cons.injEq] at hh
    exact hh.1
  have h716_sm_sh : (initSM 716).shape = [1, 8] := by
    have hh := hSh716_sm
    simp only [initGoal_716] at hh
    exact hh
  have h716_pm_sh : (initPM 716).shape = [1, 8] := by
    have hh := hSh716_pm
    simp only [initGoal_716, List.map_cons, List.map_nil, List.cons.injEq] at hh
    exact hh.1
  have h565_eq : initSM 565 = initPM 565 := by
    have hh := hRec565
    simp only [initGoal_565, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
    exact hh
  have h716_eq : initSM 716 = initPM 716 := by
    have hh := hRec716
    simp only [initGoal_716, List.map_cons, List.map_nil, reconstructWithDim_singleton] at hh
    exact hh
  refine ⟨?_, ?_, ?_⟩
  · show (denoteGraph sm initSM 566).shape = [1, 8, 32]
    rw [sm_eval_566, fw_embedding_shape, h716_sm_sh, h565_sm_sh]
    rfl
  · show List.map (fun t => Tensor.shape t)
        ([({ rank := 0, tid := 1089 } : Piece), { rank := 1, tid := 1090 },
          { rank := 2, tid := 1091 }, { rank := 3, tid := 1092 }].map
          (fun p => denoteGraph pm initPM p.tid)) =
        [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]]
    simp only [List.map_cons, List.map_nil]
    rw [pm_eval_1089, pm_eval_1090, pm_eval_1091, pm_eval_1092]
    repeat rw [fw_embedding_shape]
    rw [chunkPrimDimN_shape 1 4 0 _ _ h716_pm_sh (by omega)]
    rw [chunkPrimDimN_shape 1 4 1 _ _ h716_pm_sh (by omega)]
    rw [chunkPrimDimN_shape 1 4 2 _ _ h716_pm_sh (by omega)]
    rw [chunkPrimDimN_shape 1 4 3 _ _ h716_pm_sh (by omega)]
    rw [h565_pm_sh]
    change [[1, 2] ++ [32], [1, 2] ++ [32], [1, 2] ++ [32], [1, 2] ++ [32]] =
      [[1, 2, 32], [1, 2, 32], [1, 2, 32], [1, 2, 32]]
    simp [List.set, List.getD]
  · show denoteGraph sm initSM 566 =
        reconstructWithDim 1 pm.numRanks 0
          ([({ rank := 0, tid := 1089 } : Piece), { rank := 1, tid := 1090 },
            { rank := 2, tid := 1091 }, { rank := 3, tid := 1092 }].map
            (fun p => denoteGraph pm initPM p.tid))
    simp only [List.map_cons, List.map_nil]
    rw [sm_eval_566, pm_eval_1089, pm_eval_1090, pm_eval_1091, pm_eval_1092]
    rw [h716_eq, h565_eq]
    rw [show pm.numRanks = 4 from rfl]
    rw [reconstructWithDim_cons_cons_nonscalar]
    · exact fw_embedding_split_dim1_4_1_8_32 (initPM 716) (initPM 565) h716_pm_sh h565_pm_sh
    · rw [fw_embedding_shape]
      rw [chunkPrimDimN_shape 1 4 0 _ _ h716_pm_sh (by omega)]
      rw [h565_pm_sh]
      simp [List.set, List.getD]

end TrainVerify.Denote.GeneratedPatterns
