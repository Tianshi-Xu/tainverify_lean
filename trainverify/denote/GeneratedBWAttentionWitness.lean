import denote.Denote

namespace TrainVerify.Denote.GeneratedBWAttentionWitness

private def params : List Nat := [1, 1, 4, 4, 1, 0]

private def sliding0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_attn_sliding_window",
    ins := [10, 12, 14, 16, 18, 19], outs := [70, 71, 72], params := params }
private def sliding1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_attn_sliding_window",
    ins := [11, 13, 15, 17, 18, 19], outs := [73, 74, 75], params := params }
private def slidingGraph : GraphDecl :=
  { numRanks := 2, nodes := [sliding0, sliding1],
    replicaGroups := [
      { logical := { cid := 1, mb := 0, irname := "BW_attn_sliding_window" },
        members := [{ rank := 0, primaryOutTid := 70 }, { rank := 1, primaryOutTid := 73 }] }
    ] }

private def zigzag0 : NodeDecl :=
  { rank := 0, op := "OpName.BW_attn_zigzag",
    ins := [20, 22, 30, 31, 28, 29], outs := [80, 81, 82], params := params }
private def zigzag1 : NodeDecl :=
  { rank := 1, op := "OpName.BW_attn_zigzag",
    ins := [21, 23, 30, 31, 28, 29], outs := [83, 84, 85], params := params }
private def zigzagGraph : GraphDecl :=
  { numRanks := 2, nodes := [zigzag0, zigzag1],
    replicaGroups := [
      { logical := { cid := 2, mb := 0, irname := "BW_attn_zigzag" },
        members := [{ rank := 0, primaryOutTid := 80 }, { rank := 1, primaryOutTid := 83 }] }
    ] }

example : slidingGraph.replicaBuddies sliding0 = [sliding0, sliding1] := by native_decide
example : zigzagGraph.replicaBuddies zigzag0 = [zigzag0, zigzag1] := by native_decide

example (s : Store) :
    applyNodeDistributed slidingGraph s sliding0 70 =
      (applyNodeRingAttn_bw_sliding_window slidingGraph s sliding0).1 := by
  exact applyNodeDistributed_bw_attn_sliding_window_out_0
    slidingGraph s 0 10 12 14 16 18 19 70 71 72 params

example (s : Store) :
    applyNodeDistributed slidingGraph s sliding0 71 =
      (applyNodeRingAttn_bw_sliding_window slidingGraph s sliding0).2.1 := by
  exact applyNodeDistributed_bw_attn_sliding_window_out_1
    slidingGraph s 0 10 12 14 16 18 19 70 71 72 params (by decide)

example (s : Store) :
    applyNodeDistributed slidingGraph s sliding0 72 =
      (applyNodeRingAttn_bw_sliding_window slidingGraph s sliding0).2.2 := by
  exact applyNodeDistributed_bw_attn_sliding_window_out_2
    slidingGraph s 0 10 12 14 16 18 19 70 71 72 params (by decide) (by decide)

example (s : Store) :
    applyNodeDistributed zigzagGraph s zigzag0 80 =
      (applyNodeRingAttn_bw_zigzag zigzagGraph s zigzag0).1 := by
  exact applyNodeDistributed_bw_attn_zigzag_out_0
    zigzagGraph s 0 20 22 30 31 28 29 80 81 82 params

example (s : Store) :
    applyNodeDistributed zigzagGraph s zigzag0 81 =
      (applyNodeRingAttn_bw_zigzag zigzagGraph s zigzag0).2.1 := by
  exact applyNodeDistributed_bw_attn_zigzag_out_1
    zigzagGraph s 0 20 22 30 31 28 29 80 81 82 params (by decide)

example (s : Store) :
    applyNodeDistributed zigzagGraph s zigzag0 82 =
      (applyNodeRingAttn_bw_zigzag zigzagGraph s zigzag0).2.2 := by
  exact applyNodeDistributed_bw_attn_zigzag_out_2
    zigzagGraph s 0 20 22 30 31 28 29 80 81 82 params (by decide) (by decide)

example (s : Store) :
    applyNodeDistributed zigzagGraph s zigzag0 99 = s 99 := by
  exact applyNodeDistributed_skip zigzagGraph s zigzag0 99 (by decide) (by decide)

end TrainVerify.Denote.GeneratedBWAttentionWitness
