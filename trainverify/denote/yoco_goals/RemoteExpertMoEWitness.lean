import denote.Denote

open TrainVerify.Denote

namespace TrainVerify.Denote.RemoteExpertMoEWitness

private def input : Tensor := Tensor.mkShape [1, 1] (fun _ => 1)
private def routingProbs : Tensor := Tensor.mkShape [1, 2] (fun i => if i.1 = 1 then 1 else 0)
private def routingMap : Tensor := Tensor.mkShape [1, 2] (fun i => if i.1 = 1 then 1 else 0)
private def w13Local : Tensor := zeroTensor [1, 2, 1]
private def w2Local : Tensor := zeroTensor [1, 1, 1]
private def w13Remote : Tensor := Tensor.mkShape [1, 2, 1] (fun _ => 1)
private noncomputable def w2Remote : Tensor :=
  Tensor.mkShape [1, 1, 1] (fun _ => 15 / siluScalar 1)

private def n0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_all2all_moe_gmm",
    ins := [10, 11, 12, 13, 14], outs := [100], params := [2, 0, 1, 1, 10] }
private def n1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_all2all_moe_gmm",
    ins := [20, 21, 22, 23, 24], outs := [101], params := [2, 1, 2, 1, 10] }
private def logical : LogicalNodeId :=
  { cid := 28, mb := 0, irname := "nnscaler_all2all_moe_gmm" }
private def graph : GraphDecl :=
  { numRanks := 2, nodes := [n0, n1], replicaGroups := [{
      logical := logical,
      members := [{ rank := 0, primaryOutTid := 100 },
                  { rank := 1, primaryOutTid := 101 }] }] }

private noncomputable def store : Store := fun tid =>
  if tid = 10 then input else
  if tid = 11 then routingProbs else
  if tid = 12 then routingMap else
  if tid = 13 then w13Local else
  if tid = 14 then w2Local else
  if tid = 23 then w13Remote else
  if tid = 24 then w2Remote else
  zeroTensor []

/-- The RED counterexample: historical rank-0 local-range semantics cannot see a
    token routed exclusively to expert 1 on rank 1. -/
theorem old_local_range_remote_route_is_zero :
    valAt (fw_all2all_moe_gmm input routingProbs routingMap w13Local w2Local
      2 0 1 1 10) 0 = 0 := by
  simp [fw_all2all_moe_gmm, input, routingProbs, routingMap, w13Local,
    w2Local, valAt, prodShape, Tensor.mkShape, zeroTensor]

/-- Replica order is the declaration order and therefore fixes weight-shard
    concatenation order: local expert 0, then remote expert 1. -/
theorem exact_remote_shards_are_gathered :
    graph.replicaBuddies n0 = [n0, n1] := by decide

/-- The graph-aware production evaluator sees the remote shard and returns the
    remote expert's value 15 for rank 0's token. -/
theorem distributed_remote_expert_output :
    valAt (applyNodeFullExpertMoE_value graph store n0) 0 = 15 := by
  have hs : siluScalar (1 : Scalar) ≠ 0 := by
    unfold siluScalar sigmoidScalar
    exact mul_ne_zero one_ne_zero (ne_of_gt (Real.sigmoid_pos 1))
  unfold applyNodeFullExpertMoE_value
  rw [exact_remote_shards_are_gathered]
  simp [n0, n1, store,
    input, routingProbs, routingMap, w13Local, w2Local, w13Remote, w2Remote,
    fw_all2all_moe_gmm_full, fw_all2all_moe_gmm, allGatherPrimDimN,
    valAt, prodShape, Tensor.mkShape, zeroTensor]
  norm_num [Finset.sum_range_succ, List.getD, siluScalar] at *
  simp [List.reverse, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    siluScalar] at *
  norm_num [List.reverse, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ] at *
  field_simp [hs]

/-- The production apply-step interceptor really installs that full-expert value
    at rank 0's declared output tid; this is not merely a helper-level test. -/
theorem distributed_apply_remote_expert_output :
    valAt (applyNodeDistributed graph store n0 100) 0 = 15 := by
  calc
    valAt (applyNodeDistributed graph store n0 100) 0 =
        valAt (applyNodeFullExpertMoE_value graph store n0) 0 := by
      simpa [n0] using congrArg (fun t => valAt t 0)
        (applyNodeDistributed_moe_out graph store 0 10 11 12 13 14 100
          [2, 0, 1, 1, 10])
    _ = 15 := distributed_remote_expert_output

/-- Missing replica metadata fails closed to the local shard; it does not guess
    the same-op remote node. -/
theorem missing_metadata_is_singleton :
    let closed : GraphDecl := { numRanks := 2, nodes := [n0, n1] }
    closed.replicaBuddies n0 = [n0] ∧
      applyNodeFullExpertMoE_value closed store n0 =
        fw_all2all_moe_gmm_full input routingProbs routingMap
          [w13Local] [w2Local] 2 1 10 := by
  dsimp
  constructor
  · decide
  · apply applyNodeFullExpertMoE_value_singleton
    decide

#print axioms old_local_range_remote_route_is_zero
#print axioms distributed_remote_expert_output
#print axioms distributed_apply_remote_expert_output
#print axioms missing_metadata_is_singleton

end TrainVerify.Denote.RemoteExpertMoEWitness
