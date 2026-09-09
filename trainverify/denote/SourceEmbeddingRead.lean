import denote.SourceInitialInputRead

/-!
Uncompiled candidate: read an ordinary source FW_embedding producer in the SAME
final Store of the original successful runWithInputs. The exact source node has
two ordered inputs, one output, empty params, and an explicit global request.
This is the bounded source-rendered Denote domain, not a Torch refinement claim.

The actual1 source world uses this schema (e.g. SM [1262,1212] -> [1265],
PM [75,16] -> [89]). Verdict/runtime_world.py checks the ordinary embedding
arity, start = 0, and supported kwargs; runtime_lineage.py further checks the
full vocabulary range. Nonempty offset params are deliberately not covered.

Schedule output uniqueness proves only output nonoverwrite. Operand liveness
is a separate structural obligation over the selected node AND its suffix;
no incoming value, producer relation, or alternate Store is postulated.
-/
namespace TrainVerify.Denote.SourceEmbeddingRead
open SourceScopedEval
noncomputable section
set_option maxHeartbeats 500000

/-- Exact ordinary dispatcher equation, with no rank-zero restriction. -/
theorem step_embedding
    (g : GraphDecl) (peer : Nat → Tid) (s : Store)
    (rank : Nat) (ids weight out : Tid) :
    stepWithInputs g .global peer s
      { rank := rank, op := "OpName.FW_embedding", ins := [ids, weight],
        outs := [out], params := [] } none =
      some (applyNode g s
        { rank := rank, op := "OpName.FW_embedding", ins := [ids, weight],
          outs := [out], params := [] }) := by
  rw [stepWithInputs_ordinary _ _ _ _ _
    (by change "OpName.FW_embedding" ≠ "OpName.DATALOADER"; decide)]
  exact step_global _ _ _ _ (by change ordinary "OpName.FW_embedding" = true; decide)

/-- The original successful run determines the final producer value. The caller
supplies the exact source occurrence and structural operand nonwrites; success
supplies InputSchedule, hence output nonoverwrite. In particular, Nodup is NOT
used to infer that ordinary operands remain live. -/
theorem embedding_value_of_split
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (n : NodeDecl)
    (rank : Nat) (ids weight out : Tid) (s t : Store)
    (hnode : n =
      { rank := rank, op := "OpName.FW_embedding", ins := [ids, weight],
        outs := [out], params := [] })
    (hsplit : requests = before ++ (n, none) :: after)
    (hscope : scope n = .global)
    (hids : ∀ row ∈ (n, none) :: after, ids ∉ row.1.outs)
    (hweight : ∀ row ∈ (n, none) :: after, weight ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t out = fw_embedding (t ids) (t weight) := by
  change (if InputSchedule nodes requests then
    runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
      requests (some s) else none) = some t at hrun
  split at hrun
  · rename_i hschedule
    have hout : out ∈ n.outs := by
      rw [hnode]
      exact List.mem_cons_self
    have hfresh : ∀ row ∈ after, out ∉ row.1.outs :=
      SourceInitialInputRead.inputSchedule_not_written_after nodes requests before after
        (n, none) out hschedule hsplit hout
    rw [hsplit, SourceScopedPrefix.runUsing_append] at hrun
    cases hb : runUsing
        (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
        before (some s) with
    | none =>
      rw [hb, runUsing_none] at hrun
      contradiction
    | some middle =>
      rw [hb] at hrun
      -- Frame the whole remaining run BEFORE consuming the embedding node.
      have hidsFinal : t ids = middle ids :=
        SourceScopedPrefix.frame g scope peer ((n, none) :: after) middle t
          ids hids hrun
      have hweightFinal : t weight = middle weight :=
        SourceScopedPrefix.frame g scope peer ((n, none) :: after) middle t
          weight hweight hrun
      change runUsing
        (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
        after (stepWithInputs g (scope n) (peer n) middle n none) = some t at hrun
      have hstep : stepWithInputs g (scope n) (peer n) middle n none =
          some (applyNode g middle n) := by
        rw [hscope, hnode]
        exact step_embedding g _ middle rank ids weight out
      rw [hstep] at hrun
      calc
        t out = applyNode g middle n out :=
          SourceScopedPrefix.frame g scope peer after (applyNode g middle n) t
            out hfresh hrun
        _ = fw_embedding (middle ids) (middle weight) := by
          rw [hnode]
          exact applyNode_fw_embedding_out g middle rank ids weight out
        _ = fw_embedding (t ids) (t weight) := by
          rw [hidsFinal, hweightFinal]
  · contradiction

#print axioms step_embedding
#print axioms embedding_value_of_split
end
end TrainVerify.Denote.SourceEmbeddingRead
