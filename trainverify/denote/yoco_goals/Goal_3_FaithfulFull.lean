/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.GeneratedYOCOMoE
import denote.DenoteDistributedFaithful
import denote.yoco_goals.FaithfulStackGather

/-!
# Goal 3: topology-correct faithful full statement (TID 4928)

The historical cut theorem targets TID 4675 in `sm_goal_3` / `pm_goal_3` and
uses the ring evaluator.  It is not a theorem about the ancestry-closed generated
full graph.  The current generated full graph instead targets TID 4928.

The old full ordinary-gather candidate was false because it gathered exposed
zigzag shards.  That counterexample does not apply to the current graph: PM now
faithfully unshuffles every post-shuffle routing-map shard before stacking, then
performs the generated dim-1 all-gather

`FW_stack rank0/rank1 -> 11608/11609; AllGatherPrim(dim=1) -> 4928`.

Accordingly the public statement below uses the ordinary generated `goal_3`, but
only under `denoteGraphDistributedFaithful`; its packed-cu premise is an
independent input-store contract, not a relation over a computed graph output.
-/

set_option linter.style.longLine false
set_option linter.style.nativeDecide false
set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedGoals

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedPatterns
open TrainVerify.Denote.ZigzagCollective

noncomputable section

/-- Independent external-input contract needed by the faithful full Goal 3
closure.  The generated value classes propagate the one packed-cu witness to all
aliases used by shuffle/unshuffle nodes. -/
def Goal3FullExternalInputs (initSM initPM : Store) : Prop :=
  InputValueClassesHold smInputValueClasses initSM ∧
  InputValueClassesHold pmInputValueClasses initPM ∧
  PackedCuSeqlensWF (initPM 6248) 4096 2

/-- Topology-correct full Goal 3 proposition for generated TID 4928.

Unlike `goal_3_stmt` in the generated file, this fixes the interpreter to the
value-faithful distributed semantics.  Unlike the obsolete TID-4675 cut result,
it quantifies over the ancestry-closed `sm` / `pm` graphs and `initGoals`.
Every caller premise is about an independent input store. -/
def goal_3_stmt_full : Prop :=
  ∀ (initSM initPM : Store),
    StoreShapesHold initSM smInitEnv →
    StoreShapesHold initPM pmInitEnv →
    InitGoalsHold pm.numRanks initGoals initSM initPM →
    Goal3FullExternalInputs initSM initPM →
    InitGoalHolds pm.numRanks goal_3
      (denoteGraphDistributedFaithful sm initSM)
      (denoteGraphDistributedFaithful pm initPM)

private def goal3SmStack : NodeDecl :=
  { rank := 0, op := "OpName.FW_stack",
    ins := [4964, 5019, 5074, 5129, 5184, 5239, 5294, 5349, 5404, 5459,
      5514, 5569, 5655, 5709, 5763, 5817, 5871, 5925, 5979, 6033, 6087,
      6141, 6195, 6249],
    outs := [4928] }

private def goal3PmStack0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_stack",
    ins := [7844, 8008, 8172, 8336, 8500, 8664, 8828, 8992, 9156, 9320,
      9484, 9648, 9908, 10062, 10216, 10370, 10524, 10678, 10832, 10986,
      11140, 11294, 11448, 11602],
    outs := [11608] }

private def goal3PmStack1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_stack",
    ins := [7845, 8009, 8173, 8337, 8501, 8665, 8829, 8993, 9157, 9321,
      9485, 9649, 9909, 10063, 10217, 10371, 10525, 10679, 10833, 10987,
      11141, 11295, 11449, 11603],
    outs := [11609] }

private def goal3PmGather : NodeDecl :=
  { rank := 0, op := "OpName.AllGatherPrim", ins := [11608, 11609],
    outs := [4928], params := [1] }

/-- Kernel-checked certificate for the corrected full topology.  In particular,
TID 4928 is not the historical 4675 cut, and its PM producer gathers the two
rank stacks along dimension 1. -/
theorem goal_3_full_topology :
    sm.nodes[939]'(by native_decide) = goal3SmStack ∧
    pm.nodes[2055]'(by native_decide) = goal3PmStack0 ∧
    pm.nodes[2057]'(by native_decide) = goal3PmStack1 ∧
    pm.nodes[2061]'(by native_decide) = goal3PmGather ∧
    goal_3.ts = 4928 ∧ goal_3.tsShape = [24, 4096, 64] := by
  native_decide

private theorem goal3_pm_nodes_nonempty : ∀ n ∈ pm.nodes, n.outs ≠ [] := by
  native_decide

/-- Exact faithful reduction of the generated PM target.  This records the
actual rank-order dim-1 gather; proving Goal 3 therefore reduces to showing that
the two inputs are stacks of *unshuffled* ordinary shards. -/
theorem goal_3_pm4928_faithful (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 4928 =
      allGatherPrimDimN 1 2 0
        [denoteGraphDistributedFaithful pm initPM 11608,
         denoteGraphDistributedFaithful pm initPM 11609] := by
  refine denoteGraphDistributedFaithful_reduce2 pm initPM 2061 goal3PmGather
    11608 11609 4928 (fun a b => allGatherPrimDimN 1 2 0 [a, b])
    (by native_decide) (by native_decide) ?_
    (fun n hn => goal3_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
    (by native_decide)
    (fun n hn => goal3_pm_nodes_nonempty n (List.mem_of_mem_drop hn))
    (by native_decide) (by native_decide)
  intro s
  unfold goal3PmGather
  rw [applyNodeDistributedFaithful_eq_applyNodeDistributed_of_not_collective _ _ _
    (by decide) (by decide)]
  exact applyNode_allGatherPrimDimN_out pm s 0 [11608, 11609] 4928 1

end
end TrainVerify.Denote.GeneratedGoals
