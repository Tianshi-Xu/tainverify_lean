/- Canonical Goal 4, layer 19: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l19SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6006, 6034],
    outs := [6035], params := [1, 0] }

private def g4l19PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10910, 6034],
    outs := [10988], params := [2, 0] }

private def g4l19PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10911, 6034],
    outs := [10989], params := [2, 1] }

private theorem g4l19_sm_node :
    sm_goal_4.nodes[780]'(by native_decide) = g4l19SmUnshuffle := by
  native_decide

private theorem g4l19_pm_nodes :
    pm_goal_4.nodes[1712]'(by native_decide) = g4l19PmUnshuffle0 ∧
    pm_goal_4.nodes[1714]'(by native_decide) = g4l19PmUnshuffle1 := by
  native_decide

private theorem g4l19_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l19PmUnshuffle0 =
      [g4l19PmUnshuffle0, g4l19PmUnshuffle1] := by
  native_decide

private theorem g4l19_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l19PmUnshuffle1 =
      [g4l19PmUnshuffle0, g4l19PmUnshuffle1] := by
  native_decide

private theorem g4l19_sm_nonempty780 :
    ∀ n ∈ sm_goal_4.nodes.drop 780, n.outs ≠ [] := by native_decide
private theorem g4l19_sm_nonempty781 :
    ∀ n ∈ sm_goal_4.nodes.drop 781, n.outs ≠ [] := by native_decide
private theorem g4l19_pm_nonempty1712 :
    ∀ n ∈ pm_goal_4.nodes.drop 1712, n.outs ≠ [] := by native_decide
private theorem g4l19_pm_nonempty1713 :
    ∀ n ∈ pm_goal_4.nodes.drop 1713, n.outs ≠ [] := by native_decide
private theorem g4l19_pm_nonempty1714 :
    ∀ n ∈ pm_goal_4.nodes.drop 1714, n.outs ≠ [] := by native_decide
private theorem g4l19_pm_nonempty1715 :
    ∀ n ∈ pm_goal_4.nodes.drop 1715, n.outs ≠ [] := by native_decide

private theorem g4l19_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(781, 6035), (780, 6006), (780, 6034)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l19_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1713, 10988), (1715, 10989),
      (1712, 10910), (1712, 10911), (1712, 6034),
      (1714, 10910), (1714, 10911), (1714, 6034)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l19_red_sm6035 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 6035 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 6006 := by
  let pre := (sm_goal_4.nodes.take 780).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 6035 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l19SmUnshuffle 6035 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 780 g4l19SmUnshuffle 6035
      (by native_decide) g4l19_sm_node g4l19_sm_nonempty781
      (g4l19_sm_not_written 781 6035 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l19SmUnshuffle 6035 =
      pre 6006 := by
    unfold g4l19SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6006, 6034],
        outs := [6035], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 6006 = denoteGraphDistributedFaithful sm_goal_4 initSM 6006 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 780 6006
      g4l19_sm_nonempty780 (g4l19_sm_not_written 780 6006 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l19_red_pm10988 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10988 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10910,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10911]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6034)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1712).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10988 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l19PmUnshuffle0 10988 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1712 g4l19PmUnshuffle0 10988
      (by native_decide) g4l19_pm_nodes.1 g4l19_pm_nonempty1713
      (g4l19_pm_not_written 1713 10988 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l19PmUnshuffle0 10988 =
      opfun (pre 10910) (pre 10911) (pre 6034) := by
    unfold g4l19PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10910, 6034],
        outs := [10988], params := [2, 0] } =
        [g4l19PmUnshuffle0, g4l19PmUnshuffle1] from g4l19_pm_buddies0]
    unfold g4l19PmUnshuffle0 g4l19PmUnshuffle1 opfun
    rfl
  have h0 : pre 10910 = denoteGraphDistributedFaithful pm_goal_4 initPM 10910 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1712 10910
      g4l19_pm_nonempty1712 (g4l19_pm_not_written 1712 10910 (by decide))
  have h1 : pre 10911 = denoteGraphDistributedFaithful pm_goal_4 initPM 10911 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1712 10911
      g4l19_pm_nonempty1712 (g4l19_pm_not_written 1712 10911 (by decide))
  have hcu : pre 6034 = denoteGraphDistributedFaithful pm_goal_4 initPM 6034 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1712 6034
      g4l19_pm_nonempty1712 (g4l19_pm_not_written 1712 6034 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10988 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l19PmUnshuffle0 10988 := hcore
    _ = opfun (pre 10910) (pre 10911) (pre 6034) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10910)
        (pre 10911) (pre 6034) := congrArg (fun x => opfun x (pre 10911) (pre 6034)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10910)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10911) (pre 6034) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10910) x
        (pre 6034)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10910)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10911)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 6034) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10910)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10911)) hcu

private theorem g4l19_red_pm10989 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10989 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10910,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10911]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6034)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1714).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10989 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l19PmUnshuffle1 10989 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1714 g4l19PmUnshuffle1 10989
      (by native_decide) g4l19_pm_nodes.2 g4l19_pm_nonempty1715
      (g4l19_pm_not_written 1715 10989 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l19PmUnshuffle1 10989 =
      opfun (pre 10910) (pre 10911) (pre 6034) := by
    unfold g4l19PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10911, 6034],
        outs := [10989], params := [2, 1] } =
        [g4l19PmUnshuffle0, g4l19PmUnshuffle1] from g4l19_pm_buddies1]
    unfold g4l19PmUnshuffle0 g4l19PmUnshuffle1 opfun
    rfl
  have h0 : pre 10910 = denoteGraphDistributedFaithful pm_goal_4 initPM 10910 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1714 10910
      g4l19_pm_nonempty1714 (g4l19_pm_not_written 1714 10910 (by decide))
  have h1 : pre 10911 = denoteGraphDistributedFaithful pm_goal_4 initPM 10911 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1714 10911
      g4l19_pm_nonempty1714 (g4l19_pm_not_written 1714 10911 (by decide))
  have hcu : pre 6034 = denoteGraphDistributedFaithful pm_goal_4 initPM 6034 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1714 6034
      g4l19_pm_nonempty1714 (g4l19_pm_not_written 1714 6034 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10989 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l19PmUnshuffle1 10989 := hcore
    _ = opfun (pre 10910) (pre 10911) (pre 6034) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10910)
        (pre 10911) (pre 6034) := congrArg (fun x => opfun x (pre 10911) (pre 6034)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10910)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10911) (pre 6034) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10910) x
        (pre 6034)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10910)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10911)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 6034) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10910)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10911)) hcu

private theorem g4l19_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (6034 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l19_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 6034 = initPM 6034 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 6034 (by
      intro n hn
      native_decide +revert) g4l19_cu_not_written

private theorem g4l19_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l19_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-19 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l19_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 6006)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10910)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10911)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 6034)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 6034) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 6035)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10988)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10989)
      [4096, 64] [2048, 64] := by
  have hcu := g4l19_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 6034) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l19_red_sm6035 initSM
  have hpm0 := g4l19_red_pm10988 initPM
  have hpm1 := g4l19_red_pm10989 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10910,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10911]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6034)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10910,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10911]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6034)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 6006 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 10988,
       denoteGraphDistributedFaithful pm_goal_4 initPM 10989] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 10988, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 10988,
          denoteGraphDistributedFaithful pm_goal_4 initPM 10989] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 10988, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10910).shape := by
    exact g4l19_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10911).shape := by
    exact g4l19_unshuffle1_shape _ _ _
  refine {
    full_value := ?_
    full_shape := ?_
    rank0_shape := ?_
    rank1_shape := ?_
  }
  · exact hsm.trans (hunshuffle.trans (congrArg (allGatherPrimDimN 0 2 0) hlist))
  · exact (congrArg Tensor.shape hsm).trans hrel.full_shape
  · exact (congrArg Tensor.shape hpm0).trans (hu0shape.trans hrel.rank0_shape)
  · exact (congrArg Tensor.shape hpm1).trans (hu1shape.trans hrel.rank1_shape)

end
end TrainVerify.Denote.GeneratedPatterns

