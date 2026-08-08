/- Canonical Goal 4, layer 17: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l17SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5898, 5926],
    outs := [5927], params := [1, 0] }

private def g4l17PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10602, 5926],
    outs := [10680], params := [2, 0] }

private def g4l17PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10603, 5926],
    outs := [10681], params := [2, 1] }

private theorem g4l17_sm_node :
    sm_goal_4.nodes[708]'(by native_decide) = g4l17SmUnshuffle := by
  native_decide

private theorem g4l17_pm_nodes :
    pm_goal_4.nodes[1556]'(by native_decide) = g4l17PmUnshuffle0 ∧
    pm_goal_4.nodes[1558]'(by native_decide) = g4l17PmUnshuffle1 := by
  native_decide

private theorem g4l17_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l17PmUnshuffle0 =
      [g4l17PmUnshuffle0, g4l17PmUnshuffle1] := by
  native_decide

private theorem g4l17_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l17PmUnshuffle1 =
      [g4l17PmUnshuffle0, g4l17PmUnshuffle1] := by
  native_decide

private theorem g4l17_sm_nonempty708 :
    ∀ n ∈ sm_goal_4.nodes.drop 708, n.outs ≠ [] := by native_decide
private theorem g4l17_sm_nonempty709 :
    ∀ n ∈ sm_goal_4.nodes.drop 709, n.outs ≠ [] := by native_decide
private theorem g4l17_pm_nonempty1556 :
    ∀ n ∈ pm_goal_4.nodes.drop 1556, n.outs ≠ [] := by native_decide
private theorem g4l17_pm_nonempty1557 :
    ∀ n ∈ pm_goal_4.nodes.drop 1557, n.outs ≠ [] := by native_decide
private theorem g4l17_pm_nonempty1558 :
    ∀ n ∈ pm_goal_4.nodes.drop 1558, n.outs ≠ [] := by native_decide
private theorem g4l17_pm_nonempty1559 :
    ∀ n ∈ pm_goal_4.nodes.drop 1559, n.outs ≠ [] := by native_decide

private theorem g4l17_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(709, 5927), (708, 5898), (708, 5926)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l17_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1557, 10680), (1559, 10681),
      (1556, 10602), (1556, 10603), (1556, 5926),
      (1558, 10602), (1558, 10603), (1558, 5926)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l17_red_sm5927 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5927 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 5898 := by
  let pre := (sm_goal_4.nodes.take 708).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 5927 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l17SmUnshuffle 5927 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 708 g4l17SmUnshuffle 5927
      (by native_decide) g4l17_sm_node g4l17_sm_nonempty709
      (g4l17_sm_not_written 709 5927 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l17SmUnshuffle 5927 =
      pre 5898 := by
    unfold g4l17SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5898, 5926],
        outs := [5927], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5898 = denoteGraphDistributedFaithful sm_goal_4 initSM 5898 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 708 5898
      g4l17_sm_nonempty708 (g4l17_sm_not_written 708 5898 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l17_red_pm10680 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10680 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10602,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10603]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5926)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1556).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10680 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l17PmUnshuffle0 10680 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1556 g4l17PmUnshuffle0 10680
      (by native_decide) g4l17_pm_nodes.1 g4l17_pm_nonempty1557
      (g4l17_pm_not_written 1557 10680 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l17PmUnshuffle0 10680 =
      opfun (pre 10602) (pre 10603) (pre 5926) := by
    unfold g4l17PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10602, 5926],
        outs := [10680], params := [2, 0] } =
        [g4l17PmUnshuffle0, g4l17PmUnshuffle1] from g4l17_pm_buddies0]
    unfold g4l17PmUnshuffle0 g4l17PmUnshuffle1 opfun
    rfl
  have h0 : pre 10602 = denoteGraphDistributedFaithful pm_goal_4 initPM 10602 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1556 10602
      g4l17_pm_nonempty1556 (g4l17_pm_not_written 1556 10602 (by decide))
  have h1 : pre 10603 = denoteGraphDistributedFaithful pm_goal_4 initPM 10603 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1556 10603
      g4l17_pm_nonempty1556 (g4l17_pm_not_written 1556 10603 (by decide))
  have hcu : pre 5926 = denoteGraphDistributedFaithful pm_goal_4 initPM 5926 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1556 5926
      g4l17_pm_nonempty1556 (g4l17_pm_not_written 1556 5926 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10680 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l17PmUnshuffle0 10680 := hcore
    _ = opfun (pre 10602) (pre 10603) (pre 5926) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
        (pre 10603) (pre 5926) := congrArg (fun x => opfun x (pre 10603) (pre 5926)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10603) (pre 5926) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10602) x
        (pre 5926)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10603)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5926) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10603)) hcu

private theorem g4l17_red_pm10681 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10681 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10602,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10603]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5926)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1558).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10681 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l17PmUnshuffle1 10681 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1558 g4l17PmUnshuffle1 10681
      (by native_decide) g4l17_pm_nodes.2 g4l17_pm_nonempty1559
      (g4l17_pm_not_written 1559 10681 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l17PmUnshuffle1 10681 =
      opfun (pre 10602) (pre 10603) (pre 5926) := by
    unfold g4l17PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10603, 5926],
        outs := [10681], params := [2, 1] } =
        [g4l17PmUnshuffle0, g4l17PmUnshuffle1] from g4l17_pm_buddies1]
    unfold g4l17PmUnshuffle0 g4l17PmUnshuffle1 opfun
    rfl
  have h0 : pre 10602 = denoteGraphDistributedFaithful pm_goal_4 initPM 10602 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1558 10602
      g4l17_pm_nonempty1558 (g4l17_pm_not_written 1558 10602 (by decide))
  have h1 : pre 10603 = denoteGraphDistributedFaithful pm_goal_4 initPM 10603 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1558 10603
      g4l17_pm_nonempty1558 (g4l17_pm_not_written 1558 10603 (by decide))
  have hcu : pre 5926 = denoteGraphDistributedFaithful pm_goal_4 initPM 5926 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1558 5926
      g4l17_pm_nonempty1558 (g4l17_pm_not_written 1558 5926 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10681 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l17PmUnshuffle1 10681 := hcore
    _ = opfun (pre 10602) (pre 10603) (pre 5926) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
        (pre 10603) (pre 5926) := congrArg (fun x => opfun x (pre 10603) (pre 5926)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10603) (pre 5926) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10602) x
        (pre 5926)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10603)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5926) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10603)) hcu

private theorem g4l17_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (5926 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l17_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 5926 = initPM 5926 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 5926 (by
      intro n hn
      native_decide +revert) g4l17_cu_not_written

private theorem g4l17_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l17_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-17 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l17_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5898)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10602)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10603)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5926)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5926) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5927)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10680)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10681)
      [4096, 64] [2048, 64] := by
  have hcu := g4l17_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5926) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l17_red_sm5927 initSM
  have hpm0 := g4l17_red_pm10680 initPM
  have hpm1 := g4l17_red_pm10681 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10602,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10603]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5926)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10602,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10603]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5926)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 5898 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 10680,
       denoteGraphDistributedFaithful pm_goal_4 initPM 10681] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 10680, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 10680,
          denoteGraphDistributedFaithful pm_goal_4 initPM 10681] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 10680, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10602).shape := by
    exact g4l17_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10603).shape := by
    exact g4l17_unshuffle1_shape _ _ _
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

