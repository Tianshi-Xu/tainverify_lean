/- Canonical Goal 4, layer 16: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l16SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5844, 5872],
    outs := [5873], params := [1, 0] }

private def g4l16PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10448, 5872],
    outs := [10526], params := [2, 0] }

private def g4l16PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10449, 5872],
    outs := [10527], params := [2, 1] }

private theorem g4l16_sm_node :
    sm_goal_4.nodes[672]'(by native_decide) = g4l16SmUnshuffle := by
  native_decide

private theorem g4l16_pm_nodes :
    pm_goal_4.nodes[1478]'(by native_decide) = g4l16PmUnshuffle0 ∧
    pm_goal_4.nodes[1480]'(by native_decide) = g4l16PmUnshuffle1 := by
  native_decide

private theorem g4l16_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l16PmUnshuffle0 =
      [g4l16PmUnshuffle0, g4l16PmUnshuffle1] := by
  native_decide

private theorem g4l16_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l16PmUnshuffle1 =
      [g4l16PmUnshuffle0, g4l16PmUnshuffle1] := by
  native_decide

private theorem g4l16_sm_nonempty672 :
    ∀ n ∈ sm_goal_4.nodes.drop 672, n.outs ≠ [] := by native_decide
private theorem g4l16_sm_nonempty673 :
    ∀ n ∈ sm_goal_4.nodes.drop 673, n.outs ≠ [] := by native_decide
private theorem g4l16_pm_nonempty1478 :
    ∀ n ∈ pm_goal_4.nodes.drop 1478, n.outs ≠ [] := by native_decide
private theorem g4l16_pm_nonempty1479 :
    ∀ n ∈ pm_goal_4.nodes.drop 1479, n.outs ≠ [] := by native_decide
private theorem g4l16_pm_nonempty1480 :
    ∀ n ∈ pm_goal_4.nodes.drop 1480, n.outs ≠ [] := by native_decide
private theorem g4l16_pm_nonempty1481 :
    ∀ n ∈ pm_goal_4.nodes.drop 1481, n.outs ≠ [] := by native_decide

private theorem g4l16_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(673, 5873), (672, 5844), (672, 5872)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l16_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1479, 10526), (1481, 10527),
      (1478, 10448), (1478, 10449), (1478, 5872),
      (1480, 10448), (1480, 10449), (1480, 5872)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l16_red_sm5873 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5873 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 5844 := by
  let pre := (sm_goal_4.nodes.take 672).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 5873 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l16SmUnshuffle 5873 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 672 g4l16SmUnshuffle 5873
      (by native_decide) g4l16_sm_node g4l16_sm_nonempty673
      (g4l16_sm_not_written 673 5873 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l16SmUnshuffle 5873 =
      pre 5844 := by
    unfold g4l16SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5844, 5872],
        outs := [5873], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5844 = denoteGraphDistributedFaithful sm_goal_4 initSM 5844 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 672 5844
      g4l16_sm_nonempty672 (g4l16_sm_not_written 672 5844 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l16_red_pm10526 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10526 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10448,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10449]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5872)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1478).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10526 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l16PmUnshuffle0 10526 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1478 g4l16PmUnshuffle0 10526
      (by native_decide) g4l16_pm_nodes.1 g4l16_pm_nonempty1479
      (g4l16_pm_not_written 1479 10526 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l16PmUnshuffle0 10526 =
      opfun (pre 10448) (pre 10449) (pre 5872) := by
    unfold g4l16PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10448, 5872],
        outs := [10526], params := [2, 0] } =
        [g4l16PmUnshuffle0, g4l16PmUnshuffle1] from g4l16_pm_buddies0]
    unfold g4l16PmUnshuffle0 g4l16PmUnshuffle1 opfun
    rfl
  have h0 : pre 10448 = denoteGraphDistributedFaithful pm_goal_4 initPM 10448 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1478 10448
      g4l16_pm_nonempty1478 (g4l16_pm_not_written 1478 10448 (by decide))
  have h1 : pre 10449 = denoteGraphDistributedFaithful pm_goal_4 initPM 10449 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1478 10449
      g4l16_pm_nonempty1478 (g4l16_pm_not_written 1478 10449 (by decide))
  have hcu : pre 5872 = denoteGraphDistributedFaithful pm_goal_4 initPM 5872 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1478 5872
      g4l16_pm_nonempty1478 (g4l16_pm_not_written 1478 5872 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10526 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l16PmUnshuffle0 10526 := hcore
    _ = opfun (pre 10448) (pre 10449) (pre 5872) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10448)
        (pre 10449) (pre 5872) := congrArg (fun x => opfun x (pre 10449) (pre 5872)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10448)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10449) (pre 5872) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10448) x
        (pre 5872)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10448)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10449)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5872) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10448)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10449)) hcu

private theorem g4l16_red_pm10527 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10527 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10448,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10449]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5872)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1480).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10527 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l16PmUnshuffle1 10527 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1480 g4l16PmUnshuffle1 10527
      (by native_decide) g4l16_pm_nodes.2 g4l16_pm_nonempty1481
      (g4l16_pm_not_written 1481 10527 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l16PmUnshuffle1 10527 =
      opfun (pre 10448) (pre 10449) (pre 5872) := by
    unfold g4l16PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10449, 5872],
        outs := [10527], params := [2, 1] } =
        [g4l16PmUnshuffle0, g4l16PmUnshuffle1] from g4l16_pm_buddies1]
    unfold g4l16PmUnshuffle0 g4l16PmUnshuffle1 opfun
    rfl
  have h0 : pre 10448 = denoteGraphDistributedFaithful pm_goal_4 initPM 10448 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1480 10448
      g4l16_pm_nonempty1480 (g4l16_pm_not_written 1480 10448 (by decide))
  have h1 : pre 10449 = denoteGraphDistributedFaithful pm_goal_4 initPM 10449 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1480 10449
      g4l16_pm_nonempty1480 (g4l16_pm_not_written 1480 10449 (by decide))
  have hcu : pre 5872 = denoteGraphDistributedFaithful pm_goal_4 initPM 5872 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1480 5872
      g4l16_pm_nonempty1480 (g4l16_pm_not_written 1480 5872 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10527 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l16PmUnshuffle1 10527 := hcore
    _ = opfun (pre 10448) (pre 10449) (pre 5872) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10448)
        (pre 10449) (pre 5872) := congrArg (fun x => opfun x (pre 10449) (pre 5872)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10448)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10449) (pre 5872) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10448) x
        (pre 5872)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10448)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10449)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5872) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10448)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10449)) hcu

private theorem g4l16_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (5872 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l16_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 5872 = initPM 5872 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 5872 (by
      intro n hn
      native_decide +revert) g4l16_cu_not_written

private theorem g4l16_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l16_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-16 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l16_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5844)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10448)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10449)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5872)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5872) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5873)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10526)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10527)
      [4096, 64] [2048, 64] := by
  have hcu := g4l16_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5872) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l16_red_sm5873 initSM
  have hpm0 := g4l16_red_pm10526 initPM
  have hpm1 := g4l16_red_pm10527 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10448,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10449]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5872)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10448,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10449]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5872)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 5844 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 10526,
       denoteGraphDistributedFaithful pm_goal_4 initPM 10527] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 10526, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 10526,
          denoteGraphDistributedFaithful pm_goal_4 initPM 10527] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 10526, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10448).shape := by
    exact g4l16_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10449).shape := by
    exact g4l16_unshuffle1_shape _ _ _
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

