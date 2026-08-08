/- Canonical Goal 4, layer 23: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l23SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6222, 6250],
    outs := [6251], params := [1, 0] }

private def g4l23PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11526, 6250],
    outs := [11604], params := [2, 0] }

private def g4l23PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11527, 6250],
    outs := [11605], params := [2, 1] }

private theorem g4l23_sm_node :
    sm_goal_4.nodes[914]'(by native_decide) = g4l23SmUnshuffle := by
  native_decide

private theorem g4l23_pm_nodes :
    pm_goal_4.nodes[1998]'(by native_decide) = g4l23PmUnshuffle0 ∧
    pm_goal_4.nodes[1999]'(by native_decide) = g4l23PmUnshuffle1 := by
  native_decide

private theorem g4l23_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l23PmUnshuffle0 =
      [g4l23PmUnshuffle0, g4l23PmUnshuffle1] := by
  native_decide

private theorem g4l23_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l23PmUnshuffle1 =
      [g4l23PmUnshuffle0, g4l23PmUnshuffle1] := by
  native_decide

private theorem g4l23_sm_nonempty914 :
    ∀ n ∈ sm_goal_4.nodes.drop 914, n.outs ≠ [] := by native_decide
private theorem g4l23_sm_nonempty915 :
    ∀ n ∈ sm_goal_4.nodes.drop 915, n.outs ≠ [] := by native_decide
private theorem g4l23_pm_nonempty1998 :
    ∀ n ∈ pm_goal_4.nodes.drop 1998, n.outs ≠ [] := by native_decide
private theorem g4l23_pm_nonempty_after0 :
    ∀ n ∈ pm_goal_4.nodes.drop 1999, n.outs ≠ [] := by native_decide
private theorem g4l23_pm_nonempty_pre1 :
    ∀ n ∈ pm_goal_4.nodes.drop 1999, n.outs ≠ [] := by native_decide
private theorem g4l23_pm_nonempty2000 :
    ∀ n ∈ pm_goal_4.nodes.drop 2000, n.outs ≠ [] := by native_decide

private theorem g4l23_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(915, 6251), (914, 6222), (914, 6250)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l23_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1999, 11604), (2000, 11605),
      (1998, 11526), (1998, 11527), (1998, 6250),
      (1999, 11526), (1999, 11527), (1999, 6250)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l23_red_sm6251 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 6251 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 6222 := by
  let pre := (sm_goal_4.nodes.take 914).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 6251 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l23SmUnshuffle 6251 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 914 g4l23SmUnshuffle 6251
      (by native_decide) g4l23_sm_node g4l23_sm_nonempty915
      (g4l23_sm_not_written 915 6251 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l23SmUnshuffle 6251 =
      pre 6222 := by
    unfold g4l23SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6222, 6250],
        outs := [6251], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 6222 = denoteGraphDistributedFaithful sm_goal_4 initSM 6222 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 914 6222
      g4l23_sm_nonempty914 (g4l23_sm_not_written 914 6222 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l23_red_pm11604 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 11604 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 11526,
         denoteGraphDistributedFaithful pm_goal_4 initPM 11527]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6250)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1998).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 11604 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l23PmUnshuffle0 11604 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1998 g4l23PmUnshuffle0 11604
      (by native_decide) g4l23_pm_nodes.1 g4l23_pm_nonempty_after0
      (g4l23_pm_not_written 1999 11604 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l23PmUnshuffle0 11604 =
      opfun (pre 11526) (pre 11527) (pre 6250) := by
    unfold g4l23PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11526, 6250],
        outs := [11604], params := [2, 0] } =
        [g4l23PmUnshuffle0, g4l23PmUnshuffle1] from g4l23_pm_buddies0]
    unfold g4l23PmUnshuffle0 g4l23PmUnshuffle1 opfun
    rfl
  have h0 : pre 11526 = denoteGraphDistributedFaithful pm_goal_4 initPM 11526 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1998 11526
      g4l23_pm_nonempty1998 (g4l23_pm_not_written 1998 11526 (by decide))
  have h1 : pre 11527 = denoteGraphDistributedFaithful pm_goal_4 initPM 11527 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1998 11527
      g4l23_pm_nonempty1998 (g4l23_pm_not_written 1998 11527 (by decide))
  have hcu : pre 6250 = denoteGraphDistributedFaithful pm_goal_4 initPM 6250 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1998 6250
      g4l23_pm_nonempty1998 (g4l23_pm_not_written 1998 6250 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 11604 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l23PmUnshuffle0 11604 := hcore
    _ = opfun (pre 11526) (pre 11527) (pre 6250) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11526)
        (pre 11527) (pre 6250) := congrArg (fun x => opfun x (pre 11527) (pre 6250)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11526)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11527) (pre 6250) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11526) x
        (pre 6250)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11526)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11527)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 6250) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11526)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11527)) hcu

private theorem g4l23_red_pm11605 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 11605 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 11526,
         denoteGraphDistributedFaithful pm_goal_4 initPM 11527]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6250)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1999).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 11605 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l23PmUnshuffle1 11605 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1999 g4l23PmUnshuffle1 11605
      (by native_decide) g4l23_pm_nodes.2 g4l23_pm_nonempty2000
      (g4l23_pm_not_written 2000 11605 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l23PmUnshuffle1 11605 =
      opfun (pre 11526) (pre 11527) (pre 6250) := by
    unfold g4l23PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11527, 6250],
        outs := [11605], params := [2, 1] } =
        [g4l23PmUnshuffle0, g4l23PmUnshuffle1] from g4l23_pm_buddies1]
    unfold g4l23PmUnshuffle0 g4l23PmUnshuffle1 opfun
    rfl
  have h0 : pre 11526 = denoteGraphDistributedFaithful pm_goal_4 initPM 11526 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1999 11526
      g4l23_pm_nonempty_pre1 (g4l23_pm_not_written 1999 11526 (by decide))
  have h1 : pre 11527 = denoteGraphDistributedFaithful pm_goal_4 initPM 11527 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1999 11527
      g4l23_pm_nonempty_pre1 (g4l23_pm_not_written 1999 11527 (by decide))
  have hcu : pre 6250 = denoteGraphDistributedFaithful pm_goal_4 initPM 6250 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1999 6250
      g4l23_pm_nonempty_pre1 (g4l23_pm_not_written 1999 6250 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 11605 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l23PmUnshuffle1 11605 := hcore
    _ = opfun (pre 11526) (pre 11527) (pre 6250) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11526)
        (pre 11527) (pre 6250) := congrArg (fun x => opfun x (pre 11527) (pre 6250)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11526)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11527) (pre 6250) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11526) x
        (pre 6250)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11526)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11527)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 6250) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11526)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11527)) hcu

private theorem g4l23_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (6250 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l23_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 6250 = initPM 6250 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 6250 (by
      intro n hn
      native_decide +revert) g4l23_cu_not_written

private theorem g4l23_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l23_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-23 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l23_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 6222)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11526)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11527)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 6250)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 6250) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 6251)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11604)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11605)
      [4096, 64] [2048, 64] := by
  have hcu := g4l23_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 6250) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l23_red_sm6251 initSM
  have hpm0 := g4l23_red_pm11604 initPM
  have hpm1 := g4l23_red_pm11605 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 11526,
     denoteGraphDistributedFaithful pm_goal_4 initPM 11527]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6250)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 11526,
     denoteGraphDistributedFaithful pm_goal_4 initPM 11527]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6250)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 6222 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 11604,
       denoteGraphDistributedFaithful pm_goal_4 initPM 11605] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 11604, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 11604,
          denoteGraphDistributedFaithful pm_goal_4 initPM 11605] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 11604, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11526).shape := by
    exact g4l23_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11527).shape := by
    exact g4l23_unshuffle1_shape _ _ _
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

