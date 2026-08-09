/- Canonical Goal 3, layer 19: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l19SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6005, 6032],
    outs := [6033], params := [1, 0] }

private def g3l19PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10908, 6032],
    outs := [10986], params := [2, 0] }

private def g3l19PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10909, 6032],
    outs := [10987], params := [2, 1] }

private theorem g3l19_sm_node :
    sm.nodes[787]'(by native_decide) = g3l19SmUnshuffle := by
  native_decide

private theorem g3l19_pm_nodes :
    pm.nodes[1728]'(by native_decide) = g3l19PmUnshuffle0 ∧
    pm.nodes[1731]'(by native_decide) = g3l19PmUnshuffle1 := by
  native_decide

private theorem g3l19_pm_buddies0 :
    pm.replicaBuddies g3l19PmUnshuffle0 =
      [g3l19PmUnshuffle0, g3l19PmUnshuffle1] := by
  native_decide

private theorem g3l19_pm_buddies1 :
    pm.replicaBuddies g3l19PmUnshuffle1 =
      [g3l19PmUnshuffle0, g3l19PmUnshuffle1] := by
  native_decide

private theorem g3l19_sm_nonempty787 :
    ∀ n ∈ sm.nodes.drop 787, n.outs ≠ [] := by native_decide
private theorem g3l19_sm_nonempty788 :
    ∀ n ∈ sm.nodes.drop 788, n.outs ≠ [] := by native_decide
private theorem g3l19_pm_nonempty1728 :
    ∀ n ∈ pm.nodes.drop 1728, n.outs ≠ [] := by native_decide
private theorem g3l19_pm_nonempty1729 :
    ∀ n ∈ pm.nodes.drop 1729, n.outs ≠ [] := by native_decide
private theorem g3l19_pm_nonempty1731 :
    ∀ n ∈ pm.nodes.drop 1731, n.outs ≠ [] := by native_decide
private theorem g3l19_pm_nonempty1732 :
    ∀ n ∈ pm.nodes.drop 1732, n.outs ≠ [] := by native_decide

private theorem g3l19_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(788, 6033), (787, 6005), (787, 6032)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l19_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1729, 10986), (1732, 10987),
      (1728, 10908), (1728, 10909), (1728, 6032),
      (1731, 10908), (1731, 10909), (1731, 6032)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l19_red_sm6033 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 6033 =
      denoteGraphDistributedFaithful sm initSM 6005 := by
  let pre := (sm.nodes.take 787).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 6033 =
      applyNodeDistributedFaithful sm pre g3l19SmUnshuffle 6033 :=
    denoteGraphDistributedFaithful_node_core sm initSM 787 g3l19SmUnshuffle 6033
      (by native_decide) g3l19_sm_node g3l19_sm_nonempty788
      (g3l19_sm_not_written 788 6033 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l19SmUnshuffle 6033 =
      pre 6005 := by
    unfold g3l19SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6005, 6032],
        outs := [6033], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 6005 = denoteGraphDistributedFaithful sm initSM 6005 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 787 6005
      g3l19_sm_nonempty787 (g3l19_sm_not_written 787 6005 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l19_red_pm10986 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10986 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 10908,
         denoteGraphDistributedFaithful pm initPM 10909]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6032)) 2 0 := by
  let pre := (pm.nodes.take 1728).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 10986 =
      applyNodeDistributedFaithful pm pre g3l19PmUnshuffle0 10986 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1728 g3l19PmUnshuffle0 10986
      (by native_decide) g3l19_pm_nodes.1 g3l19_pm_nonempty1729
      (g3l19_pm_not_written 1729 10986 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l19PmUnshuffle0 10986 =
      opfun (pre 10908) (pre 10909) (pre 6032) := by
    unfold g3l19PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10908, 6032],
        outs := [10986], params := [2, 0] } =
        [g3l19PmUnshuffle0, g3l19PmUnshuffle1] from g3l19_pm_buddies0]
    unfold g3l19PmUnshuffle0 g3l19PmUnshuffle1 opfun
    rfl
  have h0 : pre 10908 = denoteGraphDistributedFaithful pm initPM 10908 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1728 10908
      g3l19_pm_nonempty1728 (g3l19_pm_not_written 1728 10908 (by decide))
  have h1 : pre 10909 = denoteGraphDistributedFaithful pm initPM 10909 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1728 10909
      g3l19_pm_nonempty1728 (g3l19_pm_not_written 1728 10909 (by decide))
  have hcu : pre 6032 = denoteGraphDistributedFaithful pm initPM 6032 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1728 6032
      g3l19_pm_nonempty1728 (g3l19_pm_not_written 1728 6032 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10986 =
        applyNodeDistributedFaithful pm pre g3l19PmUnshuffle0 10986 := hcore
    _ = opfun (pre 10908) (pre 10909) (pre 6032) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10908)
        (pre 10909) (pre 6032) := congrArg (fun x => opfun x (pre 10909) (pre 6032)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10908)
        (denoteGraphDistributedFaithful pm initPM 10909) (pre 6032) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 10908) x
        (pre 6032)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10908)
        (denoteGraphDistributedFaithful pm initPM 10909)
        (denoteGraphDistributedFaithful pm initPM 6032) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 10908)
        (denoteGraphDistributedFaithful pm initPM 10909)) hcu

private theorem g3l19_red_pm10987 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10987 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 10908,
         denoteGraphDistributedFaithful pm initPM 10909]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6032)) 2 1 := by
  let pre := (pm.nodes.take 1731).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 10987 =
      applyNodeDistributedFaithful pm pre g3l19PmUnshuffle1 10987 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1731 g3l19PmUnshuffle1 10987
      (by native_decide) g3l19_pm_nodes.2 g3l19_pm_nonempty1732
      (g3l19_pm_not_written 1732 10987 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l19PmUnshuffle1 10987 =
      opfun (pre 10908) (pre 10909) (pre 6032) := by
    unfold g3l19PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10909, 6032],
        outs := [10987], params := [2, 1] } =
        [g3l19PmUnshuffle0, g3l19PmUnshuffle1] from g3l19_pm_buddies1]
    unfold g3l19PmUnshuffle0 g3l19PmUnshuffle1 opfun
    rfl
  have h0 : pre 10908 = denoteGraphDistributedFaithful pm initPM 10908 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1731 10908
      g3l19_pm_nonempty1731 (g3l19_pm_not_written 1731 10908 (by decide))
  have h1 : pre 10909 = denoteGraphDistributedFaithful pm initPM 10909 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1731 10909
      g3l19_pm_nonempty1731 (g3l19_pm_not_written 1731 10909 (by decide))
  have hcu : pre 6032 = denoteGraphDistributedFaithful pm initPM 6032 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1731 6032
      g3l19_pm_nonempty1731 (g3l19_pm_not_written 1731 6032 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10987 =
        applyNodeDistributedFaithful pm pre g3l19PmUnshuffle1 10987 := hcore
    _ = opfun (pre 10908) (pre 10909) (pre 6032) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10908)
        (pre 10909) (pre 6032) := congrArg (fun x => opfun x (pre 10909) (pre 6032)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10908)
        (denoteGraphDistributedFaithful pm initPM 10909) (pre 6032) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 10908) x
        (pre 6032)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10908)
        (denoteGraphDistributedFaithful pm initPM 10909)
        (denoteGraphDistributedFaithful pm initPM 6032) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 10908)
        (denoteGraphDistributedFaithful pm initPM 10909)) hcu

private theorem g3l19_cu_not_written :
    ∀ n ∈ pm.nodes, (6032 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l19_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 6032 = initPM 6032 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 6032 (by
      intro n hn
      native_decide +revert) g3l19_cu_not_written

private theorem g3l19_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l19_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-19 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l19_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 6005)
      (denoteGraphDistributedFaithful pm initPM 10908)
      (denoteGraphDistributedFaithful pm initPM 10909)
      (denoteGraphDistributedFaithful pm initPM 6032)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 6032) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 6033)
      (denoteGraphDistributedFaithful pm initPM 10986)
      (denoteGraphDistributedFaithful pm initPM 10987)
      [4096, 64] [2048, 64] := by
  have hcu := g3l19_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 6032) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l19_red_sm6033 initSM
  have hpm0 := g3l19_red_pm10986 initPM
  have hpm1 := g3l19_red_pm10987 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 10908,
     denoteGraphDistributedFaithful pm initPM 10909]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6032)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 10908,
     denoteGraphDistributedFaithful pm initPM 10909]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6032)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 6005 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 10986,
       denoteGraphDistributedFaithful pm initPM 10987] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 10986, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 10986,
          denoteGraphDistributedFaithful pm initPM 10987] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 10986, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 10908).shape := by
    exact g3l19_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 10909).shape := by
    exact g3l19_unshuffle1_shape _ _ _
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
