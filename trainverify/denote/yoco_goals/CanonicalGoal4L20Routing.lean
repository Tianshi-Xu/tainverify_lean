/- Canonical Goal 4, layer 20: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l20SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6060, 6088],
    outs := [6089], params := [1, 0] }

private def g4l20PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11064, 6088],
    outs := [11142], params := [2, 0] }

private def g4l20PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11065, 6088],
    outs := [11143], params := [2, 1] }

private theorem g4l20_sm_node :
    sm_goal_4.nodes[816]'(by native_decide) = g4l20SmUnshuffle := by
  native_decide

private theorem g4l20_pm_nodes :
    pm_goal_4.nodes[1790]'(by native_decide) = g4l20PmUnshuffle0 ∧
    pm_goal_4.nodes[1792]'(by native_decide) = g4l20PmUnshuffle1 := by
  native_decide

private theorem g4l20_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l20PmUnshuffle0 =
      [g4l20PmUnshuffle0, g4l20PmUnshuffle1] := by
  native_decide

private theorem g4l20_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l20PmUnshuffle1 =
      [g4l20PmUnshuffle0, g4l20PmUnshuffle1] := by
  native_decide

private theorem g4l20_sm_nonempty816 :
    ∀ n ∈ sm_goal_4.nodes.drop 816, n.outs ≠ [] := by native_decide
private theorem g4l20_sm_nonempty817 :
    ∀ n ∈ sm_goal_4.nodes.drop 817, n.outs ≠ [] := by native_decide
private theorem g4l20_pm_nonempty1790 :
    ∀ n ∈ pm_goal_4.nodes.drop 1790, n.outs ≠ [] := by native_decide
private theorem g4l20_pm_nonempty1791 :
    ∀ n ∈ pm_goal_4.nodes.drop 1791, n.outs ≠ [] := by native_decide
private theorem g4l20_pm_nonempty1792 :
    ∀ n ∈ pm_goal_4.nodes.drop 1792, n.outs ≠ [] := by native_decide
private theorem g4l20_pm_nonempty1793 :
    ∀ n ∈ pm_goal_4.nodes.drop 1793, n.outs ≠ [] := by native_decide

private theorem g4l20_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(817, 6089), (816, 6060), (816, 6088)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l20_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1791, 11142), (1793, 11143),
      (1790, 11064), (1790, 11065), (1790, 6088),
      (1792, 11064), (1792, 11065), (1792, 6088)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l20_red_sm6089 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 6089 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 6060 := by
  let pre := (sm_goal_4.nodes.take 816).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 6089 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l20SmUnshuffle 6089 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 816 g4l20SmUnshuffle 6089
      (by native_decide) g4l20_sm_node g4l20_sm_nonempty817
      (g4l20_sm_not_written 817 6089 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l20SmUnshuffle 6089 =
      pre 6060 := by
    unfold g4l20SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6060, 6088],
        outs := [6089], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 6060 = denoteGraphDistributedFaithful sm_goal_4 initSM 6060 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 816 6060
      g4l20_sm_nonempty816 (g4l20_sm_not_written 816 6060 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l20_red_pm11142 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 11142 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 11064,
         denoteGraphDistributedFaithful pm_goal_4 initPM 11065]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6088)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1790).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 11142 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l20PmUnshuffle0 11142 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1790 g4l20PmUnshuffle0 11142
      (by native_decide) g4l20_pm_nodes.1 g4l20_pm_nonempty1791
      (g4l20_pm_not_written 1791 11142 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l20PmUnshuffle0 11142 =
      opfun (pre 11064) (pre 11065) (pre 6088) := by
    unfold g4l20PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11064, 6088],
        outs := [11142], params := [2, 0] } =
        [g4l20PmUnshuffle0, g4l20PmUnshuffle1] from g4l20_pm_buddies0]
    unfold g4l20PmUnshuffle0 g4l20PmUnshuffle1 opfun
    rfl
  have h0 : pre 11064 = denoteGraphDistributedFaithful pm_goal_4 initPM 11064 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1790 11064
      g4l20_pm_nonempty1790 (g4l20_pm_not_written 1790 11064 (by decide))
  have h1 : pre 11065 = denoteGraphDistributedFaithful pm_goal_4 initPM 11065 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1790 11065
      g4l20_pm_nonempty1790 (g4l20_pm_not_written 1790 11065 (by decide))
  have hcu : pre 6088 = denoteGraphDistributedFaithful pm_goal_4 initPM 6088 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1790 6088
      g4l20_pm_nonempty1790 (g4l20_pm_not_written 1790 6088 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 11142 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l20PmUnshuffle0 11142 := hcore
    _ = opfun (pre 11064) (pre 11065) (pre 6088) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
        (pre 11065) (pre 6088) := congrArg (fun x => opfun x (pre 11065) (pre 6088)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11065) (pre 6088) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11064) x
        (pre 6088)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11065)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 6088) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11065)) hcu

private theorem g4l20_red_pm11143 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 11143 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 11064,
         denoteGraphDistributedFaithful pm_goal_4 initPM 11065]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6088)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1792).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 11143 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l20PmUnshuffle1 11143 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1792 g4l20PmUnshuffle1 11143
      (by native_decide) g4l20_pm_nodes.2 g4l20_pm_nonempty1793
      (g4l20_pm_not_written 1793 11143 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l20PmUnshuffle1 11143 =
      opfun (pre 11064) (pre 11065) (pre 6088) := by
    unfold g4l20PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11065, 6088],
        outs := [11143], params := [2, 1] } =
        [g4l20PmUnshuffle0, g4l20PmUnshuffle1] from g4l20_pm_buddies1]
    unfold g4l20PmUnshuffle0 g4l20PmUnshuffle1 opfun
    rfl
  have h0 : pre 11064 = denoteGraphDistributedFaithful pm_goal_4 initPM 11064 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1792 11064
      g4l20_pm_nonempty1792 (g4l20_pm_not_written 1792 11064 (by decide))
  have h1 : pre 11065 = denoteGraphDistributedFaithful pm_goal_4 initPM 11065 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1792 11065
      g4l20_pm_nonempty1792 (g4l20_pm_not_written 1792 11065 (by decide))
  have hcu : pre 6088 = denoteGraphDistributedFaithful pm_goal_4 initPM 6088 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1792 6088
      g4l20_pm_nonempty1792 (g4l20_pm_not_written 1792 6088 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 11143 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l20PmUnshuffle1 11143 := hcore
    _ = opfun (pre 11064) (pre 11065) (pre 6088) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
        (pre 11065) (pre 6088) := congrArg (fun x => opfun x (pre 11065) (pre 6088)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11065) (pre 6088) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11064) x
        (pre 6088)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11065)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 6088) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11065)) hcu

private theorem g4l20_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (6088 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l20_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 6088 = initPM 6088 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 6088 (by
      intro n hn
      native_decide +revert) g4l20_cu_not_written

private theorem g4l20_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l20_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-20 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l20_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 6060)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11064)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11065)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 6088)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 6088) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 6089)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11142)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11143)
      [4096, 64] [2048, 64] := by
  have hcu := g4l20_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 6088) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l20_red_sm6089 initSM
  have hpm0 := g4l20_red_pm11142 initPM
  have hpm1 := g4l20_red_pm11143 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 11064,
     denoteGraphDistributedFaithful pm_goal_4 initPM 11065]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6088)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 11064,
     denoteGraphDistributedFaithful pm_goal_4 initPM 11065]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6088)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 6060 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 11142,
       denoteGraphDistributedFaithful pm_goal_4 initPM 11143] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 11142, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 11142,
          denoteGraphDistributedFaithful pm_goal_4 initPM 11143] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 11142, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11064).shape := by
    exact g4l20_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11065).shape := by
    exact g4l20_unshuffle1_shape _ _ _
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

