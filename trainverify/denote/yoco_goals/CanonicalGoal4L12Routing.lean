/- Canonical Goal 4, layer 12: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l12SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5628, 5656],
    outs := [5657], params := [1, 0] }

private def g4l12PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [9832, 5656],
    outs := [9910], params := [2, 0] }

private def g4l12PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [9833, 5656],
    outs := [9911], params := [2, 1] }

private theorem g4l12_sm_node :
    sm_goal_4.nodes[528]'(by native_decide) = g4l12SmUnshuffle := by
  native_decide

private theorem g4l12_pm_nodes :
    pm_goal_4.nodes[1166]'(by native_decide) = g4l12PmUnshuffle0 ∧
    pm_goal_4.nodes[1168]'(by native_decide) = g4l12PmUnshuffle1 := by
  native_decide

private theorem g4l12_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l12PmUnshuffle0 =
      [g4l12PmUnshuffle0, g4l12PmUnshuffle1] := by
  native_decide

private theorem g4l12_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l12PmUnshuffle1 =
      [g4l12PmUnshuffle0, g4l12PmUnshuffle1] := by
  native_decide

private theorem g4l12_sm_nonempty528 :
    ∀ n ∈ sm_goal_4.nodes.drop 528, n.outs ≠ [] := by native_decide
private theorem g4l12_sm_nonempty529 :
    ∀ n ∈ sm_goal_4.nodes.drop 529, n.outs ≠ [] := by native_decide
private theorem g4l12_pm_nonempty1166 :
    ∀ n ∈ pm_goal_4.nodes.drop 1166, n.outs ≠ [] := by native_decide
private theorem g4l12_pm_nonempty1167 :
    ∀ n ∈ pm_goal_4.nodes.drop 1167, n.outs ≠ [] := by native_decide
private theorem g4l12_pm_nonempty1168 :
    ∀ n ∈ pm_goal_4.nodes.drop 1168, n.outs ≠ [] := by native_decide
private theorem g4l12_pm_nonempty1169 :
    ∀ n ∈ pm_goal_4.nodes.drop 1169, n.outs ≠ [] := by native_decide

private theorem g4l12_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(529, 5657), (528, 5628), (528, 5656)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l12_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1167, 9910), (1169, 9911),
      (1166, 9832), (1166, 9833), (1166, 5656),
      (1168, 9832), (1168, 9833), (1168, 5656)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l12_red_sm5657 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5657 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 5628 := by
  let pre := (sm_goal_4.nodes.take 528).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 5657 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l12SmUnshuffle 5657 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 528 g4l12SmUnshuffle 5657
      (by native_decide) g4l12_sm_node g4l12_sm_nonempty529
      (g4l12_sm_not_written 529 5657 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l12SmUnshuffle 5657 =
      pre 5628 := by
    unfold g4l12SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5628, 5656],
        outs := [5657], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5628 = denoteGraphDistributedFaithful sm_goal_4 initSM 5628 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 528 5628
      g4l12_sm_nonempty528 (g4l12_sm_not_written 528 5628 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l12_red_pm9910 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9910 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 9832,
         denoteGraphDistributedFaithful pm_goal_4 initPM 9833]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5656)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1166).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 9910 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l12PmUnshuffle0 9910 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1166 g4l12PmUnshuffle0 9910
      (by native_decide) g4l12_pm_nodes.1 g4l12_pm_nonempty1167
      (g4l12_pm_not_written 1167 9910 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l12PmUnshuffle0 9910 =
      opfun (pre 9832) (pre 9833) (pre 5656) := by
    unfold g4l12PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [9832, 5656],
        outs := [9910], params := [2, 0] } =
        [g4l12PmUnshuffle0, g4l12PmUnshuffle1] from g4l12_pm_buddies0]
    unfold g4l12PmUnshuffle0 g4l12PmUnshuffle1 opfun
    rfl
  have h0 : pre 9832 = denoteGraphDistributedFaithful pm_goal_4 initPM 9832 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1166 9832
      g4l12_pm_nonempty1166 (g4l12_pm_not_written 1166 9832 (by decide))
  have h1 : pre 9833 = denoteGraphDistributedFaithful pm_goal_4 initPM 9833 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1166 9833
      g4l12_pm_nonempty1166 (g4l12_pm_not_written 1166 9833 (by decide))
  have hcu : pre 5656 = denoteGraphDistributedFaithful pm_goal_4 initPM 5656 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1166 5656
      g4l12_pm_nonempty1166 (g4l12_pm_not_written 1166 5656 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 9910 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l12PmUnshuffle0 9910 := hcore
    _ = opfun (pre 9832) (pre 9833) (pre 5656) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9832)
        (pre 9833) (pre 5656) := congrArg (fun x => opfun x (pre 9833) (pre 5656)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9832)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9833) (pre 5656) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9832) x
        (pre 5656)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9832)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9833)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5656) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9832)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9833)) hcu

private theorem g4l12_red_pm9911 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 9911 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 9832,
         denoteGraphDistributedFaithful pm_goal_4 initPM 9833]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5656)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1168).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 9911 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l12PmUnshuffle1 9911 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1168 g4l12PmUnshuffle1 9911
      (by native_decide) g4l12_pm_nodes.2 g4l12_pm_nonempty1169
      (g4l12_pm_not_written 1169 9911 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l12PmUnshuffle1 9911 =
      opfun (pre 9832) (pre 9833) (pre 5656) := by
    unfold g4l12PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [9833, 5656],
        outs := [9911], params := [2, 1] } =
        [g4l12PmUnshuffle0, g4l12PmUnshuffle1] from g4l12_pm_buddies1]
    unfold g4l12PmUnshuffle0 g4l12PmUnshuffle1 opfun
    rfl
  have h0 : pre 9832 = denoteGraphDistributedFaithful pm_goal_4 initPM 9832 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1168 9832
      g4l12_pm_nonempty1168 (g4l12_pm_not_written 1168 9832 (by decide))
  have h1 : pre 9833 = denoteGraphDistributedFaithful pm_goal_4 initPM 9833 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1168 9833
      g4l12_pm_nonempty1168 (g4l12_pm_not_written 1168 9833 (by decide))
  have hcu : pre 5656 = denoteGraphDistributedFaithful pm_goal_4 initPM 5656 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1168 5656
      g4l12_pm_nonempty1168 (g4l12_pm_not_written 1168 5656 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 9911 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l12PmUnshuffle1 9911 := hcore
    _ = opfun (pre 9832) (pre 9833) (pre 5656) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9832)
        (pre 9833) (pre 5656) := congrArg (fun x => opfun x (pre 9833) (pre 5656)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9832)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9833) (pre 5656) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9832) x
        (pre 5656)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9832)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9833)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5656) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9832)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9833)) hcu

private theorem g4l12_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (5656 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l12_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 5656 = initPM 5656 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 5656 (by
      intro n hn
      native_decide +revert) g4l12_cu_not_written

private theorem g4l12_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l12_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-12 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l12_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5628)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9832)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9833)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5656)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5656) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5657)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9910)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9911)
      [4096, 64] [2048, 64] := by
  have hcu := g4l12_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5656) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l12_red_sm5657 initSM
  have hpm0 := g4l12_red_pm9910 initPM
  have hpm1 := g4l12_red_pm9911 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 9832,
     denoteGraphDistributedFaithful pm_goal_4 initPM 9833]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5656)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 9832,
     denoteGraphDistributedFaithful pm_goal_4 initPM 9833]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5656)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 5628 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 9910,
       denoteGraphDistributedFaithful pm_goal_4 initPM 9911] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 9910, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 9910,
          denoteGraphDistributedFaithful pm_goal_4 initPM 9911] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 9910, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9832).shape := by
    exact g4l12_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9833).shape := by
    exact g4l12_unshuffle1_shape _ _ _
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
