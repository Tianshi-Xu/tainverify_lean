/- Canonical Goal 3, layer 12: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l12SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5627, 5654],
    outs := [5655], params := [1, 0] }

private def g3l12PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [9830, 5654],
    outs := [9908], params := [2, 0] }

private def g3l12PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [9831, 5654],
    outs := [9909], params := [2, 1] }

private theorem g3l12_sm_node :
    sm.nodes[528]'(by native_decide) = g3l12SmUnshuffle := by
  native_decide

private theorem g3l12_pm_nodes :
    pm.nodes[1168]'(by native_decide) = g3l12PmUnshuffle0 ∧
    pm.nodes[1171]'(by native_decide) = g3l12PmUnshuffle1 := by
  native_decide

private theorem g3l12_pm_buddies0 :
    pm.replicaBuddies g3l12PmUnshuffle0 =
      [g3l12PmUnshuffle0, g3l12PmUnshuffle1] := by
  native_decide

private theorem g3l12_pm_buddies1 :
    pm.replicaBuddies g3l12PmUnshuffle1 =
      [g3l12PmUnshuffle0, g3l12PmUnshuffle1] := by
  native_decide

private theorem g3l12_sm_nonempty528 :
    ∀ n ∈ sm.nodes.drop 528, n.outs ≠ [] := by native_decide
private theorem g3l12_sm_nonempty529 :
    ∀ n ∈ sm.nodes.drop 529, n.outs ≠ [] := by native_decide
private theorem g3l12_pm_nonempty1168 :
    ∀ n ∈ pm.nodes.drop 1168, n.outs ≠ [] := by native_decide
private theorem g3l12_pm_nonempty1169 :
    ∀ n ∈ pm.nodes.drop 1169, n.outs ≠ [] := by native_decide
private theorem g3l12_pm_nonempty1171 :
    ∀ n ∈ pm.nodes.drop 1171, n.outs ≠ [] := by native_decide
private theorem g3l12_pm_nonempty1172 :
    ∀ n ∈ pm.nodes.drop 1172, n.outs ≠ [] := by native_decide

private theorem g3l12_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(529, 5655), (528, 5627), (528, 5654)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l12_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1169, 9908), (1172, 9909),
      (1168, 9830), (1168, 9831), (1168, 5654),
      (1171, 9830), (1171, 9831), (1171, 5654)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l12_red_sm5655 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5655 =
      denoteGraphDistributedFaithful sm initSM 5627 := by
  let pre := (sm.nodes.take 528).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 5655 =
      applyNodeDistributedFaithful sm pre g3l12SmUnshuffle 5655 :=
    denoteGraphDistributedFaithful_node_core sm initSM 528 g3l12SmUnshuffle 5655
      (by native_decide) g3l12_sm_node g3l12_sm_nonempty529
      (g3l12_sm_not_written 529 5655 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l12SmUnshuffle 5655 =
      pre 5627 := by
    unfold g3l12SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5627, 5654],
        outs := [5655], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5627 = denoteGraphDistributedFaithful sm initSM 5627 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 528 5627
      g3l12_sm_nonempty528 (g3l12_sm_not_written 528 5627 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l12_red_pm9908 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9908 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 9830,
         denoteGraphDistributedFaithful pm initPM 9831]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5654)) 2 0 := by
  let pre := (pm.nodes.take 1168).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 9908 =
      applyNodeDistributedFaithful pm pre g3l12PmUnshuffle0 9908 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1168 g3l12PmUnshuffle0 9908
      (by native_decide) g3l12_pm_nodes.1 g3l12_pm_nonempty1169
      (g3l12_pm_not_written 1169 9908 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l12PmUnshuffle0 9908 =
      opfun (pre 9830) (pre 9831) (pre 5654) := by
    unfold g3l12PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [9830, 5654],
        outs := [9908], params := [2, 0] } =
        [g3l12PmUnshuffle0, g3l12PmUnshuffle1] from g3l12_pm_buddies0]
    unfold g3l12PmUnshuffle0 g3l12PmUnshuffle1 opfun
    rfl
  have h0 : pre 9830 = denoteGraphDistributedFaithful pm initPM 9830 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1168 9830
      g3l12_pm_nonempty1168 (g3l12_pm_not_written 1168 9830 (by decide))
  have h1 : pre 9831 = denoteGraphDistributedFaithful pm initPM 9831 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1168 9831
      g3l12_pm_nonempty1168 (g3l12_pm_not_written 1168 9831 (by decide))
  have hcu : pre 5654 = denoteGraphDistributedFaithful pm initPM 5654 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1168 5654
      g3l12_pm_nonempty1168 (g3l12_pm_not_written 1168 5654 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 9908 =
        applyNodeDistributedFaithful pm pre g3l12PmUnshuffle0 9908 := hcore
    _ = opfun (pre 9830) (pre 9831) (pre 5654) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9830)
        (pre 9831) (pre 5654) := congrArg (fun x => opfun x (pre 9831) (pre 5654)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9830)
        (denoteGraphDistributedFaithful pm initPM 9831) (pre 5654) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 9830) x
        (pre 5654)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9830)
        (denoteGraphDistributedFaithful pm initPM 9831)
        (denoteGraphDistributedFaithful pm initPM 5654) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 9830)
        (denoteGraphDistributedFaithful pm initPM 9831)) hcu

private theorem g3l12_red_pm9909 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 9909 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 9830,
         denoteGraphDistributedFaithful pm initPM 9831]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5654)) 2 1 := by
  let pre := (pm.nodes.take 1171).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 9909 =
      applyNodeDistributedFaithful pm pre g3l12PmUnshuffle1 9909 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1171 g3l12PmUnshuffle1 9909
      (by native_decide) g3l12_pm_nodes.2 g3l12_pm_nonempty1172
      (g3l12_pm_not_written 1172 9909 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l12PmUnshuffle1 9909 =
      opfun (pre 9830) (pre 9831) (pre 5654) := by
    unfold g3l12PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [9831, 5654],
        outs := [9909], params := [2, 1] } =
        [g3l12PmUnshuffle0, g3l12PmUnshuffle1] from g3l12_pm_buddies1]
    unfold g3l12PmUnshuffle0 g3l12PmUnshuffle1 opfun
    rfl
  have h0 : pre 9830 = denoteGraphDistributedFaithful pm initPM 9830 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1171 9830
      g3l12_pm_nonempty1171 (g3l12_pm_not_written 1171 9830 (by decide))
  have h1 : pre 9831 = denoteGraphDistributedFaithful pm initPM 9831 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1171 9831
      g3l12_pm_nonempty1171 (g3l12_pm_not_written 1171 9831 (by decide))
  have hcu : pre 5654 = denoteGraphDistributedFaithful pm initPM 5654 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1171 5654
      g3l12_pm_nonempty1171 (g3l12_pm_not_written 1171 5654 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 9909 =
        applyNodeDistributedFaithful pm pre g3l12PmUnshuffle1 9909 := hcore
    _ = opfun (pre 9830) (pre 9831) (pre 5654) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9830)
        (pre 9831) (pre 5654) := congrArg (fun x => opfun x (pre 9831) (pre 5654)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9830)
        (denoteGraphDistributedFaithful pm initPM 9831) (pre 5654) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 9830) x
        (pre 5654)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9830)
        (denoteGraphDistributedFaithful pm initPM 9831)
        (denoteGraphDistributedFaithful pm initPM 5654) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 9830)
        (denoteGraphDistributedFaithful pm initPM 9831)) hcu

private theorem g3l12_cu_not_written :
    ∀ n ∈ pm.nodes, (5654 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l12_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 5654 = initPM 5654 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 5654 (by
      intro n hn
      native_decide +revert) g3l12_cu_not_written

private theorem g3l12_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l12_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-12 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l12_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5627)
      (denoteGraphDistributedFaithful pm initPM 9830)
      (denoteGraphDistributedFaithful pm initPM 9831)
      (denoteGraphDistributedFaithful pm initPM 5654)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5654) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 5655)
      (denoteGraphDistributedFaithful pm initPM 9908)
      (denoteGraphDistributedFaithful pm initPM 9909)
      [4096, 64] [2048, 64] := by
  have hcu := g3l12_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5654) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l12_red_sm5655 initSM
  have hpm0 := g3l12_red_pm9908 initPM
  have hpm1 := g3l12_red_pm9909 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 9830,
     denoteGraphDistributedFaithful pm initPM 9831]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5654)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 9830,
     denoteGraphDistributedFaithful pm initPM 9831]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5654)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 5627 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 9908,
       denoteGraphDistributedFaithful pm initPM 9909] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 9908, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 9908,
          denoteGraphDistributedFaithful pm initPM 9909] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 9908, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 9830).shape := by
    exact g3l12_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 9831).shape := by
    exact g3l12_unshuffle1_shape _ _ _
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
