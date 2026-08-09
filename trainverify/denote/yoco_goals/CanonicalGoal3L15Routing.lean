/- Canonical Goal 3, layer 15: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l15SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5789, 5816],
    outs := [5817], params := [1, 0] }

private def g3l15PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10292, 5816],
    outs := [10370], params := [2, 0] }

private def g3l15PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10293, 5816],
    outs := [10371], params := [2, 1] }

private theorem g3l15_sm_node :
    sm.nodes[639]'(by native_decide) = g3l15SmUnshuffle := by
  native_decide

private theorem g3l15_pm_nodes :
    pm.nodes[1408]'(by native_decide) = g3l15PmUnshuffle0 ∧
    pm.nodes[1411]'(by native_decide) = g3l15PmUnshuffle1 := by
  native_decide

private theorem g3l15_pm_buddies0 :
    pm.replicaBuddies g3l15PmUnshuffle0 =
      [g3l15PmUnshuffle0, g3l15PmUnshuffle1] := by
  native_decide

private theorem g3l15_pm_buddies1 :
    pm.replicaBuddies g3l15PmUnshuffle1 =
      [g3l15PmUnshuffle0, g3l15PmUnshuffle1] := by
  native_decide

private theorem g3l15_sm_nonempty639 :
    ∀ n ∈ sm.nodes.drop 639, n.outs ≠ [] := by native_decide
private theorem g3l15_sm_nonempty640 :
    ∀ n ∈ sm.nodes.drop 640, n.outs ≠ [] := by native_decide
private theorem g3l15_pm_nonempty1408 :
    ∀ n ∈ pm.nodes.drop 1408, n.outs ≠ [] := by native_decide
private theorem g3l15_pm_nonempty1409 :
    ∀ n ∈ pm.nodes.drop 1409, n.outs ≠ [] := by native_decide
private theorem g3l15_pm_nonempty1411 :
    ∀ n ∈ pm.nodes.drop 1411, n.outs ≠ [] := by native_decide
private theorem g3l15_pm_nonempty1412 :
    ∀ n ∈ pm.nodes.drop 1412, n.outs ≠ [] := by native_decide

private theorem g3l15_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(640, 5817), (639, 5789), (639, 5816)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l15_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1409, 10370), (1412, 10371),
      (1408, 10292), (1408, 10293), (1408, 5816),
      (1411, 10292), (1411, 10293), (1411, 5816)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l15_red_sm5817 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5817 =
      denoteGraphDistributedFaithful sm initSM 5789 := by
  let pre := (sm.nodes.take 639).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 5817 =
      applyNodeDistributedFaithful sm pre g3l15SmUnshuffle 5817 :=
    denoteGraphDistributedFaithful_node_core sm initSM 639 g3l15SmUnshuffle 5817
      (by native_decide) g3l15_sm_node g3l15_sm_nonempty640
      (g3l15_sm_not_written 640 5817 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l15SmUnshuffle 5817 =
      pre 5789 := by
    unfold g3l15SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5789, 5816],
        outs := [5817], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5789 = denoteGraphDistributedFaithful sm initSM 5789 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 639 5789
      g3l15_sm_nonempty639 (g3l15_sm_not_written 639 5789 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l15_red_pm10370 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10370 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 10292,
         denoteGraphDistributedFaithful pm initPM 10293]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5816)) 2 0 := by
  let pre := (pm.nodes.take 1408).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 10370 =
      applyNodeDistributedFaithful pm pre g3l15PmUnshuffle0 10370 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1408 g3l15PmUnshuffle0 10370
      (by native_decide) g3l15_pm_nodes.1 g3l15_pm_nonempty1409
      (g3l15_pm_not_written 1409 10370 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l15PmUnshuffle0 10370 =
      opfun (pre 10292) (pre 10293) (pre 5816) := by
    unfold g3l15PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10292, 5816],
        outs := [10370], params := [2, 0] } =
        [g3l15PmUnshuffle0, g3l15PmUnshuffle1] from g3l15_pm_buddies0]
    unfold g3l15PmUnshuffle0 g3l15PmUnshuffle1 opfun
    rfl
  have h0 : pre 10292 = denoteGraphDistributedFaithful pm initPM 10292 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1408 10292
      g3l15_pm_nonempty1408 (g3l15_pm_not_written 1408 10292 (by decide))
  have h1 : pre 10293 = denoteGraphDistributedFaithful pm initPM 10293 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1408 10293
      g3l15_pm_nonempty1408 (g3l15_pm_not_written 1408 10293 (by decide))
  have hcu : pre 5816 = denoteGraphDistributedFaithful pm initPM 5816 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1408 5816
      g3l15_pm_nonempty1408 (g3l15_pm_not_written 1408 5816 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10370 =
        applyNodeDistributedFaithful pm pre g3l15PmUnshuffle0 10370 := hcore
    _ = opfun (pre 10292) (pre 10293) (pre 5816) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10292)
        (pre 10293) (pre 5816) := congrArg (fun x => opfun x (pre 10293) (pre 5816)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10292)
        (denoteGraphDistributedFaithful pm initPM 10293) (pre 5816) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 10292) x
        (pre 5816)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10292)
        (denoteGraphDistributedFaithful pm initPM 10293)
        (denoteGraphDistributedFaithful pm initPM 5816) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 10292)
        (denoteGraphDistributedFaithful pm initPM 10293)) hcu

private theorem g3l15_red_pm10371 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10371 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 10292,
         denoteGraphDistributedFaithful pm initPM 10293]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5816)) 2 1 := by
  let pre := (pm.nodes.take 1411).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 10371 =
      applyNodeDistributedFaithful pm pre g3l15PmUnshuffle1 10371 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1411 g3l15PmUnshuffle1 10371
      (by native_decide) g3l15_pm_nodes.2 g3l15_pm_nonempty1412
      (g3l15_pm_not_written 1412 10371 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l15PmUnshuffle1 10371 =
      opfun (pre 10292) (pre 10293) (pre 5816) := by
    unfold g3l15PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10293, 5816],
        outs := [10371], params := [2, 1] } =
        [g3l15PmUnshuffle0, g3l15PmUnshuffle1] from g3l15_pm_buddies1]
    unfold g3l15PmUnshuffle0 g3l15PmUnshuffle1 opfun
    rfl
  have h0 : pre 10292 = denoteGraphDistributedFaithful pm initPM 10292 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1411 10292
      g3l15_pm_nonempty1411 (g3l15_pm_not_written 1411 10292 (by decide))
  have h1 : pre 10293 = denoteGraphDistributedFaithful pm initPM 10293 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1411 10293
      g3l15_pm_nonempty1411 (g3l15_pm_not_written 1411 10293 (by decide))
  have hcu : pre 5816 = denoteGraphDistributedFaithful pm initPM 5816 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1411 5816
      g3l15_pm_nonempty1411 (g3l15_pm_not_written 1411 5816 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10371 =
        applyNodeDistributedFaithful pm pre g3l15PmUnshuffle1 10371 := hcore
    _ = opfun (pre 10292) (pre 10293) (pre 5816) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10292)
        (pre 10293) (pre 5816) := congrArg (fun x => opfun x (pre 10293) (pre 5816)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10292)
        (denoteGraphDistributedFaithful pm initPM 10293) (pre 5816) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 10292) x
        (pre 5816)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10292)
        (denoteGraphDistributedFaithful pm initPM 10293)
        (denoteGraphDistributedFaithful pm initPM 5816) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 10292)
        (denoteGraphDistributedFaithful pm initPM 10293)) hcu

private theorem g3l15_cu_not_written :
    ∀ n ∈ pm.nodes, (5816 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l15_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 5816 = initPM 5816 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 5816 (by
      intro n hn
      native_decide +revert) g3l15_cu_not_written

private theorem g3l15_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l15_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-15 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l15_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5789)
      (denoteGraphDistributedFaithful pm initPM 10292)
      (denoteGraphDistributedFaithful pm initPM 10293)
      (denoteGraphDistributedFaithful pm initPM 5816)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5816) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 5817)
      (denoteGraphDistributedFaithful pm initPM 10370)
      (denoteGraphDistributedFaithful pm initPM 10371)
      [4096, 64] [2048, 64] := by
  have hcu := g3l15_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5816) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l15_red_sm5817 initSM
  have hpm0 := g3l15_red_pm10370 initPM
  have hpm1 := g3l15_red_pm10371 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 10292,
     denoteGraphDistributedFaithful pm initPM 10293]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5816)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 10292,
     denoteGraphDistributedFaithful pm initPM 10293]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5816)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 5789 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 10370,
       denoteGraphDistributedFaithful pm initPM 10371] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 10370, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 10370,
          denoteGraphDistributedFaithful pm initPM 10371] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 10370, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 10292).shape := by
    exact g3l15_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 10293).shape := by
    exact g3l15_unshuffle1_shape _ _ _
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
