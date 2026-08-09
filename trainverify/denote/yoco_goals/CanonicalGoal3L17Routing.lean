/- Canonical Goal 3, layer 17: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l17SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5897, 5924],
    outs := [5925], params := [1, 0] }

private def g3l17PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10600, 5924],
    outs := [10678], params := [2, 0] }

private def g3l17PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10601, 5924],
    outs := [10679], params := [2, 1] }

private theorem g3l17_sm_node :
    sm.nodes[713]'(by native_decide) = g3l17SmUnshuffle := by
  native_decide

private theorem g3l17_pm_nodes :
    pm.nodes[1568]'(by native_decide) = g3l17PmUnshuffle0 ∧
    pm.nodes[1571]'(by native_decide) = g3l17PmUnshuffle1 := by
  native_decide

private theorem g3l17_pm_buddies0 :
    pm.replicaBuddies g3l17PmUnshuffle0 =
      [g3l17PmUnshuffle0, g3l17PmUnshuffle1] := by
  native_decide

private theorem g3l17_pm_buddies1 :
    pm.replicaBuddies g3l17PmUnshuffle1 =
      [g3l17PmUnshuffle0, g3l17PmUnshuffle1] := by
  native_decide

private theorem g3l17_sm_nonempty713 :
    ∀ n ∈ sm.nodes.drop 713, n.outs ≠ [] := by native_decide
private theorem g3l17_sm_nonempty714 :
    ∀ n ∈ sm.nodes.drop 714, n.outs ≠ [] := by native_decide
private theorem g3l17_pm_nonempty1568 :
    ∀ n ∈ pm.nodes.drop 1568, n.outs ≠ [] := by native_decide
private theorem g3l17_pm_nonempty1569 :
    ∀ n ∈ pm.nodes.drop 1569, n.outs ≠ [] := by native_decide
private theorem g3l17_pm_nonempty1571 :
    ∀ n ∈ pm.nodes.drop 1571, n.outs ≠ [] := by native_decide
private theorem g3l17_pm_nonempty1572 :
    ∀ n ∈ pm.nodes.drop 1572, n.outs ≠ [] := by native_decide

private theorem g3l17_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(714, 5925), (713, 5897), (713, 5924)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l17_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1569, 10678), (1572, 10679),
      (1568, 10600), (1568, 10601), (1568, 5924),
      (1571, 10600), (1571, 10601), (1571, 5924)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l17_red_sm5925 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5925 =
      denoteGraphDistributedFaithful sm initSM 5897 := by
  let pre := (sm.nodes.take 713).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 5925 =
      applyNodeDistributedFaithful sm pre g3l17SmUnshuffle 5925 :=
    denoteGraphDistributedFaithful_node_core sm initSM 713 g3l17SmUnshuffle 5925
      (by native_decide) g3l17_sm_node g3l17_sm_nonempty714
      (g3l17_sm_not_written 714 5925 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l17SmUnshuffle 5925 =
      pre 5897 := by
    unfold g3l17SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5897, 5924],
        outs := [5925], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5897 = denoteGraphDistributedFaithful sm initSM 5897 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 713 5897
      g3l17_sm_nonempty713 (g3l17_sm_not_written 713 5897 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l17_red_pm10678 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10678 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 10600,
         denoteGraphDistributedFaithful pm initPM 10601]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5924)) 2 0 := by
  let pre := (pm.nodes.take 1568).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 10678 =
      applyNodeDistributedFaithful pm pre g3l17PmUnshuffle0 10678 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1568 g3l17PmUnshuffle0 10678
      (by native_decide) g3l17_pm_nodes.1 g3l17_pm_nonempty1569
      (g3l17_pm_not_written 1569 10678 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l17PmUnshuffle0 10678 =
      opfun (pre 10600) (pre 10601) (pre 5924) := by
    unfold g3l17PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10600, 5924],
        outs := [10678], params := [2, 0] } =
        [g3l17PmUnshuffle0, g3l17PmUnshuffle1] from g3l17_pm_buddies0]
    unfold g3l17PmUnshuffle0 g3l17PmUnshuffle1 opfun
    rfl
  have h0 : pre 10600 = denoteGraphDistributedFaithful pm initPM 10600 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1568 10600
      g3l17_pm_nonempty1568 (g3l17_pm_not_written 1568 10600 (by decide))
  have h1 : pre 10601 = denoteGraphDistributedFaithful pm initPM 10601 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1568 10601
      g3l17_pm_nonempty1568 (g3l17_pm_not_written 1568 10601 (by decide))
  have hcu : pre 5924 = denoteGraphDistributedFaithful pm initPM 5924 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1568 5924
      g3l17_pm_nonempty1568 (g3l17_pm_not_written 1568 5924 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10678 =
        applyNodeDistributedFaithful pm pre g3l17PmUnshuffle0 10678 := hcore
    _ = opfun (pre 10600) (pre 10601) (pre 5924) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10600)
        (pre 10601) (pre 5924) := congrArg (fun x => opfun x (pre 10601) (pre 5924)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10600)
        (denoteGraphDistributedFaithful pm initPM 10601) (pre 5924) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 10600) x
        (pre 5924)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10600)
        (denoteGraphDistributedFaithful pm initPM 10601)
        (denoteGraphDistributedFaithful pm initPM 5924) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 10600)
        (denoteGraphDistributedFaithful pm initPM 10601)) hcu

private theorem g3l17_red_pm10679 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10679 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 10600,
         denoteGraphDistributedFaithful pm initPM 10601]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5924)) 2 1 := by
  let pre := (pm.nodes.take 1571).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 10679 =
      applyNodeDistributedFaithful pm pre g3l17PmUnshuffle1 10679 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1571 g3l17PmUnshuffle1 10679
      (by native_decide) g3l17_pm_nodes.2 g3l17_pm_nonempty1572
      (g3l17_pm_not_written 1572 10679 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l17PmUnshuffle1 10679 =
      opfun (pre 10600) (pre 10601) (pre 5924) := by
    unfold g3l17PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10601, 5924],
        outs := [10679], params := [2, 1] } =
        [g3l17PmUnshuffle0, g3l17PmUnshuffle1] from g3l17_pm_buddies1]
    unfold g3l17PmUnshuffle0 g3l17PmUnshuffle1 opfun
    rfl
  have h0 : pre 10600 = denoteGraphDistributedFaithful pm initPM 10600 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1571 10600
      g3l17_pm_nonempty1571 (g3l17_pm_not_written 1571 10600 (by decide))
  have h1 : pre 10601 = denoteGraphDistributedFaithful pm initPM 10601 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1571 10601
      g3l17_pm_nonempty1571 (g3l17_pm_not_written 1571 10601 (by decide))
  have hcu : pre 5924 = denoteGraphDistributedFaithful pm initPM 5924 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1571 5924
      g3l17_pm_nonempty1571 (g3l17_pm_not_written 1571 5924 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10679 =
        applyNodeDistributedFaithful pm pre g3l17PmUnshuffle1 10679 := hcore
    _ = opfun (pre 10600) (pre 10601) (pre 5924) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10600)
        (pre 10601) (pre 5924) := congrArg (fun x => opfun x (pre 10601) (pre 5924)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10600)
        (denoteGraphDistributedFaithful pm initPM 10601) (pre 5924) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 10600) x
        (pre 5924)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10600)
        (denoteGraphDistributedFaithful pm initPM 10601)
        (denoteGraphDistributedFaithful pm initPM 5924) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 10600)
        (denoteGraphDistributedFaithful pm initPM 10601)) hcu

private theorem g3l17_cu_not_written :
    ∀ n ∈ pm.nodes, (5924 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l17_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 5924 = initPM 5924 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 5924 (by
      intro n hn
      native_decide +revert) g3l17_cu_not_written

private theorem g3l17_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l17_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-17 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l17_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5897)
      (denoteGraphDistributedFaithful pm initPM 10600)
      (denoteGraphDistributedFaithful pm initPM 10601)
      (denoteGraphDistributedFaithful pm initPM 5924)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5924) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 5925)
      (denoteGraphDistributedFaithful pm initPM 10678)
      (denoteGraphDistributedFaithful pm initPM 10679)
      [4096, 64] [2048, 64] := by
  have hcu := g3l17_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5924) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l17_red_sm5925 initSM
  have hpm0 := g3l17_red_pm10678 initPM
  have hpm1 := g3l17_red_pm10679 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 10600,
     denoteGraphDistributedFaithful pm initPM 10601]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5924)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 10600,
     denoteGraphDistributedFaithful pm initPM 10601]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5924)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 5897 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 10678,
       denoteGraphDistributedFaithful pm initPM 10679] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 10678, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 10678,
          denoteGraphDistributedFaithful pm initPM 10679] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 10678, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 10600).shape := by
    exact g3l17_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 10601).shape := by
    exact g3l17_unshuffle1_shape _ _ _
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
