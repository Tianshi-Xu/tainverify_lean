/- Canonical Goal 3, layer 16: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l16SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5843, 5870],
    outs := [5871], params := [1, 0] }

private def g3l16PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10446, 5870],
    outs := [10524], params := [2, 0] }

private def g3l16PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10447, 5870],
    outs := [10525], params := [2, 1] }

private theorem g3l16_sm_node :
    sm.nodes[676]'(by native_decide) = g3l16SmUnshuffle := by
  native_decide

private theorem g3l16_pm_nodes :
    pm.nodes[1488]'(by native_decide) = g3l16PmUnshuffle0 ∧
    pm.nodes[1491]'(by native_decide) = g3l16PmUnshuffle1 := by
  native_decide

private theorem g3l16_pm_buddies0 :
    pm.replicaBuddies g3l16PmUnshuffle0 =
      [g3l16PmUnshuffle0, g3l16PmUnshuffle1] := by
  native_decide

private theorem g3l16_pm_buddies1 :
    pm.replicaBuddies g3l16PmUnshuffle1 =
      [g3l16PmUnshuffle0, g3l16PmUnshuffle1] := by
  native_decide

private theorem g3l16_sm_nonempty676 :
    ∀ n ∈ sm.nodes.drop 676, n.outs ≠ [] := by native_decide
private theorem g3l16_sm_nonempty677 :
    ∀ n ∈ sm.nodes.drop 677, n.outs ≠ [] := by native_decide
private theorem g3l16_pm_nonempty1488 :
    ∀ n ∈ pm.nodes.drop 1488, n.outs ≠ [] := by native_decide
private theorem g3l16_pm_nonempty1489 :
    ∀ n ∈ pm.nodes.drop 1489, n.outs ≠ [] := by native_decide
private theorem g3l16_pm_nonempty1491 :
    ∀ n ∈ pm.nodes.drop 1491, n.outs ≠ [] := by native_decide
private theorem g3l16_pm_nonempty1492 :
    ∀ n ∈ pm.nodes.drop 1492, n.outs ≠ [] := by native_decide

private theorem g3l16_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(677, 5871), (676, 5843), (676, 5870)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l16_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1489, 10524), (1492, 10525),
      (1488, 10446), (1488, 10447), (1488, 5870),
      (1491, 10446), (1491, 10447), (1491, 5870)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l16_red_sm5871 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5871 =
      denoteGraphDistributedFaithful sm initSM 5843 := by
  let pre := (sm.nodes.take 676).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 5871 =
      applyNodeDistributedFaithful sm pre g3l16SmUnshuffle 5871 :=
    denoteGraphDistributedFaithful_node_core sm initSM 676 g3l16SmUnshuffle 5871
      (by native_decide) g3l16_sm_node g3l16_sm_nonempty677
      (g3l16_sm_not_written 677 5871 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l16SmUnshuffle 5871 =
      pre 5843 := by
    unfold g3l16SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5843, 5870],
        outs := [5871], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5843 = denoteGraphDistributedFaithful sm initSM 5843 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 676 5843
      g3l16_sm_nonempty676 (g3l16_sm_not_written 676 5843 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l16_red_pm10524 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10524 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 10446,
         denoteGraphDistributedFaithful pm initPM 10447]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5870)) 2 0 := by
  let pre := (pm.nodes.take 1488).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 10524 =
      applyNodeDistributedFaithful pm pre g3l16PmUnshuffle0 10524 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1488 g3l16PmUnshuffle0 10524
      (by native_decide) g3l16_pm_nodes.1 g3l16_pm_nonempty1489
      (g3l16_pm_not_written 1489 10524 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l16PmUnshuffle0 10524 =
      opfun (pre 10446) (pre 10447) (pre 5870) := by
    unfold g3l16PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10446, 5870],
        outs := [10524], params := [2, 0] } =
        [g3l16PmUnshuffle0, g3l16PmUnshuffle1] from g3l16_pm_buddies0]
    unfold g3l16PmUnshuffle0 g3l16PmUnshuffle1 opfun
    rfl
  have h0 : pre 10446 = denoteGraphDistributedFaithful pm initPM 10446 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1488 10446
      g3l16_pm_nonempty1488 (g3l16_pm_not_written 1488 10446 (by decide))
  have h1 : pre 10447 = denoteGraphDistributedFaithful pm initPM 10447 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1488 10447
      g3l16_pm_nonempty1488 (g3l16_pm_not_written 1488 10447 (by decide))
  have hcu : pre 5870 = denoteGraphDistributedFaithful pm initPM 5870 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1488 5870
      g3l16_pm_nonempty1488 (g3l16_pm_not_written 1488 5870 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10524 =
        applyNodeDistributedFaithful pm pre g3l16PmUnshuffle0 10524 := hcore
    _ = opfun (pre 10446) (pre 10447) (pre 5870) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10446)
        (pre 10447) (pre 5870) := congrArg (fun x => opfun x (pre 10447) (pre 5870)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10446)
        (denoteGraphDistributedFaithful pm initPM 10447) (pre 5870) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 10446) x
        (pre 5870)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10446)
        (denoteGraphDistributedFaithful pm initPM 10447)
        (denoteGraphDistributedFaithful pm initPM 5870) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 10446)
        (denoteGraphDistributedFaithful pm initPM 10447)) hcu

private theorem g3l16_red_pm10525 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10525 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 10446,
         denoteGraphDistributedFaithful pm initPM 10447]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5870)) 2 1 := by
  let pre := (pm.nodes.take 1491).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 10525 =
      applyNodeDistributedFaithful pm pre g3l16PmUnshuffle1 10525 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1491 g3l16PmUnshuffle1 10525
      (by native_decide) g3l16_pm_nodes.2 g3l16_pm_nonempty1492
      (g3l16_pm_not_written 1492 10525 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l16PmUnshuffle1 10525 =
      opfun (pre 10446) (pre 10447) (pre 5870) := by
    unfold g3l16PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10447, 5870],
        outs := [10525], params := [2, 1] } =
        [g3l16PmUnshuffle0, g3l16PmUnshuffle1] from g3l16_pm_buddies1]
    unfold g3l16PmUnshuffle0 g3l16PmUnshuffle1 opfun
    rfl
  have h0 : pre 10446 = denoteGraphDistributedFaithful pm initPM 10446 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1491 10446
      g3l16_pm_nonempty1491 (g3l16_pm_not_written 1491 10446 (by decide))
  have h1 : pre 10447 = denoteGraphDistributedFaithful pm initPM 10447 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1491 10447
      g3l16_pm_nonempty1491 (g3l16_pm_not_written 1491 10447 (by decide))
  have hcu : pre 5870 = denoteGraphDistributedFaithful pm initPM 5870 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1491 5870
      g3l16_pm_nonempty1491 (g3l16_pm_not_written 1491 5870 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10525 =
        applyNodeDistributedFaithful pm pre g3l16PmUnshuffle1 10525 := hcore
    _ = opfun (pre 10446) (pre 10447) (pre 5870) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10446)
        (pre 10447) (pre 5870) := congrArg (fun x => opfun x (pre 10447) (pre 5870)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10446)
        (denoteGraphDistributedFaithful pm initPM 10447) (pre 5870) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 10446) x
        (pre 5870)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10446)
        (denoteGraphDistributedFaithful pm initPM 10447)
        (denoteGraphDistributedFaithful pm initPM 5870) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 10446)
        (denoteGraphDistributedFaithful pm initPM 10447)) hcu

private theorem g3l16_cu_not_written :
    ∀ n ∈ pm.nodes, (5870 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l16_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 5870 = initPM 5870 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 5870 (by
      intro n hn
      native_decide +revert) g3l16_cu_not_written

private theorem g3l16_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l16_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-16 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l16_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5843)
      (denoteGraphDistributedFaithful pm initPM 10446)
      (denoteGraphDistributedFaithful pm initPM 10447)
      (denoteGraphDistributedFaithful pm initPM 5870)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5870) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 5871)
      (denoteGraphDistributedFaithful pm initPM 10524)
      (denoteGraphDistributedFaithful pm initPM 10525)
      [4096, 64] [2048, 64] := by
  have hcu := g3l16_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5870) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l16_red_sm5871 initSM
  have hpm0 := g3l16_red_pm10524 initPM
  have hpm1 := g3l16_red_pm10525 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 10446,
     denoteGraphDistributedFaithful pm initPM 10447]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5870)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 10446,
     denoteGraphDistributedFaithful pm initPM 10447]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5870)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 5843 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 10524,
       denoteGraphDistributedFaithful pm initPM 10525] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 10524, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 10524,
          denoteGraphDistributedFaithful pm initPM 10525] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 10524, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 10446).shape := by
    exact g3l16_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 10447).shape := by
    exact g3l16_unshuffle1_shape _ _ _
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
