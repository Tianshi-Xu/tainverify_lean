/- Canonical Goal 3, layer 13: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l13SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5681, 5708],
    outs := [5709], params := [1, 0] }

private def g3l13PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [9984, 5708],
    outs := [10062], params := [2, 0] }

private def g3l13PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [9985, 5708],
    outs := [10063], params := [2, 1] }

private theorem g3l13_sm_node :
    sm.nodes[565]'(by native_decide) = g3l13SmUnshuffle := by
  native_decide

private theorem g3l13_pm_nodes :
    pm.nodes[1248]'(by native_decide) = g3l13PmUnshuffle0 ∧
    pm.nodes[1251]'(by native_decide) = g3l13PmUnshuffle1 := by
  native_decide

private theorem g3l13_pm_buddies0 :
    pm.replicaBuddies g3l13PmUnshuffle0 =
      [g3l13PmUnshuffle0, g3l13PmUnshuffle1] := by
  native_decide

private theorem g3l13_pm_buddies1 :
    pm.replicaBuddies g3l13PmUnshuffle1 =
      [g3l13PmUnshuffle0, g3l13PmUnshuffle1] := by
  native_decide

private theorem g3l13_sm_nonempty565 :
    ∀ n ∈ sm.nodes.drop 565, n.outs ≠ [] := by native_decide
private theorem g3l13_sm_nonempty566 :
    ∀ n ∈ sm.nodes.drop 566, n.outs ≠ [] := by native_decide
private theorem g3l13_pm_nonempty1248 :
    ∀ n ∈ pm.nodes.drop 1248, n.outs ≠ [] := by native_decide
private theorem g3l13_pm_nonempty1249 :
    ∀ n ∈ pm.nodes.drop 1249, n.outs ≠ [] := by native_decide
private theorem g3l13_pm_nonempty1251 :
    ∀ n ∈ pm.nodes.drop 1251, n.outs ≠ [] := by native_decide
private theorem g3l13_pm_nonempty1252 :
    ∀ n ∈ pm.nodes.drop 1252, n.outs ≠ [] := by native_decide

private theorem g3l13_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(566, 5709), (565, 5681), (565, 5708)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l13_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1249, 10062), (1252, 10063),
      (1248, 9984), (1248, 9985), (1248, 5708),
      (1251, 9984), (1251, 9985), (1251, 5708)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l13_red_sm5709 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5709 =
      denoteGraphDistributedFaithful sm initSM 5681 := by
  let pre := (sm.nodes.take 565).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 5709 =
      applyNodeDistributedFaithful sm pre g3l13SmUnshuffle 5709 :=
    denoteGraphDistributedFaithful_node_core sm initSM 565 g3l13SmUnshuffle 5709
      (by native_decide) g3l13_sm_node g3l13_sm_nonempty566
      (g3l13_sm_not_written 566 5709 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l13SmUnshuffle 5709 =
      pre 5681 := by
    unfold g3l13SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5681, 5708],
        outs := [5709], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5681 = denoteGraphDistributedFaithful sm initSM 5681 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 565 5681
      g3l13_sm_nonempty565 (g3l13_sm_not_written 565 5681 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l13_red_pm10062 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10062 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 9984,
         denoteGraphDistributedFaithful pm initPM 9985]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5708)) 2 0 := by
  let pre := (pm.nodes.take 1248).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 10062 =
      applyNodeDistributedFaithful pm pre g3l13PmUnshuffle0 10062 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1248 g3l13PmUnshuffle0 10062
      (by native_decide) g3l13_pm_nodes.1 g3l13_pm_nonempty1249
      (g3l13_pm_not_written 1249 10062 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l13PmUnshuffle0 10062 =
      opfun (pre 9984) (pre 9985) (pre 5708) := by
    unfold g3l13PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [9984, 5708],
        outs := [10062], params := [2, 0] } =
        [g3l13PmUnshuffle0, g3l13PmUnshuffle1] from g3l13_pm_buddies0]
    unfold g3l13PmUnshuffle0 g3l13PmUnshuffle1 opfun
    rfl
  have h0 : pre 9984 = denoteGraphDistributedFaithful pm initPM 9984 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1248 9984
      g3l13_pm_nonempty1248 (g3l13_pm_not_written 1248 9984 (by decide))
  have h1 : pre 9985 = denoteGraphDistributedFaithful pm initPM 9985 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1248 9985
      g3l13_pm_nonempty1248 (g3l13_pm_not_written 1248 9985 (by decide))
  have hcu : pre 5708 = denoteGraphDistributedFaithful pm initPM 5708 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1248 5708
      g3l13_pm_nonempty1248 (g3l13_pm_not_written 1248 5708 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10062 =
        applyNodeDistributedFaithful pm pre g3l13PmUnshuffle0 10062 := hcore
    _ = opfun (pre 9984) (pre 9985) (pre 5708) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9984)
        (pre 9985) (pre 5708) := congrArg (fun x => opfun x (pre 9985) (pre 5708)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9984)
        (denoteGraphDistributedFaithful pm initPM 9985) (pre 5708) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 9984) x
        (pre 5708)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9984)
        (denoteGraphDistributedFaithful pm initPM 9985)
        (denoteGraphDistributedFaithful pm initPM 5708) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 9984)
        (denoteGraphDistributedFaithful pm initPM 9985)) hcu

private theorem g3l13_red_pm10063 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10063 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 9984,
         denoteGraphDistributedFaithful pm initPM 9985]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5708)) 2 1 := by
  let pre := (pm.nodes.take 1251).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 10063 =
      applyNodeDistributedFaithful pm pre g3l13PmUnshuffle1 10063 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1251 g3l13PmUnshuffle1 10063
      (by native_decide) g3l13_pm_nodes.2 g3l13_pm_nonempty1252
      (g3l13_pm_not_written 1252 10063 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l13PmUnshuffle1 10063 =
      opfun (pre 9984) (pre 9985) (pre 5708) := by
    unfold g3l13PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [9985, 5708],
        outs := [10063], params := [2, 1] } =
        [g3l13PmUnshuffle0, g3l13PmUnshuffle1] from g3l13_pm_buddies1]
    unfold g3l13PmUnshuffle0 g3l13PmUnshuffle1 opfun
    rfl
  have h0 : pre 9984 = denoteGraphDistributedFaithful pm initPM 9984 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1251 9984
      g3l13_pm_nonempty1251 (g3l13_pm_not_written 1251 9984 (by decide))
  have h1 : pre 9985 = denoteGraphDistributedFaithful pm initPM 9985 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1251 9985
      g3l13_pm_nonempty1251 (g3l13_pm_not_written 1251 9985 (by decide))
  have hcu : pre 5708 = denoteGraphDistributedFaithful pm initPM 5708 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1251 5708
      g3l13_pm_nonempty1251 (g3l13_pm_not_written 1251 5708 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10063 =
        applyNodeDistributedFaithful pm pre g3l13PmUnshuffle1 10063 := hcore
    _ = opfun (pre 9984) (pre 9985) (pre 5708) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9984)
        (pre 9985) (pre 5708) := congrArg (fun x => opfun x (pre 9985) (pre 5708)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9984)
        (denoteGraphDistributedFaithful pm initPM 9985) (pre 5708) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 9984) x
        (pre 5708)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 9984)
        (denoteGraphDistributedFaithful pm initPM 9985)
        (denoteGraphDistributedFaithful pm initPM 5708) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 9984)
        (denoteGraphDistributedFaithful pm initPM 9985)) hcu

private theorem g3l13_cu_not_written :
    ∀ n ∈ pm.nodes, (5708 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l13_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 5708 = initPM 5708 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 5708 (by
      intro n hn
      native_decide +revert) g3l13_cu_not_written

private theorem g3l13_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l13_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-13 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l13_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5681)
      (denoteGraphDistributedFaithful pm initPM 9984)
      (denoteGraphDistributedFaithful pm initPM 9985)
      (denoteGraphDistributedFaithful pm initPM 5708)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5708) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 5709)
      (denoteGraphDistributedFaithful pm initPM 10062)
      (denoteGraphDistributedFaithful pm initPM 10063)
      [4096, 64] [2048, 64] := by
  have hcu := g3l13_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5708) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l13_red_sm5709 initSM
  have hpm0 := g3l13_red_pm10062 initPM
  have hpm1 := g3l13_red_pm10063 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 9984,
     denoteGraphDistributedFaithful pm initPM 9985]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5708)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 9984,
     denoteGraphDistributedFaithful pm initPM 9985]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5708)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 5681 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 10062,
       denoteGraphDistributedFaithful pm initPM 10063] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 10062, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 10062,
          denoteGraphDistributedFaithful pm initPM 10063] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 10062, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 9984).shape := by
    exact g3l13_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 9985).shape := by
    exact g3l13_unshuffle1_shape _ _ _
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
