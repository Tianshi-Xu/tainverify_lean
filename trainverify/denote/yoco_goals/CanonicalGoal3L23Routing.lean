/- Canonical Goal 3, layer 23: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l23SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6221, 6248],
    outs := [6249], params := [1, 0] }

private def g3l23PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11524, 6248],
    outs := [11602], params := [2, 0] }

private def g3l23PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11525, 6248],
    outs := [11603], params := [2, 1] }

private theorem g3l23_sm_node :
    sm.nodes[935]'(by native_decide) = g3l23SmUnshuffle := by
  native_decide

private theorem g3l23_pm_nodes :
    pm.nodes[2048]'(by native_decide) = g3l23PmUnshuffle0 ∧
    pm.nodes[2051]'(by native_decide) = g3l23PmUnshuffle1 := by
  native_decide

private theorem g3l23_pm_buddies0 :
    pm.replicaBuddies g3l23PmUnshuffle0 =
      [g3l23PmUnshuffle0, g3l23PmUnshuffle1] := by
  native_decide

private theorem g3l23_pm_buddies1 :
    pm.replicaBuddies g3l23PmUnshuffle1 =
      [g3l23PmUnshuffle0, g3l23PmUnshuffle1] := by
  native_decide

private theorem g3l23_sm_nonempty935 :
    ∀ n ∈ sm.nodes.drop 935, n.outs ≠ [] := by native_decide
private theorem g3l23_sm_nonempty936 :
    ∀ n ∈ sm.nodes.drop 936, n.outs ≠ [] := by native_decide
private theorem g3l23_pm_nonempty2048 :
    ∀ n ∈ pm.nodes.drop 2048, n.outs ≠ [] := by native_decide
private theorem g3l23_pm_nonempty_after0 :
    ∀ n ∈ pm.nodes.drop 2049, n.outs ≠ [] := by native_decide
private theorem g3l23_pm_nonempty_pre1 :
    ∀ n ∈ pm.nodes.drop 2051, n.outs ≠ [] := by native_decide
private theorem g3l23_pm_nonempty2052 :
    ∀ n ∈ pm.nodes.drop 2052, n.outs ≠ [] := by native_decide

private theorem g3l23_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(936, 6249), (935, 6221), (935, 6248)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l23_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(2049, 11602), (2052, 11603),
      (2048, 11524), (2048, 11525), (2048, 6248),
      (2051, 11524), (2051, 11525), (2051, 6248)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l23_red_sm6249 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 6249 =
      denoteGraphDistributedFaithful sm initSM 6221 := by
  let pre := (sm.nodes.take 935).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 6249 =
      applyNodeDistributedFaithful sm pre g3l23SmUnshuffle 6249 :=
    denoteGraphDistributedFaithful_node_core sm initSM 935 g3l23SmUnshuffle 6249
      (by native_decide) g3l23_sm_node g3l23_sm_nonempty936
      (g3l23_sm_not_written 936 6249 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l23SmUnshuffle 6249 =
      pre 6221 := by
    unfold g3l23SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6221, 6248],
        outs := [6249], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 6221 = denoteGraphDistributedFaithful sm initSM 6221 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 935 6221
      g3l23_sm_nonempty935 (g3l23_sm_not_written 935 6221 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l23_red_pm11602 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11602 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11524,
         denoteGraphDistributedFaithful pm initPM 11525]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6248)) 2 0 := by
  let pre := (pm.nodes.take 2048).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 11602 =
      applyNodeDistributedFaithful pm pre g3l23PmUnshuffle0 11602 :=
    denoteGraphDistributedFaithful_node_core pm initPM 2048 g3l23PmUnshuffle0 11602
      (by native_decide) g3l23_pm_nodes.1 g3l23_pm_nonempty_after0
      (g3l23_pm_not_written 2049 11602 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l23PmUnshuffle0 11602 =
      opfun (pre 11524) (pre 11525) (pre 6248) := by
    unfold g3l23PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11524, 6248],
        outs := [11602], params := [2, 0] } =
        [g3l23PmUnshuffle0, g3l23PmUnshuffle1] from g3l23_pm_buddies0]
    unfold g3l23PmUnshuffle0 g3l23PmUnshuffle1 opfun
    rfl
  have h0 : pre 11524 = denoteGraphDistributedFaithful pm initPM 11524 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 2048 11524
      g3l23_pm_nonempty2048 (g3l23_pm_not_written 2048 11524 (by decide))
  have h1 : pre 11525 = denoteGraphDistributedFaithful pm initPM 11525 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 2048 11525
      g3l23_pm_nonempty2048 (g3l23_pm_not_written 2048 11525 (by decide))
  have hcu : pre 6248 = denoteGraphDistributedFaithful pm initPM 6248 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 2048 6248
      g3l23_pm_nonempty2048 (g3l23_pm_not_written 2048 6248 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 11602 =
        applyNodeDistributedFaithful pm pre g3l23PmUnshuffle0 11602 := hcore
    _ = opfun (pre 11524) (pre 11525) (pre 6248) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11524)
        (pre 11525) (pre 6248) := congrArg (fun x => opfun x (pre 11525) (pre 6248)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11524)
        (denoteGraphDistributedFaithful pm initPM 11525) (pre 6248) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 11524) x
        (pre 6248)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11524)
        (denoteGraphDistributedFaithful pm initPM 11525)
        (denoteGraphDistributedFaithful pm initPM 6248) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 11524)
        (denoteGraphDistributedFaithful pm initPM 11525)) hcu

private theorem g3l23_red_pm11603 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11603 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11524,
         denoteGraphDistributedFaithful pm initPM 11525]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6248)) 2 1 := by
  let pre := (pm.nodes.take 2051).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 11603 =
      applyNodeDistributedFaithful pm pre g3l23PmUnshuffle1 11603 :=
    denoteGraphDistributedFaithful_node_core pm initPM 2051 g3l23PmUnshuffle1 11603
      (by native_decide) g3l23_pm_nodes.2 g3l23_pm_nonempty2052
      (g3l23_pm_not_written 2052 11603 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l23PmUnshuffle1 11603 =
      opfun (pre 11524) (pre 11525) (pre 6248) := by
    unfold g3l23PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11525, 6248],
        outs := [11603], params := [2, 1] } =
        [g3l23PmUnshuffle0, g3l23PmUnshuffle1] from g3l23_pm_buddies1]
    unfold g3l23PmUnshuffle0 g3l23PmUnshuffle1 opfun
    rfl
  have h0 : pre 11524 = denoteGraphDistributedFaithful pm initPM 11524 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 2051 11524
      g3l23_pm_nonempty_pre1 (g3l23_pm_not_written 2051 11524 (by decide))
  have h1 : pre 11525 = denoteGraphDistributedFaithful pm initPM 11525 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 2051 11525
      g3l23_pm_nonempty_pre1 (g3l23_pm_not_written 2051 11525 (by decide))
  have hcu : pre 6248 = denoteGraphDistributedFaithful pm initPM 6248 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 2051 6248
      g3l23_pm_nonempty_pre1 (g3l23_pm_not_written 2051 6248 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 11603 =
        applyNodeDistributedFaithful pm pre g3l23PmUnshuffle1 11603 := hcore
    _ = opfun (pre 11524) (pre 11525) (pre 6248) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11524)
        (pre 11525) (pre 6248) := congrArg (fun x => opfun x (pre 11525) (pre 6248)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11524)
        (denoteGraphDistributedFaithful pm initPM 11525) (pre 6248) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 11524) x
        (pre 6248)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11524)
        (denoteGraphDistributedFaithful pm initPM 11525)
        (denoteGraphDistributedFaithful pm initPM 6248) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 11524)
        (denoteGraphDistributedFaithful pm initPM 11525)) hcu

private theorem g3l23_cu_not_written :
    ∀ n ∈ pm.nodes, (6248 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l23_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 6248 = initPM 6248 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 6248 (by
      intro n hn
      native_decide +revert) g3l23_cu_not_written

private theorem g3l23_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l23_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-23 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l23_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 6221)
      (denoteGraphDistributedFaithful pm initPM 11524)
      (denoteGraphDistributedFaithful pm initPM 11525)
      (denoteGraphDistributedFaithful pm initPM 6248)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 6248) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 6249)
      (denoteGraphDistributedFaithful pm initPM 11602)
      (denoteGraphDistributedFaithful pm initPM 11603)
      [4096, 64] [2048, 64] := by
  have hcu := g3l23_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 6248) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l23_red_sm6249 initSM
  have hpm0 := g3l23_red_pm11602 initPM
  have hpm1 := g3l23_red_pm11603 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 11524,
     denoteGraphDistributedFaithful pm initPM 11525]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6248)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 11524,
     denoteGraphDistributedFaithful pm initPM 11525]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6248)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 6221 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 11602,
       denoteGraphDistributedFaithful pm initPM 11603] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 11602, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 11602,
          denoteGraphDistributedFaithful pm initPM 11603] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 11602, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 11524).shape := by
    exact g3l23_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 11525).shape := by
    exact g3l23_unshuffle1_shape _ _ _
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
