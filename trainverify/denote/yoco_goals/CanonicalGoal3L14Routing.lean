/- Canonical Goal 3, layer 14: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l14SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5735, 5762],
    outs := [5763], params := [1, 0] }

private def g3l14PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10138, 5762],
    outs := [10216], params := [2, 0] }

private def g3l14PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10139, 5762],
    outs := [10217], params := [2, 1] }

private theorem g3l14_sm_node :
    sm.nodes[602]'(by native_decide) = g3l14SmUnshuffle := by
  native_decide

private theorem g3l14_pm_nodes :
    pm.nodes[1328]'(by native_decide) = g3l14PmUnshuffle0 ∧
    pm.nodes[1331]'(by native_decide) = g3l14PmUnshuffle1 := by
  native_decide

private theorem g3l14_pm_buddies0 :
    pm.replicaBuddies g3l14PmUnshuffle0 =
      [g3l14PmUnshuffle0, g3l14PmUnshuffle1] := by
  native_decide

private theorem g3l14_pm_buddies1 :
    pm.replicaBuddies g3l14PmUnshuffle1 =
      [g3l14PmUnshuffle0, g3l14PmUnshuffle1] := by
  native_decide

private theorem g3l14_sm_nonempty602 :
    ∀ n ∈ sm.nodes.drop 602, n.outs ≠ [] := by native_decide
private theorem g3l14_sm_nonempty603 :
    ∀ n ∈ sm.nodes.drop 603, n.outs ≠ [] := by native_decide
private theorem g3l14_pm_nonempty1328 :
    ∀ n ∈ pm.nodes.drop 1328, n.outs ≠ [] := by native_decide
private theorem g3l14_pm_nonempty1329 :
    ∀ n ∈ pm.nodes.drop 1329, n.outs ≠ [] := by native_decide
private theorem g3l14_pm_nonempty1331 :
    ∀ n ∈ pm.nodes.drop 1331, n.outs ≠ [] := by native_decide
private theorem g3l14_pm_nonempty1332 :
    ∀ n ∈ pm.nodes.drop 1332, n.outs ≠ [] := by native_decide

private theorem g3l14_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(603, 5763), (602, 5735), (602, 5762)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l14_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1329, 10216), (1332, 10217),
      (1328, 10138), (1328, 10139), (1328, 5762),
      (1331, 10138), (1331, 10139), (1331, 5762)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l14_red_sm5763 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 5763 =
      denoteGraphDistributedFaithful sm initSM 5735 := by
  let pre := (sm.nodes.take 602).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 5763 =
      applyNodeDistributedFaithful sm pre g3l14SmUnshuffle 5763 :=
    denoteGraphDistributedFaithful_node_core sm initSM 602 g3l14SmUnshuffle 5763
      (by native_decide) g3l14_sm_node g3l14_sm_nonempty603
      (g3l14_sm_not_written 603 5763 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l14SmUnshuffle 5763 =
      pre 5735 := by
    unfold g3l14SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5735, 5762],
        outs := [5763], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5735 = denoteGraphDistributedFaithful sm initSM 5735 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 602 5735
      g3l14_sm_nonempty602 (g3l14_sm_not_written 602 5735 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l14_red_pm10216 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10216 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 10138,
         denoteGraphDistributedFaithful pm initPM 10139]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5762)) 2 0 := by
  let pre := (pm.nodes.take 1328).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 10216 =
      applyNodeDistributedFaithful pm pre g3l14PmUnshuffle0 10216 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1328 g3l14PmUnshuffle0 10216
      (by native_decide) g3l14_pm_nodes.1 g3l14_pm_nonempty1329
      (g3l14_pm_not_written 1329 10216 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l14PmUnshuffle0 10216 =
      opfun (pre 10138) (pre 10139) (pre 5762) := by
    unfold g3l14PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10138, 5762],
        outs := [10216], params := [2, 0] } =
        [g3l14PmUnshuffle0, g3l14PmUnshuffle1] from g3l14_pm_buddies0]
    unfold g3l14PmUnshuffle0 g3l14PmUnshuffle1 opfun
    rfl
  have h0 : pre 10138 = denoteGraphDistributedFaithful pm initPM 10138 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1328 10138
      g3l14_pm_nonempty1328 (g3l14_pm_not_written 1328 10138 (by decide))
  have h1 : pre 10139 = denoteGraphDistributedFaithful pm initPM 10139 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1328 10139
      g3l14_pm_nonempty1328 (g3l14_pm_not_written 1328 10139 (by decide))
  have hcu : pre 5762 = denoteGraphDistributedFaithful pm initPM 5762 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1328 5762
      g3l14_pm_nonempty1328 (g3l14_pm_not_written 1328 5762 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10216 =
        applyNodeDistributedFaithful pm pre g3l14PmUnshuffle0 10216 := hcore
    _ = opfun (pre 10138) (pre 10139) (pre 5762) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10138)
        (pre 10139) (pre 5762) := congrArg (fun x => opfun x (pre 10139) (pre 5762)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10138)
        (denoteGraphDistributedFaithful pm initPM 10139) (pre 5762) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 10138) x
        (pre 5762)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10138)
        (denoteGraphDistributedFaithful pm initPM 10139)
        (denoteGraphDistributedFaithful pm initPM 5762) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 10138)
        (denoteGraphDistributedFaithful pm initPM 10139)) hcu

private theorem g3l14_red_pm10217 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 10217 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 10138,
         denoteGraphDistributedFaithful pm initPM 10139]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5762)) 2 1 := by
  let pre := (pm.nodes.take 1331).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 10217 =
      applyNodeDistributedFaithful pm pre g3l14PmUnshuffle1 10217 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1331 g3l14PmUnshuffle1 10217
      (by native_decide) g3l14_pm_nodes.2 g3l14_pm_nonempty1332
      (g3l14_pm_not_written 1332 10217 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l14PmUnshuffle1 10217 =
      opfun (pre 10138) (pre 10139) (pre 5762) := by
    unfold g3l14PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10139, 5762],
        outs := [10217], params := [2, 1] } =
        [g3l14PmUnshuffle0, g3l14PmUnshuffle1] from g3l14_pm_buddies1]
    unfold g3l14PmUnshuffle0 g3l14PmUnshuffle1 opfun
    rfl
  have h0 : pre 10138 = denoteGraphDistributedFaithful pm initPM 10138 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1331 10138
      g3l14_pm_nonempty1331 (g3l14_pm_not_written 1331 10138 (by decide))
  have h1 : pre 10139 = denoteGraphDistributedFaithful pm initPM 10139 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1331 10139
      g3l14_pm_nonempty1331 (g3l14_pm_not_written 1331 10139 (by decide))
  have hcu : pre 5762 = denoteGraphDistributedFaithful pm initPM 5762 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1331 5762
      g3l14_pm_nonempty1331 (g3l14_pm_not_written 1331 5762 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 10217 =
        applyNodeDistributedFaithful pm pre g3l14PmUnshuffle1 10217 := hcore
    _ = opfun (pre 10138) (pre 10139) (pre 5762) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10138)
        (pre 10139) (pre 5762) := congrArg (fun x => opfun x (pre 10139) (pre 5762)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10138)
        (denoteGraphDistributedFaithful pm initPM 10139) (pre 5762) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 10138) x
        (pre 5762)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 10138)
        (denoteGraphDistributedFaithful pm initPM 10139)
        (denoteGraphDistributedFaithful pm initPM 5762) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 10138)
        (denoteGraphDistributedFaithful pm initPM 10139)) hcu

private theorem g3l14_cu_not_written :
    ∀ n ∈ pm.nodes, (5762 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l14_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 5762 = initPM 5762 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 5762 (by
      intro n hn
      native_decide +revert) g3l14_cu_not_written

private theorem g3l14_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l14_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-14 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l14_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 5735)
      (denoteGraphDistributedFaithful pm initPM 10138)
      (denoteGraphDistributedFaithful pm initPM 10139)
      (denoteGraphDistributedFaithful pm initPM 5762)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5762) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 5763)
      (denoteGraphDistributedFaithful pm initPM 10216)
      (denoteGraphDistributedFaithful pm initPM 10217)
      [4096, 64] [2048, 64] := by
  have hcu := g3l14_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 5762) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l14_red_sm5763 initSM
  have hpm0 := g3l14_red_pm10216 initPM
  have hpm1 := g3l14_red_pm10217 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 10138,
     denoteGraphDistributedFaithful pm initPM 10139]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5762)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 10138,
     denoteGraphDistributedFaithful pm initPM 10139]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 5762)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 5735 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 10216,
       denoteGraphDistributedFaithful pm initPM 10217] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 10216, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 10216,
          denoteGraphDistributedFaithful pm initPM 10217] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 10216, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 10138).shape := by
    exact g3l14_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 10139).shape := by
    exact g3l14_unshuffle1_shape _ _ _
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
