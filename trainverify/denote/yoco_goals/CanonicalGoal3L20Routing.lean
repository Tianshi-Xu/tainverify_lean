/- Canonical Goal 3, layer 20: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l20SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6059, 6086],
    outs := [6087], params := [1, 0] }

private def g3l20PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11062, 6086],
    outs := [11140], params := [2, 0] }

private def g3l20PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11063, 6086],
    outs := [11141], params := [2, 1] }

private theorem g3l20_sm_node :
    sm.nodes[824]'(by native_decide) = g3l20SmUnshuffle := by
  native_decide

private theorem g3l20_pm_nodes :
    pm.nodes[1808]'(by native_decide) = g3l20PmUnshuffle0 ∧
    pm.nodes[1811]'(by native_decide) = g3l20PmUnshuffle1 := by
  native_decide

private theorem g3l20_pm_buddies0 :
    pm.replicaBuddies g3l20PmUnshuffle0 =
      [g3l20PmUnshuffle0, g3l20PmUnshuffle1] := by
  native_decide

private theorem g3l20_pm_buddies1 :
    pm.replicaBuddies g3l20PmUnshuffle1 =
      [g3l20PmUnshuffle0, g3l20PmUnshuffle1] := by
  native_decide

private theorem g3l20_sm_nonempty824 :
    ∀ n ∈ sm.nodes.drop 824, n.outs ≠ [] := by native_decide
private theorem g3l20_sm_nonempty825 :
    ∀ n ∈ sm.nodes.drop 825, n.outs ≠ [] := by native_decide
private theorem g3l20_pm_nonempty1808 :
    ∀ n ∈ pm.nodes.drop 1808, n.outs ≠ [] := by native_decide
private theorem g3l20_pm_nonempty1809 :
    ∀ n ∈ pm.nodes.drop 1809, n.outs ≠ [] := by native_decide
private theorem g3l20_pm_nonempty1811 :
    ∀ n ∈ pm.nodes.drop 1811, n.outs ≠ [] := by native_decide
private theorem g3l20_pm_nonempty1812 :
    ∀ n ∈ pm.nodes.drop 1812, n.outs ≠ [] := by native_decide

private theorem g3l20_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(825, 6087), (824, 6059), (824, 6086)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l20_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1809, 11140), (1812, 11141),
      (1808, 11062), (1808, 11063), (1808, 6086),
      (1811, 11062), (1811, 11063), (1811, 6086)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l20_red_sm6087 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 6087 =
      denoteGraphDistributedFaithful sm initSM 6059 := by
  let pre := (sm.nodes.take 824).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 6087 =
      applyNodeDistributedFaithful sm pre g3l20SmUnshuffle 6087 :=
    denoteGraphDistributedFaithful_node_core sm initSM 824 g3l20SmUnshuffle 6087
      (by native_decide) g3l20_sm_node g3l20_sm_nonempty825
      (g3l20_sm_not_written 825 6087 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l20SmUnshuffle 6087 =
      pre 6059 := by
    unfold g3l20SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6059, 6086],
        outs := [6087], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 6059 = denoteGraphDistributedFaithful sm initSM 6059 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 824 6059
      g3l20_sm_nonempty824 (g3l20_sm_not_written 824 6059 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l20_red_pm11140 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11140 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11062,
         denoteGraphDistributedFaithful pm initPM 11063]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6086)) 2 0 := by
  let pre := (pm.nodes.take 1808).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 11140 =
      applyNodeDistributedFaithful pm pre g3l20PmUnshuffle0 11140 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1808 g3l20PmUnshuffle0 11140
      (by native_decide) g3l20_pm_nodes.1 g3l20_pm_nonempty1809
      (g3l20_pm_not_written 1809 11140 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l20PmUnshuffle0 11140 =
      opfun (pre 11062) (pre 11063) (pre 6086) := by
    unfold g3l20PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11062, 6086],
        outs := [11140], params := [2, 0] } =
        [g3l20PmUnshuffle0, g3l20PmUnshuffle1] from g3l20_pm_buddies0]
    unfold g3l20PmUnshuffle0 g3l20PmUnshuffle1 opfun
    rfl
  have h0 : pre 11062 = denoteGraphDistributedFaithful pm initPM 11062 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1808 11062
      g3l20_pm_nonempty1808 (g3l20_pm_not_written 1808 11062 (by decide))
  have h1 : pre 11063 = denoteGraphDistributedFaithful pm initPM 11063 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1808 11063
      g3l20_pm_nonempty1808 (g3l20_pm_not_written 1808 11063 (by decide))
  have hcu : pre 6086 = denoteGraphDistributedFaithful pm initPM 6086 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1808 6086
      g3l20_pm_nonempty1808 (g3l20_pm_not_written 1808 6086 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 11140 =
        applyNodeDistributedFaithful pm pre g3l20PmUnshuffle0 11140 := hcore
    _ = opfun (pre 11062) (pre 11063) (pre 6086) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11062)
        (pre 11063) (pre 6086) := congrArg (fun x => opfun x (pre 11063) (pre 6086)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11062)
        (denoteGraphDistributedFaithful pm initPM 11063) (pre 6086) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 11062) x
        (pre 6086)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11062)
        (denoteGraphDistributedFaithful pm initPM 11063)
        (denoteGraphDistributedFaithful pm initPM 6086) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 11062)
        (denoteGraphDistributedFaithful pm initPM 11063)) hcu

private theorem g3l20_red_pm11141 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11141 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11062,
         denoteGraphDistributedFaithful pm initPM 11063]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6086)) 2 1 := by
  let pre := (pm.nodes.take 1811).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 11141 =
      applyNodeDistributedFaithful pm pre g3l20PmUnshuffle1 11141 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1811 g3l20PmUnshuffle1 11141
      (by native_decide) g3l20_pm_nodes.2 g3l20_pm_nonempty1812
      (g3l20_pm_not_written 1812 11141 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l20PmUnshuffle1 11141 =
      opfun (pre 11062) (pre 11063) (pre 6086) := by
    unfold g3l20PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11063, 6086],
        outs := [11141], params := [2, 1] } =
        [g3l20PmUnshuffle0, g3l20PmUnshuffle1] from g3l20_pm_buddies1]
    unfold g3l20PmUnshuffle0 g3l20PmUnshuffle1 opfun
    rfl
  have h0 : pre 11062 = denoteGraphDistributedFaithful pm initPM 11062 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1811 11062
      g3l20_pm_nonempty1811 (g3l20_pm_not_written 1811 11062 (by decide))
  have h1 : pre 11063 = denoteGraphDistributedFaithful pm initPM 11063 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1811 11063
      g3l20_pm_nonempty1811 (g3l20_pm_not_written 1811 11063 (by decide))
  have hcu : pre 6086 = denoteGraphDistributedFaithful pm initPM 6086 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1811 6086
      g3l20_pm_nonempty1811 (g3l20_pm_not_written 1811 6086 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 11141 =
        applyNodeDistributedFaithful pm pre g3l20PmUnshuffle1 11141 := hcore
    _ = opfun (pre 11062) (pre 11063) (pre 6086) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11062)
        (pre 11063) (pre 6086) := congrArg (fun x => opfun x (pre 11063) (pre 6086)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11062)
        (denoteGraphDistributedFaithful pm initPM 11063) (pre 6086) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 11062) x
        (pre 6086)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11062)
        (denoteGraphDistributedFaithful pm initPM 11063)
        (denoteGraphDistributedFaithful pm initPM 6086) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 11062)
        (denoteGraphDistributedFaithful pm initPM 11063)) hcu

private theorem g3l20_cu_not_written :
    ∀ n ∈ pm.nodes, (6086 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l20_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 6086 = initPM 6086 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 6086 (by
      intro n hn
      native_decide +revert) g3l20_cu_not_written

private theorem g3l20_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l20_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-20 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l20_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 6059)
      (denoteGraphDistributedFaithful pm initPM 11062)
      (denoteGraphDistributedFaithful pm initPM 11063)
      (denoteGraphDistributedFaithful pm initPM 6086)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 6086) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 6087)
      (denoteGraphDistributedFaithful pm initPM 11140)
      (denoteGraphDistributedFaithful pm initPM 11141)
      [4096, 64] [2048, 64] := by
  have hcu := g3l20_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 6086) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l20_red_sm6087 initSM
  have hpm0 := g3l20_red_pm11140 initPM
  have hpm1 := g3l20_red_pm11141 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 11062,
     denoteGraphDistributedFaithful pm initPM 11063]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6086)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 11062,
     denoteGraphDistributedFaithful pm initPM 11063]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6086)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 6059 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 11140,
       denoteGraphDistributedFaithful pm initPM 11141] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 11140, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 11140,
          denoteGraphDistributedFaithful pm initPM 11141] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 11140, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 11062).shape := by
    exact g3l20_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 11063).shape := by
    exact g3l20_unshuffle1_shape _ _ _
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
