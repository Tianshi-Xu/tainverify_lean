/- Canonical Goal 3, layer 21: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l21SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6113, 6140],
    outs := [6141], params := [1, 0] }

private def g3l21PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11216, 6140],
    outs := [11294], params := [2, 0] }

private def g3l21PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11217, 6140],
    outs := [11295], params := [2, 1] }

private theorem g3l21_sm_node :
    sm.nodes[861]'(by native_decide) = g3l21SmUnshuffle := by
  native_decide

private theorem g3l21_pm_nodes :
    pm.nodes[1888]'(by native_decide) = g3l21PmUnshuffle0 ∧
    pm.nodes[1891]'(by native_decide) = g3l21PmUnshuffle1 := by
  native_decide

private theorem g3l21_pm_buddies0 :
    pm.replicaBuddies g3l21PmUnshuffle0 =
      [g3l21PmUnshuffle0, g3l21PmUnshuffle1] := by
  native_decide

private theorem g3l21_pm_buddies1 :
    pm.replicaBuddies g3l21PmUnshuffle1 =
      [g3l21PmUnshuffle0, g3l21PmUnshuffle1] := by
  native_decide

private theorem g3l21_sm_nonempty861 :
    ∀ n ∈ sm.nodes.drop 861, n.outs ≠ [] := by native_decide
private theorem g3l21_sm_nonempty862 :
    ∀ n ∈ sm.nodes.drop 862, n.outs ≠ [] := by native_decide
private theorem g3l21_pm_nonempty1888 :
    ∀ n ∈ pm.nodes.drop 1888, n.outs ≠ [] := by native_decide
private theorem g3l21_pm_nonempty1889 :
    ∀ n ∈ pm.nodes.drop 1889, n.outs ≠ [] := by native_decide
private theorem g3l21_pm_nonempty1891 :
    ∀ n ∈ pm.nodes.drop 1891, n.outs ≠ [] := by native_decide
private theorem g3l21_pm_nonempty1892 :
    ∀ n ∈ pm.nodes.drop 1892, n.outs ≠ [] := by native_decide

private theorem g3l21_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(862, 6141), (861, 6113), (861, 6140)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l21_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1889, 11294), (1892, 11295),
      (1888, 11216), (1888, 11217), (1888, 6140),
      (1891, 11216), (1891, 11217), (1891, 6140)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l21_red_sm6141 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 6141 =
      denoteGraphDistributedFaithful sm initSM 6113 := by
  let pre := (sm.nodes.take 861).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 6141 =
      applyNodeDistributedFaithful sm pre g3l21SmUnshuffle 6141 :=
    denoteGraphDistributedFaithful_node_core sm initSM 861 g3l21SmUnshuffle 6141
      (by native_decide) g3l21_sm_node g3l21_sm_nonempty862
      (g3l21_sm_not_written 862 6141 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l21SmUnshuffle 6141 =
      pre 6113 := by
    unfold g3l21SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6113, 6140],
        outs := [6141], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 6113 = denoteGraphDistributedFaithful sm initSM 6113 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 861 6113
      g3l21_sm_nonempty861 (g3l21_sm_not_written 861 6113 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l21_red_pm11294 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11294 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11216,
         denoteGraphDistributedFaithful pm initPM 11217]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6140)) 2 0 := by
  let pre := (pm.nodes.take 1888).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 11294 =
      applyNodeDistributedFaithful pm pre g3l21PmUnshuffle0 11294 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1888 g3l21PmUnshuffle0 11294
      (by native_decide) g3l21_pm_nodes.1 g3l21_pm_nonempty1889
      (g3l21_pm_not_written 1889 11294 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l21PmUnshuffle0 11294 =
      opfun (pre 11216) (pre 11217) (pre 6140) := by
    unfold g3l21PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11216, 6140],
        outs := [11294], params := [2, 0] } =
        [g3l21PmUnshuffle0, g3l21PmUnshuffle1] from g3l21_pm_buddies0]
    unfold g3l21PmUnshuffle0 g3l21PmUnshuffle1 opfun
    rfl
  have h0 : pre 11216 = denoteGraphDistributedFaithful pm initPM 11216 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1888 11216
      g3l21_pm_nonempty1888 (g3l21_pm_not_written 1888 11216 (by decide))
  have h1 : pre 11217 = denoteGraphDistributedFaithful pm initPM 11217 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1888 11217
      g3l21_pm_nonempty1888 (g3l21_pm_not_written 1888 11217 (by decide))
  have hcu : pre 6140 = denoteGraphDistributedFaithful pm initPM 6140 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1888 6140
      g3l21_pm_nonempty1888 (g3l21_pm_not_written 1888 6140 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 11294 =
        applyNodeDistributedFaithful pm pre g3l21PmUnshuffle0 11294 := hcore
    _ = opfun (pre 11216) (pre 11217) (pre 6140) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11216)
        (pre 11217) (pre 6140) := congrArg (fun x => opfun x (pre 11217) (pre 6140)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11216)
        (denoteGraphDistributedFaithful pm initPM 11217) (pre 6140) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 11216) x
        (pre 6140)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11216)
        (denoteGraphDistributedFaithful pm initPM 11217)
        (denoteGraphDistributedFaithful pm initPM 6140) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 11216)
        (denoteGraphDistributedFaithful pm initPM 11217)) hcu

private theorem g3l21_red_pm11295 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11295 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11216,
         denoteGraphDistributedFaithful pm initPM 11217]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6140)) 2 1 := by
  let pre := (pm.nodes.take 1891).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 11295 =
      applyNodeDistributedFaithful pm pre g3l21PmUnshuffle1 11295 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1891 g3l21PmUnshuffle1 11295
      (by native_decide) g3l21_pm_nodes.2 g3l21_pm_nonempty1892
      (g3l21_pm_not_written 1892 11295 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l21PmUnshuffle1 11295 =
      opfun (pre 11216) (pre 11217) (pre 6140) := by
    unfold g3l21PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11217, 6140],
        outs := [11295], params := [2, 1] } =
        [g3l21PmUnshuffle0, g3l21PmUnshuffle1] from g3l21_pm_buddies1]
    unfold g3l21PmUnshuffle0 g3l21PmUnshuffle1 opfun
    rfl
  have h0 : pre 11216 = denoteGraphDistributedFaithful pm initPM 11216 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1891 11216
      g3l21_pm_nonempty1891 (g3l21_pm_not_written 1891 11216 (by decide))
  have h1 : pre 11217 = denoteGraphDistributedFaithful pm initPM 11217 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1891 11217
      g3l21_pm_nonempty1891 (g3l21_pm_not_written 1891 11217 (by decide))
  have hcu : pre 6140 = denoteGraphDistributedFaithful pm initPM 6140 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1891 6140
      g3l21_pm_nonempty1891 (g3l21_pm_not_written 1891 6140 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 11295 =
        applyNodeDistributedFaithful pm pre g3l21PmUnshuffle1 11295 := hcore
    _ = opfun (pre 11216) (pre 11217) (pre 6140) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11216)
        (pre 11217) (pre 6140) := congrArg (fun x => opfun x (pre 11217) (pre 6140)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11216)
        (denoteGraphDistributedFaithful pm initPM 11217) (pre 6140) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 11216) x
        (pre 6140)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11216)
        (denoteGraphDistributedFaithful pm initPM 11217)
        (denoteGraphDistributedFaithful pm initPM 6140) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 11216)
        (denoteGraphDistributedFaithful pm initPM 11217)) hcu

private theorem g3l21_cu_not_written :
    ∀ n ∈ pm.nodes, (6140 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l21_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 6140 = initPM 6140 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 6140 (by
      intro n hn
      native_decide +revert) g3l21_cu_not_written

private theorem g3l21_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l21_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-21 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l21_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 6113)
      (denoteGraphDistributedFaithful pm initPM 11216)
      (denoteGraphDistributedFaithful pm initPM 11217)
      (denoteGraphDistributedFaithful pm initPM 6140)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 6140) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 6141)
      (denoteGraphDistributedFaithful pm initPM 11294)
      (denoteGraphDistributedFaithful pm initPM 11295)
      [4096, 64] [2048, 64] := by
  have hcu := g3l21_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 6140) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l21_red_sm6141 initSM
  have hpm0 := g3l21_red_pm11294 initPM
  have hpm1 := g3l21_red_pm11295 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 11216,
     denoteGraphDistributedFaithful pm initPM 11217]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6140)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 11216,
     denoteGraphDistributedFaithful pm initPM 11217]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6140)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 6113 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 11294,
       denoteGraphDistributedFaithful pm initPM 11295] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 11294, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 11294,
          denoteGraphDistributedFaithful pm initPM 11295] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 11294, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 11216).shape := by
    exact g3l21_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 11217).shape := by
    exact g3l21_unshuffle1_shape _ _ _
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
