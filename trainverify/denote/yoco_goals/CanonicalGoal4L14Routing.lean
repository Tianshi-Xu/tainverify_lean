/- Canonical Goal 4, layer 14: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l14SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5736, 5764],
    outs := [5765], params := [1, 0] }

private def g4l14PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10140, 5764],
    outs := [10218], params := [2, 0] }

private def g4l14PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10141, 5764],
    outs := [10219], params := [2, 1] }

private theorem g4l14_sm_node :
    sm_goal_4.nodes[600]'(by native_decide) = g4l14SmUnshuffle := by
  native_decide

private theorem g4l14_pm_nodes :
    pm_goal_4.nodes[1322]'(by native_decide) = g4l14PmUnshuffle0 ∧
    pm_goal_4.nodes[1324]'(by native_decide) = g4l14PmUnshuffle1 := by
  native_decide

private theorem g4l14_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l14PmUnshuffle0 =
      [g4l14PmUnshuffle0, g4l14PmUnshuffle1] := by
  native_decide

private theorem g4l14_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l14PmUnshuffle1 =
      [g4l14PmUnshuffle0, g4l14PmUnshuffle1] := by
  native_decide

private theorem g4l14_sm_nonempty600 :
    ∀ n ∈ sm_goal_4.nodes.drop 600, n.outs ≠ [] := by native_decide
private theorem g4l14_sm_nonempty601 :
    ∀ n ∈ sm_goal_4.nodes.drop 601, n.outs ≠ [] := by native_decide
private theorem g4l14_pm_nonempty1322 :
    ∀ n ∈ pm_goal_4.nodes.drop 1322, n.outs ≠ [] := by native_decide
private theorem g4l14_pm_nonempty1323 :
    ∀ n ∈ pm_goal_4.nodes.drop 1323, n.outs ≠ [] := by native_decide
private theorem g4l14_pm_nonempty1324 :
    ∀ n ∈ pm_goal_4.nodes.drop 1324, n.outs ≠ [] := by native_decide
private theorem g4l14_pm_nonempty1325 :
    ∀ n ∈ pm_goal_4.nodes.drop 1325, n.outs ≠ [] := by native_decide

private theorem g4l14_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(601, 5765), (600, 5736), (600, 5764)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l14_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1323, 10218), (1325, 10219),
      (1322, 10140), (1322, 10141), (1322, 5764),
      (1324, 10140), (1324, 10141), (1324, 5764)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l14_red_sm5765 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5765 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 5736 := by
  let pre := (sm_goal_4.nodes.take 600).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 5765 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l14SmUnshuffle 5765 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 600 g4l14SmUnshuffle 5765
      (by native_decide) g4l14_sm_node g4l14_sm_nonempty601
      (g4l14_sm_not_written 601 5765 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l14SmUnshuffle 5765 =
      pre 5736 := by
    unfold g4l14SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5736, 5764],
        outs := [5765], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5736 = denoteGraphDistributedFaithful sm_goal_4 initSM 5736 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 600 5736
      g4l14_sm_nonempty600 (g4l14_sm_not_written 600 5736 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l14_red_pm10218 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10218 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10140,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10141]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5764)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1322).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10218 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l14PmUnshuffle0 10218 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1322 g4l14PmUnshuffle0 10218
      (by native_decide) g4l14_pm_nodes.1 g4l14_pm_nonempty1323
      (g4l14_pm_not_written 1323 10218 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l14PmUnshuffle0 10218 =
      opfun (pre 10140) (pre 10141) (pre 5764) := by
    unfold g4l14PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10140, 5764],
        outs := [10218], params := [2, 0] } =
        [g4l14PmUnshuffle0, g4l14PmUnshuffle1] from g4l14_pm_buddies0]
    unfold g4l14PmUnshuffle0 g4l14PmUnshuffle1 opfun
    rfl
  have h0 : pre 10140 = denoteGraphDistributedFaithful pm_goal_4 initPM 10140 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1322 10140
      g4l14_pm_nonempty1322 (g4l14_pm_not_written 1322 10140 (by decide))
  have h1 : pre 10141 = denoteGraphDistributedFaithful pm_goal_4 initPM 10141 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1322 10141
      g4l14_pm_nonempty1322 (g4l14_pm_not_written 1322 10141 (by decide))
  have hcu : pre 5764 = denoteGraphDistributedFaithful pm_goal_4 initPM 5764 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1322 5764
      g4l14_pm_nonempty1322 (g4l14_pm_not_written 1322 5764 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10218 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l14PmUnshuffle0 10218 := hcore
    _ = opfun (pre 10140) (pre 10141) (pre 5764) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
        (pre 10141) (pre 5764) := congrArg (fun x => opfun x (pre 10141) (pre 5764)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10141) (pre 5764) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10140) x
        (pre 5764)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10141)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5764) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10141)) hcu

private theorem g4l14_red_pm10219 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10219 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10140,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10141]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5764)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1324).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10219 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l14PmUnshuffle1 10219 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1324 g4l14PmUnshuffle1 10219
      (by native_decide) g4l14_pm_nodes.2 g4l14_pm_nonempty1325
      (g4l14_pm_not_written 1325 10219 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l14PmUnshuffle1 10219 =
      opfun (pre 10140) (pre 10141) (pre 5764) := by
    unfold g4l14PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10141, 5764],
        outs := [10219], params := [2, 1] } =
        [g4l14PmUnshuffle0, g4l14PmUnshuffle1] from g4l14_pm_buddies1]
    unfold g4l14PmUnshuffle0 g4l14PmUnshuffle1 opfun
    rfl
  have h0 : pre 10140 = denoteGraphDistributedFaithful pm_goal_4 initPM 10140 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1324 10140
      g4l14_pm_nonempty1324 (g4l14_pm_not_written 1324 10140 (by decide))
  have h1 : pre 10141 = denoteGraphDistributedFaithful pm_goal_4 initPM 10141 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1324 10141
      g4l14_pm_nonempty1324 (g4l14_pm_not_written 1324 10141 (by decide))
  have hcu : pre 5764 = denoteGraphDistributedFaithful pm_goal_4 initPM 5764 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1324 5764
      g4l14_pm_nonempty1324 (g4l14_pm_not_written 1324 5764 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10219 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l14PmUnshuffle1 10219 := hcore
    _ = opfun (pre 10140) (pre 10141) (pre 5764) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
        (pre 10141) (pre 5764) := congrArg (fun x => opfun x (pre 10141) (pre 5764)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10141) (pre 5764) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10140) x
        (pre 5764)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10141)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5764) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10141)) hcu

private theorem g4l14_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (5764 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l14_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 5764 = initPM 5764 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 5764 (by
      intro n hn
      native_decide +revert) g4l14_cu_not_written

private theorem g4l14_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l14_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-14 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l14_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5736)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10140)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10141)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5764)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5764) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5765)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10218)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10219)
      [4096, 64] [2048, 64] := by
  have hcu := g4l14_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5764) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l14_red_sm5765 initSM
  have hpm0 := g4l14_red_pm10218 initPM
  have hpm1 := g4l14_red_pm10219 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10140,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10141]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5764)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10140,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10141]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5764)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 5736 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 10218,
       denoteGraphDistributedFaithful pm_goal_4 initPM 10219] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 10218, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 10218,
          denoteGraphDistributedFaithful pm_goal_4 initPM 10219] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 10218, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10140).shape := by
    exact g4l14_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10141).shape := by
    exact g4l14_unshuffle1_shape _ _ _
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

