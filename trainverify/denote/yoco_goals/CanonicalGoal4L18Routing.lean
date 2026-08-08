/- Canonical Goal 4, layer 18: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l18SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5952, 5980],
    outs := [5981], params := [1, 0] }

private def g4l18PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10756, 5980],
    outs := [10834], params := [2, 0] }

private def g4l18PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10757, 5980],
    outs := [10835], params := [2, 1] }

private theorem g4l18_sm_node :
    sm_goal_4.nodes[744]'(by native_decide) = g4l18SmUnshuffle := by
  native_decide

private theorem g4l18_pm_nodes :
    pm_goal_4.nodes[1634]'(by native_decide) = g4l18PmUnshuffle0 ∧
    pm_goal_4.nodes[1636]'(by native_decide) = g4l18PmUnshuffle1 := by
  native_decide

private theorem g4l18_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l18PmUnshuffle0 =
      [g4l18PmUnshuffle0, g4l18PmUnshuffle1] := by
  native_decide

private theorem g4l18_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l18PmUnshuffle1 =
      [g4l18PmUnshuffle0, g4l18PmUnshuffle1] := by
  native_decide

private theorem g4l18_sm_nonempty744 :
    ∀ n ∈ sm_goal_4.nodes.drop 744, n.outs ≠ [] := by native_decide
private theorem g4l18_sm_nonempty745 :
    ∀ n ∈ sm_goal_4.nodes.drop 745, n.outs ≠ [] := by native_decide
private theorem g4l18_pm_nonempty1634 :
    ∀ n ∈ pm_goal_4.nodes.drop 1634, n.outs ≠ [] := by native_decide
private theorem g4l18_pm_nonempty1635 :
    ∀ n ∈ pm_goal_4.nodes.drop 1635, n.outs ≠ [] := by native_decide
private theorem g4l18_pm_nonempty1636 :
    ∀ n ∈ pm_goal_4.nodes.drop 1636, n.outs ≠ [] := by native_decide
private theorem g4l18_pm_nonempty1637 :
    ∀ n ∈ pm_goal_4.nodes.drop 1637, n.outs ≠ [] := by native_decide

private theorem g4l18_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(745, 5981), (744, 5952), (744, 5980)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l18_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1635, 10834), (1637, 10835),
      (1634, 10756), (1634, 10757), (1634, 5980),
      (1636, 10756), (1636, 10757), (1636, 5980)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l18_red_sm5981 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5981 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 5952 := by
  let pre := (sm_goal_4.nodes.take 744).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 5981 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l18SmUnshuffle 5981 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 744 g4l18SmUnshuffle 5981
      (by native_decide) g4l18_sm_node g4l18_sm_nonempty745
      (g4l18_sm_not_written 745 5981 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l18SmUnshuffle 5981 =
      pre 5952 := by
    unfold g4l18SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5952, 5980],
        outs := [5981], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5952 = denoteGraphDistributedFaithful sm_goal_4 initSM 5952 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 744 5952
      g4l18_sm_nonempty744 (g4l18_sm_not_written 744 5952 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l18_red_pm10834 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10834 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10756,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10757]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5980)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1634).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10834 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l18PmUnshuffle0 10834 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1634 g4l18PmUnshuffle0 10834
      (by native_decide) g4l18_pm_nodes.1 g4l18_pm_nonempty1635
      (g4l18_pm_not_written 1635 10834 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l18PmUnshuffle0 10834 =
      opfun (pre 10756) (pre 10757) (pre 5980) := by
    unfold g4l18PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10756, 5980],
        outs := [10834], params := [2, 0] } =
        [g4l18PmUnshuffle0, g4l18PmUnshuffle1] from g4l18_pm_buddies0]
    unfold g4l18PmUnshuffle0 g4l18PmUnshuffle1 opfun
    rfl
  have h0 : pre 10756 = denoteGraphDistributedFaithful pm_goal_4 initPM 10756 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1634 10756
      g4l18_pm_nonempty1634 (g4l18_pm_not_written 1634 10756 (by decide))
  have h1 : pre 10757 = denoteGraphDistributedFaithful pm_goal_4 initPM 10757 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1634 10757
      g4l18_pm_nonempty1634 (g4l18_pm_not_written 1634 10757 (by decide))
  have hcu : pre 5980 = denoteGraphDistributedFaithful pm_goal_4 initPM 5980 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1634 5980
      g4l18_pm_nonempty1634 (g4l18_pm_not_written 1634 5980 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10834 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l18PmUnshuffle0 10834 := hcore
    _ = opfun (pre 10756) (pre 10757) (pre 5980) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10756)
        (pre 10757) (pre 5980) := congrArg (fun x => opfun x (pre 10757) (pre 5980)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10756)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10757) (pre 5980) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10756) x
        (pre 5980)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10756)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10757)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5980) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10756)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10757)) hcu

private theorem g4l18_red_pm10835 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10835 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10756,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10757]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5980)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1636).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10835 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l18PmUnshuffle1 10835 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1636 g4l18PmUnshuffle1 10835
      (by native_decide) g4l18_pm_nodes.2 g4l18_pm_nonempty1637
      (g4l18_pm_not_written 1637 10835 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l18PmUnshuffle1 10835 =
      opfun (pre 10756) (pre 10757) (pre 5980) := by
    unfold g4l18PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10757, 5980],
        outs := [10835], params := [2, 1] } =
        [g4l18PmUnshuffle0, g4l18PmUnshuffle1] from g4l18_pm_buddies1]
    unfold g4l18PmUnshuffle0 g4l18PmUnshuffle1 opfun
    rfl
  have h0 : pre 10756 = denoteGraphDistributedFaithful pm_goal_4 initPM 10756 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1636 10756
      g4l18_pm_nonempty1636 (g4l18_pm_not_written 1636 10756 (by decide))
  have h1 : pre 10757 = denoteGraphDistributedFaithful pm_goal_4 initPM 10757 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1636 10757
      g4l18_pm_nonempty1636 (g4l18_pm_not_written 1636 10757 (by decide))
  have hcu : pre 5980 = denoteGraphDistributedFaithful pm_goal_4 initPM 5980 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1636 5980
      g4l18_pm_nonempty1636 (g4l18_pm_not_written 1636 5980 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10835 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l18PmUnshuffle1 10835 := hcore
    _ = opfun (pre 10756) (pre 10757) (pre 5980) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10756)
        (pre 10757) (pre 5980) := congrArg (fun x => opfun x (pre 10757) (pre 5980)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10756)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10757) (pre 5980) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10756) x
        (pre 5980)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10756)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10757)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5980) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10756)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10757)) hcu

private theorem g4l18_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (5980 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l18_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 5980 = initPM 5980 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 5980 (by
      intro n hn
      native_decide +revert) g4l18_cu_not_written

private theorem g4l18_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l18_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-18 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l18_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5952)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10756)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10757)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5980)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5980) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5981)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10834)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10835)
      [4096, 64] [2048, 64] := by
  have hcu := g4l18_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5980) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l18_red_sm5981 initSM
  have hpm0 := g4l18_red_pm10834 initPM
  have hpm1 := g4l18_red_pm10835 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10756,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10757]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5980)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10756,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10757]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5980)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 5952 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 10834,
       denoteGraphDistributedFaithful pm_goal_4 initPM 10835] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 10834, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 10834,
          denoteGraphDistributedFaithful pm_goal_4 initPM 10835] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 10834, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10756).shape := by
    exact g4l18_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10757).shape := by
    exact g4l18_unshuffle1_shape _ _ _
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

