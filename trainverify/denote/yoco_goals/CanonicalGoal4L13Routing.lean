/- Canonical Goal 4, layer 13: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l13SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5682, 5710],
    outs := [5711], params := [1, 0] }

private def g4l13PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [9986, 5710],
    outs := [10064], params := [2, 0] }

private def g4l13PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [9987, 5710],
    outs := [10065], params := [2, 1] }

private theorem g4l13_sm_node :
    sm_goal_4.nodes[564]'(by native_decide) = g4l13SmUnshuffle := by
  native_decide

private theorem g4l13_pm_nodes :
    pm_goal_4.nodes[1244]'(by native_decide) = g4l13PmUnshuffle0 ∧
    pm_goal_4.nodes[1246]'(by native_decide) = g4l13PmUnshuffle1 := by
  native_decide

private theorem g4l13_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l13PmUnshuffle0 =
      [g4l13PmUnshuffle0, g4l13PmUnshuffle1] := by
  native_decide

private theorem g4l13_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l13PmUnshuffle1 =
      [g4l13PmUnshuffle0, g4l13PmUnshuffle1] := by
  native_decide

private theorem g4l13_sm_nonempty564 :
    ∀ n ∈ sm_goal_4.nodes.drop 564, n.outs ≠ [] := by native_decide
private theorem g4l13_sm_nonempty565 :
    ∀ n ∈ sm_goal_4.nodes.drop 565, n.outs ≠ [] := by native_decide
private theorem g4l13_pm_nonempty1244 :
    ∀ n ∈ pm_goal_4.nodes.drop 1244, n.outs ≠ [] := by native_decide
private theorem g4l13_pm_nonempty1245 :
    ∀ n ∈ pm_goal_4.nodes.drop 1245, n.outs ≠ [] := by native_decide
private theorem g4l13_pm_nonempty1246 :
    ∀ n ∈ pm_goal_4.nodes.drop 1246, n.outs ≠ [] := by native_decide
private theorem g4l13_pm_nonempty1247 :
    ∀ n ∈ pm_goal_4.nodes.drop 1247, n.outs ≠ [] := by native_decide

private theorem g4l13_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(565, 5711), (564, 5682), (564, 5710)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l13_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1245, 10064), (1247, 10065),
      (1244, 9986), (1244, 9987), (1244, 5710),
      (1246, 9986), (1246, 9987), (1246, 5710)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l13_red_sm5711 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5711 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 5682 := by
  let pre := (sm_goal_4.nodes.take 564).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 5711 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l13SmUnshuffle 5711 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 564 g4l13SmUnshuffle 5711
      (by native_decide) g4l13_sm_node g4l13_sm_nonempty565
      (g4l13_sm_not_written 565 5711 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l13SmUnshuffle 5711 =
      pre 5682 := by
    unfold g4l13SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5682, 5710],
        outs := [5711], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5682 = denoteGraphDistributedFaithful sm_goal_4 initSM 5682 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 564 5682
      g4l13_sm_nonempty564 (g4l13_sm_not_written 564 5682 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l13_red_pm10064 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10064 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 9986,
         denoteGraphDistributedFaithful pm_goal_4 initPM 9987]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5710)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1244).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10064 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l13PmUnshuffle0 10064 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1244 g4l13PmUnshuffle0 10064
      (by native_decide) g4l13_pm_nodes.1 g4l13_pm_nonempty1245
      (g4l13_pm_not_written 1245 10064 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l13PmUnshuffle0 10064 =
      opfun (pre 9986) (pre 9987) (pre 5710) := by
    unfold g4l13PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [9986, 5710],
        outs := [10064], params := [2, 0] } =
        [g4l13PmUnshuffle0, g4l13PmUnshuffle1] from g4l13_pm_buddies0]
    unfold g4l13PmUnshuffle0 g4l13PmUnshuffle1 opfun
    rfl
  have h0 : pre 9986 = denoteGraphDistributedFaithful pm_goal_4 initPM 9986 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1244 9986
      g4l13_pm_nonempty1244 (g4l13_pm_not_written 1244 9986 (by decide))
  have h1 : pre 9987 = denoteGraphDistributedFaithful pm_goal_4 initPM 9987 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1244 9987
      g4l13_pm_nonempty1244 (g4l13_pm_not_written 1244 9987 (by decide))
  have hcu : pre 5710 = denoteGraphDistributedFaithful pm_goal_4 initPM 5710 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1244 5710
      g4l13_pm_nonempty1244 (g4l13_pm_not_written 1244 5710 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10064 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l13PmUnshuffle0 10064 := hcore
    _ = opfun (pre 9986) (pre 9987) (pre 5710) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
        (pre 9987) (pre 5710) := congrArg (fun x => opfun x (pre 9987) (pre 5710)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9987) (pre 5710) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9986) x
        (pre 5710)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9987)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5710) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9987)) hcu

private theorem g4l13_red_pm10065 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10065 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 9986,
         denoteGraphDistributedFaithful pm_goal_4 initPM 9987]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5710)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1246).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10065 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l13PmUnshuffle1 10065 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1246 g4l13PmUnshuffle1 10065
      (by native_decide) g4l13_pm_nodes.2 g4l13_pm_nonempty1247
      (g4l13_pm_not_written 1247 10065 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l13PmUnshuffle1 10065 =
      opfun (pre 9986) (pre 9987) (pre 5710) := by
    unfold g4l13PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [9987, 5710],
        outs := [10065], params := [2, 1] } =
        [g4l13PmUnshuffle0, g4l13PmUnshuffle1] from g4l13_pm_buddies1]
    unfold g4l13PmUnshuffle0 g4l13PmUnshuffle1 opfun
    rfl
  have h0 : pre 9986 = denoteGraphDistributedFaithful pm_goal_4 initPM 9986 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1246 9986
      g4l13_pm_nonempty1246 (g4l13_pm_not_written 1246 9986 (by decide))
  have h1 : pre 9987 = denoteGraphDistributedFaithful pm_goal_4 initPM 9987 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1246 9987
      g4l13_pm_nonempty1246 (g4l13_pm_not_written 1246 9987 (by decide))
  have hcu : pre 5710 = denoteGraphDistributedFaithful pm_goal_4 initPM 5710 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1246 5710
      g4l13_pm_nonempty1246 (g4l13_pm_not_written 1246 5710 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10065 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l13PmUnshuffle1 10065 := hcore
    _ = opfun (pre 9986) (pre 9987) (pre 5710) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
        (pre 9987) (pre 5710) := congrArg (fun x => opfun x (pre 9987) (pre 5710)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9987) (pre 5710) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9986) x
        (pre 5710)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9987)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5710) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 9987)) hcu

private theorem g4l13_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (5710 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l13_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 5710 = initPM 5710 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 5710 (by
      intro n hn
      native_decide +revert) g4l13_cu_not_written

private theorem g4l13_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l13_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-13 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l13_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5682)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9986)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9987)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5710)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5710) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5711)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10064)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10065)
      [4096, 64] [2048, 64] := by
  have hcu := g4l13_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5710) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l13_red_sm5711 initSM
  have hpm0 := g4l13_red_pm10064 initPM
  have hpm1 := g4l13_red_pm10065 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 9986,
     denoteGraphDistributedFaithful pm_goal_4 initPM 9987]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5710)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 9986,
     denoteGraphDistributedFaithful pm_goal_4 initPM 9987]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5710)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 5682 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 10064,
       denoteGraphDistributedFaithful pm_goal_4 initPM 10065] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 10064, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 10064,
          denoteGraphDistributedFaithful pm_goal_4 initPM 10065] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 10064, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9986).shape := by
    exact g4l13_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 9987).shape := by
    exact g4l13_unshuffle1_shape _ _ _
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

