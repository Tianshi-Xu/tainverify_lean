/- Canonical Goal 4, layer 15: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l15SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5790, 5818],
    outs := [5819], params := [1, 0] }

private def g4l15PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10294, 5818],
    outs := [10372], params := [2, 0] }

private def g4l15PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10295, 5818],
    outs := [10373], params := [2, 1] }

private theorem g4l15_sm_node :
    sm_goal_4.nodes[636]'(by native_decide) = g4l15SmUnshuffle := by
  native_decide

private theorem g4l15_pm_nodes :
    pm_goal_4.nodes[1400]'(by native_decide) = g4l15PmUnshuffle0 ∧
    pm_goal_4.nodes[1402]'(by native_decide) = g4l15PmUnshuffle1 := by
  native_decide

private theorem g4l15_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l15PmUnshuffle0 =
      [g4l15PmUnshuffle0, g4l15PmUnshuffle1] := by
  native_decide

private theorem g4l15_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l15PmUnshuffle1 =
      [g4l15PmUnshuffle0, g4l15PmUnshuffle1] := by
  native_decide

private theorem g4l15_sm_nonempty636 :
    ∀ n ∈ sm_goal_4.nodes.drop 636, n.outs ≠ [] := by native_decide
private theorem g4l15_sm_nonempty637 :
    ∀ n ∈ sm_goal_4.nodes.drop 637, n.outs ≠ [] := by native_decide
private theorem g4l15_pm_nonempty1400 :
    ∀ n ∈ pm_goal_4.nodes.drop 1400, n.outs ≠ [] := by native_decide
private theorem g4l15_pm_nonempty1401 :
    ∀ n ∈ pm_goal_4.nodes.drop 1401, n.outs ≠ [] := by native_decide
private theorem g4l15_pm_nonempty1402 :
    ∀ n ∈ pm_goal_4.nodes.drop 1402, n.outs ≠ [] := by native_decide
private theorem g4l15_pm_nonempty1403 :
    ∀ n ∈ pm_goal_4.nodes.drop 1403, n.outs ≠ [] := by native_decide

private theorem g4l15_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(637, 5819), (636, 5790), (636, 5818)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l15_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1401, 10372), (1403, 10373),
      (1400, 10294), (1400, 10295), (1400, 5818),
      (1402, 10294), (1402, 10295), (1402, 5818)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l15_red_sm5819 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 5819 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 5790 := by
  let pre := (sm_goal_4.nodes.take 636).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 5819 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l15SmUnshuffle 5819 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 636 g4l15SmUnshuffle 5819
      (by native_decide) g4l15_sm_node g4l15_sm_nonempty637
      (g4l15_sm_not_written 637 5819 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l15SmUnshuffle 5819 =
      pre 5790 := by
    unfold g4l15SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [5790, 5818],
        outs := [5819], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 5790 = denoteGraphDistributedFaithful sm_goal_4 initSM 5790 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 636 5790
      g4l15_sm_nonempty636 (g4l15_sm_not_written 636 5790 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l15_red_pm10372 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10372 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10294,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10295]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5818)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1400).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10372 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l15PmUnshuffle0 10372 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1400 g4l15PmUnshuffle0 10372
      (by native_decide) g4l15_pm_nodes.1 g4l15_pm_nonempty1401
      (g4l15_pm_not_written 1401 10372 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l15PmUnshuffle0 10372 =
      opfun (pre 10294) (pre 10295) (pre 5818) := by
    unfold g4l15PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [10294, 5818],
        outs := [10372], params := [2, 0] } =
        [g4l15PmUnshuffle0, g4l15PmUnshuffle1] from g4l15_pm_buddies0]
    unfold g4l15PmUnshuffle0 g4l15PmUnshuffle1 opfun
    rfl
  have h0 : pre 10294 = denoteGraphDistributedFaithful pm_goal_4 initPM 10294 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1400 10294
      g4l15_pm_nonempty1400 (g4l15_pm_not_written 1400 10294 (by decide))
  have h1 : pre 10295 = denoteGraphDistributedFaithful pm_goal_4 initPM 10295 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1400 10295
      g4l15_pm_nonempty1400 (g4l15_pm_not_written 1400 10295 (by decide))
  have hcu : pre 5818 = denoteGraphDistributedFaithful pm_goal_4 initPM 5818 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1400 5818
      g4l15_pm_nonempty1400 (g4l15_pm_not_written 1400 5818 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10372 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l15PmUnshuffle0 10372 := hcore
    _ = opfun (pre 10294) (pre 10295) (pre 5818) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10294)
        (pre 10295) (pre 5818) := congrArg (fun x => opfun x (pre 10295) (pre 5818)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10294)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10295) (pre 5818) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10294) x
        (pre 5818)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10294)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10295)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5818) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10294)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10295)) hcu

private theorem g4l15_red_pm10373 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 10373 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 10294,
         denoteGraphDistributedFaithful pm_goal_4 initPM 10295]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5818)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1402).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 10373 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l15PmUnshuffle1 10373 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1402 g4l15PmUnshuffle1 10373
      (by native_decide) g4l15_pm_nodes.2 g4l15_pm_nonempty1403
      (g4l15_pm_not_written 1403 10373 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l15PmUnshuffle1 10373 =
      opfun (pre 10294) (pre 10295) (pre 5818) := by
    unfold g4l15PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [10295, 5818],
        outs := [10373], params := [2, 1] } =
        [g4l15PmUnshuffle0, g4l15PmUnshuffle1] from g4l15_pm_buddies1]
    unfold g4l15PmUnshuffle0 g4l15PmUnshuffle1 opfun
    rfl
  have h0 : pre 10294 = denoteGraphDistributedFaithful pm_goal_4 initPM 10294 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1402 10294
      g4l15_pm_nonempty1402 (g4l15_pm_not_written 1402 10294 (by decide))
  have h1 : pre 10295 = denoteGraphDistributedFaithful pm_goal_4 initPM 10295 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1402 10295
      g4l15_pm_nonempty1402 (g4l15_pm_not_written 1402 10295 (by decide))
  have hcu : pre 5818 = denoteGraphDistributedFaithful pm_goal_4 initPM 5818 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1402 5818
      g4l15_pm_nonempty1402 (g4l15_pm_not_written 1402 5818 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 10373 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l15PmUnshuffle1 10373 := hcore
    _ = opfun (pre 10294) (pre 10295) (pre 5818) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10294)
        (pre 10295) (pre 5818) := congrArg (fun x => opfun x (pre 10295) (pre 5818)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10294)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10295) (pre 5818) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10294) x
        (pre 5818)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10294)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10295)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 5818) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 10294)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 10295)) hcu

private theorem g4l15_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (5818 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l15_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 5818 = initPM 5818 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 5818 (by
      intro n hn
      native_decide +revert) g4l15_cu_not_written

private theorem g4l15_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l15_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-15 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l15_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5790)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10294)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10295)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5818)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 5818) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 5819)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10372)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10373)
      [4096, 64] [2048, 64] := by
  have hcu := g4l15_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 5818) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l15_red_sm5819 initSM
  have hpm0 := g4l15_red_pm10372 initPM
  have hpm1 := g4l15_red_pm10373 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10294,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10295]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5818)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 10294,
     denoteGraphDistributedFaithful pm_goal_4 initPM 10295]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 5818)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 5790 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 10372,
       denoteGraphDistributedFaithful pm_goal_4 initPM 10373] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 10372, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 10372,
          denoteGraphDistributedFaithful pm_goal_4 initPM 10373] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 10372, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10294).shape := by
    exact g4l15_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 10295).shape := by
    exact g4l15_unshuffle1_shape _ _ _
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

