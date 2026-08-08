/- Canonical Goal 4, layer 22: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l22SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6168, 6196],
    outs := [6197], params := [1, 0] }

private def g4l22PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11372, 6196],
    outs := [11450], params := [2, 0] }

private def g4l22PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11373, 6196],
    outs := [11451], params := [2, 1] }

private theorem g4l22_sm_node :
    sm_goal_4.nodes[888]'(by native_decide) = g4l22SmUnshuffle := by
  native_decide

private theorem g4l22_pm_nodes :
    pm_goal_4.nodes[1946]'(by native_decide) = g4l22PmUnshuffle0 ∧
    pm_goal_4.nodes[1948]'(by native_decide) = g4l22PmUnshuffle1 := by
  native_decide

private theorem g4l22_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l22PmUnshuffle0 =
      [g4l22PmUnshuffle0, g4l22PmUnshuffle1] := by
  native_decide

private theorem g4l22_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l22PmUnshuffle1 =
      [g4l22PmUnshuffle0, g4l22PmUnshuffle1] := by
  native_decide

private theorem g4l22_sm_nonempty888 :
    ∀ n ∈ sm_goal_4.nodes.drop 888, n.outs ≠ [] := by native_decide
private theorem g4l22_sm_nonempty889 :
    ∀ n ∈ sm_goal_4.nodes.drop 889, n.outs ≠ [] := by native_decide
private theorem g4l22_pm_nonempty1946 :
    ∀ n ∈ pm_goal_4.nodes.drop 1946, n.outs ≠ [] := by native_decide
private theorem g4l22_pm_nonempty1947 :
    ∀ n ∈ pm_goal_4.nodes.drop 1947, n.outs ≠ [] := by native_decide
private theorem g4l22_pm_nonempty1948 :
    ∀ n ∈ pm_goal_4.nodes.drop 1948, n.outs ≠ [] := by native_decide
private theorem g4l22_pm_nonempty1949 :
    ∀ n ∈ pm_goal_4.nodes.drop 1949, n.outs ≠ [] := by native_decide

private theorem g4l22_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(889, 6197), (888, 6168), (888, 6196)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l22_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1947, 11450), (1949, 11451),
      (1946, 11372), (1946, 11373), (1946, 6196),
      (1948, 11372), (1948, 11373), (1948, 6196)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l22_red_sm6197 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 6197 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 6168 := by
  let pre := (sm_goal_4.nodes.take 888).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 6197 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l22SmUnshuffle 6197 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 888 g4l22SmUnshuffle 6197
      (by native_decide) g4l22_sm_node g4l22_sm_nonempty889
      (g4l22_sm_not_written 889 6197 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l22SmUnshuffle 6197 =
      pre 6168 := by
    unfold g4l22SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6168, 6196],
        outs := [6197], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 6168 = denoteGraphDistributedFaithful sm_goal_4 initSM 6168 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 888 6168
      g4l22_sm_nonempty888 (g4l22_sm_not_written 888 6168 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l22_red_pm11450 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 11450 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 11372,
         denoteGraphDistributedFaithful pm_goal_4 initPM 11373]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6196)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1946).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 11450 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l22PmUnshuffle0 11450 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1946 g4l22PmUnshuffle0 11450
      (by native_decide) g4l22_pm_nodes.1 g4l22_pm_nonempty1947
      (g4l22_pm_not_written 1947 11450 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l22PmUnshuffle0 11450 =
      opfun (pre 11372) (pre 11373) (pre 6196) := by
    unfold g4l22PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11372, 6196],
        outs := [11450], params := [2, 0] } =
        [g4l22PmUnshuffle0, g4l22PmUnshuffle1] from g4l22_pm_buddies0]
    unfold g4l22PmUnshuffle0 g4l22PmUnshuffle1 opfun
    rfl
  have h0 : pre 11372 = denoteGraphDistributedFaithful pm_goal_4 initPM 11372 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1946 11372
      g4l22_pm_nonempty1946 (g4l22_pm_not_written 1946 11372 (by decide))
  have h1 : pre 11373 = denoteGraphDistributedFaithful pm_goal_4 initPM 11373 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1946 11373
      g4l22_pm_nonempty1946 (g4l22_pm_not_written 1946 11373 (by decide))
  have hcu : pre 6196 = denoteGraphDistributedFaithful pm_goal_4 initPM 6196 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1946 6196
      g4l22_pm_nonempty1946 (g4l22_pm_not_written 1946 6196 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 11450 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l22PmUnshuffle0 11450 := hcore
    _ = opfun (pre 11372) (pre 11373) (pre 6196) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
        (pre 11373) (pre 6196) := congrArg (fun x => opfun x (pre 11373) (pre 6196)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11373) (pre 6196) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11372) x
        (pre 6196)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11373)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 6196) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11373)) hcu

private theorem g4l22_red_pm11451 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 11451 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 11372,
         denoteGraphDistributedFaithful pm_goal_4 initPM 11373]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6196)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1948).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 11451 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l22PmUnshuffle1 11451 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1948 g4l22PmUnshuffle1 11451
      (by native_decide) g4l22_pm_nodes.2 g4l22_pm_nonempty1949
      (g4l22_pm_not_written 1949 11451 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l22PmUnshuffle1 11451 =
      opfun (pre 11372) (pre 11373) (pre 6196) := by
    unfold g4l22PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11373, 6196],
        outs := [11451], params := [2, 1] } =
        [g4l22PmUnshuffle0, g4l22PmUnshuffle1] from g4l22_pm_buddies1]
    unfold g4l22PmUnshuffle0 g4l22PmUnshuffle1 opfun
    rfl
  have h0 : pre 11372 = denoteGraphDistributedFaithful pm_goal_4 initPM 11372 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1948 11372
      g4l22_pm_nonempty1948 (g4l22_pm_not_written 1948 11372 (by decide))
  have h1 : pre 11373 = denoteGraphDistributedFaithful pm_goal_4 initPM 11373 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1948 11373
      g4l22_pm_nonempty1948 (g4l22_pm_not_written 1948 11373 (by decide))
  have hcu : pre 6196 = denoteGraphDistributedFaithful pm_goal_4 initPM 6196 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1948 6196
      g4l22_pm_nonempty1948 (g4l22_pm_not_written 1948 6196 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 11451 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l22PmUnshuffle1 11451 := hcore
    _ = opfun (pre 11372) (pre 11373) (pre 6196) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
        (pre 11373) (pre 6196) := congrArg (fun x => opfun x (pre 11373) (pre 6196)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11373) (pre 6196) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11372) x
        (pre 6196)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11373)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 6196) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11373)) hcu

private theorem g4l22_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (6196 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l22_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 6196 = initPM 6196 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 6196 (by
      intro n hn
      native_decide +revert) g4l22_cu_not_written

private theorem g4l22_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l22_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-22 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l22_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 6168)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11372)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11373)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 6196)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 6196) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 6197)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11450)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11451)
      [4096, 64] [2048, 64] := by
  have hcu := g4l22_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 6196) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l22_red_sm6197 initSM
  have hpm0 := g4l22_red_pm11450 initPM
  have hpm1 := g4l22_red_pm11451 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 11372,
     denoteGraphDistributedFaithful pm_goal_4 initPM 11373]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6196)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 11372,
     denoteGraphDistributedFaithful pm_goal_4 initPM 11373]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6196)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 6168 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 11450,
       denoteGraphDistributedFaithful pm_goal_4 initPM 11451] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 11450, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 11450,
          denoteGraphDistributedFaithful pm_goal_4 initPM 11451] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 11450, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11372).shape := by
    exact g4l22_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11373).shape := by
    exact g4l22_unshuffle1_shape _ _ _
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

