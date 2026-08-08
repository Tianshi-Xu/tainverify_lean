/- Canonical Goal 4, layer 21: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_4
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g4l21SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6114, 6142],
    outs := [6143], params := [1, 0] }

private def g4l21PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11218, 6142],
    outs := [11296], params := [2, 0] }

private def g4l21PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11219, 6142],
    outs := [11297], params := [2, 1] }

private theorem g4l21_sm_node :
    sm_goal_4.nodes[852]'(by native_decide) = g4l21SmUnshuffle := by
  native_decide

private theorem g4l21_pm_nodes :
    pm_goal_4.nodes[1868]'(by native_decide) = g4l21PmUnshuffle0 ∧
    pm_goal_4.nodes[1870]'(by native_decide) = g4l21PmUnshuffle1 := by
  native_decide

private theorem g4l21_pm_buddies0 :
    pm_goal_4.replicaBuddies g4l21PmUnshuffle0 =
      [g4l21PmUnshuffle0, g4l21PmUnshuffle1] := by
  native_decide

private theorem g4l21_pm_buddies1 :
    pm_goal_4.replicaBuddies g4l21PmUnshuffle1 =
      [g4l21PmUnshuffle0, g4l21PmUnshuffle1] := by
  native_decide

private theorem g4l21_sm_nonempty852 :
    ∀ n ∈ sm_goal_4.nodes.drop 852, n.outs ≠ [] := by native_decide
private theorem g4l21_sm_nonempty853 :
    ∀ n ∈ sm_goal_4.nodes.drop 853, n.outs ≠ [] := by native_decide
private theorem g4l21_pm_nonempty1868 :
    ∀ n ∈ pm_goal_4.nodes.drop 1868, n.outs ≠ [] := by native_decide
private theorem g4l21_pm_nonempty1869 :
    ∀ n ∈ pm_goal_4.nodes.drop 1869, n.outs ≠ [] := by native_decide
private theorem g4l21_pm_nonempty1870 :
    ∀ n ∈ pm_goal_4.nodes.drop 1870, n.outs ≠ [] := by native_decide
private theorem g4l21_pm_nonempty1871 :
    ∀ n ∈ pm_goal_4.nodes.drop 1871, n.outs ≠ [] := by native_decide

private theorem g4l21_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(853, 6143), (852, 6114), (852, 6142)]) :
    ∀ n ∈ sm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l21_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1869, 11296), (1871, 11297),
      (1868, 11218), (1868, 11219), (1868, 6142),
      (1870, 11218), (1870, 11219), (1870, 6142)]) :
    ∀ n ∈ pm_goal_4.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g4l21_red_sm6143 (initSM : Store) :
    denoteGraphDistributedFaithful sm_goal_4 initSM 6143 =
      denoteGraphDistributedFaithful sm_goal_4 initSM 6114 := by
  let pre := (sm_goal_4.nodes.take 852).foldl
    (applyNodeDistributedFaithful sm_goal_4) initSM
  have hcore : denoteGraphDistributedFaithful sm_goal_4 initSM 6143 =
      applyNodeDistributedFaithful sm_goal_4 pre g4l21SmUnshuffle 6143 :=
    denoteGraphDistributedFaithful_node_core sm_goal_4 initSM 852 g4l21SmUnshuffle 6143
      (by native_decide) g4l21_sm_node g4l21_sm_nonempty853
      (g4l21_sm_not_written 853 6143 (by decide))
  have happly : applyNodeDistributedFaithful sm_goal_4 pre g4l21SmUnshuffle 6143 =
      pre 6114 := by
    unfold g4l21SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm_goal_4 pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6114, 6142],
        outs := [6143], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 6114 = denoteGraphDistributedFaithful sm_goal_4 initSM 6114 :=
    denoteGraphDistributedFaithful_prefix_read sm_goal_4 initSM 852 6114
      g4l21_sm_nonempty852 (g4l21_sm_not_written 852 6114 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g4l21_red_pm11296 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 11296 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 11218,
         denoteGraphDistributedFaithful pm_goal_4 initPM 11219]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6142)) 2 0 := by
  let pre := (pm_goal_4.nodes.take 1868).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 11296 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l21PmUnshuffle0 11296 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1868 g4l21PmUnshuffle0 11296
      (by native_decide) g4l21_pm_nodes.1 g4l21_pm_nonempty1869
      (g4l21_pm_not_written 1869 11296 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l21PmUnshuffle0 11296 =
      opfun (pre 11218) (pre 11219) (pre 6142) := by
    unfold g4l21PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11218, 6142],
        outs := [11296], params := [2, 0] } =
        [g4l21PmUnshuffle0, g4l21PmUnshuffle1] from g4l21_pm_buddies0]
    unfold g4l21PmUnshuffle0 g4l21PmUnshuffle1 opfun
    rfl
  have h0 : pre 11218 = denoteGraphDistributedFaithful pm_goal_4 initPM 11218 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1868 11218
      g4l21_pm_nonempty1868 (g4l21_pm_not_written 1868 11218 (by decide))
  have h1 : pre 11219 = denoteGraphDistributedFaithful pm_goal_4 initPM 11219 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1868 11219
      g4l21_pm_nonempty1868 (g4l21_pm_not_written 1868 11219 (by decide))
  have hcu : pre 6142 = denoteGraphDistributedFaithful pm_goal_4 initPM 6142 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1868 6142
      g4l21_pm_nonempty1868 (g4l21_pm_not_written 1868 6142 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 11296 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l21PmUnshuffle0 11296 := hcore
    _ = opfun (pre 11218) (pre 11219) (pre 6142) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11218)
        (pre 11219) (pre 6142) := congrArg (fun x => opfun x (pre 11219) (pre 6142)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11218)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11219) (pre 6142) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11218) x
        (pre 6142)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11218)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11219)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 6142) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11218)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11219)) hcu

private theorem g4l21_red_pm11297 (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 11297 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm_goal_4 initPM 11218,
         denoteGraphDistributedFaithful pm_goal_4 initPM 11219]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6142)) 2 1 := by
  let pre := (pm_goal_4.nodes.take 1870).foldl
    (applyNodeDistributedFaithful pm_goal_4) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm_goal_4 initPM 11297 =
      applyNodeDistributedFaithful pm_goal_4 pre g4l21PmUnshuffle1 11297 :=
    denoteGraphDistributedFaithful_node_core pm_goal_4 initPM 1870 g4l21PmUnshuffle1 11297
      (by native_decide) g4l21_pm_nodes.2 g4l21_pm_nonempty1871
      (g4l21_pm_not_written 1871 11297 (by decide))
  have happly : applyNodeDistributedFaithful pm_goal_4 pre g4l21PmUnshuffle1 11297 =
      opfun (pre 11218) (pre 11219) (pre 6142) := by
    unfold g4l21PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm_goal_4.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11219, 6142],
        outs := [11297], params := [2, 1] } =
        [g4l21PmUnshuffle0, g4l21PmUnshuffle1] from g4l21_pm_buddies1]
    unfold g4l21PmUnshuffle0 g4l21PmUnshuffle1 opfun
    rfl
  have h0 : pre 11218 = denoteGraphDistributedFaithful pm_goal_4 initPM 11218 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1870 11218
      g4l21_pm_nonempty1870 (g4l21_pm_not_written 1870 11218 (by decide))
  have h1 : pre 11219 = denoteGraphDistributedFaithful pm_goal_4 initPM 11219 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1870 11219
      g4l21_pm_nonempty1870 (g4l21_pm_not_written 1870 11219 (by decide))
  have hcu : pre 6142 = denoteGraphDistributedFaithful pm_goal_4 initPM 6142 :=
    denoteGraphDistributedFaithful_prefix_read pm_goal_4 initPM 1870 6142
      g4l21_pm_nonempty1870 (g4l21_pm_not_written 1870 6142 (by decide))
  calc
    denoteGraphDistributedFaithful pm_goal_4 initPM 11297 =
        applyNodeDistributedFaithful pm_goal_4 pre g4l21PmUnshuffle1 11297 := hcore
    _ = opfun (pre 11218) (pre 11219) (pre 6142) := happly
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11218)
        (pre 11219) (pre 6142) := congrArg (fun x => opfun x (pre 11219) (pre 6142)) h0
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11218)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11219) (pre 6142) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11218) x
        (pre 6142)) h1
    _ = opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11218)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11219)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 6142) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm_goal_4 initPM 11218)
        (denoteGraphDistributedFaithful pm_goal_4 initPM 11219)) hcu

private theorem g4l21_cu_not_written :
    ∀ n ∈ pm_goal_4.nodes, (6142 : Tid) ∉ n.outs := by
  native_decide

private theorem g4l21_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm_goal_4 initPM 6142 = initPM 6142 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm_goal_4 pm_goal_4.nodes
    initPM 6142 (by
      intro n hn
      native_decide +revert) g4l21_cu_not_written

private theorem g4l21_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g4l21_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-21 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal4_l21_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 6114)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11218)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11219)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 6142)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 6142) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm_goal_4 initSM 6143)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11296)
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11297)
      [4096, 64] [2048, 64] := by
  have hcu := g4l21_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm_goal_4 initPM 6142) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g4l21_red_sm6143 initSM
  have hpm0 := g4l21_red_pm11296 initPM
  have hpm1 := g4l21_red_pm11297 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 11218,
     denoteGraphDistributedFaithful pm_goal_4 initPM 11219]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6142)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm_goal_4 initPM 11218,
     denoteGraphDistributedFaithful pm_goal_4 initPM 11219]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm_goal_4 initPM 6142)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm_goal_4 initSM 6114 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm_goal_4 initPM 11296,
       denoteGraphDistributedFaithful pm_goal_4 initPM 11297] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm_goal_4 initPM 11296, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm_goal_4 initPM 11296,
          denoteGraphDistributedFaithful pm_goal_4 initPM 11297] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm_goal_4 initPM 11296, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11218).shape := by
    exact g4l21_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm_goal_4 initPM 11219).shape := by
    exact g4l21_unshuffle1_shape _ _ _
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

