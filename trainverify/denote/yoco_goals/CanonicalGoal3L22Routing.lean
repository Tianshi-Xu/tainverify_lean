/- Canonical Goal 3, layer 22: faithful routing-map unshuffle boundary. -/
import denote.yoco_goals.Goal_3_FaithfulFull
import denote.yoco_goals.FaithfulStackGather

set_option maxRecDepth 1000000

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated
open TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote.ZigzagCollective

noncomputable section

private def g3l22SmUnshuffle : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6167, 6194],
    outs := [6195], params := [1, 0] }

private def g3l22PmUnshuffle0 : NodeDecl :=
  { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11370, 6194],
    outs := [11448], params := [2, 0] }

private def g3l22PmUnshuffle1 : NodeDecl :=
  { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11371, 6194],
    outs := [11449], params := [2, 1] }

private theorem g3l22_sm_node :
    sm.nodes[898]'(by native_decide) = g3l22SmUnshuffle := by
  native_decide

private theorem g3l22_pm_nodes :
    pm.nodes[1968]'(by native_decide) = g3l22PmUnshuffle0 ∧
    pm.nodes[1971]'(by native_decide) = g3l22PmUnshuffle1 := by
  native_decide

private theorem g3l22_pm_buddies0 :
    pm.replicaBuddies g3l22PmUnshuffle0 =
      [g3l22PmUnshuffle0, g3l22PmUnshuffle1] := by
  native_decide

private theorem g3l22_pm_buddies1 :
    pm.replicaBuddies g3l22PmUnshuffle1 =
      [g3l22PmUnshuffle0, g3l22PmUnshuffle1] := by
  native_decide

private theorem g3l22_sm_nonempty898 :
    ∀ n ∈ sm.nodes.drop 898, n.outs ≠ [] := by native_decide
private theorem g3l22_sm_nonempty899 :
    ∀ n ∈ sm.nodes.drop 899, n.outs ≠ [] := by native_decide
private theorem g3l22_pm_nonempty1968 :
    ∀ n ∈ pm.nodes.drop 1968, n.outs ≠ [] := by native_decide
private theorem g3l22_pm_nonempty1969 :
    ∀ n ∈ pm.nodes.drop 1969, n.outs ≠ [] := by native_decide
private theorem g3l22_pm_nonempty1971 :
    ∀ n ∈ pm.nodes.drop 1971, n.outs ≠ [] := by native_decide
private theorem g3l22_pm_nonempty1972 :
    ∀ n ∈ pm.nodes.drop 1972, n.outs ≠ [] := by native_decide

private theorem g3l22_sm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(899, 6195), (898, 6167), (898, 6194)]) :
    ∀ n ∈ sm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l22_pm_not_written (k tid : Nat)
    (h : (k, tid) ∈ [(1969, 11448), (1972, 11449),
      (1968, 11370), (1968, 11371), (1968, 6194),
      (1971, 11370), (1971, 11371), (1971, 6194)]) :
    ∀ n ∈ pm.nodes.drop k, tid ∉ n.outs := by
  simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    native_decide +revert

private theorem g3l22_red_sm6195 (initSM : Store) :
    denoteGraphDistributedFaithful sm initSM 6195 =
      denoteGraphDistributedFaithful sm initSM 6167 := by
  let pre := (sm.nodes.take 898).foldl
    (applyNodeDistributedFaithful sm) initSM
  have hcore : denoteGraphDistributedFaithful sm initSM 6195 =
      applyNodeDistributedFaithful sm pre g3l22SmUnshuffle 6195 :=
    denoteGraphDistributedFaithful_node_core sm initSM 898 g3l22SmUnshuffle 6195
      (by native_decide) g3l22_sm_node g3l22_sm_nonempty899
      (g3l22_sm_not_written 899 6195 (by decide))
  have happly : applyNodeDistributedFaithful sm pre g3l22SmUnshuffle 6195 =
      pre 6167 := by
    unfold g3l22SmUnshuffle
    rw [applyNodeDistributedFaithful_unshuffle_out]
    rw [applyNodeFaithfulUnshuffleValue_cpSize_one sm pre
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [6167, 6194],
        outs := [6195], params := [1, 0] }
      (by native_decide) (by native_decide) (by native_decide)]
    rfl
  have hread : pre 6167 = denoteGraphDistributedFaithful sm initSM 6167 :=
    denoteGraphDistributedFaithful_prefix_read sm initSM 898 6167
      g3l22_sm_nonempty898 (g3l22_sm_not_written 898 6167 (by decide))
  exact hcore.trans (happly.trans hread)

private theorem g3l22_red_pm11448 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11448 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11370,
         denoteGraphDistributedFaithful pm initPM 11371]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6194)) 2 0 := by
  let pre := (pm.nodes.take 1968).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 0
  have hcore : denoteGraphDistributedFaithful pm initPM 11448 =
      applyNodeDistributedFaithful pm pre g3l22PmUnshuffle0 11448 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1968 g3l22PmUnshuffle0 11448
      (by native_decide) g3l22_pm_nodes.1 g3l22_pm_nonempty1969
      (g3l22_pm_not_written 1969 11448 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l22PmUnshuffle0 11448 =
      opfun (pre 11370) (pre 11371) (pre 6194) := by
    unfold g3l22PmUnshuffle0
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 0, op := "OpName.FW_maybe_unshuffle", ins := [11370, 6194],
        outs := [11448], params := [2, 0] } =
        [g3l22PmUnshuffle0, g3l22PmUnshuffle1] from g3l22_pm_buddies0]
    unfold g3l22PmUnshuffle0 g3l22PmUnshuffle1 opfun
    rfl
  have h0 : pre 11370 = denoteGraphDistributedFaithful pm initPM 11370 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1968 11370
      g3l22_pm_nonempty1968 (g3l22_pm_not_written 1968 11370 (by decide))
  have h1 : pre 11371 = denoteGraphDistributedFaithful pm initPM 11371 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1968 11371
      g3l22_pm_nonempty1968 (g3l22_pm_not_written 1968 11371 (by decide))
  have hcu : pre 6194 = denoteGraphDistributedFaithful pm initPM 6194 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1968 6194
      g3l22_pm_nonempty1968 (g3l22_pm_not_written 1968 6194 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 11448 =
        applyNodeDistributedFaithful pm pre g3l22PmUnshuffle0 11448 := hcore
    _ = opfun (pre 11370) (pre 11371) (pre 6194) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11370)
        (pre 11371) (pre 6194) := congrArg (fun x => opfun x (pre 11371) (pre 6194)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11370)
        (denoteGraphDistributedFaithful pm initPM 11371) (pre 6194) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 11370) x
        (pre 6194)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11370)
        (denoteGraphDistributedFaithful pm initPM 11371)
        (denoteGraphDistributedFaithful pm initPM 6194) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 11370)
        (denoteGraphDistributedFaithful pm initPM 11371)) hcu

private theorem g3l22_red_pm11449 (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 11449 =
      fw_maybe_unshuffle_collective
        [denoteGraphDistributedFaithful pm initPM 11370,
         denoteGraphDistributedFaithful pm initPM 11371]
        (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6194)) 2 1 := by
  let pre := (pm.nodes.take 1971).foldl
    (applyNodeDistributedFaithful pm) initPM
  let opfun := fun a b cu =>
    fw_maybe_unshuffle_collective [a, b] (decodeCuSeqlens cu) 2 1
  have hcore : denoteGraphDistributedFaithful pm initPM 11449 =
      applyNodeDistributedFaithful pm pre g3l22PmUnshuffle1 11449 :=
    denoteGraphDistributedFaithful_node_core pm initPM 1971 g3l22PmUnshuffle1 11449
      (by native_decide) g3l22_pm_nodes.2 g3l22_pm_nonempty1972
      (g3l22_pm_not_written 1972 11449 (by decide))
  have happly : applyNodeDistributedFaithful pm pre g3l22PmUnshuffle1 11449 =
      opfun (pre 11370) (pre 11371) (pre 6194) := by
    unfold g3l22PmUnshuffle1
    rw [applyNodeDistributedFaithful_unshuffle_out]
    unfold applyNodeFaithfulUnshuffleValue
    rw [show pm.replicaBuddies
      { rank := 1, op := "OpName.FW_maybe_unshuffle", ins := [11371, 6194],
        outs := [11449], params := [2, 1] } =
        [g3l22PmUnshuffle0, g3l22PmUnshuffle1] from g3l22_pm_buddies1]
    unfold g3l22PmUnshuffle0 g3l22PmUnshuffle1 opfun
    rfl
  have h0 : pre 11370 = denoteGraphDistributedFaithful pm initPM 11370 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1971 11370
      g3l22_pm_nonempty1971 (g3l22_pm_not_written 1971 11370 (by decide))
  have h1 : pre 11371 = denoteGraphDistributedFaithful pm initPM 11371 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1971 11371
      g3l22_pm_nonempty1971 (g3l22_pm_not_written 1971 11371 (by decide))
  have hcu : pre 6194 = denoteGraphDistributedFaithful pm initPM 6194 :=
    denoteGraphDistributedFaithful_prefix_read pm initPM 1971 6194
      g3l22_pm_nonempty1971 (g3l22_pm_not_written 1971 6194 (by decide))
  calc
    denoteGraphDistributedFaithful pm initPM 11449 =
        applyNodeDistributedFaithful pm pre g3l22PmUnshuffle1 11449 := hcore
    _ = opfun (pre 11370) (pre 11371) (pre 6194) := happly
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11370)
        (pre 11371) (pre 6194) := congrArg (fun x => opfun x (pre 11371) (pre 6194)) h0
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11370)
        (denoteGraphDistributedFaithful pm initPM 11371) (pre 6194) :=
      congrArg (fun x => opfun (denoteGraphDistributedFaithful pm initPM 11370) x
        (pre 6194)) h1
    _ = opfun (denoteGraphDistributedFaithful pm initPM 11370)
        (denoteGraphDistributedFaithful pm initPM 11371)
        (denoteGraphDistributedFaithful pm initPM 6194) :=
      congrArg (opfun (denoteGraphDistributedFaithful pm initPM 11370)
        (denoteGraphDistributedFaithful pm initPM 11371)) hcu

private theorem g3l22_cu_not_written :
    ∀ n ∈ pm.nodes, (6194 : Tid) ∉ n.outs := by
  native_decide

private theorem g3l22_cu_input (initPM : Store) :
    denoteGraphDistributedFaithful pm initPM 6194 = initPM 6194 := by
  unfold denoteGraphDistributedFaithful
  exact foldl_applyNodeDistributedFaithful_at_not_written pm pm.nodes
    initPM 6194 (by
      intro n hn
      native_decide +revert) g3l22_cu_not_written

private theorem g3l22_unshuffle0_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 0).shape = z0.shape := by
  exact fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 0

private theorem g3l22_unshuffle1_shape (z0 z1 : Tensor) (cu : List Nat) :
    (fw_maybe_unshuffle_collective [z0, z1] cu 2 1).shape = z1.shape := by
  simpa only [List.getD_cons_succ, List.getD_cons_zero] using
    (fw_maybe_unshuffle_collective_shape [z0, z1] cu 2 1)

/-- The canonical layer-22 routing map becomes an ordinary two-rank relation
after its generated faithful unshuffle nodes.  The zigzag premise is produced
by the layer computation; the decoded equality is derived solely from the
external `PackedCuSeqlensWF` contract. -/
theorem canonical_goal3_l22_routing_unshuffle
    (initSM initPM : Store)
    (hrel : Zigzag2Rel
      (denoteGraphDistributedFaithful sm initSM 6167)
      (denoteGraphDistributedFaithful pm initPM 11370)
      (denoteGraphDistributedFaithful pm initPM 11371)
      (denoteGraphDistributedFaithful pm initPM 6194)
      [4096, 64] [2048, 64])
    (hPacked : PackedCuSeqlensWF (initPM 6194) 4096 2) :
    Ordinary2Rel
      (denoteGraphDistributedFaithful sm initSM 6195)
      (denoteGraphDistributedFaithful pm initPM 11448)
      (denoteGraphDistributedFaithful pm initPM 11449)
      [4096, 64] [2048, 64] := by
  have hcu := g3l22_cu_input initPM
  have hdec : decodeCuSeqlens
      (denoteGraphDistributedFaithful pm initPM 6194) = [0, 2 * 2048] := by
    exact (congrArg decodeCuSeqlens hcu).trans (by
      simpa only [Nat.reduceMul] using hPacked.decoded_single)
  have hsm := g3l22_red_sm6195 initSM
  have hpm0 := g3l22_red_pm11448 initPM
  have hpm1 := g3l22_red_pm11449 initPM
  let u0 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 11370,
     denoteGraphDistributedFaithful pm initPM 11371]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6194)) 2 0
  let u1 := fw_maybe_unshuffle_collective
    [denoteGraphDistributedFaithful pm initPM 11370,
     denoteGraphDistributedFaithful pm initPM 11371]
    (decodeCuSeqlens (denoteGraphDistributedFaithful pm initPM 6194)) 2 1
  have hunshuffle : denoteGraphDistributedFaithful sm initSM 6167 =
      allGatherPrimDimN 0 2 0 [u0, u1] :=
    Zigzag2Rel.unshuffle_gather_single 2048 [64] hrel
      (by decide) (by decide) (by decide) hdec
  have hlist : [u0, u1] =
      [denoteGraphDistributedFaithful pm initPM 11448,
       denoteGraphDistributedFaithful pm initPM 11449] := by
    calc
      [u0, u1] = [denoteGraphDistributedFaithful pm initPM 11448, u1] :=
        congrArg (fun x => [x, u1]) hpm0.symm
      _ = [denoteGraphDistributedFaithful pm initPM 11448,
          denoteGraphDistributedFaithful pm initPM 11449] :=
        congrArg (fun x => [denoteGraphDistributedFaithful pm initPM 11448, x])
          hpm1.symm
  have hu0shape : u0.shape =
      (denoteGraphDistributedFaithful pm initPM 11370).shape := by
    exact g3l22_unshuffle0_shape _ _ _
  have hu1shape : u1.shape =
      (denoteGraphDistributedFaithful pm initPM 11371).shape := by
    exact g3l22_unshuffle1_shape _ _ _
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
