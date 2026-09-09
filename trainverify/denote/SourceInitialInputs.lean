import denote.SourceScopedPrefix
import denote.RelationCompiler

/-!
Candidate, not compiled in the P2 lane. The source authority is
`Verdict/runtime_input_feed.py`: requests retain execution_to_source order;
port 0 is input_ids, port 1 is position_ids. Apply the bridge separately to
those ports. DP units select consecutive batch rows; TP ranks within a unit
receive copies, not additional batch shards. No historical-capture sample
association, Torch refinement, or equality of arbitrary Stores is asserted.
-/
namespace TrainVerify.Denote.SourceInitialInputs
open SourceScopedEval RelationCompiler
noncomputable section
set_option maxHeartbeats 500000

/-- Read a supplied tensor at the end of the SAME successful ordered request
schedule. The exact split fixes the loader occurrence; later writers must not
clobber this port. The successful checked schedule also enforces graph order.
No assumptions about the incoming Store's loader TIDs are needed. -/
theorem input_value_after
    (g : GraphDecl) (scope : NodeDecl → GroupScopedEval.Request)
    (peer : NodeDecl → Nat → Tid) (nodes : List NodeDecl)
    (requests before after : List InputRequest) (n : NodeDecl) (feed : PortFeed)
    (s t : Store) (tid : Tid) (value : Tensor)
    (hsplit : requests = before ++ (n, some feed) :: after)
    (hscope : scope n = .group none) (hc : InputContract n feed)
    (hmem : (tid, value) ∈ feed)
    (hfresh : ∀ row ∈ after, tid ∉ row.1.outs)
    (hrun : runWithInputs g scope peer nodes (some requests) (some s) = some t) :
    t tid = value := by
  change (if InputSchedule nodes requests then
    runUsing (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
      requests (some s) else none) = some t at hrun
  split at hrun
  · rw [hsplit, SourceScopedPrefix.runUsing_append] at hrun
    cases hb : runUsing
        (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
        before (some s) with
    | none =>
      rw [hb, runUsing_none] at hrun
      contradiction
    | some middle =>
      rw [hb] at hrun
      change runUsing
        (fun row a => stepWithInputs g (scope row.1) (peer row.1) a row.1 row.2)
        after (stepWithInputs g (scope n) (peer n) middle n (some feed)) = some t at hrun
      have hstep : stepWithInputs g (scope n) (peer n) middle n (some feed) =
          some (storeSet middle feed) := by
        rw [hscope]
        change checkedInputStep middle n feed = some (storeSet middle feed)
        exact checkedInputStep_valid middle n feed hc
      rw [hstep] at hrun
      exact (SourceScopedPrefix.frame g scope peer after (storeSet middle feed) t
        tid hfresh hrun).trans
        (checkedInputStep_value middle (storeSet middle feed) n feed tid value hmem
          (checkedInputStep_valid middle n feed hc))
  · contradiction

/-- The local sample row i is precisely global row unit * rows + i.
This uses chunk's existing coordinate theorem, rather than an unordered gather
or a shape-only argument. It generalizes to any positive number of DP units. -/
theorem batch_row_coordinate
    (full piece : Tensor) (units unit rows width : Nat)
    (hfull : full.shape = [rows * units, width])
    (hlocal : piece = chunkPrimDimN 0 units unit full)
    (hunits : 0 < units) (hunit : unit < units) (hwidth : 0 < width)
    (i j : Nat) (hi : i < rows) (hj : j < width) :
    valAt piece (i * width + j) = valAt full ((unit * rows + i) * width + j) := by
  have hdiv : rows * units / units = rows := Nat.mul_div_cancel rows hunits
  rw [hlocal]
  have h := chunkPrimDimN0_valAt units unit (rows * units) width full
    hfull hunits hwidth hunit i (by rw [hdiv]; exact hi) j hj
  rw [hdiv] at h
  exact h

private theorem batch_chunk_shape (full : Tensor) (rows width rank : Nat)
    (hfull : full.shape = [rows * 2, width]) :
    (chunkPrimDimN 0 2 rank full).shape = [rows, width] := by
  rw [chunkPrimDimN_shape 0 2 rank full _ hfull (by decide)]
  simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel rows (by decide : 0 < 2)]

private theorem copied_pair (a b : Tensor) (shape : Shape)
    (ha : a.shape = shape) (hb : b = a) : ReplicatedRel a [a, b] shape := by
  refine ⟨(by intro h; cases h), ha, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with h | h
    · exact h
    · have he : x = b := List.mem_singleton.mp h
      exact he.trans hb
  · intro x hx
    rcases List.mem_cons.mp hx with h | h
    · rw [h]; exact ha
    · have he : x = b := List.mem_singleton.mp h
      rw [he, hb]; exact ha

/-- Minimal DP2/TP2 value bridge. Four explicit caller tensor equations are
required, NOT the final relation. Gather one TP representative per DP unit;
replication is proved only inside each unit. Both TP lanes retain DP order. -/
theorem batchSplit_tpCopies_two
    (full p00 p01 p10 p11 : Tensor) (rows width : Nat)
    (hfull : full.shape = [rows * 2, width])
    (h00 : p00 = chunkPrimDimN 0 2 0 full)
    (h01 : p01 = chunkPrimDimN 0 2 0 full)
    (h10 : p10 = chunkPrimDimN 0 2 1 full)
    (h11 : p11 = chunkPrimDimN 0 2 1 full) :
    ChunkedRel full [p00, p10] 0 [rows * 2, width] [rows, width] ∧
    ChunkedRel full [p01, p11] 0 [rows * 2, width] [rows, width] ∧
    ReplicatedRel p00 [p00, p01] [rows, width] ∧
    ReplicatedRel p10 [p10, p11] [rows, width] := by
  have hs00 : p00.shape = [rows, width] := by
    rw [h00]; exact batch_chunk_shape full rows width 0 hfull
  have hs01 : p01.shape = [rows, width] := by
    rw [h01]; exact batch_chunk_shape full rows width 0 hfull
  have hs10 : p10.shape = [rows, width] := by
    rw [h10]; exact batch_chunk_shape full rows width 1 hfull
  have hs11 : p11.shape = [rows, width] := by
    rw [h11]; exact batch_chunk_shape full rows width 1 hfull
  refine ⟨?_, ?_, copied_pair p00 p01 _ hs00 (h01.trans h00.symm),
    copied_pair p10 p11 _ hs10 (h11.trans h10.symm)⟩
  · exact ChunkedRel.of_chunks_two hfull hs00 hs10 (by change 0 < 2; decide) rfl h00 h10
  · exact ChunkedRel.of_chunks_two hfull hs01 hs11 (by change 0 < 2; decide) rfl h01 h11

/-- Adapter to the existing relation compiler on actual endpoint Stores.
Obtain each read equation from input_value_after (or the emitted loader read
and prefix frame). Only the five named input TIDs are constrained. In the
current receipt input_ids uses SM 1262, PM 75/378/681/984; position_ids uses
SM 1263, PM 76/379/682/985. The caller retains full-ref identity and port order. -/
theorem initial_relations_two
    (sm pm : Store) (smTid p00Tid p01Tid p10Tid p11Tid : Tid)
    (full p00 p01 p10 p11 : Tensor) (rows width : Nat)
    (hsm : sm smTid = full)
    (hr00 : pm p00Tid = p00) (hr01 : pm p01Tid = p01)
    (hr10 : pm p10Tid = p10) (hr11 : pm p11Tid = p11)
    (hfull : full.shape = [rows * 2, width])
    (h00 : p00 = chunkPrimDimN 0 2 0 full)
    (h01 : p01 = chunkPrimDimN 0 2 0 full)
    (h10 : p10 = chunkPrimDimN 0 2 1 full)
    (h11 : p11 = chunkPrimDimN 0 2 1 full) :
    (RelationFact.chunked smTid [p00Tid, p10Tid] 0
      [rows * 2, width] [rows, width]).Holds sm pm ∧
    (RelationFact.chunked smTid [p01Tid, p11Tid] 0
      [rows * 2, width] [rows, width]).Holds sm pm ∧
    ReplicatedRel (pm p00Tid) [pm p00Tid, pm p01Tid] [rows, width] ∧
    ReplicatedRel (pm p10Tid) [pm p10Tid, pm p11Tid] [rows, width] := by
  change ChunkedRel (sm smTid) [pm p00Tid, pm p10Tid] 0
      [rows * 2, width] [rows, width] ∧
    ChunkedRel (sm smTid) [pm p01Tid, pm p11Tid] 0
      [rows * 2, width] [rows, width] ∧ _
  rw [hsm, hr00, hr01, hr10, hr11]
  exact batchSplit_tpCopies_two full p00 p01 p10 p11 rows width hfull h00 h01 h10 h11

#print axioms input_value_after
#print axioms batch_row_coordinate
#print axioms batchSplit_tpCopies_two
#print axioms initial_relations_two
end
end TrainVerify.Denote.SourceInitialInputs
