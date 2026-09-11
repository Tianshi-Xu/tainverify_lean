import denote.SourceMatmulUnit
import denote.KRankMatmulQueryAxis

/-!
# Query-sharded matmul with a replicated right operand within one batch unit

UNCOMPILED library candidate: compilation and the printed axiom audit are
reserved for the parent. This file neither authenticates source-graph DP
ownership nor advances any source renderer or its acceptance status.

The left operand is gathered in ordered query shards. Every right operand
is the same batch chunk of the global right operand; those copies are never
gathered. `Q`, `K`, and `M` remain independent. Actual producer equations and
input contracts imply both output shapes and output reconstruction.
-/

namespace TrainVerify.Denote

set_option maxHeartbeats 500000

-- Fresh universally quantified lists keep the induction motive independent
-- of every caller's shapes, reconstruction, and producer equations.
private theorem source_query_matmul_zipWith_copies (sharedY : Tensor) :
    ∀ (xs ys : List Tensor), xs.length = ys.length →
      (∀ y ∈ ys, y = sharedY) →
      List.zipWith fw_matmul xs ys =
        xs.map (fun x => fw_matmul x sharedY) := by
  intro xs
  induction xs with
  | nil =>
      intro ys _ _
      cases ys <;> rfl
  | cons x xs ih =>
      intro ys hlen hcopies
      cases ys with
      | nil =>
          simp only [List.length_cons, List.length_nil] at hlen
          omega
      | cons y ys =>
          have hy : y = sharedY := hcopies y (List.mem_cons_self)
          have htail : ∀ z ∈ ys, z = sharedY := by
            intro z hz
            exact hcopies z (List.mem_cons_of_mem _ hz)
          have hlen' : xs.length = ys.length := Nat.succ.inj hlen
          change fw_matmul x y :: List.zipWith fw_matmul xs ys =
            fw_matmul x sharedY :: xs.map (fun z => fw_matmul z sharedY)
          rw [hy, ih ys hlen' htail]

/-- Actual global matmul and ordered pairwise local matmuls have the required
shapes and reconstruct along the query axis within the selected batch chunk.
The right-hand copies are value-equal to that chunk, not concatenated shards.
Both length guards exclude zip truncation. No output shape or reconstruction
is assumed, and this algebraic contract does not assert DP ownership. -/
theorem source_query_matmul_unit_output_reconstruct
    (D T B H Q K M u : Nat)
    (fullX fullY globalout : Tensor) (xs ys outputs : List Tensor)
    (hD : 0 < D) (hT : 0 < T) (hB : 0 < B) (hH : 0 < H)
    (hQ : 0 < Q) (hK : 0 < K) (hM : 0 < M) (hu : u < D)
    (hfullX : fullX.shape = [B * D, H, Q * T, K])
    (hfullY : fullY.shape = [B * D, H, K, M])
    (hlen : xs.length = T) (hylen : ys.length = T)
    (hxs : ∀ x ∈ xs, x.shape = [B, H, Q, K])
    (hcopies : ∀ y ∈ ys, y = chunkPrimDimN 0 D u fullY)
    (hpre : chunkPrimDimN 0 D u fullX = allGatherPrimDimN 2 T 0 xs)
    (hglobal : globalout = fw_matmul fullX fullY)
    (hlocal : outputs = List.zipWith fw_matmul xs ys) :
    globalout.shape = [B * D, H, Q * T, M] ∧
      (∀ out ∈ outputs, out.shape = [B, H, Q, M]) ∧
      chunkPrimDimN 0 D u globalout = allGatherPrimDimN 2 T 0 outputs := by
  have hchunkY : (chunkPrimDimN 0 D u fullY).shape = [B, H, K, M] := by
    rw [chunkPrimDimN_shape 0 D u fullY _ hfullY hD.ne']
    simp only [List.set, List.getD_cons_zero, Nat.mul_div_cancel B hD]
  have houtputs : outputs =
      xs.map (fun x => fw_matmul x (chunkPrimDimN 0 D u fullY)) :=
    hlocal.trans (source_query_matmul_zipWith_copies
      (chunkPrimDimN 0 D u fullY) xs ys (hlen.trans hylen.symm) hcopies)
  refine ⟨?_, ?_, ?_⟩
  · rw [hglobal]
    exact fw_matmul_rank4_shape fullX fullY (B * D) H (Q * T) K M
      hfullX hfullY
  · intro out hout
    rw [houtputs] at hout
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hout
    exact fw_matmul_rank4_shape x (chunkPrimDimN 0 D u fullY) B H Q K M
      (hxs x hx) hchunkY
  · rw [hglobal]
    rw [fw_matmul_batch_chunk_dim0_rank4 D u B H (Q * T) K M fullX fullY
      hD hB hH (Nat.mul_pos hQ hT) hK hM hu hfullX hfullY]
    rw [hpre, houtputs]
    exact fw_matmul_allGatherPrimDimN_dim2_K_rank4
      xs (chunkPrimDimN 0 D u fullY) T B H Q K M
      hT hQ hK hM hlen hxs hchunkY

#print axioms source_query_matmul_unit_output_reconstruct

end TrainVerify.Denote
