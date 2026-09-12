# Original matmul dV → ReduceScatter checkpoint

The generic original backward collective reader now supports ReduceScatter in addition to AG/AA. It authenticates the current graph against freshly reloaded capture/generated-source authority, ordered peers, fullrefs, backward contexts, effective dimensions, source writers and gradient read points. Additional RS domain guards enforce positive equal peer shapes, divisibility, correct group-local destination index and output shape. No partial valmap is erased or converted into a scaling rule.

Actual PM edges: matmul131/367/603/839 second outputs → RS132/368/604/840. Groups are [0,1] and [2,3]. Each destination receives `chunkPrimDimN dim groupSize localIndex (tensorSum [dV_peer0,dV_peer1])`, not an average and not matmul's first output. dV is an activation gradient, not parameter dW.

Evidence:
- RED at unsupported ReduceScatter in the generic reader; then all four actual nodes accepted.
- Worker covered 21 RS cases and 9 AG/AA positive regressions. A logged targeted run had 29 passes plus one test-setup failure caused by generic `copy.copy` on transient `Cell`; slot-preserving cloning fixed it and both affected cases passed. The initial wider run exceeded the tool's 420-second foreground deadline; no full old AG/AA negative-suite pass is claimed.
- Parent integration focused run: **8 passed, 16 deselected** (four original nodes, contribution composition, dy-valmap negative control, joint-contract and exact CPU witness checks). Receipt `.hermes/backward-kernel/dv-rs-focused.xml`.
- Fresh exact kernel: four `ActualBWDVReduceScatterRead` source reads and four `ActualBWMatmulDVReduceScatter` compositions, using existing exact `ActualBWMatmulRead` producer proofs and the existing general `SourceReduceScatterRead` lemma.
- Stronger joint witness: two actual BW_matmul nodes plus ReduceScatter in ONE successful checked run. Noncontiguous group [0,2] selects world rank2/local index1. Both saved primals remain intact; second-output contribution tables differ; the exact result is `[78,96,342,384]`, shape [1,2,1,2]. Nonzero/nonconstant inputs/results, source group/shape conditions, and no-average result are kernel-proved. The same two-matmul data are checked with float64 autograd and sum-of-chunks versus chunk-of-sum.
- All audited proof dependencies are standard `propext`, `Classical.choice`, `Quot.sound`. Independent static review: `.hermes/backward-kernel/dv-rs-review.json`.

Reproduce from existing trusted captures via `iroha-tasks/trainverify-backward/render_actual_dv_reduce_scatter.py`, then the existing `check_kernel.py` on `SourceReduceScatterRead`, `MatmulDVReduceScatterWitness`, generated source-read module, and composition module. Reuse the capture interpreter and explicit tree-local PYTHONPATH; no recapture or shared rank-cell cache writes.

This remains original same-final-Store reads/composition and local successful-run nonvacuity. It does not establish full-capture success, SM/PM gradient equivalence, NCCL execution refinement, or parameter/WRED closure. Those status flags remain false.
