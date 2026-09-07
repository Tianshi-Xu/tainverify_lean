# Fresh configuration-driven capture on local V100s

## Active dependency baseline

New capture runs use the internally maintained `nnscaler==0.9+internal.1`,
built from `/home/v-zhouziyu/work/nnscaler-internal` at
`6b95728ac9301d06f361791a3981240bb2db15aa`. The capture environment has been
installed from the reviewed internal wheel. `scripts/requirements-capture.txt`
records this selection without imposing a Torch/CUDA matrix; install the internal
distribution before resolving that requirements file. Capture receipts include
the actual imported nnScaler version and path.

The executed checkpoint below is historical evidence from the earlier pinned
source plus its explicitly recorded private fix. Those artifacts are retained,
not relabelled as captures of the new internal baseline.

## Current compiler checkpoint (internal dependency)

The current real TP2/TP4 exports in
`/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/` use the
installed internal dependency above. Fresh captures exist for plan/runtime
1/1, 2/2, 4/4 and 2/4; a separate batch-2 single-model capture supplies the
canonical global-batch reference for the pending two-scale-unit work.

The first real closure failures drove general, kernel-checked identities and
compiler/renderer wiring for sequence/vocabulary-sharded `BW_embedding`, and
sequence/row-reduction/column-sharded `BW_linear` dX, sequence-axis `BW_sum`,
and sequence/head-sharded rank-4→rank-3 `BW_view`. These mathematical identities depend only
on `propext`, `Classical.choice`, and `Quot.sound`. Generated conditional
witnesses additionally retain the existing native metadata-check trust base.
ROW migration also binds initial weight-lineage shapes to the operator's shapes;
a coordinated lineage-shape mismatch was reproduced and is now rejected.

Acceptance remains incremental: focused Python tests, exact generated witnesses,
and changed real graph frames, not repeated full-bundle rebuilds. The ROW
checkpoint has 106 focused tests, five parameterized K=1/2/3/4/5 conditional
witnesses, a joint dX/dW witness, and four exact conditional frames from the
legacy real GPT authority checked. These do **not** establish whole-model
public closure.

The subsequent column/sum checkpoint passed 151 focused tests, five general
column dX witnesses, a general-batch collective dX witness, and four sequence-axis
BW_sum witnesses. Column math and both BW_view flattening math theorems use only
the same three kernel axioms. Ten exact BW_view witnesses cover axes 1/2,
K=1..5 and nontrivial batch sizes; the view-focused integration set passed 73
Python tests. These are bounded conditional proofs, not fresh public closure.
Independent source review found and closed a mixed-column shape-helper migration
omission using a batch-2 exact Lean regression.

The fresh TP2/TP4 shared DAG now reaches the missing `BW_matmul` second-output
contraction-reduction producer upstream of ReduceScatter (TP2 SM 104 / PM
355–356). The inputs are query-axis shards; legacy backward matmul rules still
assume four ranks and fixed dimensions. This is the next active proof/compiler
capability gap, not a newly established upstream numerical bug.

For plan2/runtime4, the expanded capture contains both scale units and gradient
reducers. Export still rejects this case: raw integer tensor IDs alias distinct
DP-local inputs, collectives require group-local cardinality/rank, and the
canonical reference must represent the global batch. Removing `num_dp` guards
alone would be unsound. Source findings and exact receipts are in the audit
root's `group-scope/`, `row-real-frames/`, and `row-shape-witnesses/` directories.
B200/FlashAttention/YOCO hardware acceptance remains separate and pending.

## Historical executed checkpoint (2026-09-06)

The dedicated environment is `~/.venvs/trainverify-capture` (Python 3.11,
Torch 2.6.0+cu124, nnScaler 0.9 built from the pinned source). Four Tesla
V100-DGXS-32GB devices were detected and used. The system/Hermes environment was
not changed. No FlashAttention or shape-only execution substitutes were installed.

`scripts/gpt_capture.py` accepts JSON model parameters, native `ComputeConfig`,
policy, seed and batch size. It runs a genuine CUDA forward/backward, invokes
native nnScaler tracing/partition/codegen and observes the real `ModuleCodeGen`
constructor without changing its result. Dill preserves annotation closures.
The sidecar gives explicit World dimensions; runtime and plan sizes are separate.
Only builtin TP/DP policies are admitted because this entry does not know PP stage
placement. This is the repository's deterministic `genmodel.model.gpt.GPT`, with
a scalar sum objective and ordinary attention—not a canonical GPT-2 training
objective and not llm-train YOCO.

Executed model configuration: hidden=64, layers=2, heads=4, FFN=256, vocabulary=256,
sequence=16, batch=1, seed=7. Native `tp` policy uses seed=7. Four separate real
captures succeeded: `(plan,runtime)=(1,1),(2,2),(4,4),(2,4)`.

## A real upstream runtime bug, and its local fix

The original capture generated this invalid runtime call:

```python
torch.softmax(x, dim=-1, _stacklevel=3, dtype=None)
```

`_stacklevel` belongs to `torch.nn.functional.softmax`, not `torch.softmax`.
Actual two-rank generated training failed with `TypeError` on both ranks.
A minimal genuine `parallelize()` reproduction also failed on:

- pinned nnScaler `d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf`;
- public `microsoft/nnscaler` HEAD fetched at
  `1585c15d4ca99e23a410c90f9bad2664125524d4`.

This is an executable code-generation/API bug, not a demonstrated wrong-number
parallel algorithm. The fix in the private nnScaler clone omits `_stacklevel`
only for `signature == 'torch.softmax'`, retaining the functional-wrapper branch.
The minimal generated primitive then matched the source exactly; the functional
softmax positive control also passed. No upstream push or issue was made.

Original captures and failure logs were preserved. Fresh captures from the patched
private source have the suffix `-softmax-fixed`; do not call them unmodified-pin
captures. The installed capture environment currently contains this private fix.

## Actual generated distributed training

Generated TP2 and TP4 code, and two TP2 scale units on four GPUs, ran forward,
backward and gradient reducers. Every rank compared its output and all 25 local
parameter-gradient shards against the canonical full model:

| plan/runtime | ranks checked | largest absolute gradient error |
|---|---:|---:|
| 2/2 | 2 | 1.1444091796875e-5 |
| 4/4 | 4 | 7.62939453125e-6 |
| 2/4 | 4 | 2.288818359375e-5 |

Output tolerances: rtol=2e-5, atol=2e-4. Gradient tolerances: rtol=2e-4, atol=2e-4.
The two-scale-unit check uses distinct token IDs per unit. The reference sums
parameter gradients over the two unit samples, matching the generated reducers'
explicit `reduce_op='sum'`. A preliminary per-sample-only reference was wrong
for that reduction contract; it is not a second upstream bug.

## Translation and proof boundary

Real captures exposed and drove fixes for three TrainVerify translation defects:

1. collective normalization invented rank 0 and chose the last writer before
   emitted collective deduplication; retain observed rank candidates and select
   the surviving writer from the actual emitted schedule;
2. both directions of the fused AllGather/ReduceScatter classes were labelled
   ReduceScatter; now map each forward/backward branch to the actual runtime op;
3. ReduceScatter was omitted from cross-rank input fusion; it now receives the
   real inputs from every rank instead of one local tensor.

The original fail-closed shape/ownership checks were not weakened. Fresh TP2 and
TP4 exports include all four adapter primitive families and pass the strict
whole-model loader and shared proof planning:

| plan | output targets | SM/PM nodes | communication records | shared proof steps |
|---|---:|---:|---:|---:|
| 2 | 26 | 124 / 425 | 159 | 669 |
| 4 | 26 | 124 / 823 | 307 | 1147 |

Both planners report zero diagnostics. This is **not relation/public closure**:
TP2 stops at target 3's missing BW-reduction pre-fact; TP4 stops at the
BW-embedding sequence theorem's unsupported shape domain. The 2/4 capture exists
and runs numerically, but graph export still rejects `num_dp != 1` because exact
subgroup scope is not implemented.

Exact generated graph declaration modules compiled in Lean. The legacy unsplit
`GeneratedData.lean` also contains `prove_goal_* := by sorry` templates; its
successful elaboration is **not** a proof receipt and no fresh public theorem is
claimed. No canonical Whole source/cache was overwritten or published.

Focused verification: **93 tests passed in 8.69 s**, including a real CUDA capture
CLI test and the installed-nnScaler direction/fusion regressions. Independent
review confirmed the translation changes; its capture-policy finding was fixed
and the bounded closure review passed. An isolated removal of the policy gate
actually compiled PP and wrote a false TP World; the healthy entry rejected the
same valid PP configuration before creating output. That deliberately invalid
artifact remains only under the external `policy-mutant/` audit directory.

## YOCO limitation

The unchanged pinned llm-train import was actually attempted and rejected
`torch._dynamo.config.recompile_limit` on Torch 2.6. Separately, its mandatory
FlashAttention-2/BF16 model path is not a V100 runtime path: the inspected
FlashAttention 2.7.4.post1 source explicitly requires compute capability >=8,
while these V100s are 7.0. Registered-op tracing executes the real kernels; CPU
tracing alone does not remove that requirement. The GPT evidence above does not
establish a fresh YOCO-MoE A0.4B or YOCO-3B capture.

## Reproduction artifacts

All data and logs are under `~/trainverify-audits/fresh-capture/`:

- `config-p*-r*.json`, original `p*-r*/capture.pkl` and patched `*-softmax-fixed/`;
- `repro_softmax.py`, `repro_functional_softmax.py`, `nnscaler-softmax.patch`;
- `softmax-pinned.log`, `softmax-public.log`, original two-rank runtime failure;
- `distributed_run.py`, `runtime-*-fixed.log`, `runtime-p2-r4-distinct.log`,
  and exact per-rank `runtime-rank*.json` results;
- `checked-p2/FreshGPT/`, `checked-p4/FreshGPT/` generated declarations;
- `check_model.py`, `model-p2.log`, `model-p4.log` with actual proof blockers.

From the repository root:

```bash
PY=~/.venvs/trainverify-capture/bin/python
OMP_NUM_THREADS=4 "$PY" -m scripts.gpt_capture \
  --config ~/trainverify-audits/fresh-capture/config-p2-r4.json \
  --out /absolute/new/nonexistent/capture-directory
```

The command creates a real capture; it does not certify that a public Lean proof
or a production AutoDist plan has completed.
