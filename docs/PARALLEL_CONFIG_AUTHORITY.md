# Configuration-driven parallel authority

## Status and acceptance boundary

The production `emit2 --whole-model` path now accepts an explicit parallel
configuration, evaluates the pinned llm-train topology helpers, attaches one
checked topology to `ModelAuthorityIR`, propagates it to target projections, and
uses the existing shared proof/relation DAG and closed-bundle compiler. This is
**configuration plumbing plus fail-closed graph binding**, not completion of the
general parallel verifier.

A topology record is source-derived, not an observed GPU capture. Binding it to
an existing GraphDecl does not establish that the graph was captured using that
configuration. The optional record is absent on legacy paths; it is never
inferred from rank count or tensor shapes.

## Source and representation

- llm-train: `9a1be1d5fd1c063d80be82797692cdc7d23cfbef`,
  `llm/parallelism.py` and `llm/nnscaler_train.py`.
- Companion nnScaler constraints: `d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf`,
  `nnscaler/parallel.py` and `nnscaler/autodist/autodist_config.py`.
- `trainverify/parallel_topology.py` provides `ParallelConfig`, `ParallelGroup`,
  `ParallelTopology`, `derive_topology`, structural validation and JSON I/O.
- `derive_topology` executes the explicitly trusted repository's immutable
  `revision:llm/parallelism.py`; it is not a sandbox. Revision syntax is checked
  before lookup. Deserializing JSON checks structure, **not source provenance**.
- Resolved CP/EP, contiguous scale-unit/CP/EP groups, strided data lanes, ordered
  members and group-local coordinates are explicit. Singleton semantic groups
  remain present even when eager runtime creation omits them. Different roles
  with equal physical membership are not collapsed.
- The independent validator reconstructs per-rank coordinates rather than
  calling the topology emitter. Same-count coordinated role/member/offset
  mutations are rejected.
- CP and EP are nested under this source, not independent Cartesian axes.
  Auto zero sentinels resolve through the actual source helper.
- ZeRO size compatibility is checked; optimizer/reducer membership is not
  invented. Pipeline count is not stage placement. MoE fixed partitions
  (`EP < plan`) are rejected with pipeline exploration, following the actual
  downstream nnScaler constraint, even though the llm-only helper accepts them.

## Shared graph boundary

`bridge_emitter/parallel_authority.py` distinguishes graph-local ranks from
runtime ranks using an explicit `plan` or `runtime` scope. A plan graph maps to
one complete ordered scale unit. The record is shared, not copied into separate
per-target authority architectures.

For fixed source custom operators, CP/EP roles are checked against actual
writers, explicit ordered replica groups, group-local shuffle parameters and
all target graph/shape environments. A logical replica group is used as a
communication group **only if** its ordered members equal the source group.
No automatic subdivision, reordering or dimension-based ownership inference is
allowed. Correct subgroup metadata that the current full-graph backend cannot
consume reports `unsupported-group-local-proof`, separately from contradictory
or absent group metadata.

Generic adapter collectives currently report `missing-collective-role`. Their
communication membership must come from the adapter/capture, not from assuming
that every collective is CP, EP or the full plan.

The model authority digest includes the topology and rank map. Relation DAG
construction rechecks the actual model and compares the supplied proof DAG's
existing authority digest; changing configuration/scope cannot silently reuse
an old DAG. A topology comment in generated `Main.lean` records the checked
scope, but is explicitly **not a Lean topology theorem**. Existing public and
kernel/axiom/publication gates remain in force. Configuration-bound CLI runs
require explicit noncanonical output, preserving the existing Whole snapshots.

## Production invocation

Example configuration for checking compatibility with an existing two-rank
YOCO authority (this does not recapture the model):

```json
{"plan_ngpus":2,"runtime_ngpus":2,"cp_size":2,"ep_size":2,
 "dp_sharded":false,"moe_expert_num":8,"zero_group_size":2,"pipeline_stages":1}
```

From the repository root:

```bash
BRIDGE_DENOTE_DIR=denote/yoco_goals \
BRIDGE_GEN_DIR=trainverify/denote \
BRIDGE_GEN_FILE=GeneratedYOCOMoE.lean \
BRIDGE_MOD_PREFIX=denote.yoco_goals \
python trainverify/bridge_emitter/emit2.py \
  --whole-model --targets 1-5 --model-id yoco-a04b \
  --namespace ParallelYOCOProbe --module-prefix ParallelYOCOProbe \
  --aggregate-theorem all_outputs --out /tmp/ParallelYOCOProbe --dry-run \
  --parallel-config /path/to/config.json \
  --parallel-upstream-root /path/to/trusted/llm-train \
  --parallel-revision 9a1be1d5fd1c063d80be82797692cdc7d23cfbef \
  --parallel-graph-scope plan
```

This command was exercised against the actual saved YOCO authority. Its first
blocker is `missing-collective-role: AllToAllPrim rank 0`. All completion flags
remain false. It is a capture/translation authority gap, not a detected
llm-train semantic bug and not evidence that the configuration is illegal.

## Verified checkpoint

- 241 focused Python tests plus 116 subtests passed with the explicit pinned
  source enabled; six additional selected model-authority/CLI regressions passed.
  No full model campaign was rerun.
- A real source-derived `(plan=3,runtime=6,CP=3,EP=1)` topology, mapped to scale
  unit 1, was fed through the production builder with the **existing synthetic
  CP3 graph/public fixture**. The graph fixture replaces only the loader; source
  helper execution, graph binding, shared planners, rendering and Lean are real.
  This is a plan-local graph proof, not a multi-unit training proof.
- Facts, states, three segments, chain, public target and complete `Main` compiled.
  The public aggregate has 250 axioms under the existing kernel3 plus generated
  native-decision baseline. It is not kernel3-only.
- Exact Lean checking exposed an existing single-target conjunction-rendering
  bug (`refine ⟨?_⟩` against a universally quantified Prop). The generic singleton
  case now directly uses its one closed theorem; public statement is unchanged.
  Only `Main` and the axiom caller needed recompilation after the fix.
- Independent production review and a bounded delta review passed (static only).
- Separately, an executed pinned-source differential checked 975 legal topology
  configurations, 36,486 rank cases and 733,694 assertions, including actual AST
  helper/emitter execution and explicitly symbolic partition doubles. No
  reachable valid-configuration upstream bug was confirmed. This is not a GPU
  run, full graph capture or proof of absence of bugs. Current private llm-train
  upstream could not be authenticated; no finding is claimed as a new current
  upstream bug.

Local receipts: `~/trainverify-audits/parallel-topology/` and
`~/trainverify-audits/parallel-topology-upstream/`.

## Next actual boundary

Follow adapter `ranks` and collective grouping from
`Verdict/nnscaler_backend/build_graph.py` into `Verdict/graph_to_lean.py`.
The latter currently emits replica groups only for selected custom operators,
not primitive adapter communication. Preserve explicit communication authority
separately from logical-replica identity, and bind token/expert ownership before
opening subgroup proof backends. Do not bypass the new gate by assigning every
`AllToAllPrim` a full-plan role.
