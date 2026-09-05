# General parallel-configuration status

## CP2 entry compiler closure

The shared ordinary-to-zigzag entry now accepts homogeneous FW_maybe_shuffle or
BW_maybe_unshuffle triples, through the same FaithfulShuffleCertificate and
singleton/ordinary-RMSNorm compound renderer. BW uses its actual distributed
writer equality before the existing BW-unshuffle/FW-shuffle semantic equality.
Mixed-op triples, CP>2 and hybrid BW attention remain outside this slice.
BW requires explicit ordered buddy groups; the pre-existing FW legacy path is
unchanged. Certificate, shape, metadata-region, public packed-cu and live-state
checks remain tied to the actual nodes.

Four exact-source audits use independent synthetic graph declarations matching
FW/BW nodes and ordered buddies: singleton and RMSNorm compound, both directions
into zigzag. All four compile; native-decision axiom counts are respectively
42/59 (FW singleton/compound) and 51/68 (BW singleton/compound), with no other
nonstandard axioms. These callers retain the existing native_decide trust base;
they are not kernel3-only. Reversed graph buddies and an overwritten live frame
fact are independently rejected by Lean. This is conditional segment closure,
not a new real-model backward authority or publication-completeness claim.
The frozen final focused gate passes 73 tests. All three whole-model canonical
bundles regenerate byte-identically; no publication artifacts were updated.

## Ordered-K singleton entry compiler

The shared compiler now exposes a retained `zigzag_k` boundary for homogeneous
`FW_maybe_shuffle` or `BW_maybe_unshuffle` singleton entry graphs with positive
K (the existing CP2 route is preserved). Typed certificates bind ordered graph
writers, source bindings, explicit replica groups, shapes, and packed metadata
provenance. The initial domain uses positive tensor extents and two-element
(single-sequence) metadata; packed multi-sequence inputs are not yet admitted.
The boundary is shared across target projections, not an ordinary public gather
terminal, and the public extractor rejects that substitution.

Parent Lean checks cover FW/BW CP3 inhabited input/output witnesses, K1/K5
conditional entry certificates, and CP3 graphs whose node order differs from
semantic rank order. All eight positive sources compile with the existing
generated native-decision baseline and no other nonstandard axioms. Wrong graph
buddy order, an overwritten retained fact, and FW/BW in-place source overwrites
are rejected by Lean. The latter currently reach rendering but cannot pass the
kernel gate; cross-buddy source overwrite is rejected by dependency planning.
The parent focused gate passes 125 tests; eight additional coordinated-metadata
and cross-buddy negatives also pass. Independent base and delta reviews passed.
All three canonical model bundles remain byte-identical; no publication output
was updated.

The ordinary `FW_contiguous` prefix now composes with FW/BW K-entry through the
same shared DAG: the prefix target uses one certificate and the entry target
reuses it together with the entry certificate. The prefix post is the exact
internal entry pre-fact, not a new external assumption. The shared chain contains
two closed singleton segments. Initial contiguous inputs require exact InitGoal
binding plus fresh graph-producer authentication; no intermediate init shortcut
is used. Only the K-entry normalization path enables this initial-source extension.

Parent checks pass 116 focused tests and 73 CP2/dispatch regressions. The two
new producer/dimension guards each fail their targeted tests when disabled in
memory. Six exact Lean sources compile: FW/BW CP3 composed inhabited witnesses,
K5 conditional compositions, and CP3 reordered-entry conditional compositions.
All retain the generated native-decision baseline with no other nonstandard
axioms. Corrupting a prefix producer or skipping its state transition is rejected
by Lean.

Two boundaries remain explicit: K1 prefix is not yet supported by the existing
contiguous backend (K1 singleton entry is unchanged); permuting contiguous writer
node order away from semantic rank order still fails in the contiguous renderer.
Reordered-entry acceptance does not imply reordered-prefix acceptance. No
ring/attention or compound expansion is inferred from this two-segment closure.

## Ordered-K shared relation foundation

`RelationCompiler.ZigzagKRel` and `RelationFact.zigzagK` retain the canonical
full tensor, an ordered list of actual collective outputs, and the metadata
tensor. The existential ordinary sources satisfy `ShardedRel` on dimension 0;
the same K binds their count, the output count, and `ZigzagCuWF`.
`ZigzagKRel.of_sharded` establishes the exact list of shuffle values, not an
ordinary gather equality of zigzag outputs. Frame transport includes every PM
rank TID and the metadata TID.

`ZigzagKRelationWitness.lean` supplies an inhabited CP3 boundary with full shape
`[12,2]`, shard shape `[4,2]`, and packed metadata `[0,12]`. It proves the token
positions `[[0,1,10,11],[2,3,8,9],[4,5,6,7]]`, distinct actual values across all
ranks, and the complete frame dependencies. Parent integration builds both
modules; the audited declarations use at most kernel3. Focused downstream
K-rank modules and the four existing CP2 entry proofs also compile against the
new relation module. Independent exact-commit semantic review passed.

This is the shared semantic foundation for the singleton entry compiler above.
Existing CP2 interfaces are unchanged; general prefix composition and
ring-attention obligations beyond the supported two-segment boundary remain
separate.

## CP frontier: arbitrary-K single-sequence inverse

`KRankZigzagSingle.lean` proves the value-level left inverse
`unshuffle(shuffle(xs)) = xs[rank]` for any positive CP count K, positive
half-shard width d, exactly K ordered inputs, and homogeneous shape
`(2*d) :: tail`. It uses the existing faithful collective/index functions and
pinned nnScaler metadata equations. The tail can have zero volume.

`KRankZigzagSingleWitness.lean` checks K=1/3/5 callers and distinguishes CP3
rank-order gather `[0,5,1,4,2,3]` from canonical order. Both modules build;
the two core and six witness declarations have kernel3-or-less axioms.

This is a mathematical prerequisite, **not CP/ring closure**. Packed
multi-sequence inverse, general process-group ownership composition, and ring
attention remain separate obligations. The K singleton entry compiler above
uses its own explicit graph authority checks; the inverse alone does not widen
compiler acceptance. The synthetic BW_maybe_unshuffle substitution on YOCO
topology supplied the RED reproduction for the CP2 entry slice above; it is not
a new captured backward model graph.

## Scope split

Parallel support is not one boolean:

- **TP:** ordinary linear/matmul/embedding/elementwise and collective relations;
- **CP/ring:** ordered token ownership, shuffle/unshuffle, packed sequence metadata, ring attention;
- **EP/MoE:** expert ownership, routing, all-to-all and full-expert boundaries;
- **DP:** reduction groups and optimizer-gradient reconstruction;
- **PP:** stage boundaries and composition authority.

A dynamic TP collective does not imply arbitrary CP/EP/DP/PP combinations.

## Existing evidence

The checked GPT-2 authority is already SM=1 / PM=4. Its ordinary forward path uses dynamic-K relation families. Therefore the previous statement “the project only supports TP=2” was false.

The first pure-TP fixed-rank boundary found on that authoritative ancestry was GPT Goal 107 `BW_sum` at compiler segment `segment_000188`. The previous matcher required exactly ranks `(0,1,2,3)`, the renderer required `k == 4`, and the Lean backend was a concrete four-shard theorem.

## Completed vertical slice: dynamic-K `BW_sum`

The boundary is now identified by:

```text
bw-sum-scalar-broadcast-dim2-k-rank
```

The compiler now derives `K` from the exact ordered PM writer list and accepts `K >= 2`, including non-power-of-two `K=3`. It validates:

- PM writer ranks are exactly `0..K-1`;
- every writer is binary `BW_sum`;
- the scalar gradient is one shared, pure-init singleton authority;
- all PM output shard shapes agree;
- SM/PM outputs form an exact equal-shard dim-2 reconstruction.

The renderer emits an exact `1+K` writer frame, dynamic `allGatherPrimDimN 2 K`, and no fixed rank-four backend identity.

The kernel theorem is:

```lean
TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim2_rank3
```

It is list-based and proves arbitrary nonempty ordered `K`, for homogeneous rank-3 shards `[d0,d1,d2]` with positive gathered width `d2`. It does not assume a power of two or GPT's concrete `[1,8,32]` shard.

## Verification receipts

- Python matcher/renderer controls: K=2, K=3 and K=4, plus fail-closed mutations for rank, rank-3 theorem domain, input/output shape agreement, zero extents, parameters, and scalar reduction authority.
- Focused Python gate: `58 passed` across BW_sum, compound dispatch, registry and real GPT Goal 107 checks.
- Full influence gate: `510 passed in 3345.85s (0:55:45)`.
- Generic Lean theorem: `lake build denote.KRankBWSum` succeeded and materialized `denote/KRankBWSum.olean`.
- Exact renderer replay over real GPT Goal 107 segment `segment_000188` compiled successfully as a staged one-segment Lean module.
- The singleton and interleaved `FW_sum`/`BW_sum` compound dispatch paths both use the same dynamic-K theorem identity; the old rank-four backend is removed rather than retained as fallback.
- All canonical formal whole-model generations remained byte-identical:
  - GPT-2: 97 files, 1,968,291 bytes;
  - YOCO-MoE 0.4B: 2,832 files, 55,891,040 bytes;
  - YOCO-3B: 1,363 files, 37,377,383 bytes.

## Completed vertical slice: dynamic-K `BW_linear` dX

Goal 107 `segment_000189` now uses `bw-linear-dx-row-reduction-k-rank` and
`bw_linear_dx_allGatherPrimDimN_dim2_rank3`. K is arbitrary and nonempty, but
this theorem deliberately retains local gradient `[1,8,32]` and weight
`[32,32]`. Other dX layouts remain on their checked legacy rules.
The actual Goal 107 segment source was compiled and axiom-audited separately;
canonical GPT targets `(2,3,48)` do **not** cover Goal 107.

## Completed vertical slice: dynamic-K `BW_layernorm` dX

Rule: `bw-layernorm-dx-dim1-k-rank`.
Theorem: `bw_layernorm_dx_allGatherPrimDimN_dim1_3d` in
`denote/KRankBWLayernorm.lean`.

The ordered gradient/activation lists have length K. Local shapes are `[b,s,d]`,
full shapes `[b,s*K,d]`, with positive K,b,s,d and shared singleton gamma/beta.
The proof transports the actual row-local backward values, including both
row sums, through the rank/local-index gather map. It does not duplicate a
fixed-rank theorem. Width `d=1` preserves the parser's singleton **reduction**
parameter authority; other widths use singleton sharded authority.

Matcher, typed payload, transition digest, exact writer footprint, singleton
renderer, compound dX caller, and import selection use the new identity.
The triple renderer still requires K=4 and `[1,2,32]` because dgamma/dbeta remain
on their checked rank-four reduction theorems; this is not full backward
LayerNorm generalization.

Incremental evidence for this slice:

- `101 passed in 13.59s`: new controls, actual GPT Goal 107 integration,
  BW_sum/dX regression, registry/compound/import policy, and incremental selector.
- New theorem and committed K=3 / `[2,3,7]` generated witness built via Lake.
- Extra exact-source witnesses compiled for K=5 / `[2,3,7]`, K=3 / `[2,3,1]`,
  K=1 / `[1,1,1]`, and the retained rank-four triple path.
- All nine affected Goal 107 segment sources compiled in 54.46s:
  `192,201,232,242,278,290,325,336,364` (each `segment_` suffix is zero-padded).
- General theorem axiom footprint: `propext`, `Classical.choice`, `Quot.sound`.
  Generated graph certificates additionally use explicit `native_decide` axioms;
  no `sorryAx` or unexpected axiom was observed.
- GPT canonical bundle regenerated byte-identically: 97 files / 1,968,291 bytes.
  This checks the selected public targets only, not backward Goal 107.

These are focused research receipts, not a new full-suite/three-model publication.

## Completed vertical slice: dynamic-K / variadic `BW_multiref` sum

`bw-multiref-sum-sharded-k-rank` now uses `tensorSum_allGather_dim_K`
from `denote.KRankBWMultiref`, shared by singleton and WRED compound renderers.
The value theorem supports any positive K and nonempty ordered operand list,
with homogeneous shard shapes. It preserves the scalar fold's order and
multiplicity; it does not expand one theorem per K or per arity.

The matcher currently accepts positive rank-3 shards along dim 1 or dim 2,
with K >= 2 and exact rank order, input shapes, writer parameters and projection.
K=1 remains ambiguous at this shape-inferred frontier, so it fails closed
rather than guessing an ownership axis. The theorem itself has no K=2 lower bound.
Typed certificates now bind full/shard shapes; selectors authenticate the exact
payload, and production compound imports include the new theorem module.

A real repeated-operand boundary `sum(a,a)` exposed two separate failures:
transition dependency sets deduplicate facts while operand payloads must not;
and sequential Lean rewrites of the same SM value fail on the second rewrite.
Selectors now match the dependency set without changing the operand payload,
and the shared value proof builds positional list congruence before rewriting.

Incremental evidence:

- `137 passed in 16.44s`, including matcher/metadata/digest mutations, actual
  transition-builder repeated-input regression, production WRED import header,
  existing LayerNorm/BW_sum and actual GPT Goal 107 integration.
- Lake built the new theorem and committed K=3 / arity=5 generated witness.
- Exact-source Lean and axiom checks passed for K=5, arity=1, shard width=1,
  repeated operands and the WRED compound path.
- All 12 real Goal 107 affected segments passed fresh exact-source Lean and
  axiom audit in 61.89s: `202,231,233,243,277,279,292,324,327,338,363,366`.
- General theorem has only `propext`, `Classical.choice`, `Quot.sound`;
  generated witnesses additionally carry the established `native_decide` items.
- Canonical GPT bundle remains byte-identical (97 files / 1,968,291 bytes).
- Independent closure review passed after the repeated-input fix.

These are conditional segment and focused regression receipts, not a new
three-model whole-publication run.

## Completed vertical slice: dynamic-K weight-column `BW_linear dX`

The 32-wide column case now uses `bw-linear-dx-column-sharded-k-rank` and
`TrainVerify.Denote.bw_linear_dx_weight_allGatherPrimDimN_dim1_rank3`
from module `denote.KRankBWLinearDxColumn`. The theorem uses
ordered `zipWith`, arbitrary positive K, joined gradient `[1,8,32]`, local
activation `[1,8,32]` and weight `[32,32]`, and reconstructed feature width `32*K`.
Its conclusion is value-level dX gather, not reduction or a shape-only identity.
The old `g213` theorem dispatch is removed. The dynamic theorem is shared with
the dX/dW dual renderer; dW itself deliberately retains its K4 boundary.

Validation:
- K1/2/3/4/5 matcher, typed/digest/shape/rank/parameter negative cases,
  production dual header and ordinary-Python golden comparison.
- **167 focused tests passed (16.38 s)**.
- Fresh leaf/witness Lake build; exact generated K1, K3, K5 and K4 dual Lean
  executions; theorem/segment axiom audits with no forbidden axioms.
- Actual GPT Goal107 affected segments `000195` and `000236` compiled together
  from current rendered bytes (32.88 s), both axiom reports checked.
- Canonical GPT 97-file comparison remains byte-identical; that is separate from
  the noncanonical Goal107 execution above. No new full-suite/publication claim.
- Independent source review PASS; noncanonical artifacts are outside the repo at
  `/home/v-zhouziyu/trainverify-audits/parallel-linear-column/`.

## Completed vertical slice: positive-width column `BW_linear dX`

The same list-ABI theorem and certificate family now cover positive output width
`O`, local feature width `I`, and ordered rank count `K`. Batch and sequence remain
`1` and `8`: gradient `[1,8,O]`, local activation/dX `[1,8,I]`, local weight `[O,I]`,
full activation/dX `[1,8,I*K]`, full weight `[O,I*K]`.

The singleton, optional view, dual, and mixed collective callers share the same
generic dX theorem. The old `g245`/`g276` dX registry and dispatch are removed.
Independent dW remains K4 and only its checked `(O,I)` domains `(32,32)`, `(128,8)`,
`(32,8)` are accepted. The mixed AllGather/view/AllToAll path retains K4, exact
collective descriptors, and its optional dW retains `(32,8)`.

Validation:
- **170 focused tests passed (28.72 s)**, including zero/negative widths,
  non-power-of-two ranks, unequal widths, recomputed-digest role/axis/footprint
  mutations, real GPT107 view/collective descriptor mutations, and dW theorem binding.
- Fresh generic theorem and committed witness Lake builds passed.
- Exact generated Lean witnesses passed for `(K,O,I)=(3,7,5),(1,1,1),(5,3,1)`,
  the retained 32-wide K3 case, and all three checked K4 dW dual domains.
  Additional singleton+view and dual+view witnesses passed Lean/axiom checks.
- All ten affected real Goal107 segments passed exact-source Lean/axiom audit
  in 53.22 s: `195,199,205,228,229,236,240,246,311,320` (zero-padded segment IDs).
- The generic theorem retains the kernel axiom triple; generated graph proofs
  retain their explicit `native_decide` trust items, with no forbidden axioms.
- Review reproductions exposed pre-existing dW role-set and collective payload
  validation gaps; ordered role equality and descriptor/shape/footprint checks
  now reject those mutations before rendering. Joined-view shapes and writer
  step IDs are also bound to the exact materialized facts and transition.
- Current re-emission is byte-identical to the previously kernel-checked width
  and ten-real-segment artifacts; the canonical GPT 97-file snapshot is unchanged.
- Audit sources and receipts: `/home/v-zhouziyu/trainverify-audits/parallel-linear-widths/`.

These are conditional segment checks, not a new three-model public closure.

## Remaining ordinary TP and other axes

Other fixed-layout/fixed-rank BW_linear families (including independent dW),
BW_layernorm parameter reductions, and column dX batch/sequence extents still
require semantic migrations. The next adjacent family is input-column dW;
its value theorem and authority must be generalized independently from dX.
Then proceed to CP/ring, EP/MoE, DP, PP and only compose independently closed
axes. Arbitrary `DP×TP×PP×CP×EP` configuration support is not implemented.

YOCO's two-rank zigzag/ring rules are a separate CP/EP topology problem and are not evidence that ordinary TP remains limited to two ranks.


## Input-column dW dynamic K / positive O-I slice

- `KRankBWLinearDwColumn.lean` proves input-column dW for arbitrary positive K/O/I at batch1/sequence8. It gathers dW along weight dim1 from activation dim2 shards; it is not a reduction theorem. The three former g154/g211/g214 cases are specializations of this one statement.
- The existing dW certificate now names `bw-linear-dw-input-column-sharded-k-rank`. Matching binds the complete ordered activation and weight tuples to exact dim2/dim1 authority, including K1 axis metadata, and preserves the joined gradient's SM/PM frontier pair during normalization.
- Existing column dX+dW dual and dual+view callers use the list theorem for arbitrary positive K/O/I. Their mathematical statement is not restricted to the former three shape pairs. The mixed collective caller retains K4, axes2→1, and its existing optional-dW shape boundary. No standalone dW closed backend or broader collective support is claimed by this slice.
- Fresh exact-source Lean and axiom checks passed for K3/O7/I5, K1/unit widths, K5/I1, all three legacy width pairs, dual+view, the generic theorem, and the 10 reachable GPT107 column segments. GPT150/214 relation tests cover the new dW matcher; these are not claimed as new standalone end-to-end Lean closures.
- Incremental selection includes both column derivative modules/witnesses, their focused tests, and relevant dW family regressions. Publication/full-suite gates remain separate. Focused gate: **200 passed (52.50 s)**; module and committed witness `lake build` passed. The commute theorem has kernel3 axioms; generated callers use the existing kernel-plus-per-caller-native_decide baseline, not a kernel3-only claim.


## Standalone input-column dW closed backend

- The existing dynamic dW identity now has a registered singleton backend. It shares the column single-output frame/writer machinery with dX, selecting the actual `.2` writer and dim1 output gather; it does not introduce a fictitious dX fact or copy the complete frame proof template.
- The dW certificate remains bound to ordered gradient/activation/weight roles, exact SM/PM output-projection IDs, ranks, shape/axis records, digest, and pre/post-state coverage. Compound grammar and collective domains are unchanged.
- **210 focused tests passed (50.22 s)**. Fresh Lean and existing-baseline axiom checks passed for standalone K1/K3/K5 and actual GPT150 `segment_000313` / GPT214 `segment_000236`. Generated callers retain permitted native_decide axioms; no kernel3-only claim is made for them.
- Previously checked dX/dual sources re-emit unchanged. These are exact-segment checks, not a new all-target public-closure claim.
