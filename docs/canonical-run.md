# Canonical saved-capture observer

`python -m trainverify.canonical_run run` calls the actual
`Verdict.graph_to_lean.main`, including `runtime_world.render →
runtime_input_feed.bind → runtime_initial_relations.attach →
runtime_world.publish`. It does not use frontier replay's early-exit hook or
replace any renderer. Hooks call the original with unchanged arguments and
return its exact result; observation errors are deferred until attachment and
the compiler finish. Repeated nested predecessor calls are allowed.

This checks generation/publication bookkeeping, not Lean kernel acceptance,
whole-model/public completion, execution inhabitation or Torch refinement.
`passed: true` requires the exact `RuntimeLineageBlocked` class/message below,
full source readback and all configured observations. `public_complete`,
`torch_refinement` and `kernel_checked` remain false. Other exceptions,
missing publication, public `GeneratedData.lean`, changed inputs/source, partial
stage observations or a rejected budget never pass.

```text
runtime-world-render/public-adapter: world definitions rendered; scoped dependent chain/input adapter/DP mathematics unavailable; values unproved
```

## Explicit trust roots

Use absolute paths. All generated output must be outside the source root in a
fresh run directory. Use `PYTHONDONTWRITEBYTECODE=1`, with only the approved
source root and its `Verdict` directory on `PYTHONPATH`. No Git worktree is
created and `.git` is not required.

The operator-approved source manifest has exactly these fields:

```json
{
  "version": 1,
  "root": "/approved/sealed-source",
  "baseline_commit": "<40 lowercase hex digits>",
  "files": {"Verdict/graph_to_lean.py": "<sha256 of this file>"},
  "symlinks": {"docs/internal-link": "../internal-target"}
}
```

`files` must cover **every regular file**, not just Python/runtime files.
`symlinks` must cover every link by its original target spelling; only internal
file links are allowed. There are no cache or untracked-file exclusions.
Missing, changed and extra files fail. The illustration is not a complete
manifest. `tree_identity(root)` produces the two inventory fields; the parent
must independently approve baseline provenance and the complete change set
before freezing its digest. A baseline label plus freshly measured bytes does
not prove Git ancestry. Loaded local namespace packages, bare Verdict imports,
backend packages and source files are checked against the same approved root.

`--config` uses the existing `artifact_tools.Configuration` layout, including
explicit relocations and pinned binding sets. `--recipe` accepts the existing
frontier-replay recipe, reusing only its version, pins, seed, batch authority and
rank-code directory. Its target/ancestors do **not** select canonical stages.
Original capture pickle/JSON pairs, seed/batch and the complete rank `.py`
inventory must be pinned. The saved SM/PM run directories are inventoried
before/after the run as additional drift evidence, not independently accepted
parameter authority: the real seed/input binder still authenticates them.

The original seed bytes are never edited. `runtime-seed.json` is an explicit,
hash-bound derived copy of its four paths after layout resolution. Exact-file
relocations must agree with directory lookups used by the compiler; do not use
one to disguise a missing capture pair. This is not a sandbox for hostile
pickle inputs, same-UID concurrent mutation, or untrusted toolchains.

`--stages` is independently supplied and pinned:

```json
{
  "version": 1,
  "stages": [
    {"module": "Verdict.runtime_frontier_middle_exchange_values", "receipt_key": "frontier_middle_exchange_values"},
    {"module": "Verdict.runtime_frontier_score_matmul_values", "receipt_key": "frontier_score_matmul_values"},
    {"module": "Verdict.runtime_frontier_score_exchange_values", "receipt_key": "frontier_score_exchange_values"}
  ]
}
```

Choose a contiguous canonical attachment suffix through the intended final
stage, in direct-call order. These are operator expectations, never populated
from observed results. All nested calls must receive the same original six
objects; all returned detail objects must match the final attached receipt in
JSON wire representation. Tuple/list wire normalization is allowed; bool/int,
float/int, array/peer order and missing facts are not conflated. There is no
hardcoded model, tensor ID, rank count or expected stage count.

**The sealed baseline alone does not attach the new score stages.** The parent
must integrate/approve their actual attachment before using the score-stage
configuration; an old source must fail this expected cover, not report success.

## Full run command (not a fragment replay)

After source approval and resource admission, use a fresh external `TV_RUN`:

```bash
cd "$TV_ROOT"
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$TV_ROOT:$TV_ROOT/Verdict" \
  timeout --signal=TERM --kill-after=30s 7200s "$TV_PY" -m trainverify.canonical_run run \
  --config "$TV_LAYOUT" --recipe "$TV_RECIPE" --recipe-sha256 "$RECIPE_SHA" \
  --source-manifest "$SOURCE_MANIFEST" --source-manifest-sha256 "$MANIFEST_SHA" \
  --expected-commit "$BASELINE_COMMIT" \
  --stages "$EXPECTED_STAGES" --stages-sha256 "$STAGES_SHA" \
  --out "$TV_RUN" >"$TV_RUN.launcher.log" 2>&1
status=$?
printf '%s\n' "$status" >"$TV_RUN.launcher-exit"
```

The CLI returns 0 only for verified generation bookkeeping; its underlying
compiler still has exception exit 1, recorded separately. CLI rejection returns
2. The external timeout/OS status is independent: a killed process, absent
observation, timeout or segmentation fault must never be counted as PASS.
There is no built-in RAM/process-tree sandbox; apply the parent's admission and
containment policy. The launcher log also retains preflight/import messages.

Files include `command.json` (recipe/layout/source/stage/executable/input
identities and exact compiler argv), `generator.log` (Python and native stdout/
stderr plus original traceback), `observation.json` (immutable original timing,
exit/exception, complete attached source/receipt, stages and import checks),
`runtime-seed.json` and `run-result.json`. The published directory is checked
against the production closed `_proof_bundle` inventory, including every
module's membership, source hash, imports, dependency order, metadata and the
unchanged strict aggregate UTF-8 budget.

At this baseline `_proof_bundle` is imported **locally** inside `attach`, not an
`initial` module attribute. The observer therefore wraps its actual owner,
`runtime_world._proof_bundle`, and records refusal only while the real attach
is active. The original gate runs unchanged. The first exact budget refusal's
complete positional/keyword payload is saved to
`diagnostic/first-refused-bundle.json`. It is JSON diagnostic data, **not**
a published Lean directory or proof inventory; never admit it as publication.
This retains the entire pre-codec entry/support material for later comparison.

## Recheck existing output without rerunning

```bash
"$TV_PY" -m trainverify.canonical_run recheck \
  --run-dir "$TV_RUN" --command-sha256 "$COMMAND_SHA" \
  --observation-sha256 "$OBSERVATION_SHA" --output "$TV_RUN/rechecked.json"
```

This rereads pinned original evidence and verifies current source/input/log and
publication bytes. It invokes no compiler, attachment, world render or publish.
It creates a separate no-clobber result and leaves the original failed/successful
exit and logs intact. Both command and observation hashes are required; stage
expectations come from the original pinned configuration. Missing/incomplete
observations or a genuine compiler/budget failure cannot be repaired into PASS.
The original source root remains sealed: if changing the observer itself,
retain original evidence/source and require a separately reviewed migration,
not a rewritten source manifest presented as the old run.

## Fast validation only

```bash
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH="$TV_ROOT:$TV_ROOT/Verdict" "$TV_PY" -m pytest \
  scripts/tests/test_canonical_run.py -q -p no:cacheprovider \
  --basetemp="$TV_CHECKS/pytest-tmp" --junitxml="$TV_CHECKS/pytest.xml"
```

Tests use real small `WorldDefinitions`, a real portable world renderer,
production publication/readback and the real aggregate gate. Expensive
compiler-control-flow tests are explicitly mocked and are **not actual saved
captures**. No long capture, Lean/kernel compilation or installation is needed.
