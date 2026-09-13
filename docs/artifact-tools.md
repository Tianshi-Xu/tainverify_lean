# Artifact tooling and historical paths

Maintain executable tooling in Git. Keep captures, generated Lean, objects,
logs, machine-specific configuration and historical receipts outside Git.
Historical `.py` files inside sealed evidence are **frozen evidence**, not
supported entry points or import dependencies. Do not execute or edit them to
repair old absolute paths.

The maintained entry points are:

- `python -m trainverify.artifact_tools`: verify pinned artifacts, resolve old
  logical paths, check a historical kernel receipt, render complete mixed
  frontier contracts, run a direct Lean check, and plan/apply link relocation.
- `python -m trainverify.frontier_replay`: replay a configured frontier from
  existing trusted captures and a specified clean Git commit.
- `trainverify.score_exchange_audit`: the independent original-source score
  AA(1,3) census and asymmetric integer layout oracle, exposed by
  `artifact_tools check-score-exchange`. Both following divisions remain
  inventory only. This is not a Torch-refinement or kernel claim.

These replace fixed-path `render_actual.py`, `check_raw.py`,
`check_frontier_joint.py`/`check_joint.py`, and kernel/path-verification wrappers.
Use pytest directly with an external `--basetemp`, `--junitxml` and
`-p no:cacheprovider`; fixed-input historical test drivers are not needed.

## Explicit layout

Set `TV_LAYOUT` to an operator-owned JSON file. Example (paths are illustrative):

```json
{
  "version": 1,
  "relocations": [
    {"kind": "directory", "source": "/old/worktree", "target": "/srv/evidence/source-snapshot"}
  ],
  "binding_sets": [
    {"path": "/srv/evidence/receipt.json", "sha256": "<64 lowercase hex digits>", "field": ["bound_files"], "base": null}
  ],
  "lean": {
    "executable": "/srv/toolchain/bin/lean",
    "sha256": "<64 lowercase hex digits>",
    "paths": ["/srv/evidence/objects", "/srv/libraries"]
  }
}
```

A binding set selects a nonempty `path -> SHA256` object inside a hash-pinned
JSON receipt. `field: []` selects its root. `base` is an explicit directory for
relative keys; otherwise keys must be canonical absolute paths. Duplicate JSON
keys, non-finite JSON values, conflicting bindings, overlapping source mappings
and targets that still depend on a retired root are rejected.

`kind: "file"` supports **exact-file** relocations already established by a
source-migration receipt. It does not redirect an entire missing source tree.
The logical path and expected hash stay unchanged; only the lookup location is
mapped. Never regenerate expected hashes from changed artifacts to get green.

```bash
python -m trainverify.artifact_tools verify --config "$TV_LAYOUT" --output /new/run/integrity.json
python -m trainverify.artifact_tools resolve --config "$TV_LAYOUT" --path /old/worktree/some/file
python -m trainverify.artifact_tools verify-kernel --config "$TV_LAYOUT" \
  --receipt /evidence/Stage-kernel.json --sha256 "$RECEIPT_SHA"
```

Integrity checking is not semantic reauthentication, a new kernel run, a
whole-capture execution witness, or publication admission. Historical receipts
remain byte-for-byte intact. Supplied configuration, executables, source and
hash roots are trusted local operator inputs, not hostile uploads.

## Rendering and checking

```bash
python -m trainverify.artifact_tools render-joint --config "$TV_LAYOUT" \
  --detail /evidence/detail.json --sha256 "$DETAIL_SHA" --module Stage \
  --source-output /new/run/ProjectionFrontierJoint.lean
python -m trainverify.artifact_tools check-lean --config "$TV_LAYOUT" \
  --source /new/run/ProjectionFrontierJoint.lean --sha256 "$SOURCE_SHA" \
  --out-dir /new/run/joint-check \
  --query TrainVerify.Denote.RuntimeWorld.projectionFrontierJoint
```

The joint builder retains global shape, every local shape and sharded or
replicated values under the same original full-run and
`InitialParameterValues` hypotheses. It adds no output/value premise.

The direct checker uses a new output directory, authenticated direct imports,
the first applicable Lean namespace root, explicit search paths and bounded
resources. It never invokes Lake or overwrites accepted objects. Axiom queries
must match exactly; only `propext`, `Classical.choice` and `Quot.sound` are
allowed. This checks the supplied source and queries, not an inferred complete
export inventory. `--module` can explicitly specify the staged module name.
All transitive cache/library trust remains the responsibility of the supplied
configuration and the existing accepted closure.

For an interface check after relocation, create a small source importing the
already accepted joint module and printing its axioms. Only the new observer is
compiled; accepted proof modules are reused.

## Saved-source replay

The external recipe has exact fields `version`, `target`, `ancestors`, `pins`,
`seed_bundle`, `batch_authority`, and `rank_code_directory`.

- `pins` authenticates original absolute input filenames before the compiler is
  entered, including both capture pickle/JSON pairs, seed bundle, batch receipt,
  and the complete generated-rank `.py` inventory.
- `target` has `module` (the Python renderer), `name` (flat Lean fragment name)
  and `imports` (explicit Lean module names).
- `ancestors` lists the selected predecessor chain oldest first, with the same
  fields plus `detail` (a filename stem). Python module identities, predecessor
  order, first fragment imports and exact once-only calls are checked.
- The existing seed bundle supplies capture directories and the input handoff.
  Its original bytes are not rewritten. The compiler must still validate its
  original runtime/parameter authority.

```bash
PYTHONDONTWRITEBYTECODE=1 python -m trainverify.frontier_replay \
  --config "$TV_LAYOUT" --recipe /evidence/replay-recipe.json \
  --recipe-sha256 "$RECIPE_SHA" --expected-commit "$COMMIT" --out /new/run/replay
```

This is trusted local pickle input, never an upload reader. It creates a private
verifier cache beneath the new output directory, does not recapture, preserves
identical six-object predecessor calls, and stops at the original attachment
hook before canonical/world publication outputs. Rendered flags remain false
and uncompiled. Patch hooks are restored on success and failure.

## Removing compatibility links

First inventory **all consumer roots**, active scripts, shell configuration,
import paths and running jobs. Move live code to the maintained entry points;
old receipts are data, not executable shell commands. `TRAINVERIFY_NNSCALER_SOURCE`
is explicit for the optional pinned-source AST test; a configured missing path
fails rather than silently skipping.

```bash
python -m trainverify.artifact_tools plan-links --config "$TV_LAYOUT" \
  --scan-root /all/consumer/root --output /new/run/link-plan.json
python -m trainverify.artifact_tools apply-links --config "$TV_LAYOUT" \
  --plan /new/run/link-plan.json --sha256 "$PLAN_SHA" --output /new/run/links.json
# Only after reviewing the plan and validating new tool/cache entry points:
python -m trainverify.artifact_tools remove-aliases --config "$TV_LAYOUT" \
  --scan-root /all/consumer/root --output /new/run/aliases.json
```

Repeat `--scan-root` where needed. Scope completeness is the operator's
responsibility: no tool can infer consumers outside the declared roots. The
planner includes Git metadata and does not silently skip traversal errors.
Each rewrite must preserve the actual target inode and type. Plans reject
omissions within their roots, duplicate entries, unrelated no-op replacements,
wrong targets and changed source entries. Directory-root locks coordinate
callers using the same roots; directories must otherwise be quiescent and
operator-owned. This is not a sandbox against hostile same-UID mutation.

A failed rewrite leaves old aliases in place and can resume from the original
plan. Alias removal is a separate action, refuses remaining legacy link
references, verifies exact alias ownership and rechecks pinned artifacts. No
source, object, historical receipt or archive directory is deleted by these
commands. JSON reports and generated sources use no-clobber output creation.
