# Existing score-division joint: source-first cold rebuild

## Outcome: SUCCESS

The complete existing `ScoreDivFrontierJoint` was compiled from source, including both score-division units and all six mixed rows. **All 239 required task modules compiled successfully**, followed by a newly compiled `ColdContracts` probe. No historical task `.olean`, old shared package cache, or installed historical `.elan` tree was used as a build input.

This is result reconstruction, not an assertion that every historical binary or receipt was restored byte-for-byte. The accepted generated `.lean` files were reused **unchanged as candidate source**, not newly generated. No mathematical frontier was extended, no theorem statement was weakened, and no canonical attachment was made.

The machine-readable outcome is `result.json`.

## Current closure and minimal missing material

Pinned public source: `https://github.com/Tianshi-Xu/tainverify_lean.git`, commit `97547f38242a61d89b30e1970ec8faf64d82a105`.

| Required task source origin | Modules |
|---|---:|
| Exact bytes in the pinned public tree | 94 |
| Exact bytes in pinned reachable public history | 2 |
| Required accepted source snapshots absent from that tree/history | 143 |
| **Total** | **239** |

The two historical sources are `TrainVerifyRuntimePrefixSupport` at `c23a0c68a6b4a8daa29fb06c9f0e54cd83459fe6` and `TrainVerifyRuntimePrefixNamesV3` at `629f259c00e5b2625ca8395a58ff8f9e7a623f85`. Exact paths, blob IDs and SHA256 values are in `source-manifest.json`; both were independently retrieved through the fresh public clone.

The 143 missing sources contain **2,638,213 bytes**, packaged as the **320,194-byte** `minimal-missing-sources.tar.gz`. This is minimal at unchanged-import/module granularity: 127 numbered prefix modules plus the required world, accepted frontier and joint sources. It is not the old 850-source aggregate preservation inventory.

A load-bearing discovery was that the current search path selects `RuntimeWorld` from `dp-prefix-cost-closure/frontier-next-layernorm/actual1`. Its source was identified by the selected object's matching source/build receipt. The three differently hashed `RuntimeWorld.lean` variants in the aggregate binding roster are not interchangeable with that current source.

Pinned Lean's actual `--src-deps` parser, with explicit `LEAN_SRC_PATH`, independently confirmed the graph. The complete task + official package + standard-library source closure contains **5,151 modules**. Every task header dependency set matches the build scheduler's graph, with implicit `Init` accounted for separately. See `complete-import-closure.json`.

Only reachable modules were compiled. No unrelated numbered old `Goal_N` corpus was built. Required shared relation helpers remain in the unchanged import closure.

## Kernel and contract verification

- **239/239** task modules: real direct-Lean exit 0, newly produced object files, exact source/dependency/object hashes recorded in `build-receipts.jsonl`.
- **154** saved complete Lean Expr contracts preserved exactly, including universes and binders.
- **162** standalone final axiom queries passed: the saved frontier contracts plus the seven division declarations and the joint.
- **8,223** explicit source axiom queries, including the `#a` macro aliases, passed the kernel3 policy.
- **7,896** saved axiom-query contracts across **131 modules** were preserved exactly.
- All 239 candidate source hashes remain unchanged. The division and joint's original complete explicit statements were re-elaborated, not replaced with reduced statements.
- The final theorem reports only `[propext, Classical.choice, Quot.sound]`.
- A source token scan excluding nested comments and strings found no `sorry`, `admit`, new `axiom`, `native_decide`, `unsafe`, or `implemented_by` tokens.
- A negative control removing the new task object root failed with `unknown module prefix 'denote'`; it did not discover any old task cache.

Evidence: `contract-verification.json`, `contracts.json`, `all-module-axioms.json`, `source-policy-scan.json`, `negative-control.json`, and the per-module logs/timings.

The result retains the original conditional store/denotation/initial-parameter contract. It is not an executable whole-capture witness or a new raw capture.

## Official native dependencies and resource bounds

The complete official Lean 4.32.2 Linux distribution was freshly downloaded and extracted. Its archive SHA256 is:

`5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa`

This matches the digest published by GitHub release asset `492935897`. The executable reports Lean commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`.

All nine package repositories were freshly cloned at the exact Lake manifest revisions. `lake exe cache get`, under a private HOME, restored **8,639 official cache entries**. The initial official `mathlib4-master` endpoint had no matching entries; the official `https://lakecache.blob.core.windows.net/mathlib4` fallback supplied them. The eleven locally compiled official cache-bootstrap modules are explicitly listed in `official-provenance.json`.

`official-files.json` records **127,135 files** from the complete extracted toolchain and fresh package build trees, including native libraries, extensionless cache executable, `.o.export` files, object parts, traces and generated metadata. Toolchain/package Git pins, download log, host native-library hashes, tested platform and dynamic linkage are recorded in `official-provenance.json`. All 4,912 non-task import objects and every direct recorded build dependency were rehashed against this provenance during finalization.

The main task DAG took **4,848.63 seconds (80.81 minutes)**. The scheduler allowed at most four single-threaded Lean compilers; observed peak aggregate compiler RSS was **12.44 GiB**. Every module had a 1,800-second timeout. There were no task compilation failures or timeouts. Detailed timing/RSS measurements and object-production monitoring are retained; the long sequential prefix chain was not replaced by cached task objects.

## Portable recipe and publication deliverable

Publish/review **`portable-rebuild-inputs.tar.gz`**:

- Size: **416,269 bytes**.
- SHA256: `299c1f12b2d1c80180a797bdafbc6af5743a18f83ccc1d63daab9076e49c48b8`.
- Contains the minimal missing-source bundle, source manifest, runnable restore/build/verification scripts, saved contract metadata and official dependency pins.
- Contains **no task or package objects**.

On compatible Linux x86-64 with Python 3.11+, Git, curl, tar, zstd and `/usr/bin/time`, unpack it into an empty directory and run:

```sh
python3 restore.py --build
```

The recipe reconstructs sources from public Git plus the source bundle, provisions official dependencies, builds only the task DAG, then runs the contract and axiom checks. It uses the existing direct-Lean invocation and public `trainverify.artifact_contracts` machinery, not a new proof architecture.

The actual full compile above used the same scripts and fetched dependencies. Separately, the final portable capsule was unpacked into a new directory containing none of the discovery scripts or prior caches. `restore.py --skip-provision` performed fresh shallow public Git fetches and restored all 239 sources in 32.90 seconds; every restored file was then independently rehashed. This additional capsule test was a source-restoration test, not a second full compile. See `portable-capsule-test.json` and `result.json:portable_capsule_source_test`.

## Remaining scope

There is **no remaining Lean reconstruction blocker** for this defined result. After publication of the portable inputs, this verified Lean recipe no longer requires the historical task source/object trees. New task objects are reproducible outputs, not preservation prerequisites.

Publication and deletion were not performed. Raw capture/input/Python-runtime reconstruction belongs to the separate worker and is not implied by this Lean result. Historical receipt-byte preservation and canonical attachment are separate decisions; neither was made a prerequisite for this successful result rebuild.
