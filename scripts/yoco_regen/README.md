# YOCO-MoE A0.4B authority regeneration

This directory separates two workflows that must not be confused.

## Reviewed revisions

- llm-train: `9a1be1d5fd1c063d80be82797692cdc7d23cfbef`
- nnScaler: `d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf`
  (`li/ep-cp`, the companion branch for llm-train's explicit CP/EP API)

The nnScaler `main` revision at review time did not accept llm-train's
`cp_size` and `require_full_plan_sequence_partition` arguments. Do not replace
the pinned companion revision with `main` without rerunning the compile tests.

## CPU smoke

`compile_cpu_smoke.py` uses the deterministic built-in `tp` policy and reduced
model defaults. It checks imports, tracing, code generation, pickle extraction,
and the expected shuffle/unshuffle wiring. Its metadata contains
`"authority": false`; these artifacts must never replace production authority.
The output directory must not already exist; the smoke is built in a private
staging directory and published without replacing any existing path.

```bash
python scripts/yoco_regen/patch_mgener_dump.py \
  /path/to/pinned-nnscaler/nnscaler/parallel.py
# Reinstall that patched source into the venv, then:
python scripts/yoco_regen/compile_cpu_smoke.py \
  --llm-train /path/to/llm-train \
  --out-dir /tmp/yoco-smoke --plans 1 2
python scripts/yoco_regen/inspect_mgener.py /tmp/yoco-smoke/pm_mgener.pkl \
  --llm-train /path/to/llm-train \
  --nnscaler /path/to/pinned-nnscaler \
  --trust-local-pickle
```

For the four-layer smoke, expected logical counts are one shuffle, five
unshuffles, and two stacks in SM. PM expands each to two rank-local nodes. The
four auxiliary unshuffles must feed the two stacks; the fifth restores hidden
state layout.

## Production authority

`generate_authority.sh` is fail-closed and requires a two-GPU node. It uses
llm-train's real `run_mode=compile` / `pas_autodist` path, full 24-layer model,
sequence length 4096, and `pcs/all2all_moe.yaml`.
Both source repositories are materialized as private, no-hardlink clones at the
reviewed commits before any code executes. Neither caller checkout is modified.
The private llm clone receives one canonical, hash-bound hardware compatibility
patch: compute capability 12.x uses the generic A100/H100 Triton autotune
candidate set instead of the B200-only candidate set. This changes launch
configuration selection only, not operator values, graph annotations, model
code, or the reviewed base revision. The patched `llm/kernel/gemm.py` digest is
bound into both rank-0 dump receipts and final provenance metadata.

The pinned nnScaler dynamic-programming solver is built from a fixed-commit Git
archive in an owner-only temporary tree. The full archive SHA-256 and the three
direct build inputs are checked, the source tree is made read-only, and compiler
outputs go to a separate private directory. Before building, the generator clears
loader/compiler/Python injection variables; every builder process uses Python
`-S`, an allowlisted environment and trusted absolute interpreter. The resulting
ELF must equal the reviewed canonical digest, not a self-declared runtime hash.
This output identity check remains authoritative even on hosts that prohibit
unprivileged user or mount namespaces.

Before each `torchrun`, the canonical fixed-commit archive, exact patched
`parallel.py`, startup guard, and ELF are independently hashed. The archive,
patched module and guard become a deterministic Python runtime ZIP in a fully
sealed memfd; the ELF and worker shim use separate fully sealed memfds. No runtime
package is extracted or mounted. Both the torchrun controller and every worker
start with Python `-S` and resolve the runtime through `/proc/<holder>/fd/*` while
the holder remains alive. This prevents `.pth` startup and host-path replacement.
The `sitecustomize` guard rechecks both memfd seal sets and hashes, installs an
exact-name extension finder for `nnscaler.autodist.dp_solver`, verifies the loaded
module path, and calls `os._exit(126)` on any failure. Site-packages therefore
cannot substitute solver or nnScaler code. The build artifact is hardlinked into
the authority; its SHA-256 plus the pinned archive/source hashes are bound through
receipts and metadata. Generation uses `umask 077` and a
fixed environment for archive extraction, while torchrun receives only the five
explicitly required provenance/runtime fields plus generator-owned values; ambient
nnScaler controls are never forwarded. A closed publication allowlist rejects any
residual build/cache entry, directory, symlink, foreign inode, or group/world-
writable artifact. Validation
and no-replace rename occur in one dirfd-bound process, and the publication parent
plus every non-sticky ancestor must be root/current-user-controlled and
non-group/world-writable.

Before generation, profile the actual two-GPU interconnect with the pinned
nnScaler environment:

```bash
torchrun --standalone --nproc_per_node=2 -m nnscaler.profiler.benchmark_comm
```

The generator requires the resulting GPU-specific `comm/intra_2.json`, validates
its closed primitive/size/timing schema, copies it once into an owner-only staged
HOME, and makes nnScaler consume that immutable private copy through its normal
default-profile lookup. The authority copy is a hardlink to the same validated
inode. Its SHA-256 is bound into both receipts and the out-of-band hardware
digest. Missing profile data is fatal; the nnScaler MI200 fallback is not
production authority.

```bash
/usr/bin/env -i \
  HOME="$HOME" \
  TRAINVERIFY_CLEAN_ENV=1 \
  YOCO_PYTHON=/absolute/path/to/trusted/venv/bin/python \
  YOCO_LLM_TRAIN_REPO=/clean/pinned/llm-train \
  YOCO_NNSCALER_REPO=/clean/pinned/nnscaler \
  YOCO_AUTHORITY_OUT=/output/yoco-a04b-9a1be1d \
  /bin/bash --noprofile --norc scripts/yoco_regen/generate_authority.sh
```

The external `env -i` boundary is mandatory: the generator rejects any inherited
field outside its closed startup schema before the first Python process. This is
what excludes loader variables such as `LD_AUDIT`; setting the sentinel in a broad
ambient environment is intentionally rejected.

The output contains:

- `sm_mgener.pkl`, `pm_mgener.pkl`
- rank-0 dump receipts binding policy, topology, pickle hash, and patched-source hash
- `comm_profile_intra_2.json`, measured on the actual two-GPU node
- `nnscaler_dp_solver.so`, the exact private-build solver consumed by AutoDist
- Verdict-compatible `sm_mgener.json`, `pm_mgener.json`
- `sm_provenance.json`, `pm_provenance.json`
- `gen_args.json` with exact revisions, topology, package versions, GPU model,
  memory, compute capability, NVIDIA driver, CUDA runtime, NCCL version, canonical
  hardware-patch identity/hash, and artifact hashes
- `.trainverify-stage-owner`, an inert random ownership marker retained for
  fail-closed cleanup auditing

After generation, run `inspect_mgener.py` on both sides before emitting Lean.
Do not infer PM changes by inspecting PM alone.

## Lean emission

```bash
python scripts/yoco_regen/emit_yoco_a04b.py \
  --authority-dir /output/yoco-a04b-9a1be1d \
  --llm-train /clean/pinned/llm-train \
  --nnscaler /clean/pinned/nnscaler \
  --expected-hardware-sha256 <digest-captured-over-trusted-ssh> \
  --snapshot-dir /output/yoco-a04b-9a1be1d-lean-refresh \
  --trust-new-authority
```

The explicit trust flag acknowledges that Python pickle is executable input and
that the artifacts were produced locally by the pinned production generator.
The expected hardware digest is a required out-of-band trust anchor. Capture
`gen_args.json.hardware_sha256` directly from the GPU host over the already
authenticated SSH session before transferring the authority directory, and
store it separately from that directory. A digest read only from the transferred
artifact is not an independent trust anchor and must not be used here.
Before unpickling, the emitter verifies ownership, non-writable permissions,
fixed revisions, world/provenance schemas, production policy, topology, and
pickle hashes. It writes every generated file into a sibling staging directory
and atomically publishes one complete snapshot only after graph emission and
manifest validation succeed.

The emitter serializes rank loading to avoid the multiprocessing/import
deadlock seen with dynamically registered private-model operators. It computes
artifact and metadata hashes at execution time and passes the pinned revisions
to `graph_to_lean.py`; no digest is copied from an older authority.

Numeric TIDs, node indices, certificates, and old false-goal classifications
must be regenerated from the new graph rather than patched by number.

Only production `pas_autodist` artifacts may be written to the repository.
Inspect both SM and PM before replacing generated Lean files.
