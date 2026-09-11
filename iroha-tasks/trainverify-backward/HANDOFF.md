# Backward / DP work line

## Ownership and baseline
- Owner: Methode, Discord backward thread; independent branch `trainverify-backward`.
- Worktree: `/home/v-zhouziyu/work/trainverify-backward`.
- Immutable base: `b1b2fb45a521488f9b7b517982e11fabaaaf0d10` (clean when created).
- Forward tree is read-only: `/home/v-zhouziyu/work/trainverify-dp-prefix-cost-closure`.
- Own this document and new backward-specific authority/read helper/tests only. No canonical renderer/scanner/import/public entry edits; exact module contracts and commits will be handed to forward integration.

## Existing evidence and reuse
- `Verdict/runtime_prefix.py` already supports BW_linear, with ordered `[dy,x,w]`, two outputs and rank2/rank3 shape checks. Existing dX/dW theorem families are under audit, not to be reimplemented blindly.
- `denote/SourceValueRead.lean` supplies original successful run / SAME-final-Store source reads; `SourceLinearRead.lean` is the forward pattern.
- Forward local acceptance: audit `dp-prefix-cost-closure/output-projection/STATUS.md` records output projection source commit `d9f53deb49f839d731a031c64c1e08ad27f464a6`. This is historical evidence, not a new build in this worktree.
- Existing real captures to reuse, without recapture: `trainverify-audits/general-parallel-internal1/global-b2/capture.pkl` and `p2-r4/capture.pkl`.

## First slice / open obligations
Audit original FW/BW pairing, saved x/w identity/version and cotangent before adding source read certificates. Distinguish source authority from exported DTO and renderer. No assumptions about loss/seed/DP scaling; no output equality premises.

Input reconstruction from the forward chain, seed provenance, branch accumulation and DP/WRED remain explicit upstream obligations until actually discharged. Local conditional read theorem is not a whole-model result.

## Source boundary checkpoint (Python-only)
- Own: `trainverify/backward_linear_authority.py`, `scripts/tests/test_backward_linear_authority.py`, this document and `inspect_capture.py`.
- `bind(cells, source_index)` consumes actual transient `IRBpOperation` / `.mirror`, complete original ordered IR metadata and source fullrefs. It records the independent cotangent/saved-X/saved-W roles, dX/dW outputs and contraction convention; it rejects changed saved versions/owners, reordered outputs, mismatched derivative identities and exact-fullref suffix overwrite.
- Raw caller cells must come from the existing source loader. Binding this record to writer/export/call authority, lowered graph execution order and the shared proof DAG remains the next interface step. This record is not itself an authenticated whole-model certificate.
- Actual captures: first BW is SM cid62 / FW cid57 and PM rank0 cid348 / FW cid345. Source formulas: `Denote.lean:381` rank2/rank3 backward agrees with local `torch.nn.functional.linear` derivative over supplied cotangent; no added local scaling. PM first dX has value-part `(0,2)` (partial sum, not a numerical division by two). Original runtime seed/normalization remains an external obligation.
- Executed strict RED→GREEN: missing binder → positive; six fullref/order failures → guard → green; five newly exposed mirror/metadata/version/suffix failures → guard → green. `saved-ir` is rejected by the prior saved-fullref guard, not counted as new metadata-guard coverage.
- Test fixture clones all Cell slots explicitly: ordinary `copy.copy(Cell)` drops transient IR authority through `__getstate__`; clone acceptance is checked before mutations.
- Focused command (13 passed, 0 skipped):
  `TRAINVERIFY_CAPTURE_ROOT=/home/v-zhouziyu/trainverify-audits/general-parallel-internal1 PYTHONPATH=/home/v-zhouziyu/work/trainverify-backward:/home/v-zhouziyu/work/trainverify-backward/Verdict /home/v-zhouziyu/.venvs/trainverify-capture/bin/python -m pytest /home/v-zhouziyu/work/trainverify-backward/scripts/tests/test_backward_linear_authority.py -q --tb=short`
- Source-only inspection: same PYTHONPATH/Python, run `/home/v-zhouziyu/work/trainverify-backward/iroha-tasks/trainverify-backward/inspect_capture.py`; uses `_prepare_rank_cells` in memory, never build_graph rank-cell cache.

## Verification/resource status
- No Lean/Lake/capture launched by this line yet. Outputs will be local, under existing global one-Lean policy; no `.lake/build` symlink.
- UNCOMPILED local authority candidate; all proof/kernel/public/Torch flags false. No main integration, push or publication; no cron.
- Next: add `SourceBWLinearRead` original successful run dX/dW conclusions and source/export join; forward saved-X reconstruction, cotangent producer chain, DP/WRED remain unclosed.
