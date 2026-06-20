# opaque-Store full-build run 3 — FAILURE report (Goal149Bridge stack overflow)

**Run:** `/tmp/mt_opaque3.log`, MT_OPAQUE3_EXIT=1, ~9811s user time (~2.7h wall).
**Progress:** reached `[1590/1641]` (97%) before failing on `denote.gpt_ly4_regen.Goal149Bridge`.
**Branch:** `work-from-main-2026-06-12`, HEAD `5f65ecc` — **NO commit made** (per fail protocol).

## What failed
```
✖ [1590/1641] Building denote.gpt_ly4_regen.Goal149Bridge (144s)
info: stderr:
Stack overflow detected. Aborting.
error: Lean exited with code 134
error: build failed
```
Code 134 = SIGABRT from Lean's native **stack overflow** guard. NOT a type error, NOT a timeout-at-whnf, NOT an unknown const. So per-line `error:` grep finds no source line — the abort is a C-stack overflow during elaboration.

## Reproduced in isolation (deterministic)
- `ulimit -s 8192` (default) → `Stack overflow detected. Aborting.` exit 134 (~140s).
- `ulimit -s unlimited` → **STILL** `Stack overflow detected. Aborting.` exit 134.
=> Raising the OS stack limit does **not** help. Lean elaboration worker threads use their own fixed stack; the abort is internal. `set_option maxRecDepth 100000` (already present, line 236) also does not help — this is a native stack abort, not Lean's recursion-depth guard.

## Root cause (NOT the Goal25/Goal48 transform-breakage family)
The obtain-transform on Goal149 is **correct** (lines 952-954: `obtain ⟨Ssm,hSsm⟩…`, `obtain ⟨Spm,hSpm⟩…`, `rw [← hSsm, ← hSpm]` — exactly the fixed pattern). There is no leftover `by rfl` / `show (denoteGraph …)` problem here.

The overflow is **size-induced**. Goal149 is a FAMILY-A multi-tp bridge with **228 prereqs**. The generated proof contains a single flat alternation:

`denote/gpt_ly4_regen/Goal149Bridge.lean:719`
```
    rcases hg with rfl | rfl | rfl | … (228-way) … | rfl
```
plus the matching 228-hypothesis lines:
- L1184: `rw [← hSsm, ← hSpm] at hg2 hg3 … hg312` (228 hyps on one line)
- L719-947: 228 `· exact hgNNN` bullets

The 228-way `rcases … with rfl|rfl|…` builds a deeply right-nested elaboration term that blows the worker-thread C stack.

## Why earlier (bigger) bridges "passed"
They didn't. Build order compiled Goal150-189 / 250-289 **first** (all ≤219 prereqs, simpler) — those built OK. Goal149 is the **first** of the big multi-tp group to be reached.
The even-larger siblings were **never reached** and will fail identically:
- Goal107=265, 108=264, 109=265, 110=264, … 147=229, 148=229, 149=228 prereqs.
- i.e. Goal107-149 (the whole 228-265-prereq FAMILY-A block) is the failing class.

## Fix direction (needs emitter change + regen of Goal107-149, ~43 files)
The flat N-way `rcases hg with rfl|…|rfl` does not scale past ~220 alternations. Options for `bridge_emitter`:
1. **Chunk the case split**: split the membership list into sub-lists and `rcases` each chunk separately (e.g. groups of ~50), so no single alternation exceeds the stack-safe width. Most robust.
2. Replace the giant `rcases hg with rfl|…` + per-case `exact hgNNN` with a **lookup/`fin_cases`-free** structural approach, e.g. build the goal from a `List.mem`-driven helper that dispatches via a decidable index rather than a nested Or-elimination term.
3. As a cheap stopgap, see if `set_option maxRecDepth` is irrelevant (it is) and whether a `decide`/`omega`-based membership discharge avoids the nested term — needs a spike.

Recommend option 1 (chunked rcases) — smallest emitter change, keeps the existing per-case `exact hgNNN` structure, just bounds alternation width.

## Status
- No commit. Working tree clean at 5f65ecc.
- Rollback not needed (nothing changed).
- cron `trainverify-opaque-build-watch-3` removed after this report (one-shot).
