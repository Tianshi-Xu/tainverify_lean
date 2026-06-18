#!/usr/bin/env python3
"""Bridge emitter — Phase 4: end-to-end pipeline.

    python3 emit.py <N> [--dry-run]

Pipeline:
  1. parser.load_goal_ir(N) -> IR
  2. topology.analyze(IR) -> Topo
  3. trace_input_sources(IR) -> InputSource list  (where does each pm input come from?)
  4. choose template family (currently only FAMILY-A: multi-tp + 0 mid + per-rank)
  5. probe.run_probe() -> node-index map
  6. renderer.render_family_a() -> Lean source
  7. write GoalNBridge.lean
  8. (optional) compile + #print axioms check
"""
import os, sys, re, json, subprocess, argparse
sys.path.insert(0, os.path.dirname(__file__))
from parser import load_goal_ir, analyze, GoalIR
from probe import run_probe
from renderer import render_family_a, InputSource

REPO = os.path.expanduser("~/.openclaw/workspace/tainverify_lean")
TV   = os.path.join(REPO, "trainverify")
DENOTE = "denote/gpt_ly4_regen"

def trace_input_sources(ir: GoalIR) -> list:
    """For each pm-input tid (in pm_goal_NInitShapes), find its origin.

    origin can be:
      - ('tp', upstream_goal_id, rank)  - it's the rank-th tp of that goal
      - ('ts', upstream_goal_id)        - it's the ts (single output) of that goal
      - ('init', initGoal_tid)          - replicated initGoal
    Returns list[InputSource] for sm and pm inputs (both).
    """
    sources = []
    # load all prereq goals' lineage from GeneratedData
    gen_text = open(os.path.join(TV, DENOTE, "GeneratedData.lean")).read()

    def goal_def(gid):
        m = re.search(rf'def\s+goal_{gid}\b.*?(?=\ndef\s)', gen_text, re.S)
        if not m: return ""
        return m.group(0)

    # build reverse maps from prereqs
    tid_to_origin = {}   # tid -> InputSource
    for gid in ir.prereqs:
        blk = goal_def(gid)
        if not blk: continue
        ts_m = re.search(r'ts\s*:=\s*(\d+)', blk)
        sh_m = re.search(r'tsShape\s*:=\s*\[([0-9,\s]*)\]', blk)
        if ts_m:
            tid = int(ts_m.group(1))
            sh = [int(x) for x in re.findall(r'\d+', sh_m.group(1))] if sh_m else None
            # Do NOT clobber an existing tp/ts_tp origin: if this tid is already known
            # as some goal's tp (its PM-side provenance), a later goal where the same
            # tid happens to be that goal's `ts` (SM output) must not overwrite it —
            # PM inputs need the tp lineage. (e.g. goal_184 tid 1008 is goal_290.tp,
            # but also goal_291.ts; the tp origin is the correct one.)
            prev_ts = tid_to_origin.get(tid)
            if prev_ts is None or prev_ts.kind == "ts":
                tid_to_origin[tid] = InputSource(tid=tid, kind="ts", upstream=gid, shape=sh)
        # tps
        tps = [(int(r), int(t)) for r, t in
               re.findall(r'\{\s*rank\s*:=\s*(\d+),\s*tid\s*:=\s*(\d+)\s*\}', blk)]
        tpsh_m = re.search(r'tpShapes\s*:=\s*\[(.*?)\]\s*(?:,\s*gatherDim|\})', blk, re.S)
        tp_shapes = []
        if tpsh_m:
            for sm_ in re.finditer(r'\[([0-9,\s]*)\]', tpsh_m.group(1)):
                tp_shapes.append([int(x) for x in re.findall(r'\d+', sm_.group(1))])
        for i, (r, t) in enumerate(tps):
            sh = tp_shapes[i] if i < len(tp_shapes) else None
            prev = tid_to_origin.get(t)
            kind = "tp"
            # single-tp upstream: same tid is both the goal's ts (sm side) and a tp
            # (pm side) -> need BOTH sm and pm shape vars.
            if prev is not None and prev.kind == "ts" and prev.upstream == gid:
                kind = "ts_tp"
            tid_to_origin[t] = InputSource(tid=t, kind=kind, upstream=gid,
                                          upstream_rank=r, shape=sh, n_tps=len(tps))

    # initGoal_W: scan GeneratedData for `def initGoal_W := ...` with shape
    init_pattern = re.findall(
        r'def\s+initGoal_(\d+)\s*:.*?\bts\s*:=\s*(\d+).*?\btsShape\s*:=\s*\[([0-9,\s]*)\]',
        gen_text, re.S)
    init_map = {}    # tid -> (initgoal_name_tid, shape)
    for nm, tid, sh in init_pattern:
        init_map[int(tid)] = (int(nm),
                              [int(x) for x in re.findall(r'\d+', sh)])

    # initGoal_W tps: a sharded init weight has tps=[chunk tids] (e.g. initGoal_575
    # with tps [1229..1232]). These chunk tids appear as pm-node inputs but have no
    # standalone `def initGoal_<chunk>`. Map each chunk tid -> (parent W, rank, shape, n).
    init_tp_map = {}   # chunk_tid -> (parent_initgoal_tid, rank, shape, n_tps)
    for im in re.finditer(r'def\s+initGoal_(\d+)\s*:.*?(?=\ndef\s|\Z)', gen_text, re.S):
        blk = im.group(0)
        w = int(im.group(1))
        tps = [(int(r), int(t)) for r, t in
               re.findall(r'\{\s*rank\s*:=\s*(\d+),\s*tid\s*:=\s*(\d+)\s*\}', blk)]
        tpsh_m = re.search(r'tpShapes\s*:=\s*\[(.*?)\]\s*\}', blk, re.S)
        tp_sh = []
        if tpsh_m:
            for sm_ in re.finditer(r'\[([0-9,\s]*)\]', tpsh_m.group(1)):
                tp_sh.append([int(x) for x in re.findall(r'\d+', sm_.group(1))])
        # only treat as chunk-source when tid differs from parent ts (real shard,
        # not the replicated single-tp `tid==ts` case)
        for i, (r, t) in enumerate(tps):
            if t == w:
                continue
            sh = tp_sh[i] if i < len(tp_sh) else None
            init_tp_map[t] = (w, r, sh, len(tps))

    # collect mini-graph inputs (sm + pm) — these are the tids that need provenance
    all_inputs = set()
    for nd in ir.sm_nodes:
        all_inputs.update(nd.ins)
    for nd in ir.pm_nodes:
        all_inputs.update(nd.ins)
    # subtract tids that are PRODUCED by mini-graph nodes themselves
    produced = set()
    for nd in ir.sm_nodes + ir.pm_nodes:
        produced.update(nd.outs)
    # PER-SIDE produced sets: a tid may be produced internally on one side yet be a
    # genuine LEAF input on the other (e.g. goal_266 tid 926 = goal_265.ts: it is the
    # SM weight leaf input, but on the PM side it is the AllReducePrim output). Using a
    # single global `produced` set wrongly drops such a tid from leaf_inputs, so its
    # store-shape var never gets traced => KeyError in store_shapes_blocks. Any tid that
    # is declared in sm_shapes/pm_shapes (needs a shape var) but is NOT produced on its
    # OWN side must still receive a source entry.
    sm_produced = set()
    for nd in ir.sm_nodes:
        sm_produced.update(nd.outs)
    pm_produced = set()
    for nd in ir.pm_nodes:
        pm_produced.update(nd.outs)
    shape_tids_sm = {t for t, _ in getattr(ir, "sm_shapes", [])}
    shape_tids_pm = {t for t, _ in getattr(ir, "pm_shapes", [])}
    # store-shape tids that are leaves on their own side (regardless of other-side production)
    own_side_leaf_shape = ((shape_tids_sm - sm_produced) | (shape_tids_pm - pm_produced))
    leaf_inputs = sorted((all_inputs - produced) | own_side_leaf_shape)

    sources = []
    missing = []
    for tid in leaf_inputs:
        origin = tid_to_origin.get(tid)
        # A bare `ts` origin is only an SM-side coincidence (this tid happens to be some
        # prereq goal's ts/SM-output). If the tid is ALSO a genuine init-weight shard
        # (init_tp_map) or a named init source (init_map), those carry the correct PM-side
        # provenance and must win over the coincidental ts. (Same precedence rule as the
        # ts-vs-tp guard above; fixes goal_107 vocab shards 1067/1068 mis-tagged as
        # goal_311/312 ts instead of initGoal_563 rank2/rank3 chunks.)
        if origin is not None and origin.kind == "ts" and (tid in init_tp_map or tid in init_map):
            origin = None
        if origin is not None:
            sources.append(origin)
        elif tid in init_map:
            w, sh = init_map[tid]
            sources.append(InputSource(tid=tid, kind="init", upstream=w, shape=sh))
        elif tid in init_tp_map:
            # chunk tid of a sharded init weight (initGoal_W.tps[rank])
            w, r, sh, ntps = init_tp_map[tid]
            sources.append(InputSource(tid=tid, kind="init_tp", upstream=w,
                                       upstream_rank=r, shape=sh, n_tps=ntps))
        else:
            # fallback: maybe initGoal directly named by tid (initGoal_<tid>)
            # look for `def initGoal_<tid>` and read tsShape
            m = re.search(rf'def\s+initGoal_{tid}\b.*?tsShape\s*:=\s*\[([0-9,\s]*)\]',
                         gen_text, re.S)
            if m:
                sh = [int(x) for x in re.findall(r'\d+', m.group(1))]
                sources.append(InputSource(tid=tid, kind="init", upstream=tid, shape=sh))
            else:
                missing.append(tid)
    return sources, missing

def compute_imports(prereqs: list) -> list:
    """Decide which upstream bridges to import. CORRECT version: import a bridge
    for EVERY prereq that has a GoalNBridge.lean file (main-chain AND residual),
    not just the max main-chain bridge. Rationale: the highest main-chain bridge's
    transitive import chain does NOT necessarily cover all lower prereq intermediates
    (the lineage DAG has side-branches, e.g. goal_65's chain skips goal_56). Lean
    dedupes transitive imports, so importing every prereq bridge is redundant-but-safe.
    Base goals with no bridge file (e.g. goal_2) are skipped; their intermediates are
    provided transitively by any importing bridge / BridgeKit.
    Always includes BridgeKit (graph-generic sm_val/pm_val/... gears) and
    SpikeBridge (storeShapes_weaken / mem_of_shapeEnvOfList weakening gears),
    which every bridge's assembly block needs regardless of prereqs."""
    import os as _os
    base = ["denote.gpt_ly4_regen.BridgeKit", "denote.gpt_ly4_regen.SpikeBridge"]
    if not prereqs:
        return list(base)
    _denote = _os.path.join(_os.path.dirname(__file__), "..", "denote", "gpt_ly4_regen")
    imports = list(base)
    for p in sorted(set(prereqs)):
        bf = _os.path.join(_denote, f"Goal{p}Bridge.lean")
        if _os.path.exists(bf):
            imports.append(f"denote.gpt_ly4_regen.Goal{p}Bridge")
    return imports

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--no-compile", action="store_true")
    ap.add_argument("--family", default="auto", choices=["auto", "A"])
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    n = args.n

    print(f"[1/7] Loading goal_{n} IR...")
    ir = load_goal_ir(n, REPO)
    print(f"  sm: {len(ir.sm_nodes)} node(s), pm: {len(ir.pm_nodes)} node(s), "
          f"prereqs: {len(ir.prereqs)}")

    print(f"[2/7] Analyzing topology...")
    topo = analyze(ir)
    print(f"  single_tp={topo.single_tp}, mid_tids={len(topo.mid_tids)}, "
          f"final_tps={topo.final_tps}")

    fam = args.family
    if fam == "auto":
        if not topo.single_tp and len(topo.mid_tids) == 0 and len(ir.sm_nodes) == 1:
            fam = "A"
        else:
            print(f"[ABORT] goal_{n} not in family-A (single_tp={topo.single_tp}, "
                  f"mid={len(topo.mid_tids)}, sm_nodes={len(ir.sm_nodes)}). "
                  f"Other families not yet supported.")
            sys.exit(2)
    print(f"[3/7] Family: {fam}")

    print(f"[4/7] Tracing input sources...")
    input_sources, missing = trace_input_sources(ir)
    if missing:
        print(f"  WARNING: unresolved input tids: {missing}")
    for s in input_sources:
        print(f"  tid={s.tid} <- {s.kind}:{s.upstream}"
              f"{' rank='+str(s.upstream_rank) if s.kind=='tp' else ''}"
              f" shape={s.shape}")

    imports = compute_imports(ir.prereqs)
    imports.append(f"denote.gpt_ly4_regen.Goal_{n}")
    print(f"[5/7] Imports: {imports}")

    print(f"[6/7] Probing node indices...")
    sm_tids = [nd.outs[0] for nd in ir.sm_nodes]
    pm_tids = [nd.outs[0] for nd in ir.pm_nodes]
    # use highest existing bridge as probe import (so pm/sm are defined)
    probe_import = imports[0] if imports[0].endswith("Bridge") else f"denote.gpt_ly4_regen.GeneratedData"
    probe_res = run_probe(REPO, probe_import, sm_tids, pm_tids, timeout=600)
    if probe_res.get("_returncode", 1) != 0 or not probe_res["sm"] or not probe_res["pm"]:
        print(f"  PROBE FAILED rc={probe_res.get('_returncode')}")
        print(probe_res.get("_raw", "")[-1500:])
        sys.exit(3)
    print(f"  SM nodes: {probe_res['sm']}")
    print(f"  PM nodes (first 4): {dict(list(probe_res['pm'].items())[:4])}")

    print(f"[7/7] Rendering...")
    text = render_family_a(n, ir, topo, probe_res, input_sources, ir.prereqs, imports)
    out_path = args.out or os.path.join(TV, DENOTE, f"Goal{n}Bridge.lean")
    if args.dry_run:
        print(f"--- DRY RUN; would write to {out_path} ---")
        print(text[:2500])
        print(f"... (total {len(text)} chars)")
        return

    with open(out_path, "w") as f:
        f.write(text)
    print(f"  wrote {out_path} ({len(text)} chars)")

    if args.no_compile:
        print("done (compile skipped).")
        return

    print(f"[verify] compiling...")
    r = subprocess.run(
        ["lake", "env", "lean", f"{DENOTE}/Goal{n}Bridge.lean"],
        cwd=TV, capture_output=True, text=True, timeout=900,
    )
    if r.returncode == 0 and "sorry" not in (r.stdout + r.stderr).lower():
        print(f"  ✅ COMPILE OK exit=0, no sorry")
    else:
        print(f"  ❌ COMPILE FAILED exit={r.returncode}")
        print((r.stdout + r.stderr)[-2500:])

if __name__ == "__main__":
    main()
