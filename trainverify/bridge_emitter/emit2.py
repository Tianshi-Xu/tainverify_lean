#!/usr/bin/env python3
"""Bridge emitter — UNIVERSAL end-to-end pipeline (emit2).

    python3 emit2.py <N> [--dry-run] [--no-compile] [--out PATH]

Like emit.py but drives renderer_uni.render_universal (any topology, no family-A gate).
"""
import os, sys, re, subprocess, argparse
sys.path.insert(0, os.path.dirname(__file__))
from parser import load_goal_ir, analyze, GoalIR
from probe import build_probe, DENOTE_DIR
from emit import trace_input_sources, compute_imports
from target_config import DENOTE_DIR as _RELDIR, MOD_PREFIX, GEN_FILE

REPO = os.path.expanduser("~/.openclaw/workspace/tainverify_lean")
TV   = os.path.join(REPO, "trainverify")
DENOTE = _RELDIR

# Auto-detect pm.numRanks from generated-data file and expose via BRIDGE_PM_NUMRANKS
# env var BEFORE importing renderer_uni (which reads it at module load).
from parser import GEN_DIR as _GD_INIT
_gd_path_init = os.path.join(REPO, _GD_INIT, GEN_FILE)
try:
    _gd_text_init = open(_gd_path_init).read()
    _pm_m_init = re.search(r'def\s+pm\s*:\s*GraphDecl.*?numRanks\s*:=\s*(\d+)', _gd_text_init, re.S)
    if _pm_m_init and "BRIDGE_PM_NUMRANKS" not in os.environ:
        os.environ["BRIDGE_PM_NUMRANKS"] = _pm_m_init.group(1)
except Exception:
    pass
import renderer_uni as RU

# parse #eval probe output, capturing ALL writer indices per tid (take max = last writer)
LINE_RE = re.compile(r'(SM|PM):(\d+)\s+\[(.*?)\]\s*$', re.M)
TUP_RE = re.compile(r'\(\s*(\d+),\s*\(\s*(?:OpName\.)?([A-Za-z0-9_]+),\s*'
                    r'\(\s*\[([0-9,\s]*)\]\s*,\s*\[([0-9,\s]*)\]')


def parse_probe_last(raw: str):
    res = {"sm": {}, "pm": {}}
    # group lines by side:tid since a tid may have multiple writer tuples
    for m in re.finditer(r'(SM|PM):(\d+)\s+\[', raw):
        side = m.group(1); tid = int(m.group(2))
        # capture the bracketed list following this marker
        start = m.end() - 1
        depth = 0; i = start
        while i < len(raw):
            if raw[i] == '[':
                depth += 1
            elif raw[i] == ']':
                depth -= 1
                if depth == 0:
                    break
            i += 1
        body = raw[start:i+1]
        best = None
        writers = []
        for t in TUP_RE.finditer(body):
            idx = int(t.group(1)); op = t.group(2)
            params = [int(x) for x in re.findall(r'\d+', t.group(4))] or None
            writers.append({"node_idx": idx, "op": op, "params": params})
            if best is None or idx > best[0]:
                best = (idx, op, params)
        if best is not None:
            key = "sm" if side == "SM" else "pm"
            # `best` = max-index writer (the in-place collective when a tid is written
            # twice). `writers` keeps ALL writer tuples so the in-place producer (the
            # earlier, non-collective writer of the same tid) can be recovered.
            res[key][tid] = {"node_idx": best[0], "op": best[1], "params": best[2],
                             "writers": writers}
    return res


def run_probe_all(imports, sm_tids, pm_tids, timeout=900, multi_out=False):
    from probe import _eval_line
    # The probe only evaluates `denoteGraph sm/pm` over the GLOBAL graphs (provided by
    # GeneratedData via BridgeKit) — it never references prereq-bridge theorems. So we
    # drop any prereq-bridge import whose .olean has not been built; otherwise a single
    # un-built (or un-buildable, e.g. ordering-blocked) sibling bridge would make the
    # probe file fail to elaborate. Base infra imports are kept verbatim.
    def _has_olean(mod):
        if not mod.endswith("Bridge"):
            return True
        rel = mod.replace(".", "/") + ".olean"
        return os.path.exists(os.path.join(TV, ".lake/build/lib/lean", rel))
    imports = [m for m in imports if _has_olean(m)]
    header = ("\n".join(f"import {m}" for m in imports) + "\n"
              "set_option maxRecDepth 100000\n"
              "set_option maxHeartbeats 4000000\n"
              "namespace TrainVerify.Denote.GeneratedGoals\n"
              "open TrainVerify.Denote TrainVerify.Denote.Generated\n")
    # For multi-output nodes (e.g. FW_multiref outs=[t1,t2]) an exact `o = [t]`
    # match fails; use membership `t ∈ o` so a node is found by ANY of its outputs.
    pat = (lambda t: f"{t} ∈ o") if multi_out else (lambda t: f"o = [{t}]")
    lines = [header]
    for t in sm_tids:
        lines.append(_eval_line("sm", pat(t), f'"SM:{t}"'))
    for t in pm_tids:
        lines.append(_eval_line("pm", pat(t), f'"PM:{t}"'))
    lines.append("end TrainVerify.Denote.GeneratedGoals")
    src = "\n".join(lines)
    p = os.path.join(TV, DENOTE_DIR, "ProbeAuto.lean")
    with open(p, "w") as f:
        f.write(src)
    try:
        out = subprocess.run(["lake", "env", "lean", f"{DENOTE_DIR}/ProbeAuto.lean"],
                             cwd=TV, capture_output=True, text=True, timeout=timeout)
        raw = out.stdout + "\n" + out.stderr
        parsed = parse_probe_last(raw)
        parsed["_returncode"] = out.returncode
        parsed["_raw"] = raw
        return parsed
    finally:
        if os.path.exists(p):
            os.remove(p)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("n", type=int)
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--no-compile", action="store_true")
    ap.add_argument("--out", default=None)
    ap.add_argument("--quiet", action="store_true")
    args = ap.parse_args()
    n = args.n
    log = (lambda *a: None) if args.quiet else print

    ir = load_goal_ir(n, REPO)
    topo = analyze(ir)
    log(f"[g{n}] single_tp={topo.single_tp} mid={len(topo.mid_tids)} finals={len(topo.final_tps)} "
        f"smop={ir.sm_nodes[0].op}")

    input_sources, missing = trace_input_sources(ir)
    if missing:
        log(f"  WARNING unresolved inputs: {missing}")

    imports = compute_imports(ir.prereqs)
    imports.append(f"{MOD_PREFIX}.Goal_{n}")
    # NOTE (prereq-trim 2026-06-21): we used to ALSO union-in the ORIGINAL bridge's
    # imports for regression robustness. That is now HARMFUL: the renderer body only
    # references `goal_M_intermediate` for M in ir.prereqs (the *trimmed* prereq set),
    # so compute_imports(ir.prereqs) already lists exactly the GoalNBridge imports the
    # body needs. Unioning the stale original imports perpetuates the old fat (~264)
    # import list and defeats the whole DAG-trim. We therefore only union NON-bridge
    # imports from the original (rare base-infra a handwritten original may have had);
    # any `GoalNBridge` import the body doesn't reference is intentionally dropped.
    orig = os.path.join(TV, DENOTE, f"Goal{n}Bridge.lean")
    if os.path.exists(orig):
        orig_imports = [l.split(None, 1)[1].strip()
                        for l in open(orig) if l.startswith("import ")]
        seen = set(imports)
        for m in orig_imports:
            # skip GoalNBridge imports: those must come from compute_imports(ir.prereqs)
            if re.match(rf"{re.escape(MOD_PREFIX)}\.Goal\d+Bridge$", m):
                continue
            if m not in seen:
                imports.append(m); seen.add(m)

    # The universal renderer always emits sm_val/pm_val/initGoals_preserved/...
    # which live in BridgeKit; storeShapes_weaken lives in SpikeBridge. Guarantee
    # both are imported no matter which import-building path ran above (handwritten
    # originals predate BridgeKit and don't import it).
    kits = [f"{MOD_PREFIX}.BridgeKit"]
    if os.path.exists(os.path.join(TV, DENOTE, "SpikeBridge.lean")):
        kits.append(f"{MOD_PREFIX}.SpikeBridge")
    # BRIDGE_EXTRA_IMPORTS: comma-separated module names always prepended to
    # imports. Use this to pull in a target-specific `Pattern_N.lean` (e.g. yoco
    # keeps `prove_goal_N` in `denote.yoco_goals.Pattern_N` instead of the
    # gpt_ly4 convention where `prove_goal_N_cut` lives in the Goal file).
    _extra_imports = os.environ.get("BRIDGE_EXTRA_IMPORTS", "").strip()
    if _extra_imports:
        for m in [x.strip() for x in _extra_imports.split(",") if x.strip()]:
            if m not in kits:
                kits.append(m)
    for kit in kits:
        if kit not in imports:
            imports.insert(0, kit)

    # Keep every prereq-bridge import whose bridge SOURCE (.lean) exists. We build in
    # strict topological order, so a prereq bridge's .olean is guaranteed present by the
    # time this downstream goal is compiled. (The earlier worker dropped imports lacking
    # an .olean to survive UNORDERED validation, but that produces a broken bridge: the
    # proof body still references `goal_K_intermediate`, so dropping the import => an
    # unknown-identifier error. With ordered builds we must KEEP the import.)
    def _bridge_src_exists(mod):
        if not mod.endswith("Bridge"):
            return True
        rel = mod.replace(".", "/") + ".lean"
        return os.path.exists(os.path.join(TV, rel))
    imports = [m for m in imports if _bridge_src_exists(m)]

    # probe ALL pm node outs + sm out (one tid per node; dedupe)
    # Family-aware tid selection: the multiref-2-second family's goal finals are the
    # SECOND outputs of each multiref node (SM final = lineage.ts; PM finals =
    # topo.final_tps), NOT outs[0]. Probing outs[0] (the throwaway first output)
    # fails to resolve. Pick the tids the renderer will actually frame.
    # Multi-output backward goals (BW_linear/matmul/add/layernorm): the SM/PM nodes
    # are multi-output, and the goal frames the projection at bw_idx = position of
    # lineage.ts among the SM node's outs. Probe each node's FRAMED output (outs[idx]
    # for BW nodes, outs[0] otherwise) using membership matching.
    _bw_sm = ir.sm_nodes[0] if ir.sm_nodes else None
    _is_bw_multi_goal = (_bw_sm is not None and RU.is_bw_multi(_bw_sm.op)
                         and ir.lineage.ts in _bw_sm.outs
                         and not (RU.is_multiref2_second(ir, topo)
                                  or RU.is_multirefN_nth(ir, topo)
                                  or RU.is_multiref_first_collective(ir, topo)))
    if RU.is_multiref2_second(ir, topo) or RU.is_multirefN_nth(ir, topo):
        sm_tids = [ir.lineage.ts]
        pm_tids = sorted(set(topo.final_tps))
    elif RU.is_multiref_first_collective(ir, topo):
        # Family B: SM final = i-th output (lineage.ts); PM tids = multiref-i-th-out
        # MIDs (outs[idx]) + collective finals (outs[0]). Multiref nodes are multi-
        # output so membership matching is required (multi_out=True).
        num_out, midx = RU._mref_mid_index(ir, topo)
        sm_tids = [ir.lineage.ts]
        mid_set = set(topo.mid_tids)
        final_set = set(topo.final_tps)
        pm_tids = sorted(
            {nd.outs[midx] for nd in ir.pm_nodes
             if nd.op == "FW_multiref" and nd.outs[midx] in mid_set}
            | {nd.outs[0] for nd in ir.pm_nodes if nd.outs[0] in final_set})
    elif _is_bw_multi_goal:
        bw_idx = _bw_sm.outs.index(ir.lineage.ts)
        sm_tids = [ir.lineage.ts]
        def _lout(nd):
            return nd.outs[bw_idx] if RU.is_bw_multi(nd.op) else nd.outs[0]
        # Probe every node's framed output AND its first output. The first output is
        # needed for in-place collectives (CROSS_DP_WRED): the collective's output tid
        # equals a per-rank BW node's framed output, so the framed tid resolves (via
        # `parse_probe_last`, highest-index-wins) to the COLLECTIVE node, hiding the
        # per-rank producer. Probing the producer's distinct outs[0] recovers its index.
        pm_tids = sorted({_lout(nd) for nd in ir.pm_nodes}
                         | {nd.outs[0] for nd in ir.pm_nodes})
    else:
        sm_tids = [nd.outs[0] for nd in ir.sm_nodes]
        pm_tids = sorted({nd.outs[0] for nd in ir.pm_nodes})
    log(f"  probing with {len(imports)} imports ...")
    _multi_out = (RU.is_multiref2_second(ir, topo) or RU.is_multirefN_nth(ir, topo)
                  or RU.is_multiref_first_collective(ir, topo) or _is_bw_multi_goal)
    probe = run_probe_all(imports, sm_tids, pm_tids, multi_out=_multi_out)
    if probe["_returncode"] != 0 or not probe["sm"]:
        log(f"  PROBE FAILED rc={probe['_returncode']}")
        log(probe.get("_raw", "")[-1500:])
        sys.exit(3)
    missing_idx = [t for t in pm_tids if t not in probe["pm"]] + [t for t in sm_tids if t not in probe["sm"]]
    if missing_idx:
        log(f"  PROBE missing indices for {missing_idx}")
        sys.exit(3)

    text = RU.render_universal(n, ir, topo, probe, input_sources, ir.prereqs, imports)
    # Apply BRIDGE_NAMESPACE / EXTRA_OPENS / PROVE_GOAL / PM_NUMRANKS substitutions.
    _ns = os.environ.get("BRIDGE_NAMESPACE", "GeneratedGoals")
    _extra = os.environ.get("BRIDGE_EXTRA_OPENS", "")
    _extra_str = (" " + _extra) if _extra else ""
    _prove_fmt = os.environ.get("BRIDGE_PROVE_GOAL_FMT", "prove_goal_{n}_cut")
    _prove_ref = _prove_fmt.format(n=n)
    # Auto-detect pm.numRanks from the generated-data file (parses `def pm : GraphDecl := by refine { numRanks := N, ... }`).
    from parser import GEN_DIR
    from target_config import GEN_FILE
    _gd_text = open(os.path.join(REPO, GEN_DIR, GEN_FILE)).read()
    _pm_nr_m = re.search(r'def\s+pm\s*:\s*GraphDecl.*?numRanks\s*:=\s*(\d+)', _gd_text, re.S)
    _pm_nr = _pm_nr_m.group(1) if _pm_nr_m else os.environ.get("BRIDGE_PM_NUMRANKS", "4")
    text = (text
            .replace("@@BRIDGE_NAMESPACE@@", _ns)
            .replace("@@EXTRA_OPENS@@", _extra_str)
            .replace(f"@@PROVE_GOAL_{n}@@", _prove_ref)
            .replace("@@PM_NUMRANKS@@", _pm_nr))
    out_path = args.out or os.path.join(TV, DENOTE, f"Goal{n}Bridge.lean")
    if args.dry_run:
        log(text)
        return
    with open(out_path, "w") as f:
        f.write(text)
    log(f"  wrote {out_path} ({len(text)} chars)")

    if args.no_compile:
        return
    r = subprocess.run(["lake", "env", "lean", f"{DENOTE}/Goal{n}Bridge.lean"],
                       cwd=TV, capture_output=True, text=True, timeout=900)
    ok = r.returncode == 0 and "sorry" not in (r.stdout + r.stderr).lower()
    log(("  OK" if ok else "  FAIL") + f" exit={r.returncode}")
    if not ok:
        log((r.stdout + r.stderr)[-2500:])
        sys.exit(1)


if __name__ == "__main__":
    main()
