#!/usr/bin/env python3
"""Bridge emitter — Phase 2: node-index probe subsystem.

The bridge references `pm.nodes[IDX]'(by native_decide) = {...}` where IDX is the
position in the FLATTENED full graph. This can't be computed at generation time —
it requires compiling the graph and running `#eval`. This is the two-stage build:
  emit temp probe .lean  ->  lake env lean  ->  parse #eval output  ->  index map.

Probes for each tid we need to locate in the full sm/pm graph, returns:
  { "sm": {tid: (node_idx, op, params)}, "pm": {tid: (node_idx, op, params)} }
"""
import re, os, subprocess, tempfile, json, sys
sys.path.insert(0, os.path.dirname(__file__))
from target_config import DENOTE_DIR

PROBE_HEADER = """import {import_mod}
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace TrainVerify.Denote.GeneratedGoals
open TrainVerify.Denote TrainVerify.Denote.Generated
"""

def _eval_line(graph: str, outs_pat: str, tag: str) -> str:
    # outs_pat is a Lean Bool expr over `o` (the node's outs)
    return (
        f'#eval ({tag} : String) ++ " " ++ toString '
        f'((List.range {graph}.nodes.length).filterMap (fun i =>\n'
        f'  if h : i < {graph}.nodes.length then\n'
        f'    let o := ({graph}.nodes[i]\'h).outs\n'
        f'    let p := ({graph}.nodes[i]\'h).params\n'
        f'    let op := ({graph}.nodes[i]\'h).op\n'
        f'    (if {outs_pat} then some (i, op, o, p) else none)\n'
        f'  else none))'
    )

def build_probe(import_mod: str, sm_tids: list, pm_tids: list) -> str:
    lines = [PROBE_HEADER.format(import_mod=import_mod)]
    # one eval per tid keeps parsing unambiguous
    # Use `t ∈ o` membership check so multi-output nodes (FW_inner_chunk_ce with
    # outs=[a,b], FW_multiref, FW_topk_routing etc.) also match. This is safe
    # because the *emitted* bridge only asserts `outs := [tid]` for single-output
    # nodes; for multi-output nodes the emitter uses the full outs list literal
    # (which the applyNode_XXX_out lemmas accept).
    for t in sm_tids:
        lines.append(_eval_line("sm", f"{t} ∈ o", f'"SM:{t}"'))
    for t in pm_tids:
        lines.append(_eval_line("pm", f"{t} ∈ o", f'"PM:{t}"'))
    lines.append("end TrainVerify.Denote.GeneratedGoals")
    return "\n".join(lines)

# Lean 4 prints the 4-tuple (i, op, outs, params) as NESTED right-assoc pairs:
#   SM:634 [(56, (OpName.FW_gelu, ([634], [])))]
#   PM:2141 [(367, (OpName.AllToAllPrim, ([2141], [2, 1])))]
# Structure after id:  , (OP, ([OUTS], [PARAMS]))
EVAL_RE = re.compile(
    r'(SM|PM):(\d+)\s+\[\(\s*(\d+),\s*'      # side:tid [(idx,
    r'\(\s*(?:OpName\.)?([A-Za-z0-9_]+),\s*'    # (OpName.OP,
    r'\(\s*\[([0-9,\s]*)\]\s*,\s*'            # ([OUTS],
    r'\[([0-9,\s]*)\]'                          # [PARAMS]
)

def parse_probe_output(text: str):
    res = {"sm": {}, "pm": {}}
    for m in EVAL_RE.finditer(text):
        side, tid, idx, op, outs, params = m.groups()
        key = "sm" if side == "SM" else "pm"
        pr = None
        if params and params not in ("none",):
            pr = [int(x) for x in re.findall(r'\d+', params)]
        res[key][int(tid)] = {"node_idx": int(idx), "op": op, "params": pr}
    return res

def run_probe(root: str, import_mod: str, sm_tids: list, pm_tids: list,
              timeout: int = 900) -> dict:
    tv = os.path.join(root, "trainverify")
    probe_src = build_probe(import_mod, sm_tids, pm_tids)
    probe_path = os.path.join(tv, DENOTE_DIR, "ProbeAuto.lean")
    with open(probe_path, "w") as f:
        f.write(probe_src)
    try:
        out = subprocess.run(
            ["lake", "env", "lean", f"{DENOTE_DIR}/ProbeAuto.lean"],
            cwd=tv, capture_output=True, text=True, timeout=timeout,
        )
        combined = out.stdout + "\n" + out.stderr
        parsed = parse_probe_output(combined)
        parsed["_raw"] = combined
        parsed["_returncode"] = out.returncode
        return parsed
    finally:
        if os.path.exists(probe_path):
            os.remove(probe_path)

def main():
    # demo: probe goal_52's tids
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    import_mod = sys.argv[1] if len(sys.argv) > 1 else "denote.gpt_ly4_regen.Goal51Bridge"
    sm_tids = [int(x) for x in sys.argv[2].split(",")] if len(sys.argv) > 2 else [634]
    pm_tids = [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [2141,2142,2143,2144,2145,2146,2147,2148,634]
    print(f"probing import={import_mod} sm={sm_tids} pm={pm_tids} ...")
    res = run_probe(root, import_mod, sm_tids, pm_tids)
    print("returncode:", res.get("_returncode"))
    print("SM:", json.dumps(res["sm"], indent=2))
    print("PM:", json.dumps(res["pm"], indent=2))
    if not res["sm"] and not res["pm"]:
        print("=== RAW (parse failed) ===")
        print(res.get("_raw", "")[-2000:])

if __name__ == "__main__":
    main()
