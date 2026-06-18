#!/usr/bin/env python3
"""Bridge emitter — Phase 1: parser + topology analyzer.

Parses a goal's structured inputs from Goal_N.lean / GeneratedData.lean and
derives the bridge topology (single/multi tp, intermediate-tensor layers,
operator chain). NO Lean dependency — pure text parsing, unit-testable.

Usage:
    python3 parser.py <N> [--root <repo_root>]
prints a JSON-ish dump of the parsed IR + topology for goal N.
"""
import re, sys, json, os
from dataclasses import dataclass, field, asdict
from typing import Optional

DENOTE_DIR = "trainverify/denote/gpt_ly4_regen"

# ---------- data classes ----------
@dataclass
class Node:
    rank: int
    op: str                       # e.g. "FW_gelu", "AllToAllPrim"
    ins: list                     # list[int]
    outs: list                    # list[int]
    params: Optional[list] = None # list[int] or None

@dataclass
class LineageGoal:
    ts: int
    tsShape: list
    tps: list            # list[(rank, tid)]
    tpShapes: list
    gatherDim: Optional[int] = None

@dataclass
class GoalIR:
    n: int
    sm_nodes: list                # list[Node]
    pm_nodes: list                # list[Node]
    sm_shapes: list               # list[(tid, shape)]
    pm_shapes: list               # list[(tid, shape)]
    lineage: LineageGoal
    prereqs: list                 # list[int]

# ---------- low-level parsers ----------
NODE_RE = re.compile(
    r'\{\s*rank\s*:=\s*(\d+),\s*op\s*:=\s*"OpName\.([A-Za-z0-9_]+)",\s*'
    r'ins\s*:=\s*\[([0-9,\s]*)\],\s*outs\s*:=\s*\[([0-9,\s]*)\]'
    r'(?:,\s*params\s*:=\s*\[([0-9,\s]*)\])?\s*\}'
)

def _ints(s):
    s = s.strip()
    return [int(x) for x in s.split(',') if x.strip()] if s else []

def parse_nodes(block: str):
    nodes = []
    for m in NODE_RE.finditer(block):
        rank, op, ins, outs, params = m.groups()
        nodes.append(Node(
            rank=int(rank), op=op,
            ins=_ints(ins), outs=_ints(outs),
            params=_ints(params) if params is not None else None,
        ))
    return nodes

def extract_def_block(text: str, def_name: str) -> str:
    """Grab the body of `def <def_name> ... := by exact [ ... ]` or `:= [...]`."""
    # find "def <name>" then capture until the next top-level "def " or EOF
    m = re.search(rf'def\s+{re.escape(def_name)}\b.*?(?=\ndef\s)', text, re.S)
    if not m:
        m = re.search(rf'def\s+{re.escape(def_name)}\b.*\Z', text, re.S)
    return m.group(0) if m else ""

def parse_shapes(block: str):
    """parse `(tid, [a, b, c]),` entries."""
    out = []
    for m in re.finditer(r'\(\s*(\d+),\s*\[([0-9,\s]*)\]\s*\)', block):
        tid = int(m.group(1)); shape = _ints(m.group(2))
        out.append((tid, shape))
    return out

def parse_lineage(gen_text: str, n: int) -> LineageGoal:
    blk = extract_def_block(gen_text, f"goal_{n}")
    # ts
    ts = int(re.search(r'ts\s*:=\s*(\d+)', blk).group(1))
    tsShape = _ints(re.search(r'tsShape\s*:=\s*\[([0-9,\s]*)\]', blk).group(1))
    # tps: list of { rank := r, tid := t }
    tps = [(int(r), int(t)) for r, t in
           re.findall(r'\{\s*rank\s*:=\s*(\d+),\s*tid\s*:=\s*(\d+)\s*\}', blk)]
    # tpShapes: list of [..]
    tpsh_m = re.search(r'tpShapes\s*:=\s*\[(.*?)\]\s*(?:,\s*gatherDim|\})', blk, re.S)
    tpShapes = []
    if tpsh_m:
        for sm in re.finditer(r'\[([0-9,\s]*)\]', tpsh_m.group(1)):
            tpShapes.append(_ints(sm.group(1)))
    gd_m = re.search(r'gatherDim\s*:=\s*(\d+)', blk)
    gatherDim = int(gd_m.group(1)) if gd_m else None
    return LineageGoal(ts=ts, tsShape=tsShape, tps=tps, tpShapes=tpShapes, gatherDim=gatherDim)

def parse_prereqs(goal_text: str, n: int):
    m = re.search(rf'def\s+goal_{n}_prereqs\s*:\s*List LineageGoal\s*:=\s*\[(.*?)\]', goal_text, re.S)
    if not m:
        return []
    return [int(x) for x in re.findall(r'goal_(\d+)', m.group(1))]

# ---------- top-level ----------
def load_goal_ir(n: int, root: str) -> GoalIR:
    goal_path = os.path.join(root, DENOTE_DIR, f"Goal_{n}.lean")
    gen_path  = os.path.join(root, DENOTE_DIR, "GeneratedData.lean")
    goal_text = open(goal_path).read()
    gen_text  = open(gen_path).read()

    sm_block = extract_def_block(goal_text, f"sm_goal_{n}")
    pm_block = extract_def_block(goal_text, f"pm_goal_{n}")
    sm_sh_block = extract_def_block(goal_text, f"sm_goal_{n}InitShapes")
    pm_sh_block = extract_def_block(goal_text, f"pm_goal_{n}InitShapes")

    return GoalIR(
        n=n,
        sm_nodes=parse_nodes(sm_block),
        pm_nodes=parse_nodes(pm_block),
        sm_shapes=parse_shapes(sm_sh_block),
        pm_shapes=parse_shapes(pm_sh_block),
        lineage=parse_lineage(gen_text, n),
        prereqs=parse_prereqs(goal_text, n),
    )

# ---------- topology ----------
@dataclass
class Topology:
    n: int
    single_tp: bool                 # True if 1 final tp, False if multi (4)
    final_tps: list                 # tids of final outputs (lineage order)
    pm_inputs: list                 # tids that are pm-graph inputs (InitShapes tids)
    mid_tids: list                  # intermediate tensor tids (need pm_full_*)
    op_layers: list                 # list of layer dicts (data-flow ordered)
    sm_out: int
    sm_op: str

def analyze(ir: GoalIR) -> Topology:
    final_tps = [t for (_, t) in ir.lineage.tps]
    pm_inputs = [tid for (tid, _) in ir.pm_shapes]
    pm_all_outs = [o for nd in ir.pm_nodes for o in nd.outs]
    final_set = set(final_tps)
    in_set = set(pm_inputs)
    # mid = produced by pm graph, not final, not input
    mid_tids = [o for o in pm_all_outs if o not in final_set and o not in in_set]
    # dedupe preserving order
    seen = set(); mid_tids = [x for x in mid_tids if not (x in seen or seen.add(x))]

    # group pm nodes into layers by op signature (collective vs per-rank)
    op_layers = []
    for nd in ir.pm_nodes:
        op_layers.append({
            "rank": nd.rank, "op": nd.op, "ins": nd.ins,
            "outs": nd.outs, "params": nd.params,
            "is_final": any(o in final_set for o in nd.outs),
            "is_mid": any(o in set(mid_tids) for o in nd.outs),
        })

    sm_node = ir.sm_nodes[0] if ir.sm_nodes else None
    return Topology(
        n=ir.n,
        single_tp=(len(final_tps) == 1),
        final_tps=final_tps,
        pm_inputs=pm_inputs,
        mid_tids=mid_tids,
        op_layers=op_layers,
        sm_out=(sm_node.outs[0] if sm_node else -1),
        sm_op=(sm_node.op if sm_node else "?"),
    )

# ---------- cli ----------
def main():
    n = int(sys.argv[1])
    root = os.path.expanduser("~/.openclaw/workspace/tainverify_lean")
    if "--root" in sys.argv:
        root = sys.argv[sys.argv.index("--root") + 1]
    ir = load_goal_ir(n, root)
    topo = analyze(ir)
    print("=== IR ===")
    print(f"goal_{n}")
    print(f"  sm_nodes: {[(nd.op, nd.ins, nd.outs, nd.params) for nd in ir.sm_nodes]}")
    print(f"  pm_nodes ({len(ir.pm_nodes)}):")
    for nd in ir.pm_nodes:
        print(f"    r{nd.rank} {nd.op} ins={nd.ins} outs={nd.outs} params={nd.params}")
    print(f"  sm_shapes: {ir.sm_shapes}")
    print(f"  pm_shapes: {ir.pm_shapes}")
    print(f"  lineage: ts={ir.lineage.ts} tsShape={ir.lineage.tsShape} "
          f"tps={ir.lineage.tps} gatherDim={ir.lineage.gatherDim}")
    print(f"  prereqs ({len(ir.prereqs)}): {ir.prereqs}")
    print("=== TOPOLOGY ===")
    print(f"  single_tp: {topo.single_tp}")
    print(f"  final_tps: {topo.final_tps}")
    print(f"  pm_inputs: {topo.pm_inputs}")
    print(f"  mid_tids ({len(topo.mid_tids)}): {topo.mid_tids}")
    print(f"  sm_out: {topo.sm_out} ({topo.sm_op})")
    print(f"  expected pm_full segments: {len(topo.mid_tids)}")
    print(f"  expected pm_frame/denote_pm segments: {len(topo.final_tps)}")

if __name__ == "__main__":
    main()
