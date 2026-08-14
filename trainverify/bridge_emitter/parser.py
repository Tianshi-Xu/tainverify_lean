#!/usr/bin/env python3
"""Bridge emitter — Phase 1: parser + topology analyzer.

Parses a goal's structured inputs from Goal_N.lean / GeneratedData.lean and
derives the bridge topology (single/multi tp, intermediate-tensor layers,
operator chain). NO Lean dependency — pure text parsing, unit-testable.

Usage:
    python3 parser.py <N> [--root <repo_root>]
prints a JSON-ish dump of the parsed IR + topology for goal N.
"""
import re, sys, os
from dataclasses import dataclass, field
from typing import Optional
sys.path.insert(0, os.path.dirname(__file__))
from target_config import DENOTE_DIR as _RELDIR, GEN_FILE

DENOTE_DIR = "trainverify/" + _RELDIR  # keep backward-compat absolute form

# Allow the generated-data file to live outside DENOTE_DIR (yoco keeps it in denote/,
# while gpt_ly4 keeps it in denote/gpt_ly4_regen/). BRIDGE_GEN_DIR (optional env var)
# overrides the directory; default is DENOTE_DIR.
import os as _os
GEN_DIR = _os.environ.get("BRIDGE_GEN_DIR", "trainverify/" + _RELDIR)

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
    replicated: bool = False

@dataclass
class GoalIR:
    n: int
    sm_nodes: list                # list[Node]
    pm_nodes: list                # list[Node]
    sm_shapes: list               # list[(tid, shape)]
    pm_shapes: list               # list[(tid, shape)]
    lineage: LineageGoal
    prereqs: list                 # list[int]
    sm_num_ranks: int = 1
    pm_num_ranks: int = 1
    init_lineages: dict[int, LineageGoal] = field(default_factory=dict)
    full_init_goal_ids: tuple[int, ...] = ()

# ---------- low-level parsers ----------
NODE_FIELD_RE = re.compile(
    r'\b(rank|op|ins|outs|params)\s*:=\s*("[^"]*"|\[[^\]]*\]|\d+)'
)

def _ints(s):
    s = s.strip()
    return [int(x) for x in s.split(',') if x.strip()] if s else []

def parse_nodes(block: str):
    nodes_header = re.search(r"\bnodes\s*:=\s*\[", block)
    if nodes_header is None:
        placeholder = re.search(r"\bnodes\s*:=\s*\?_", block)
        if placeholder is None:
            raise ValueError("graph declaration has no nodes list")
        nodes_header = re.search(r"\bexact\s*\[", block[placeholder.end():])
        if nodes_header is None:
            raise ValueError("graph nodes placeholder has no exact list")
        list_start = placeholder.end() + nodes_header.end() - 1
    else:
        list_start = nodes_header.end() - 1
    depth = 0
    list_end = None
    for index in range(list_start, len(block)):
        if block[index] == "[":
            depth += 1
        elif block[index] == "]":
            depth -= 1
            if depth == 0:
                list_end = index
                break
    if list_end is None:
        raise ValueError("unterminated graph nodes list")
    source = block[list_start + 1:list_end]
    nodes = []
    position = 0
    while position < len(source):
        separator = re.match(r"[\s,]*", source[position:])
        assert separator is not None
        position += separator.end()
        if position == len(source):
            break
        if source[position] != "{":
            raise ValueError(f"unparsed graph node text at offset {position}")
        record_end = source.find("}", position + 1)
        if record_end < 0:
            raise ValueError("unterminated graph node record")
        record = source[position + 1:record_end]
        fields = {}
        consumed = []
        for match in NODE_FIELD_RE.finditer(record):
            name, value = match.groups()
            if name in fields:
                raise ValueError(f"duplicate graph node field {name}")
            fields[name] = value
            consumed.append(match.span())
        residue_parts = []
        cursor = 0
        for start, end in consumed:
            residue_parts.append(record[cursor:start])
            cursor = end
        residue_parts.append(record[cursor:])
        if re.sub(r"[\s,]", "", "".join(residue_parts)):
            raise ValueError("unparsed or unknown graph node field")
        missing = {"rank", "op", "ins", "outs"} - fields.keys()
        if missing:
            raise ValueError(f"graph node is missing fields {sorted(missing)}")
        op_match = re.fullmatch(r'"OpName\.([A-Za-z0-9_]+)"', fields["op"])
        if op_match is None:
            raise ValueError("graph node op is not an OpName literal")
        list_values = {}
        for name in ("ins", "outs", "params"):
            if name not in fields:
                continue
            value_match = re.fullmatch(r"\[([0-9,\s]*)\]", fields[name])
            if value_match is None:
                raise ValueError(f"graph node {name} is not a Nat list literal")
            list_values[name] = _ints(value_match.group(1))
        nodes.append(Node(
            rank=int(fields["rank"]), op=op_match.group(1),
            ins=list_values["ins"], outs=list_values["outs"],
            params=list_values.get("params"),
        ))
        position = record_end + 1
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


def parse_num_ranks(block: str, graph_name: str) -> int:
    match = re.search(r"numRanks\s*:=\s*(\d+)", block)
    if match is None:
        raise ValueError(f"{graph_name} has no literal numRanks header")
    return int(match.group(1))

def parse_lineage_block(blk: str, name: str) -> LineageGoal:
    if not blk:
        raise ValueError(f"missing lineage definition {name}")
    # ts
    ts_match = re.search(r'ts\s*:=\s*(\d+)', blk)
    shape_match = re.search(r'tsShape\s*:=\s*\[([0-9,\s]*)\]', blk)
    if ts_match is None or shape_match is None:
        raise ValueError(f"malformed lineage definition {name}")
    ts = int(ts_match.group(1))
    tsShape = _ints(shape_match.group(1))
    # tps: list of { rank := r, tid := t }
    tps = [(int(r), int(t)) for r, t in
           re.findall(r'\{\s*rank\s*:=\s*(\d+),\s*tid\s*:=\s*(\d+)\s*\}', blk)]
    # tpShapes: list of [..]
    tpsh_m = re.search(
        r'tpShapes\s*:=\s*\[(.*?)\]\s*(?:,\s*gatherDim|,\s*replicated|\})',
        blk,
        re.S,
    )
    tpShapes = []
    if tpsh_m:
        for sm in re.finditer(r'\[([0-9,\s]*)\]', tpsh_m.group(1)):
            tpShapes.append(_ints(sm.group(1)))
    gd_m = re.search(r'gatherDim\s*:=\s*(\d+)', blk)
    gatherDim = int(gd_m.group(1)) if gd_m else None
    replicated_m = re.search(r'replicated\s*:=\s*(true|false)', blk)
    replicated = replicated_m is not None and replicated_m.group(1) == "true"
    return LineageGoal(
        ts=ts,
        tsShape=tsShape,
        tps=tps,
        tpShapes=tpShapes,
        gatherDim=gatherDim,
        replicated=replicated,
    )


def parse_lineage(gen_text: str, n: int) -> LineageGoal:
    return parse_lineage_block(extract_def_block(gen_text, f"goal_{n}"), f"goal_{n}")


def parse_full_init_goal_ids(goal_text: str, gen_text: str, n: int) -> tuple[int, ...]:
    full_block = extract_def_block(goal_text, f"goal_{n}_full_initGoals")
    if re.search(r":=\s*initGoals\b", full_block):
        source = extract_def_block(gen_text, "initGoals")
    else:
        source = full_block
    return tuple(int(value) for value in re.findall(r"initGoal_(\d+)", source))

def parse_prereqs(goal_text: str, n: int):
    m = re.search(rf'def\s+goal_{n}_prereqs\s*:\s*List LineageGoal\s*:=\s*\[(.*?)\]', goal_text, re.S)
    if not m:
        return []
    # Match both `goal_5` (gpt_ly4 convention) and `intermediateGoal_5930` (yoco
    # convention) as prereq references. Skip `initGoal_XXX` (those are always in
    # `initGoals` at the graph level, never in the per-goal prereq list).
    return [int(x) for x in re.findall(r'(?:^|[\s,\[])(?:intermediate)?[Gg]oal_(\d+)', m.group(1))]

# ---------- top-level ----------
def load_goal_ir(n: int, root: str) -> GoalIR:
    goal_path = os.path.join(root, DENOTE_DIR, f"Goal_{n}.lean")
    gen_path  = os.path.join(root, GEN_DIR, GEN_FILE)
    goal_text = open(goal_path).read()
    gen_text  = open(gen_path).read()

    sm_block = extract_def_block(goal_text, f"sm_goal_{n}")
    pm_block = extract_def_block(goal_text, f"pm_goal_{n}")
    sm_sh_block = extract_def_block(goal_text, f"sm_goal_{n}InitShapes")
    pm_sh_block = extract_def_block(goal_text, f"pm_goal_{n}InitShapes")

    full_init_goal_ids = parse_full_init_goal_ids(goal_text, gen_text, n)
    needed_init_tids = {
        int(tid) for node in parse_nodes(sm_block) for tid in node.ins
    }
    init_lineages = {
        tid: parse_lineage_block(
            extract_def_block(gen_text, f"initGoal_{tid}"), f"initGoal_{tid}"
        )
        for tid in sorted(needed_init_tids & set(full_init_goal_ids))
    }
    return GoalIR(
        n=n,
        sm_nodes=parse_nodes(sm_block),
        pm_nodes=parse_nodes(pm_block),
        sm_shapes=parse_shapes(sm_sh_block),
        pm_shapes=parse_shapes(pm_sh_block),
        lineage=parse_lineage(gen_text, n),
        prereqs=parse_prereqs(goal_text, n),
        sm_num_ranks=parse_num_ranks(sm_block, f"sm_goal_{n}"),
        pm_num_ranks=parse_num_ranks(pm_block, f"pm_goal_{n}"),
        init_lineages=init_lineages,
        full_init_goal_ids=full_init_goal_ids,
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
    root = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
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
