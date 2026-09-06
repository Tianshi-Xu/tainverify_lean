#!/usr/bin/env python3
"""Bridge emitter — Phase 1: parser + topology analyzer.

Parses a goal's structured inputs from Goal_N.lean / GeneratedData.lean and
derives the bridge topology (single/multi tp, intermediate-tensor layers,
operator chain). NO Lean dependency — pure text parsing, unit-testable.

Usage:
    python3 parser.py <N> [--root <repo_root>]
prints a JSON-ish dump of the parsed IR + topology for goal N.
"""
import ast
import os
import re
import sys
from dataclasses import dataclass, field
from typing import TYPE_CHECKING

if TYPE_CHECKING:
    from .parallel_authority import ParallelGraphAuthority

sys.path.insert(0, os.path.dirname(__file__))
from target_config import DENOTE_DIR as _RELDIR
from target_config import GEN_FILE, MOD_PREFIX

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
    params: list | None = None # list[int] or None

@dataclass
class LineageGoal:
    ts: int
    tsShape: list
    tps: list            # list[(rank, tid)]
    tpShapes: list
    gatherDim: int | None = None
    replicated: bool = False

@dataclass(frozen=True)
class ReplicaNodeRef:
    rank: int
    primary_out_tid: int


@dataclass(frozen=True)
class ReplicaGroup:
    cid: int
    mb: int
    irname: str
    members: tuple[ReplicaNodeRef, ...]


@dataclass(frozen=True)
class InputValueClass:
    source: str
    tids: tuple[int, ...]


@dataclass(frozen=True)
class PackedCuContract:
    side: str
    tid: int
    total_tokens: int
    num_ranks: int


@dataclass(frozen=True)
class TensorValueBoundContract:
    side: str
    tid: int
    length: int
    upper_bound: int


@dataclass(frozen=True)
class AdapterCommunication:
    rank: int
    primary_out_tid: int
    op: str
    ranks: tuple[int, ...]
    inputs: tuple[tuple[int, int], ...]


def parse_adapter_communications(source: str, name: str) -> tuple[AdapterCommunication, ...] | None:
    """Read the literal capture tuple format, not arbitrary Lean/Python code.

    None means absent authority; () means an explicit assertion of no adapters.
    Only the wire subset shared by Lean literals and Python literal_eval is used.
    """
    declarations = re.findall(rf"(?m)^\s*def\s+{re.escape(name)}\s*:", source)
    if not declarations:
        return None
    if len(declarations) != 1:
        raise ValueError(f"ambiguous adapter communication declaration: {name}")
    block = extract_def_block(source, name)
    try:
        raw = ast.literal_eval(block.split(":=", 1)[1].strip())
    except (ValueError, SyntaxError, IndexError) as exc:
        raise ValueError(f"{name} requires literal adapter communication tuples") from exc
    if type(raw) is not list:
        raise ValueError(f"{name} requires a literal list")
    result = []
    for row in raw:
        if type(row) is not tuple or len(row) != 5:
            raise ValueError("adapter communication needs rank, output, op, ranks, inputs")
        rank, output, op, ranks, inputs = row
        if type(op) is not str or type(ranks) is not list or type(inputs) is not list:
            raise ValueError("invalid adapter communication field types")
        if any(type(pair) is not tuple or len(pair) != 2 for pair in inputs):
            raise ValueError("adapter inputs require literal (rank, tid) pairs")
        numbers = [rank, output, *ranks, *(v for pair in inputs for v in pair)]
        if any(type(v) is not int or v < 0 for v in numbers):
            raise ValueError("adapter rank/tid values must be natural integers, not bool")
        result.append(AdapterCommunication(rank, output, op, tuple(ranks), tuple(inputs)))
    return tuple(result)


@dataclass
class GoalIR:
    n: int
    sm_nodes: list                # list[Node]
    pm_nodes: list                # list[Node]
    sm_shapes: list               # list[(tid, shape)]
    pm_shapes: list               # list[(tid, shape)]
    lineage: LineageGoal
    prereqs: list                 # list[int]
    sm_graph_ref: str = ""
    pm_graph_ref: str = ""
    public_statement_module: str = ""
    public_statement_ref: str = ""
    public_statement_uses_contract_wrapper: bool = True
    public_statement_contract_ref: str = ""
    public_statement_uses_faithful_evaluator: bool = False
    lineage_ref: str = ""
    init_goals_ref: str = ""
    sm_num_ranks: int = 1
    pm_num_ranks: int = 1
    sm_replica_groups: tuple[ReplicaGroup, ...] = ()
    pm_replica_groups: tuple[ReplicaGroup, ...] = ()
    packed_cu_contracts: tuple[PackedCuContract, ...] = ()
    tensor_value_bound_contracts: tuple[TensorValueBoundContract, ...] = ()
    sm_input_value_classes: tuple[InputValueClass, ...] = ()
    pm_input_value_classes: tuple[InputValueClass, ...] = ()
    sm_input_value_classes_ref: str = ""
    pm_input_value_classes_ref: str = ""
    init_lineages: dict[int, LineageGoal] = field(default_factory=dict)
    full_init_goal_ids: tuple[int, ...] = ()
    parallel_authority: "ParallelGraphAuthority | None" = None
    sm_adapter_communications: tuple[AdapterCommunication, ...] | None = None
    pm_adapter_communications: tuple[AdapterCommunication, ...] | None = None

# ---------- low-level parsers ----------
RANGE_MAP_VALUE_RE = (
    r"\(\(List\.range\s+\d+\)\.map\s+"
    r"\(fun\s+[A-Za-z_][A-Za-z0-9_]*\s*=>\s*\d+\s*\+\s*"
    r"[A-Za-z_][A-Za-z0-9_]*\)\)"
)
NODE_FIELD_RE = re.compile(
    rf'\b(rank|op|ins|outs|params)\s*:=\s*("[^"]*"|\[[^\]]*\]|{RANGE_MAP_VALUE_RE}|\d+)'
)

def _ints(s):
    s = s.strip()
    return [int(x) for x in s.split(',') if x.strip()] if s else []

def _balanced_region(source: str, start: int, opening: str, closing: str) -> tuple[str, int]:
    if start >= len(source) or source[start] != opening:
        raise ValueError(f"expected {opening!r} at offset {start}")
    depth = 0
    in_string = False
    escaped = False
    for index in range(start, len(source)):
        char = source[index]
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            continue
        if char == '"':
            in_string = True
        elif char == opening:
            depth += 1
        elif char == closing:
            depth -= 1
            if depth == 0:
                return source[start + 1:index], index + 1
    raise ValueError(f"unterminated {opening}{closing} region")


def _record_list(source: str, context: str) -> tuple[str, ...]:
    records = []
    position = 0
    while position < len(source):
        separator = re.match(r"[\s,]*", source[position:])
        assert separator is not None
        position += separator.end()
        if position == len(source):
            break
        if source[position] != "{":
            raise ValueError(f"unparsed {context} text at offset {position}")
        record, position = _balanced_region(source, position, "{", "}")
        records.append(record)
    return tuple(records)


def parse_replica_groups(block: str) -> tuple[ReplicaGroup, ...]:
    match = re.search(r"\breplicaGroups\s*:=\s*\[", block)
    if match is None:
        return ()
    source, _end = _balanced_region(block, match.end() - 1, "[", "]")
    groups = []
    for record in _record_list(source, "replica group"):
        logical = re.search(
            r'\blogical\s*:=\s*\{\s*cid\s*:=\s*(\d+)\s*,\s*mb\s*:=\s*(\d+)\s*,\s*irname\s*:=\s*"([^"]*)"\s*\}',
            record,
        )
        members_match = re.search(r"\bmembers\s*:=\s*\[", record)
        if logical is None or members_match is None:
            raise ValueError("replica group lacks logical identity or members")
        member_source, member_end = _balanced_region(record, members_match.end() - 1, "[", "]")
        trailing = record[member_end:].strip()
        if trailing:
            raise ValueError(f"unparsed replica group suffix: {trailing!r}")
        members = []
        for member in _record_list(member_source, "replica member"):
            parsed = re.fullmatch(
                r'\s*rank\s*:=\s*(\d+)\s*,\s*primaryOutTid\s*:=\s*(\d+)\s*',
                member,
            )
            if parsed is None:
                raise ValueError(f"malformed replica member: {member!r}")
            members.append(ReplicaNodeRef(int(parsed.group(1)), int(parsed.group(2))))
        if not members:
            raise ValueError("replica group has no members")
        groups.append(ReplicaGroup(
            cid=int(logical.group(1)),
            mb=int(logical.group(2)),
            irname=logical.group(3),
            members=tuple(members),
        ))
    return tuple(groups)


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
            if value_match is not None:
                list_values[name] = _ints(value_match.group(1))
                continue
            range_match = re.fullmatch(
                r"\(\(List\.range\s+(\d+)\)\.map\s+"
                r"\(fun\s+([A-Za-z_][A-Za-z0-9_]*)\s*=>\s*(\d+)\s*\+\s*"
                r"([A-Za-z_][A-Za-z0-9_]*)\)\)",
                fields[name],
            )
            if name != "ins" or range_match is None or range_match.group(2) != range_match.group(4):
                raise ValueError(f"graph node {name} is not a supported Nat list expression")
            count = int(range_match.group(1))
            base = int(range_match.group(3))
            list_values[name] = [base + offset for offset in range(count)]
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
    m = re.search(rf'def\s+{re.escape(def_name)}\b.*?(?=\ndef\s)', text, re.DOTALL)
    if not m:
        m = re.search(rf'def\s+{re.escape(def_name)}\b.*\Z', text, re.DOTALL)
    return m.group(0) if m else ""

def parse_shapes(block: str):
    """Parse a complete literal `(tid, shape)` authority list."""
    assignment = re.search(r":=\s*(?:by\s+exact\s*)?\[", block)
    if assignment is None:
        raise ValueError("shape authority has no literal list")
    source, end = _balanced_region(block, assignment.end() - 1, "[", "]")
    if block[end:].strip():
        raise ValueError("unparsed shape authority suffix")
    matches = list(re.finditer(r'\(\s*(\d+),\s*\[([0-9,\s]*)\]\s*\)', source))
    residue = []
    cursor = 0
    for match in matches:
        residue.append(source[cursor:match.start()])
        cursor = match.end()
    residue.append(source[cursor:])
    if re.sub(r"[\s,]", "", "".join(residue)):
        raise ValueError("unparsed shape authority entry")
    out = [(int(match.group(1)), _ints(match.group(2))) for match in matches]
    tids = [tid for tid, _shape in out]
    if len(tids) != len(set(tids)):
        raise ValueError("shape authority contains duplicate TID")
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
    if re.search(r"\btps\s*:=\s*\[", blk) is None:
        raise ValueError(f"lineage definition {name} is missing tps authority")
    tps = [(int(r), int(t)) for r, t in
           re.findall(r'\{\s*rank\s*:=\s*(\d+),\s*tid\s*:=\s*(\d+)\s*\}', blk)]
    # tpShapes: list of [..]
    tpsh_m = re.search(
        r'tpShapes\s*:=\s*\[(.*?)\]\s*(?:,\s*gatherDim|,\s*replicated|\})',
        blk,
        re.DOTALL,
    )
    if tpsh_m is None:
        raise ValueError(f"lineage definition {name} is missing tpShapes authority")
    tpShapes = [
        _ints(sm.group(1))
        for sm in re.finditer(r'\[([0-9,\s]*)\]', tpsh_m.group(1))
    ]
    if not tps:
        raise ValueError(f"lineage definition {name} has empty tps authority")
    if len(tps) != len(tpShapes):
        raise ValueError(f"lineage definition {name} tps/tpShapes cardinality mismatch")
    ranks = [rank for rank, _tid in tps]
    if len(ranks) != len(set(ranks)):
        raise ValueError(f"lineage definition {name} contains duplicate ranks")
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


def public_statement_name(statement_text: str, n: int) -> str:
    """Resolve the exact exported statement, preferring the modern full name."""
    for name in (f"goal_{n}_stmt_full", f"goal_{n}_stmt"):
        if re.search(rf"\bdef\s+{re.escape(name)}\s*:", statement_text):
            return name
    raise ValueError(f"cannot resolve exported statement for goal {n}")


def parse_full_init_goal_ids(goal_text: str, gen_text: str, n: int) -> tuple[int, ...]:
    try:
        full_block = extract_def_block(goal_text, f"goal_{n}_full_initGoals")
    except ValueError:
        full_block = ""
    try:
        statement_name = public_statement_name(goal_text, n)
    except ValueError:
        statement_block = ""
    else:
        statement_block = extract_def_block(goal_text, statement_name)
    direct_generated = re.search(
        r"CoarseLineageHoldsWithInit(?:DistributedFaithful(?:WithContract)?)?[^\n]*\binitGoals\b",
        statement_block,
    ) or re.search(r"InitGoalsHold[^\n]*\binitGoals\b", statement_block)
    if re.search(r":=\s*(?:[A-Za-z_][A-Za-z0-9_.]*\.)?initGoals\b", full_block) or direct_generated:
        source = extract_def_block(gen_text, "initGoals")
    else:
        source = full_block
    return tuple(int(value) for value in re.findall(r"initGoal_(\d+)", source))

def parse_full_init_goals_name(statement_text: str, n: int) -> str:
    """Recover the exact init-goal list consumed by the exported full statement."""
    block = extract_def_block(statement_text, public_statement_name(statement_text, n))
    direct = re.search(
        r"InitGoalsHold\s+\S+\s+([A-Za-z_][A-Za-z0-9_.]*)\b", block
    )
    compact = re.search(
        r"CoarseLineageHoldsWithInit(?:DistributedFaithful(?:WithContract)?)?"
        r"(?:\s+\S+){5}\s+([A-Za-z_][A-Za-z0-9_.]*)\b",
        block,
    )
    matches = [match.group(1) for match in (direct, compact) if match is not None]
    if len(matches) != 1:
        raise ValueError(
            f"goal_{n}_stmt_full must expose exactly one init-goal list, found {matches}"
        )
    return matches[0]


def parse_public_statement_contract_ref(statement_text: str, n: int) -> str:
    """Return an explicit named external-contract premise, if present."""
    block = extract_def_block(statement_text, public_statement_name(statement_text, n))
    for match in re.finditer(
        r"(?m)^\s*([A-Za-z_][A-Za-z0-9_'.]*)\s+initSM\s+initPM\s*→\s*$",
        block,
    ):
        name = match.group(1).rsplit(".", 1)[-1]
        try:
            contract = _definition_from_sources(name, statement_text)
        except ValueError:
            continue
        if re.search(
            rf"def\s+{re.escape(name)}\s*\(initSM\s+initPM\s*:\s*Store\)\s*:\s*Prop\s*:=",
            contract,
        ):
            return _qualified_definition_name(name, statement_text)
    constructor = re.search(
        r"\bCoarseLineageHoldsWithInitDistributedFaithfulWithContract\b(.*)",
        block,
        re.DOTALL,
    )
    if constructor is not None:
        names = re.findall(r"[A-Za-z_][A-Za-z0-9_'.]*", constructor.group(1))
        for candidate in reversed(names):
            name = candidate.rsplit(".", 1)[-1]
            try:
                contract = _definition_from_sources(name, statement_text)
            except ValueError:
                continue
            if re.search(
                rf"def\s+{re.escape(name)}\s*\(initSM\s+initPM\s*:\s*Store\)\s*:\s*Prop\s*:=",
                contract,
            ):
                return _qualified_definition_name(name, statement_text)
    return ""


def parse_input_value_classes_ref(
    statement_text: str, n: int, side: str, *sources: str
) -> str:
    """Resolve the exact value-class list named by the public caller contract."""
    if side not in {"sm", "pm"}:
        raise ValueError(f"invalid input-value class side: {side!r}")
    contract_ref = parse_public_statement_contract_ref(statement_text, n)
    if not contract_ref:
        return ""
    contract_name = contract_ref.rsplit(".", 1)[-1]
    contract = _definition_from_sources(contract_name, statement_text)
    store = "initSM" if side == "sm" else "initPM"
    class_name = f"{side}InputValueClasses"
    matches = re.findall(
        rf"InputValueClassesHold\s+([A-Za-z_][A-Za-z0-9_'.]*{class_name}|{class_name})\s+{store}\b",
        contract,
    )
    if len(matches) != 1:
        raise ValueError(
            f"{contract_ref} must name exactly one {side.upper()} input-value class list"
        )
    ref = matches[0]
    if "." not in ref:
        ref = _qualified_definition_name(ref, *sources)
    return ref


def parse_prereqs(goal_text: str, n: int):
    m = re.search(rf'def\s+goal_{n}_prereqs\s*:\s*List LineageGoal\s*:=\s*\[(.*?)\]', goal_text, re.DOTALL)
    if not m:
        return []
    # Match both `goal_5` (gpt_ly4 convention) and `intermediateGoal_5930` (yoco
    # convention) as prereq references. Skip `initGoal_XXX` (those are always in
    # `initGoals` at the graph level, never in the per-goal prereq list).
    return [int(x) for x in re.findall(r'(?:^|[\s,\[])(?:intermediate)?[Gg]oal_(\d+)', m.group(1))]

# ---------- top-level ----------
def _public_full_scope(n: int, goal_path: str, goal_text: str, gen_text: str) -> tuple[str, str, str, str, str, str, str, str, str]:
    """Resolve graph and shape-list symbols from the exported full proposition."""
    statement_name = f"goal_{n}_stmt_full"
    candidates: list[tuple[str, str]] = []
    goal_dir = os.path.dirname(goal_path)
    for filename in sorted(os.listdir(goal_dir)):
        if not filename.endswith(".lean"):
            continue
        path = os.path.join(goal_dir, filename)
        if path == goal_path:
            text = goal_text
        else:
            with open(path) as handle:
                text = handle.read()
        if re.search(rf"\bdef\s+{re.escape(statement_name)}\s*:", text):
            candidates.append((path, text))
    if not candidates and re.search(rf"\bdef\s+goal_{n}_stmt\s*:", gen_text):
        candidates.append(("<generated>", gen_text))
        statement_name = f"goal_{n}_stmt"
    if len(candidates) != 1:
        raise ValueError(
            f"expected exactly one exported {statement_name} definition, found {len(candidates)}"
        )
    _statement_path, statement_text = candidates[0]
    if _statement_path == "<generated>":
        relative = GEN_DIR.removeprefix("trainverify/").strip("/").replace("/", ".")
        statement_module = relative + "." + os.path.splitext(GEN_FILE)[0]
    else:
        statement_module = MOD_PREFIX + "." + os.path.splitext(os.path.basename(_statement_path))[0]
    return _public_scope_from_statement(statement_text, statement_module, statement_name)


def _public_scope_from_statement(
    statement_text: str, statement_module: str, statement_name: str
) -> tuple[str, str, str, str, str, str, str, str, str]:
    """Resolve graph/shape authority from one already-inventoried statement."""
    statement_block = extract_def_block(statement_text, statement_name)

    compact = re.search(
        r"CoarseLineageHoldsWithInit(?:DistributedFaithful(?:WithContract)?)?\s+"
        r"([A-Za-z0-9_.]+)\s+([A-Za-z0-9_.]+)\s+"
        r"[A-Za-z0-9_.]+\s+([A-Za-z0-9_.]+)\s+([A-Za-z0-9_.]+)",
        statement_block,
    )
    if compact is not None:
        sm_name, pm_name, sm_env_name, pm_env_name = compact.groups()
    else:
        def one(pattern: str, label: str) -> str:
            matches = re.findall(pattern, statement_block)
            unique = list(dict.fromkeys(matches))
            if len(unique) != 1:
                raise ValueError(f"cannot uniquely resolve {label} from {statement_name}")
            return unique[0]

        sm_env_name = one(r"StoreShapesHold\s+initSM\s+([A-Za-z0-9_.]+)", "SM shape env")
        pm_env_name = one(r"StoreShapesHold\s+initPM\s+([A-Za-z0-9_.]+)", "PM shape env")
        sm_name = one(
            r"denoteGraphDistributedFaithful\s+([A-Za-z0-9_.]+)\s+initSM",
            "SM graph",
        )
        pm_name = one(
            r"denoteGraphDistributedFaithful\s+([A-Za-z0-9_.]+)\s+initPM",
            "PM graph",
        )

    def basename(name: str) -> str:
        return name.rsplit(".", 1)[-1]

    def shape_list_name(env_name: str) -> str:
        base = basename(env_name)
        if not base.endswith("Env"):
            raise ValueError(f"shape environment {env_name} does not end in Env")
        return base[:-3] + "Shapes"

    return (
        statement_text,
        statement_module,
        sm_name,
        pm_name,
        basename(sm_name),
        basename(pm_name),
        shape_list_name(sm_env_name),
        shape_list_name(pm_env_name),
        statement_name,
    )


def _qualified_definition_name(name: str, *sources: str) -> str:
    """Resolve a referenced definition to the namespace that actually declares it."""
    base = name.rsplit(".", 1)[-1]
    matches = []
    pattern = re.compile(
        rf"(?m)^\s*(?:(?:private|noncomputable)\s+)*def\s+{re.escape(base)}\b"
    )
    for source in sources:
        for found in pattern.finditer(source):
            namespaces = re.findall(r"(?m)^\s*namespace\s+([A-Za-z0-9_.]+)\s*$", source[:found.start()])
            qualifier = namespaces[-1] if namespaces else ""
            matches.append(f"{qualifier}.{base}" if qualifier else base)
    unique = list(dict.fromkeys(matches))
    if len(unique) != 1:
        raise ValueError(f"cannot uniquely qualify definition {name}: {unique}")
    return unique[0]


def _definition_from_sources(name: str, *sources: str) -> str:
    matches = []
    seen_sources: set[str] = set()
    header = re.compile(
        rf"(?m)^(?:(?:private|noncomputable)\s+)*def\s+"
        rf"{re.escape(name)}(?=\s*[:(])"
    )
    next_def = re.compile(r"(?m)^(?:(?:private|noncomputable)\s+)*def\s+")
    for source in sources:
        if source in seen_sources:
            continue
        seen_sources.add(source)
        starts = list(header.finditer(source))
        for match in starts:
            following = next_def.search(source, match.end())
            end = following.start() if following is not None else len(source)
            matches.append(source[match.start():end])
    if len(matches) != 1:
        raise ValueError(f"cannot uniquely resolve definition {name}: found {len(matches)}")
    return matches[0]


def parse_packed_cu_contracts(statement_text: str, *sources: str) -> tuple[PackedCuContract, ...]:
    match = re.search(
        r"CoarseLineageHoldsWithInitDistributedFaithfulWithContract"
        r"\s+\S+\s+\S+\s+\S+\s+\S+\s+\S+\s+\S+\s+([A-Za-z_][A-Za-z0-9_'.]*)",
        statement_text,
    )
    if match is None:
        # Some public theorems spell out the contract as an explicit forall
        # implication rather than using the WithContract wrapper.  In that
        # form the exported statement file itself is the authority.
        contract_block = statement_text
    else:
        contract_name = match.group(1).split(".")[-1]
        contract_block = _definition_from_sources(contract_name, *sources)
    facts = []
    seen = set()
    for fact in re.finditer(
        r"PackedCuSeqlensWF\s+\(init(SM|PM)\s+(\d+)\)\s+(\d+)\s+(\d+)",
        contract_block,
    ):
        item = PackedCuContract(
            side=fact.group(1).lower(),
            tid=int(fact.group(2)),
            total_tokens=int(fact.group(3)),
            num_ranks=int(fact.group(4)),
        )
        key = (item.side, item.tid, item.total_tokens, item.num_ranks)
        if key not in seen:
            facts.append(item)
            seen.add(key)
    return tuple(facts)


def parse_tensor_value_bound_contracts(
    statement_text: str, *sources: str
) -> tuple[TensorValueBoundContract, ...]:
    """Extract public `scalarToNat (valAt ...) < upper` contracts."""
    match = re.search(
        r"CoarseLineageHoldsWithInitDistributedFaithfulWithContract"
        r"\s+\S+\s+\S+\s+\S+\s+\S+\s+\S+\s+\S+\s+([A-Za-z_][A-Za-z0-9_'.]*)",
        statement_text,
    )
    contract_block = statement_text if match is None else _definition_from_sources(
        match.group(1).split(".")[-1], *sources
    )
    facts = []
    seen = set()
    pattern = re.compile(
        r"∀\s+([A-Za-z_][A-Za-z0-9_]*)\s*<\s*(\d+)\s*,\s*"
        r"scalarToNat\s*\(valAt\s+\(init(SM|PM)\s+(\d+)\)\s+\1\)\s*<\s*(\d+)"
    )
    for fact in pattern.finditer(contract_block):
        item = TensorValueBoundContract(
            side=fact.group(3).lower(), tid=int(fact.group(4)),
            length=int(fact.group(2)), upper_bound=int(fact.group(5)),
        )
        key = (item.side, item.tid, item.length, item.upper_bound)
        if key not in seen:
            facts.append(item)
            seen.add(key)
    return tuple(facts)


def parse_input_value_classes(
    *sources: str, name: str, required: bool = True
) -> tuple[InputValueClass, ...]:
    try:
        block = _definition_from_sources(name, *sources)
    except ValueError as exc:
        if not required and str(exc).endswith("found 0"):
            return ()
        raise
    entry_re = re.compile(
        r'\{\s*source\s*:=\s*"([^"\n]+)"\s*,\s*tids\s*:=\s*\[([0-9,\s]+)\]\s*\}',
        re.DOTALL,
    )
    matches = list(entry_re.finditer(block))
    declared_count = len(re.findall(r"\bsource\s*:=", block))
    if declared_count != len(matches):
        raise ValueError(f"{name}: malformed or unconsumed InputValueClass entry")
    result = []
    seen_sources = set()
    for match in matches:
        source = match.group(1)
        tids = tuple(int(value) for value in re.findall(r"\d+", match.group(2)))
        if source in seen_sources or not tids or len(set(tids)) != len(tids):
            raise ValueError(f"{name}: duplicate source or malformed tid list")
        seen_sources.add(source)
        result.append(InputValueClass(source=source, tids=tids))
    return tuple(result)


def load_goal_ir(n: int, root: str) -> GoalIR:
    goal_path = os.path.join(root, DENOTE_DIR, f"Goal_{n}.lean")
    gen_path = os.path.join(root, GEN_DIR, GEN_FILE)
    with open(gen_path) as handle:
        gen_text = handle.read()
    if os.path.isfile(goal_path):
        with open(goal_path) as handle:
            goal_text = handle.read()
    elif re.search(rf"\bdef\s+goal_{n}_stmt\s*:", gen_text):
        # A generated-only whole-graph authority needs no redundant Goal_N
        # wrapper. Treat the generated module as the exact public scope.
        goal_path = gen_path
        goal_text = gen_text
    else:
        raise FileNotFoundError(goal_path)
    nodes_path = os.path.join(os.path.dirname(gen_path), "GeneratedGraphNodes.lean")
    nodes_text = ""
    if os.path.exists(nodes_path):
        with open(nodes_path) as handle:
            nodes_text = handle.read()

    (
        statement_text, public_statement_module, sm_graph_ref, pm_graph_ref,
        sm_name, pm_name, sm_shapes_name, pm_shapes_name, statement_name,
    ) = _public_full_scope(n, goal_path, goal_text, gen_text)
    sources = (goal_text, statement_text, gen_text, nodes_text)
    sm_block = _definition_from_sources(sm_name, *sources)
    pm_block = _definition_from_sources(pm_name, *sources)
    sm_sh_block = _definition_from_sources(sm_shapes_name, *sources)
    pm_sh_block = _definition_from_sources(pm_shapes_name, *sources)

    scope_text = goal_text + "\n" + statement_text
    packed_cu_contracts = parse_packed_cu_contracts(statement_text, *sources)
    tensor_value_bound_contracts = parse_tensor_value_bound_contracts(statement_text, *sources)
    sm_input_value_classes = parse_input_value_classes(
        *sources,
        name="smInputValueClasses",
        required="smInputValueClasses" in statement_text,
    )
    pm_input_value_classes = parse_input_value_classes(
        *sources,
        name="pmInputValueClasses",
        required="pmInputValueClasses" in statement_text,
    )
    full_init_goal_ids = parse_full_init_goal_ids(scope_text, gen_text, n)

    def graph_nodes(block: str):
        try:
            return parse_nodes(block)
        except ValueError as inline_error:
            reference = re.search(r"\bnodes\s*:=\s*([A-Za-z_][A-Za-z0-9_.]*)", block)
            if reference is None:
                raise inline_error
            definition = _definition_from_sources(reference.group(1), nodes_text)
            assignment = definition.find(":=")
            if assignment < 0:
                raise ValueError(f"node payload {reference.group(1)} has no assignment")
            return parse_nodes("nodes := " + definition[assignment + 2:])

    sm_nodes_parsed = graph_nodes(sm_block)
    pm_nodes_parsed = graph_nodes(pm_block)
    needed_init_tids = {
        int(tid) for node in sm_nodes_parsed for tid in node.ins
    }
    init_lineages = {
        tid: parse_lineage_block(
            extract_def_block(gen_text, f"initGoal_{tid}"), f"initGoal_{tid}"
        )
        for tid in sorted(needed_init_tids & set(full_init_goal_ids))
    }
    return GoalIR(
        n=n,
        sm_nodes=sm_nodes_parsed,
        pm_nodes=pm_nodes_parsed,
        sm_shapes=parse_shapes(sm_sh_block),
        pm_shapes=parse_shapes(pm_sh_block),
        lineage=parse_lineage(gen_text, n),
        prereqs=parse_prereqs(scope_text, n),
        sm_graph_ref=_qualified_definition_name(sm_graph_ref, *sources),
        pm_graph_ref=_qualified_definition_name(pm_graph_ref, *sources),
        public_statement_module=public_statement_module,
        public_statement_ref=_qualified_definition_name(
            statement_name, statement_text
        ),
        public_statement_uses_contract_wrapper=(
            "CoarseLineageHoldsWithInitDistributedFaithfulWithContract"
            in extract_def_block(statement_text, statement_name)
        ),
        public_statement_contract_ref=parse_public_statement_contract_ref(
            statement_text, n
        ),
        public_statement_uses_faithful_evaluator=any(
            marker in extract_def_block(statement_text, statement_name)
            for marker in (
                "CoarseLineageHoldsWithInitDistributedFaithful",
                "denoteGraphDistributedFaithful",
            )
        ),
        lineage_ref=_qualified_definition_name(f"goal_{n}", *sources),
        init_goals_ref=_qualified_definition_name(
            parse_full_init_goals_name(statement_text, n), *sources
        ),
        sm_num_ranks=parse_num_ranks(sm_block, sm_name),
        pm_num_ranks=parse_num_ranks(pm_block, pm_name),
        sm_replica_groups=parse_replica_groups(sm_block),
        pm_replica_groups=parse_replica_groups(pm_block),
        sm_adapter_communications=parse_adapter_communications(gen_text, sm_name.rsplit(".", 1)[-1] + "AdapterCommunications"),
        pm_adapter_communications=parse_adapter_communications(gen_text, pm_name.rsplit(".", 1)[-1] + "AdapterCommunications"),
        packed_cu_contracts=packed_cu_contracts,
        tensor_value_bound_contracts=tensor_value_bound_contracts,
        sm_input_value_classes=sm_input_value_classes,
        pm_input_value_classes=pm_input_value_classes,
        sm_input_value_classes_ref=parse_input_value_classes_ref(
            statement_text, n, "sm", *sources
        ),
        pm_input_value_classes_ref=parse_input_value_classes_ref(
            statement_text, n, "pm", *sources
        ),
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
