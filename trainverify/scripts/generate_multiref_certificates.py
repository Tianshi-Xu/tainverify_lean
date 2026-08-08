#!/usr/bin/env python3
"""Generate explicit faithful-multiref graph certificates from YOCO authority.

The graph and lineage declarations in ``GeneratedYOCOMoE.lean`` are the sole
source of node indices, ranks, inputs, outputs, arities, and goal PM tids.  The
emitted Lean records still expose every collective and prefix/suffix condition;
Lean checks those conditions against the complete generated graph.
"""

from __future__ import annotations

import argparse
import os
import re
import tempfile
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUTHORITY = ROOT / "denote/GeneratedYOCOMoE.lean"
DEFAULT_OUTPUT = ROOT / "denote/yoco_goals/GeneratedMultirefCertificates.lean"
DEFAULT_GOALS = (7744,)

NODE_RE = re.compile(
    r'^\s*\{ rank := (?P<rank>\d+), op := "(?P<op>[^"]+)", '
    r'ins := \[(?P<ins>[\d, ]*)\], outs := \[(?P<outs>[\d, ]*)\]'
    r'(?:, params := \[(?P<params>[\d, ]*)\])? \},\s*$'
)
COMPUTED_MULTIREF_OUTS_RE = re.compile(
    r'^\s*\{ rank := (?P<rank>\d+), op := "OpName\.FW_multiref", '
    r'ins := \[(?P<input>\d+)\], outs := \(\(List\.range (?P<count>\d+)\)'
    r'\.map \(fun r => (?P<base>\d+) \+ r\)\), params := \[(?P<arity>\d+)\] \},\s*$'
)
COMPUTED_ZIGZAG_INS_RE = re.compile(
    r'^\s*\{ rank := (?P<rank>\d+), op := "OpName\.FW_attn_zigzag", '
    r'ins := \(\(List\.range \d+\)\.map \(fun r => \d+ \+ r\)\), '
    r'outs := \[(?P<outs>[\d, ]+)\], params := \[(?P<params>[\d, ]+)\] \},\s*$'
)
DEF_HEADER_RE = re.compile(r"^\s*def\s+(?P<name>[A-Za-z0-9_']+)", re.M)
GOAL_NAME_RE = re.compile(r"intermediateGoal_(?P<goal>\d+)")
GOAL_TS_RE = re.compile(r"\bts := (?P<ts>\d+)")
GOAL_TPS_RE = re.compile(r"\btps := \[(?P<tps>.*?)\]", re.S)


@dataclass(frozen=True)
class Node:
    index: int
    rank: int
    op: str
    ins: tuple[int, ...]
    outs: tuple[int, ...]
    params: tuple[int, ...]


def numbers(text: str | None) -> tuple[int, ...]:
    if text is None or text == "":
        return ()
    fields = text.split(",")
    if any(not field.strip() or not field.strip().isdigit() for field in fields):
        raise ValueError(f"malformed numeric list: [{text}]")
    return tuple(int(field.strip()) for field in fields)


def parse_graphs(lines: list[str]) -> dict[str, list[Node]]:
    graphs: dict[str, list[Node]] = {}
    current: str | None = None
    in_nodes = False
    for line in lines:
        if line.startswith("def sm : GraphDecl := by"):
            current, in_nodes = "sm", False
            graphs[current] = []
            continue
        if line.startswith("def pm : GraphDecl := by"):
            current, in_nodes = "pm", False
            graphs[current] = []
            continue
        if current and line.strip() == "exact [":
            in_nodes = True
            continue
        if in_nodes and line.strip() == "]":
            current, in_nodes = None, False
            continue
        if in_nodes and current:
            match = NODE_RE.match(line)
            if match:
                graphs[current].append(
                    Node(
                        index=len(graphs[current]),
                        rank=int(match["rank"]),
                        op=match["op"],
                        ins=numbers(match["ins"]),
                        outs=numbers(match["outs"]),
                        params=numbers(match["params"]),
                    )
                )
                continue
            computed = COMPUTED_MULTIREF_OUTS_RE.match(line)
            if computed:
                count = int(computed["count"])
                arity = int(computed["arity"])
                if count != arity:
                    raise ValueError(
                        f"{current} computed multiref count {count} != arity {arity}: {line}"
                    )
                base = int(computed["base"])
                graphs[current].append(
                    Node(
                        index=len(graphs[current]),
                        rank=int(computed["rank"]),
                        op="OpName.FW_multiref",
                        ins=(int(computed["input"]),),
                        outs=tuple(range(base, base + count)),
                        params=(arity,),
                    )
                )
                continue
            # Preserve output/operator identity for computed-input zigzag nodes.
            # The input list itself is irrelevant to multiref certificate
            # generation, but producer uniqueness must still see these writes.
            zigzag = COMPUTED_ZIGZAG_INS_RE.match(line)
            if zigzag:
                graphs[current].append(
                    Node(
                        index=len(graphs[current]),
                        rank=int(zigzag["rank"]),
                        op="OpName.FW_attn_zigzag",
                        ins=(),
                        outs=numbers(zigzag["outs"]),
                        params=numbers(zigzag["params"]),
                    )
                )
                continue
            raise ValueError(f"unparsed {current} graph entry: {line}")
    if set(graphs) != {"sm", "pm"}:
        raise ValueError(f"expected sm/pm graphs, found {sorted(graphs)}")
    return graphs


def parse_goals(text: str) -> dict[int, tuple[int, tuple[int, ...]]]:
    result: dict[int, tuple[int, tuple[int, ...]]] = {}
    declarations = list(DEF_HEADER_RE.finditer(text))
    for index, declaration in enumerate(declarations):
        name_match = GOAL_NAME_RE.fullmatch(declaration["name"])
        if name_match is None:
            continue
        goal = int(name_match["goal"])
        if goal in result:
            raise ValueError(f"duplicate intermediate goal {goal}")
        end = declarations[index + 1].start() if index + 1 < len(declarations) else len(text)
        body = text[declaration.end() : end]
        ts_match = GOAL_TS_RE.search(body)
        tps_match = GOAL_TPS_RE.search(body)
        if ts_match is None or tps_match is None:
            raise ValueError(f"could not parse intermediate goal {goal}")
        tps = tuple(int(tid) for tid in re.findall(r"tid := (\d+)", tps_match["tps"]))
        if len(tps) != len(set(tps)):
            raise ValueError(f"intermediate goal {goal} has duplicate PM tids")
        result[goal] = (int(ts_match["ts"]), tps)
    return result


def producer(nodes: list[Node], tid: int) -> Node:
    matches = [node for node in nodes if tid in node.outs]
    if len(matches) != 1:
        raise ValueError(f"tid {tid}: expected one producer, found {len(matches)}")
    node = matches[0]
    if node.op != "OpName.FW_multiref":
        raise ValueError(f"tid {tid}: producer is {node.op}, not FW_multiref")
    if len(node.ins) != 1 or len(node.params) != 1:
        raise ValueError(f"tid {tid}: malformed multiref signature {node}")
    if node.params[0] != len(node.outs):
        raise ValueError(
            f"tid {tid}: arity {node.params[0]} does not match {len(node.outs)} outputs"
        )
    return node


def lean_list(values: tuple[int, ...]) -> str:
    return "[" + ", ".join(map(str, values)) + "]"


def emit_certificate(graph: str, goal: int, tid: int, node: Node) -> str:
    name = f"multirefCert_{graph}_{goal}_{tid}"
    return f"""-- Generated from `{graph}.nodes[{node.index}]`; all side conditions remain visible.
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
-- Native evaluation checks finite predicates over the complete generated graph.
def {name} : FaithfulMultirefCertificate {graph} where
  index := {node.index}
  rank := {node.rank}
  input := {node.ins[0]}
  outputs := {lean_list(node.outs)}
  arity := {node.params[0]}
  output := {tid}
  inBounds := by native_decide
  nodeAt := by native_decide
  arityMatches := by decide
  outputMember := by decide
  notShuffleCollective := by decide
  notUnshuffleCollective := by decide
  notAttentionCollective := by decide
  suffixOutputsNonempty := by native_decide
  outputNotWrittenAfter := by native_decide
  prefixReadOutputsNonempty := by native_decide
  inputNotWrittenFromNode := by native_decide
"""


def render(goals_requested: tuple[int, ...]) -> str:
    if len(goals_requested) != len(set(goals_requested)):
        raise ValueError("duplicate --goals values would emit duplicate Lean declarations")
    text = AUTHORITY.read_text()
    graphs = parse_graphs(text.splitlines())
    goals = parse_goals(text)
    chunks = ["""/- Auto-generated by scripts/generate_multiref_certificates.py.
   Source of truth: denote/GeneratedYOCOMoE.lean.  Do not edit by hand. -/
import denote.MultirefCertificate
import denote.GeneratedYOCOMoE

set_option linter.style.nativeDecide false

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated

noncomputable section
"""]
    for goal in goals_requested:
        if goal not in goals:
            raise ValueError(f"unknown intermediate goal {goal}")
        ts, tps = goals[goal]
        if not tps:
            raise ValueError(f"goal {goal} has no PM tensors")
        chunks.append(emit_certificate("sm", goal, ts, producer(graphs["sm"], ts)))
        for tid in tps:
            chunks.append(emit_certificate("pm", goal, tid, producer(graphs["pm"], tid)))
    chunks.append("end\n\nend TrainVerify.Denote.GeneratedPatterns\n")
    return "\n".join(chunks)


def write_atomic(path: Path, content: str) -> None:
    """Atomically replace only the canonical generated certificate file."""
    path = path.absolute()
    expected = DEFAULT_OUTPUT.absolute()
    if path != expected:
        raise ValueError(f"refusing non-canonical output path: {path}")
    if path.is_symlink():
        raise ValueError(f"refusing to replace symlink output: {path}")
    root = ROOT.resolve()
    try:
        relative_parent = path.parent.relative_to(root)
    except ValueError as error:
        raise ValueError(f"output escapes repository root: {path}") from error
    cursor = root
    for component in relative_parent.parts:
        cursor /= component
        if cursor.is_symlink():
            raise ValueError(f"refusing symlinked output parent: {cursor}")
    if path.resolve() == AUTHORITY.resolve():
        raise ValueError(f"refusing to overwrite authority: {AUTHORITY}")
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(fd, "w") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except BaseException:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--write", action="store_true")
    parser.add_argument("--goals", type=int, nargs="+", default=DEFAULT_GOALS)
    args = parser.parse_args()
    if args.check and args.write:
        parser.error("--check and --write are mutually exclusive")
    generated = render(tuple(args.goals))
    # Checking is the safe default. Mutating output always requires --write.
    if args.check or not args.write:
        if not DEFAULT_OUTPUT.exists() or DEFAULT_OUTPUT.read_text() != generated:
            raise SystemExit(
                f"stale multiref certificates: run {Path(__file__).name} --write"
            )
        print(f"verified {DEFAULT_OUTPUT} from {AUTHORITY}")
    else:
        write_atomic(DEFAULT_OUTPUT, generated)
        print(f"wrote {DEFAULT_OUTPUT}")


if __name__ == "__main__":
    main()
