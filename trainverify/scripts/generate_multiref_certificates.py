#!/usr/bin/env python3
"""Generate explicit faithful-multiref graph certificates from YOCO authority.

The graph and lineage declarations in ``GeneratedYOCOMoE.lean`` are the sole
source of node indices, ranks, inputs, outputs, arities, and goal PM tids.  The
emitted Lean records still expose every collective and prefix/suffix condition;
Lean checks those conditions against the complete generated graph.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
AUTHORITY = ROOT / "denote/GeneratedYOCOMoE.lean"
DEFAULT_OUTPUT = ROOT / "denote/yoco_goals/GeneratedMultirefCertificates.lean"
DEFAULT_GOALS = (7747,)

NODE_RE = re.compile(
    r'^\s*\{ rank := (?P<rank>\d+), op := "(?P<op>[^"]+)", '
    r'ins := \[(?P<ins>[\d, ]*)\], outs := \[(?P<outs>[\d, ]*)\]'
    r'(?:, params := \[(?P<params>[\d, ]*)\])? \},\s*$'
)
GOAL_RE = re.compile(
    r"^def intermediateGoal_(?P<goal>\d+) : LineageGoal :=\n"
    r"\s*\{ ts := (?P<ts>\d+),.*?tps := \[(?P<tps>.*?)\]",
    re.M,
)


@dataclass(frozen=True)
class Node:
    index: int
    rank: int
    op: str
    ins: tuple[int, ...]
    outs: tuple[int, ...]
    params: tuple[int, ...]


def numbers(text: str | None) -> tuple[int, ...]:
    if not text:
        return ()
    return tuple(int(value) for value in text.split(",") if value.strip())


def parse_graphs(lines: list[str]) -> dict[str, list[Node | None]]:
    graphs: dict[str, list[Node | None]] = {}
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
            if not match:
                # A few collective nodes use computed input lists.  They still
                # consume an index, but cannot produce a scalar multiref tid.
                if line.lstrip().startswith("{ rank :="):
                    graphs[current].append(None)
                    continue
                raise ValueError(f"unparsed {current} graph entry: {line}")
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
    if set(graphs) != {"sm", "pm"}:
        raise ValueError(f"expected sm/pm graphs, found {sorted(graphs)}")
    return graphs


def parse_goals(text: str) -> dict[int, tuple[int, tuple[int, ...]]]:
    result: dict[int, tuple[int, tuple[int, ...]]] = {}
    for match in GOAL_RE.finditer(text):
        tps = tuple(int(tid) for tid in re.findall(r"tid := (\d+)", match["tps"]))
        result[int(match["goal"])] = (int(match["ts"]), tps)
    return result


def producer(nodes: list[Node | None], tid: int) -> Node:
    matches = [node for node in nodes if node is not None and tid in node.outs]
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


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--goals", type=int, nargs="+", default=DEFAULT_GOALS)
    args = parser.parse_args()
    generated = render(tuple(args.goals))
    if args.check:
        if not args.output.exists() or args.output.read_text() != generated:
            raise SystemExit(f"stale multiref certificates: run {Path(__file__).name}")
        print(f"verified {args.output} from {AUTHORITY}")
    else:
        args.output.write_text(generated)
        print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
