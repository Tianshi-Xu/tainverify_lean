#!/usr/bin/env python3
"""Generate/check deterministic metadata for YOCO distributed MoE migrations.

The checked-in GeneratedYOCOMoE graph is generation IR rendered as Lean data.  This
module lexes and parses its ``GraphDecl``/``LineageGoal`` values structurally; it
never searches or rewrites proof text.  Zigzag entries are deliberately emitted
as fail-closed blockers until their migration is separately authorised.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterator, Sequence

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_GRAPH = ROOT / "trainverify" / "denote" / "GeneratedYOCOMoE.lean"
DEFAULT_MANIFEST = ROOT / "trainverify" / "denote" / "GeneratedYOCOMoE.manifest.json"
DEFAULT_ARTIFACT = ROOT / "trainverify" / "denote" / "yoco_moe_migration_metadata.json"

# This is the reviewed audit table, not a range inferred from the graph.  Keeping
# every row explicit makes omissions, accidental expansion and status changes fail.
# (layer, kind, SM goal tid, SM node index, PM buddy tids, PM node indices, state)
AUDIT_TABLE: tuple[tuple[int, str, int, int, tuple[int, int], tuple[int, int], str], ...] = (
    (3, "sliding", 4822, 109, (7863, 7864), (279, 282), "ready"),
    (4, "sliding", 4876, 148, (8049, 8050), (357, 360), "ready"),
    (5, "sliding", 4930, 187, (8235, 8236), (435, 438), "ready"),
    (6, "sliding", 4984, 226, (8421, 8422), (513, 516), "ready"),
    (7, "sliding", 5038, 265, (8607, 8608), (591, 594), "ready"),
    (8, "sliding", 5092, 304, (8793, 8794), (669, 672), "ready"),
    (9, "sliding", 5146, 343, (8979, 8980), (747, 750), "ready"),
    (10, "sliding", 5200, 382, (9165, 9166), (825, 828), "ready"),
    (11, "sliding", 5254, 421, (9351, 9352), (903, 906), "ready"),
    (12, "sliding", 5308, 460, (9537, 9538), (981, 984), "ready"),
    (13, "zigzag", 5365, 527, (9741, 9742), (1116, 1119), "blocked"),
    (14, "zigzag", 5414, 562, (9913, 9914), (1186, 1189), "blocked"),
    (15, "zigzag", 5463, 597, (10085, 10086), (1256, 1259), "blocked"),
    (16, "zigzag", 5512, 632, (10257, 10258), (1326, 1329), "blocked"),
    (17, "zigzag", 5561, 667, (10429, 10430), (1396, 1399), "blocked"),
    (18, "zigzag", 5610, 702, (10601, 10602), (1466, 1469), "blocked"),
    (19, "zigzag", 5659, 737, (10773, 10774), (1536, 1539), "blocked"),
    (20, "zigzag", 5708, 772, (10945, 10946), (1606, 1609), "blocked"),
    (21, "zigzag", 5757, 807, (11117, 11118), (1676, 1679), "blocked"),
    (22, "zigzag", 5806, 842, (11289, 11290), (1746, 1749), "blocked"),
    (23, "zigzag", 5855, 877, (11461, 11462), (1816, 1819), "blocked"),
    # L24 has two extra PM nodes before the rank-1 writer: 1891, not affine 1889.
    (24, "zigzag", 5904, 912, (11633, 11634), (1886, 1891), "blocked"),
)


@dataclass(frozen=True)
class Token:
    value: str | int
    offset: int


def lex_lean_data(text: str) -> list[Token]:
    """Small deterministic lexer for generated Lean data declarations."""
    tokens: list[Token] = []
    i = 0
    n = len(text)
    while i < n:
        c = text[i]
        if c.isspace():
            i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i + 2)
            i = n if end < 0 else end + 1
        elif text.startswith("/-", i):
            start = i
            depth = 1
            i += 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError(f"unterminated block comment at byte {start}")
        elif text.startswith(":=", i):
            tokens.append(Token(":=", i))
            i += 2
        elif c in "{}[](),:?.":
            tokens.append(Token(c, i))
            i += 1
        elif c == '"':
            start = i
            i += 1
            chars: list[str] = []
            while i < n and text[i] != '"':
                if text[i] == "\\":
                    i += 1
                    if i >= n:
                        raise ValueError(f"unterminated string at byte {start}")
                    escapes = {"n": "\n", "r": "\r", "t": "\t", '"': '"', "\\": "\\"}
                    chars.append(escapes.get(text[i], text[i]))
                else:
                    chars.append(text[i])
                i += 1
            if i >= n:
                raise ValueError(f"unterminated string at byte {start}")
            i += 1
            tokens.append(Token("".join(chars), start))
        elif c.isdigit():
            start = i
            while i < n and text[i].isdigit():
                i += 1
            tokens.append(Token(int(text[start:i]), start))
        elif c.isalpha() or c == "_":
            start = i
            while i < n and (text[i].isalnum() or text[i] in "_'"):
                i += 1
            tokens.append(Token(text[start:i], start))
        else:
            # Operators and syntax outside the generated data subset are harmless.
            tokens.append(Token(c, i))
            i += 1
    return tokens


class DataParser:
    def __init__(self, tokens: Sequence[Token]):
        self.tokens = tokens
        self.pos = 0

    def peek(self) -> str | int:
        if self.pos >= len(self.tokens):
            raise ValueError("unexpected end of generated Lean data")
        return self.tokens[self.pos].value

    def take(self, expected: str | int | None = None) -> str | int:
        value = self.peek()
        if expected is not None and value != expected:
            where = self.tokens[self.pos].offset
            raise ValueError(f"expected {expected!r}, got {value!r} at byte {where}")
        self.pos += 1
        return value

    def value(self) -> Any:
        current = self.peek()
        if isinstance(current, int):
            return self.take()
        if current == "[":
            return self.list_value()
        if current == "{":
            return self.record_value()
        if current == "(":
            return self.parenthesized_expression()
        if isinstance(current, str):
            # Strings and identifiers are both represented by their decoded text;
            # generated NodeDecl.op is a string, while no selected numeric field is.
            return self.take()
        raise ValueError(f"unsupported generated value {current!r}")

    def parenthesized_expression(self) -> dict[str, list[str | int]]:
        """Consume an opaque generated expression while retaining token structure.

        A few unrelated fan-out declarations use ``List.range ... |>.map`` rather
        than literal lists. They must still be consumed to preserve node indices,
        but migration rows never select those declarations.
        """
        values: list[str | int] = []
        depths = {"(": 0, "[": 0, "{": 0}
        closing = {")": "(", "]": "[", "}": "{"}
        while True:
            current = self.peek()
            values.append(self.take())
            if current in depths:
                depths[str(current)] += 1
            elif current in closing:
                opener = closing[str(current)]
                depths[opener] -= 1
                if any(depth < 0 for depth in depths.values()):
                    raise ValueError("unbalanced generated expression")
            if all(depth == 0 for depth in depths.values()):
                break
        return {"lean_tokens": values}

    def list_value(self) -> list[Any]:
        self.take("[")
        result: list[Any] = []
        while self.peek() != "]":
            result.append(self.value())
            if self.peek() == ",":
                self.take(",")
            elif self.peek() != "]":
                raise ValueError("expected comma or closing bracket")
        self.take("]")
        return result

    def record_value(self) -> dict[str, Any]:
        self.take("{")
        result: dict[str, Any] = {}
        while self.peek() != "}":
            key = self.take()
            if not isinstance(key, str):
                raise ValueError(f"record key must be an identifier, got {key!r}")
            self.take(":=")
            result[key] = self.value()
            if self.peek() == ",":
                self.take(",")
            elif self.peek() != "}":
                raise ValueError("expected comma or closing brace")
        self.take("}")
        return result


def _definition_positions(tokens: Sequence[Token]) -> Iterator[tuple[str, int]]:
    for i in range(len(tokens) - 1):
        if tokens[i].value == "def" and isinstance(tokens[i + 1].value, str):
            yield str(tokens[i + 1].value), i + 2


def _find_after(tokens: Sequence[Token], start: int, needle: str, stop: int | None = None) -> int:
    end = len(tokens) if stop is None else stop
    for i in range(start, end):
        if tokens[i].value == needle:
            return i + 1
    raise ValueError(f"missing {needle!r} in generated definition")


def parse_generated_graph(data: bytes) -> tuple[dict[str, list[dict[str, Any]]], dict[int, dict[str, Any]]]:
    tokens = lex_lean_data(data.decode("utf-8"))
    definitions = list(_definition_positions(tokens))
    starts = {name: start for name, start in definitions}
    graphs: dict[str, list[dict[str, Any]]] = {}
    for graph_name in ("sm", "pm"):
        start = starts.get(graph_name)
        if start is None:
            raise ValueError(f"missing {graph_name} GraphDecl")
        exact = _find_after(tokens, start, "exact")
        parser = DataParser(tokens)
        parser.pos = exact
        raw_nodes = parser.list_value()
        nodes: list[dict[str, Any]] = []
        for raw in raw_nodes:
            if not isinstance(raw, dict):
                raise ValueError(f"{graph_name} nodes must be records")
            node = {
                "rank": raw.get("rank"),
                "op": raw.get("op"),
                "ins": raw.get("ins"),
                "outs": raw.get("outs"),
                "params": raw.get("params", []),
            }
            if not isinstance(node["rank"], int) or not isinstance(node["op"], str):
                raise ValueError(f"malformed {graph_name} NodeDecl")
            nodes.append(node)
        graphs[graph_name] = nodes

    goals: dict[int, dict[str, Any]] = {}
    prefix = "intermediateGoal_"
    for name, start in definitions:
        suffix = name[len(prefix):] if name.startswith(prefix) else ""
        if not suffix or not suffix.isdigit():
            continue
        assign = _find_after(tokens, start, ":=", min(start + 12, len(tokens)))
        parser = DataParser(tokens)
        parser.pos = assign
        raw = parser.record_value()
        tid = int(suffix)
        if raw.get("ts") != tid or not isinstance(raw.get("tps"), list):
            raise ValueError(f"malformed lineage goal {name}")
        goals[tid] = raw
    return graphs, goals


def _writer(nodes: Sequence[dict[str, Any]], tid: int, rank: int | None = None) -> tuple[int, dict[str, Any]]:
    matches = [
        (index, node) for index, node in enumerate(nodes)
        if tid in node["outs"] and (rank is None or node["rank"] == rank)
    ]
    if len(matches) != 1:
        raise ValueError(f"expected exactly one writer for tid={tid}, rank={rank}; got {len(matches)}")
    return matches[0]


def _audit_dict(row: tuple[int, str, int, int, tuple[int, int], tuple[int, int], str]) -> dict[str, Any]:
    layer, kind, tid, sm_index, buddy_tids, pm_indices, state = row
    return {
        "layer": layer,
        "kind": kind,
        "goal_tid": tid,
        "sm_node_index": sm_index,
        "buddy_tids": list(buddy_tids),
        "pm_node_indices": list(pm_indices),
        "state": state,
    }


def validate_affine_invariants(entries: Sequence[dict[str, Any]]) -> None:
    groups = {kind: [entry for entry in entries if entry["kind"] == kind] for kind in ("sliding", "zigzag")}
    expected = {
        "sliding": {"layer": 1, "goal": 54, "sm": 39, "buddy": 186, "pm0": 78, "pm1": 78},
        "zigzag": {"layer": 1, "goal": 49, "sm": 35, "buddy": 172, "pm0": 70, "pm1": 70},
    }
    for kind, members in groups.items():
        for previous, current in zip(members, members[1:]):
            deltas = {
                "layer": current["layer"] - previous["layer"],
                "goal": current["goal_tids"]["sm"] - previous["goal_tids"]["sm"],
                "sm": current["node_indices"]["sm"] - previous["node_indices"]["sm"],
                "buddy": current["goal_tids"]["pm"][0] - previous["goal_tids"]["pm"][0],
                "pm0": current["node_indices"]["pm"][0] - previous["node_indices"]["pm"][0],
                "pm1": current["node_indices"]["pm"][1] - previous["node_indices"]["pm"][1],
            }
            for field, wanted in expected[kind].items():
                if kind == "zigzag" and current["layer"] == 24 and field == "pm1":
                    if deltas[field] != 72:
                        raise ValueError("L24 PM rank-1 node-index exception must be +72")
                elif deltas[field] != wanted:
                    raise ValueError(
                        f"{kind} L{previous['layer']}->L{current['layer']} {field} "
                        f"delta {deltas[field]} != {wanted}"
                    )
        if kind == "zigzag" and any(
            entry["migration"]["state"] != "blocked" or not entry["migration"]["fail_closed"]
            for entry in members
        ):
            raise ValueError("zigzag migrations must remain blocked fail-closed")


def generate_metadata(graph_data: bytes, manifest_data: bytes) -> dict[str, Any]:
    manifest = json.loads(manifest_data)
    graph_digest = hashlib.sha256(graph_data).hexdigest()
    if manifest.get("generated_lean_sha256") != graph_digest:
        raise ValueError("authority manifest does not hash the parsed GeneratedYOCOMoE graph")
    graphs, goals = parse_generated_graph(graph_data)
    entries: list[dict[str, Any]] = []
    for ordinal, row in enumerate(AUDIT_TABLE):
        layer, kind, tid, expected_sm_index, expected_buddies, expected_pm_indices, state = row
        goal = goals.get(tid)
        if goal is None:
            raise ValueError(f"audit goal {tid} is absent from structured lineage data")
        buddies = goal["tps"]
        buddy_pairs = [(item.get("rank"), item.get("tid")) for item in buddies]
        if buddy_pairs != [(0, expected_buddies[0]), (1, expected_buddies[1])]:
            raise ValueError(f"goal {tid} buddy ordering differs from exact audit table: {buddy_pairs}")
        sm_index, sm_node = _writer(graphs["sm"], tid)
        pm_writers = [_writer(graphs["pm"], buddy_tid, rank) for rank, buddy_tid in buddy_pairs]
        pm_indices = tuple(item[0] for item in pm_writers)
        if sm_index != expected_sm_index or pm_indices != expected_pm_indices:
            raise ValueError(
                f"goal {tid} node indices differ from exact audit table: "
                f"SM={sm_index}, PM={pm_indices}"
            )
        nodes = [sm_node, *(node for _, node in pm_writers)]
        if any(node["op"] != "OpName.FW_all2all_moe_gmm" for node in nodes):
            raise ValueError(f"goal {tid} is not an all2all MoE NodeDecl")
        group_start = 3 if kind == "sliding" else 13
        entry = {
            "layer": layer,
            "kind": kind,
            "affine_group": f"{kind}-moe-l{group_start}-l{12 if kind == 'sliding' else 24}",
            "affine_ordinal": layer - group_start,
            "goal_tids": {"sm": tid, "pm": list(expected_buddies)},
            "node_indices": {"sm": sm_index, "pm": list(pm_indices)},
            "node_decls": {"sm": sm_node, "pm": [node for _, node in pm_writers]},
            "buddy_ordering": [
                {"ordinal": buddy_ordinal, "rank": rank, "tid": buddy_tid}
                for buddy_ordinal, (rank, buddy_tid) in enumerate(buddy_pairs)
            ],
            "migration": {
                "state": state,
                "fail_closed": state == "blocked",
                "blocker": (
                    "zigzag distributed migration is not authorised by this metadata set"
                    if state == "blocked" else None
                ),
            },
        }
        entries.append(entry)
    validate_affine_invariants(entries)
    return {
        "schema_version": 1,
        "model": manifest.get("model", "YOCO-MoE-A0.4B"),
        "source": {
            "graph": "trainverify/denote/GeneratedYOCOMoE.lean",
            "manifest": "trainverify/denote/GeneratedYOCOMoE.manifest.json",
            "generated_lean_sha256": graph_digest,
        },
        "audit_table": [_audit_dict(row) for row in AUDIT_TABLE],
        "entries": entries,
    }


def canonical_bytes(metadata: dict[str, Any]) -> bytes:
    return (json.dumps(metadata, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode("utf-8")


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--graph", type=Path, default=DEFAULT_GRAPH)
    parser.add_argument("--manifest", type=Path, default=DEFAULT_MANIFEST)
    parser.add_argument("--artifact", type=Path, default=DEFAULT_ARTIFACT)
    parser.add_argument("--check", action="store_true", help="compare generated bytes with the artifact")
    parser.add_argument("--stdout", action="store_true", help="write generated JSON to stdout instead")
    args = parser.parse_args(argv)
    try:
        generated = canonical_bytes(generate_metadata(args.graph.read_bytes(), args.manifest.read_bytes()))
        if args.check:
            checked_in = args.artifact.read_bytes()
            if checked_in != generated:
                print(f"stale migration metadata: regenerate {args.artifact}", file=sys.stderr)
                return 1
            print(f"migration metadata matches ({len(AUDIT_TABLE)} exact audit rows)")
        elif args.stdout:
            sys.stdout.buffer.write(generated)
        else:
            args.artifact.parent.mkdir(parents=True, exist_ok=True)
            args.artifact.write_bytes(generated)
            print(f"wrote {args.artifact} ({len(AUDIT_TABLE)} exact audit rows)")
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(f"metadata generation failed closed: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
