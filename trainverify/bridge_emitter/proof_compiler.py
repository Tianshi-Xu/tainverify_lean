"""Typed, fail-closed proof planning for bridge-emitter GoalIR graphs.

This module does not emit Lean proof text.  It turns a parsed goal into a
machine-readable certificate dependency DAG and rejects the first unsupported
or structurally ambiguous node before rendering starts.
"""
from __future__ import annotations

from dataclasses import asdict, dataclass
from enum import Enum
import json
import math
from typing import Iterable, Optional

try:  # package import in tests
    from .parser import GoalIR, Node
except ImportError:  # direct script import used by bridge_emitter
    from parser import GoalIR, Node


class RuleKind(str, Enum):
    POINTWISE = "pointwise"
    COLLECTIVE = "collective"
    MULTI_OUTPUT = "multi_output"
    SPECIAL = "special"


class RelationKind(str, Enum):
    GATHER = "gather"
    REPLICATED = "replicated"


class RelationEffect(str, Enum):
    PRESERVE = "preserve"
    COLLECTIVE = "collective"
    PROJECT = "project"
    SPECIAL = "special"


class DiagnosticCode(str, Enum):
    UNSUPPORTED_OPERATOR = "proof.unsupported-operator"
    INVALID_SIGNATURE = "proof.invalid-rule-signature"
    DUPLICATE_PRODUCER = "proof.duplicate-producer"
    MISSING_PRODUCER = "proof.missing-producer"
    CYCLE = "proof.cycle"
    INVALID_LINEAGE = "proof.invalid-lineage"
    INVALID_GRAPH = "proof.invalid-graph"


@dataclass(frozen=True)
class RuleSpec:
    op: str
    kind: RuleKind
    output_count: Optional[int]
    input_count: Optional[int] = None
    min_inputs: int = 1
    parameter_count: Optional[int] = None
    allowed_parameter_counts: Optional[tuple[int, ...]] = None
    min_parameter_count: Optional[int] = None
    input_count_is_num_ranks: bool = False
    rank_sensitive: bool = False
    denote_fn: Optional[str] = None
    apply_lemmas: tuple[str, ...] = ()
    output_projections: tuple[str, ...] = ()
    relation_effect: RelationEffect = RelationEffect.PRESERVE

    def signature_error(self, node: Node, num_ranks: int) -> Optional[str]:
        if len(set(node.outs)) != len(node.outs):
            return "output tids must be unique within a node"
        if self.output_count is not None and len(node.outs) != self.output_count:
            return f"expected {self.output_count} outputs, got {len(node.outs)}"
        if self.input_count is not None and len(node.ins) != self.input_count:
            return f"expected {self.input_count} inputs, got {len(node.ins)}"
        if self.input_count_is_num_ranks and len(node.ins) != num_ranks:
            return f"expected numRanks={num_ranks} inputs, got {len(node.ins)}"
        if len(node.ins) < self.min_inputs:
            return f"expected at least {self.min_inputs} inputs, got {len(node.ins)}"
        if self.parameter_count is not None and len(node.params or []) != self.parameter_count:
            return (
                f"expected {self.parameter_count} parameters, "
                f"got {len(node.params or [])}"
            )
        if (
            self.allowed_parameter_counts is not None
            and len(node.params or []) not in self.allowed_parameter_counts
        ):
            return (
                f"expected parameter count in {self.allowed_parameter_counts}, "
                f"got {len(node.params or [])}"
            )
        if (
            self.min_parameter_count is not None
            and len(node.params or []) < self.min_parameter_count
        ):
            return (
                f"expected at least {self.min_parameter_count} parameters, "
                f"got {len(node.params or [])}"
            )
        if self.op == "FW_multiref" and (node.params or [0])[0] < len(node.outs):
            return (
                "FW_multiref params[0] must cover every output: "
                f"got n={(node.params or [0])[0]} for {len(node.outs)} outputs"
            )
        return None


class RuleRegistry:
    def __init__(self, rules: Iterable[RuleSpec] = ()) -> None:
        self._rules: dict[str, RuleSpec] = {}
        for rule in rules:
            self.register(rule)

    def register(self, rule: RuleSpec) -> None:
        if rule.op in self._rules:
            raise ValueError(f"duplicate proof rule for {rule.op}")
        self._rules[rule.op] = rule

    def get(self, op: str) -> Optional[RuleSpec]:
        return self._rules.get(op)

    def require(self, op: str) -> RuleSpec:
        rule = self.get(op)
        if rule is None:
            raise KeyError(op)
        return rule

    def operations(self) -> tuple[str, ...]:
        return tuple(sorted(self._rules))


def build_default_registry() -> RuleRegistry:
    """Type the renderer's currently implemented rule vocabulary.

    The typed layer is deliberately constructed from the existing metadata in
    this first migration step, so rendering remains byte-compatible.  Later
    changes can move metadata ownership here without changing the planner API.
    """
    try:
        from . import renderer_uni as renderer
    except ImportError:
        import renderer_uni as renderer

    pointwise_inputs = {
        "FW_layernorm": 3,
        "FW_gelu": 1,
        "FW_linear": 2,
        "FW_matmul": 2,
        "FW_embedding": 2,
        "FW_sum": 1,
        "FW_add": 2,
        "FW_view": 1,
        "FW_transpose": 1,
        "FW_softmax": 1,
        "FW_contiguous": 1,
        "FW_div": 1,
        "BW_sum": 2,
        "BW_gelu": 2,
        "BW_view": 2,
        "BW_transpose": 2,
        "BW_contiguous": 2,
        "BW_div": 2,
        "BW_softmax": 2,
        "BW_embedding": 3,
    }
    arbitrary_parameters = {
        "FW_layernorm",
        "FW_softmax",
        "FW_contiguous",
        "FW_div",
        "BW_softmax",
        "BW_contiguous",
        "BW_div",
    }
    nonempty_parameters = {"FW_view", "BW_view"}
    exact_two_parameters = {"FW_transpose", "BW_transpose"}
    # Offset embeddings have distinct Lean denotations/lemmas and must become
    # separate typed rules before the generic planner can certify them.
    optional_offset: set[str] = set()

    rules: list[RuleSpec] = []
    for op, meta in sorted(renderer.POINTWISE.items()):
        variable_inputs = op == "BW_multiref"
        parameter_count = (
            None
            if op in arbitrary_parameters | optional_offset | nonempty_parameters
            else 0
        )
        if op in exact_two_parameters:
            parameter_count = 2
        rules.append(
            RuleSpec(
                op=op,
                kind=RuleKind.POINTWISE,
                output_count=1,
                input_count=None if variable_inputs else pointwise_inputs[op],
                min_inputs=1 if variable_inputs else pointwise_inputs[op],
                parameter_count=parameter_count,
                allowed_parameter_counts=(0, 1) if op in optional_offset else None,
                min_parameter_count=1 if op in nonempty_parameters else None,
                denote_fn=meta[0],
                apply_lemmas=(meta[1],),
            )
        )
    for op, meta in sorted(renderer.COLLECTIVE.items()):
        rules.append(
            RuleSpec(
                op=op,
                kind=RuleKind.COLLECTIVE,
                output_count=1,
                input_count=1 if meta["kind"] == "single" else None,
                input_count_is_num_ranks=meta["kind"] == "list",
                parameter_count=int(meta["nparams"]),
                rank_sensitive=True,
                denote_fn=str(meta["fn"]),
                apply_lemmas=tuple(
                    str(item)
                    for item in dict.fromkeys((meta["mini"], meta["full"]))
                ),
                relation_effect=RelationEffect.COLLECTIVE,
            )
        )
    for op, meta in sorted(renderer.BW_MULTI.items()):
        rules.append(
            RuleSpec(
                op=op,
                kind=RuleKind.MULTI_OUTPUT,
                output_count=len(meta["outs"]),
                input_count=meta["nargs"],
                denote_fn=meta["fn"],
                apply_lemmas=tuple(item[0] for item in meta["outs"]),
                output_projections=tuple(item[1] for item in meta["outs"]),
                relation_effect=RelationEffect.PROJECT,
            )
        )
    # FW_multiref is rendered by dedicated topology families rather than the
    # universal pointwise path.  It is still a typed, rank-insensitive rule;
    # output cardinality is carried by params and therefore variable.
    rules.append(
        RuleSpec(
            op="FW_multiref",
            kind=RuleKind.SPECIAL,
            output_count=None,
            input_count=1,
            parameter_count=1,
            relation_effect=RelationEffect.SPECIAL,
        )
    )
    return RuleRegistry(rules)


@dataclass(frozen=True)
class RelationRequirement:
    kind: RelationKind
    gather_dim: Optional[int]
    sm_tid: int
    pm_pieces: tuple[tuple[int, int], ...]


@dataclass(frozen=True)
class Diagnostic:
    code: DiagnosticCode
    message: str
    side: Optional[str] = None
    node_index: Optional[int] = None
    op: Optional[str] = None
    output_tid: Optional[int] = None


@dataclass(frozen=True)
class CertificateStep:
    step_id: str
    side: str
    node_index: int
    output_index: int
    output_tid: int
    op: str
    rule_kind: RuleKind
    relation_effect: RelationEffect
    rank: int
    input_tids: tuple[int, ...]
    parameters: tuple[int, ...]
    denote_fn: Optional[str]
    apply_lemmas: tuple[str, ...]
    output_projection: Optional[str]
    dependencies: tuple[str, ...]
    external_inputs: tuple[int, ...]


@dataclass(frozen=True)
class ProofPlan:
    goal_id: int
    relation: RelationRequirement
    steps: tuple[CertificateStep, ...]
    target_steps: tuple[str, ...]
    diagnostics: tuple[Diagnostic, ...]
    schema_version: int = 1

    @property
    def supported(self) -> bool:
        return not self.diagnostics

    def to_dict(self) -> dict:
        def encode(value):
            if isinstance(value, Enum):
                return value.value
            if isinstance(value, tuple):
                return [encode(item) for item in value]
            if isinstance(value, list):
                return [encode(item) for item in value]
            if isinstance(value, dict):
                return {key: encode(item) for key, item in value.items()}
            if hasattr(value, "__dataclass_fields__"):
                return {key: encode(item) for key, item in asdict(value).items()}
            return value

        return {
            "schema_version": self.schema_version,
            "status": "supported" if self.supported else "unsupported",
            "goal_id": self.goal_id,
            "relation": encode(self.relation),
            "target_steps": list(self.target_steps),
            "steps": [encode(step) for step in self.steps],
            "diagnostics": [encode(issue) for issue in self.diagnostics],
        }

    def to_json(self) -> str:
        return json.dumps(
            self.to_dict(), sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ) + "\n"


class ProofPlanningError(RuntimeError):
    def __init__(self, plan: ProofPlan) -> None:
        if plan.supported:
            raise ValueError("cannot raise ProofPlanningError for a supported plan")
        self.plan = plan
        issue = plan.diagnostics[0]
        where = issue.side or "graph"
        if issue.node_index is not None:
            where += f"[{issue.node_index}]"
        super().__init__(f"{issue.code.value} at {where}: {issue.message}")


def _relation_requirement(ir: GoalIR) -> tuple[RelationRequirement, Optional[Diagnostic]]:
    lineage = ir.lineage
    relation = RelationRequirement(
        kind=RelationKind.REPLICATED if lineage.replicated else RelationKind.GATHER,
        gather_dim=None if lineage.replicated else (lineage.gatherDim or 0),
        sm_tid=lineage.ts,
        pm_pieces=tuple((int(rank), int(tid)) for rank, tid in lineage.tps),
    )
    if not lineage.tps:
        return relation, Diagnostic(
            DiagnosticCode.INVALID_LINEAGE,
            "lineage has no PM pieces",
            output_tid=lineage.ts,
        )
    if len(lineage.tps) != len(lineage.tpShapes):
        return relation, Diagnostic(
            DiagnosticCode.INVALID_LINEAGE,
            "lineage tps and tpShapes lengths differ",
            output_tid=lineage.ts,
        )
    for side, shapes in (("sm", ir.sm_shapes), ("pm", ir.pm_shapes)):
        shape_tids = [int(tid) for tid, _shape in shapes]
        if len(set(shape_tids)) != len(shape_tids):
            return relation, Diagnostic(
                DiagnosticCode.INVALID_GRAPH,
                "InitShapes contains a duplicate tensor id",
                side=side,
            )
    for side, nodes, num_ranks in (
        ("sm", ir.sm_nodes, ir.sm_num_ranks),
        ("pm", ir.pm_nodes, ir.pm_num_ranks),
    ):
        for node_index, node in enumerate(nodes):
            if node.rank < 0 or node.rank >= num_ranks:
                return relation, Diagnostic(
                    DiagnosticCode.INVALID_GRAPH,
                    f"node rank {node.rank} is outside [0, {num_ranks})",
                    side=side,
                    node_index=node_index,
                    op=node.op,
                    output_tid=int(node.outs[0]) if node.outs else None,
                )
    piece_ranks = [int(rank) for rank, _tid in lineage.tps]
    if (
        piece_ranks != sorted(piece_ranks)
        or len(set(piece_ranks)) != len(piece_ranks)
        or any(rank < 0 or rank >= ir.pm_num_ranks for rank in piece_ranks)
    ):
        return relation, Diagnostic(
            DiagnosticCode.INVALID_LINEAGE,
            f"lineage PM piece ranks must be a strictly increasing subset of [0, {ir.pm_num_ranks})",
            output_tid=lineage.ts,
        )
    if lineage.replicated and any(shape != lineage.tsShape for shape in lineage.tpShapes):
        return relation, Diagnostic(
            DiagnosticCode.INVALID_LINEAGE,
            "replicated lineage piece shape differs from the SM shape",
            output_tid=lineage.ts,
        )
    if not lineage.replicated:
        gather_dim = lineage.gatherDim or 0
        if gather_dim < 0 or gather_dim >= len(lineage.tsShape):
            return relation, Diagnostic(
                DiagnosticCode.INVALID_LINEAGE,
                f"gather dimension {gather_dim} is outside target shape rank {len(lineage.tsShape)}",
                output_tid=lineage.ts,
            )
        if any(len(shape) != len(lineage.tsShape) for shape in lineage.tpShapes):
            return relation, Diagnostic(
                DiagnosticCode.INVALID_LINEAGE,
                "lineage PM piece rank differs from the SM target shape rank",
                output_tid=lineage.ts,
            )
        for dim, expected in enumerate(lineage.tsShape):
            if dim == gather_dim:
                actual = sum(shape[dim] for shape in lineage.tpShapes)
                if actual != expected:
                    return relation, Diagnostic(
                        DiagnosticCode.INVALID_LINEAGE,
                        f"gathered dimension {dim} has extent {actual}, expected {expected}",
                        output_tid=lineage.ts,
                    )
            elif any(shape[dim] != expected for shape in lineage.tpShapes):
                return relation, Diagnostic(
                    DiagnosticCode.INVALID_LINEAGE,
                    f"non-gather dimension {dim} does not match target extent {expected}",
                    output_tid=lineage.ts,
                )
    return relation, None


def _collective_shape_issue(ir: GoalIR) -> Optional[Diagnostic]:
    """Validate dimension-bearing collectives against ordered inferred shapes."""
    shape_preserving = {
        "FW_layernorm", "FW_gelu", "FW_softmax",
        "FW_contiguous", "FW_div",
    }

    def broadcast_shape(left: list[int], right: list[int]) -> Optional[list[int]]:
        width = max(len(left), len(right))
        left_padded = [1] * (width - len(left)) + left
        right_padded = [1] * (width - len(right)) + right
        if any(a != b and a != 1 and b != 1 for a, b in zip(left_padded, right_padded)):
            return None
        return [max(a, b) for a, b in zip(left_padded, right_padded)]
    inferred_shapes: dict[str, dict[int, list[int]]] = {}
    for side, nodes, initial_shapes, num_ranks in (
        ("sm", ir.sm_nodes, ir.sm_shapes, ir.sm_num_ranks),
        ("pm", ir.pm_nodes, ir.pm_shapes, ir.pm_num_ranks),
    ):
        shapes = {int(tid): list(shape) for tid, shape in initial_shapes}
        for node_index, node in enumerate(nodes):
            input_shapes = [shapes.get(int(tid)) for tid in node.ins]
            dimensions: list[int] = []
            if node.op in {"AllGatherPrim", "ChunkPrim"}:
                dimensions = [int((node.params or [0])[0])]
            elif node.op == "AllToAllPrim":
                dimensions = [int(value) for value in (node.params or [])]
            if dimensions:
                if any(shape is None for shape in input_shapes):
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: cannot establish input shapes for dimension validation",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                validated_shapes = [shape for shape in input_shapes if shape is not None]
                for dimension in dimensions:
                    if any(
                        dimension < 0 or dimension >= len(shape)
                        for shape in validated_shapes
                    ):
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: dimension {dimension} is outside an input shape rank",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )

            output_shape: Optional[list[int]] = None
            known_shapes = [shape for shape in input_shapes if shape is not None]
            if node.op == "FW_embedding" and len(input_shapes) == 2:
                ids_shape, weight_shape = input_shapes
                if ids_shape is not None and weight_shape is not None and len(weight_shape) == 2:
                    output_shape = list(ids_shape) + [weight_shape[1]]
            elif node.op in shape_preserving and input_shapes and input_shapes[0] is not None:
                output_shape = list(input_shapes[0])
            elif node.op == "FW_sum":
                output_shape = [1]
            elif node.op == "FW_add" and len(input_shapes) == 2:
                left_shape, right_shape = input_shapes
                if left_shape is not None and right_shape is not None:
                    output_shape = broadcast_shape(left_shape, right_shape)
                    if output_shape is None:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: input shapes are not broadcast-compatible",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
            elif node.op == "FW_view" and node.params:
                output_shape = [int(value) for value in node.params]
                input_shape = input_shapes[0] if input_shapes else None
                if input_shape is not None:
                    input_size = math.prod(input_shape)
                    output_size = math.prod(output_shape)
                    if input_size != output_size:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: reshape changes element count "
                            f"from {input_size} to {output_size}",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
            elif node.op == "FW_transpose" and input_shapes and input_shapes[0] is not None:
                output_shape = list(input_shapes[0])
                first, second = (int(value) for value in (node.params or []))
                if first >= len(output_shape) or second >= len(output_shape):
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: transpose dimension is outside input rank",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                output_shape[first], output_shape[second] = output_shape[second], output_shape[first]
            elif node.op == "FW_linear" and len(input_shapes) == 2:
                value_shape, weight_shape = input_shapes
                if value_shape is not None and weight_shape is not None:
                    if len(value_shape) not in {2, 3} or len(weight_shape) != 2:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: unsupported input/weight rank",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    elif value_shape[-1] != weight_shape[1]:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: linear inner dimensions differ",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    else:
                        output_shape = list(value_shape[:-1]) + [weight_shape[0]]
            elif node.op == "AllReducePrim" and known_shapes:
                if any(shape != known_shapes[0] for shape in known_shapes[1:]):
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: input shapes differ",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                output_shape = list(known_shapes[0])
            elif node.op == "AllGatherPrim" and known_shapes:
                if any(shape != known_shapes[0] for shape in known_shapes[1:]):
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: input shapes differ",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                output_shape = list(known_shapes[0])
                dimension = int((node.params or [0])[0])
                output_shape[dimension] *= num_ranks
            elif node.op == "ChunkPrim" and known_shapes:
                output_shape = list(known_shapes[0])
                dimension = int((node.params or [0])[0])
                if output_shape[dimension] % num_ranks != 0:
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: dimension extent is not divisible by numRanks",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                output_shape[dimension] //= num_ranks
            elif node.op == "AllToAllPrim" and known_shapes:
                if any(shape != known_shapes[0] for shape in known_shapes[1:]):
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: input shapes differ",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                output_shape = list(known_shapes[0])
                input_dim, output_dim = (int(value) for value in (node.params or []))
                output_shape[input_dim] *= num_ranks
                if output_shape[output_dim] % num_ranks != 0:
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: output dimension extent is not divisible by numRanks",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                output_shape[output_dim] //= num_ranks
            if output_shape is not None:
                for tid in node.outs:
                    shapes[int(tid)] = list(output_shape)
            elif node.outs:
                return Diagnostic(
                    DiagnosticCode.INVALID_SIGNATURE,
                    f"operator {node.op}: no registered shape inference for all inputs",
                    side=side,
                    node_index=node_index,
                    op=node.op,
                    output_tid=int(node.outs[0]),
                )
        inferred_shapes[side] = shapes

    target_contracts = [
        ("sm", int(ir.lineage.ts), list(ir.lineage.tsShape)),
        *[
            ("pm", int(tid), list(shape))
            for (_rank, tid), shape in zip(ir.lineage.tps, ir.lineage.tpShapes)
        ],
    ]
    for side, tid, declared_shape in target_contracts:
        inferred_shape = inferred_shapes[side].get(tid)
        if inferred_shape is None:
            return Diagnostic(
                DiagnosticCode.INVALID_LINEAGE,
                f"cannot establish final {side.upper()} shape for lineage tid {tid}",
                side=side,
                output_tid=tid,
            )
        if inferred_shape != declared_shape:
            return Diagnostic(
                DiagnosticCode.INVALID_LINEAGE,
                f"final {side.upper()} shape {inferred_shape} for tid {tid} "
                f"differs from lineage declaration {declared_shape}",
                side=side,
                output_tid=tid,
            )
    return None


def compile_proof_plan(ir: GoalIR, registry: RuleRegistry) -> ProofPlan:
    """Build a deterministic certificate dependency DAG for one GoalIR.

    Inputs listed in the side's InitShapes are trusted graph boundaries.  Every
    other consumed tid must have an earlier producer.  Multiple writers are
    rejected except an in-place collective that consumes and rewrites the same
    tid; those use the immediately preceding writer as their dependency.
    """
    relation, relation_issue = _relation_requirement(ir)
    if relation_issue is not None:
        return ProofPlan(ir.n, relation, (), (), (relation_issue,))

    side_nodes = {"sm": list(ir.sm_nodes), "pm": list(ir.pm_nodes)}
    side_inputs = {
        "sm": {int(tid) for tid, _shape in ir.sm_shapes},
        "pm": {int(tid) for tid, _shape in ir.pm_shapes},
    }
    writers: dict[str, dict[int, list[tuple[int, int]]]] = {"sm": {}, "pm": {}}

    # Rule and signature validation is graph-wide and ordered.  Report the
    # first real unsupported node before secondary producer-index effects can
    # obscure it.
    for side in ("sm", "pm"):
        for node_index, node in enumerate(side_nodes[side]):
            rule = registry.get(node.op)
            output_tid = int(node.outs[0]) if node.outs else None
            if rule is None:
                issue = Diagnostic(
                    DiagnosticCode.UNSUPPORTED_OPERATOR,
                    f"operator {node.op} has no registered proof rule",
                    side=side,
                    node_index=node_index,
                    op=node.op,
                    output_tid=output_tid,
                )
                return ProofPlan(ir.n, relation, (), (), (issue,))
            num_ranks = ir.sm_num_ranks if side == "sm" else ir.pm_num_ranks
            signature_error = rule.signature_error(node, num_ranks)
            if signature_error is not None:
                issue = Diagnostic(
                    DiagnosticCode.INVALID_SIGNATURE,
                    f"operator {node.op}: {signature_error}",
                    side=side,
                    node_index=node_index,
                    op=node.op,
                    output_tid=output_tid,
                )
                return ProofPlan(ir.n, relation, (), (), (issue,))

    for side in ("sm", "pm"):
        for node_index, node in enumerate(side_nodes[side]):
            for output_index, tid in enumerate(node.outs):
                prior = writers[side].setdefault(int(tid), [])
                if prior:
                    rule = registry.get(node.op)
                    previous = side_nodes[side][prior[-1][0]]
                    equivalent_rank_rewrite = (
                        rule is not None
                        and not rule.rank_sensitive
                        and previous.op == node.op
                        and previous.ins == node.ins
                        and previous.outs == node.outs
                        and (previous.params or []) == (node.params or [])
                        and set(node.outs).isdisjoint(node.ins)
                        and set(previous.outs).isdisjoint(previous.ins)
                    )
                    valid_in_place = (
                        rule is not None
                        and rule.kind is RuleKind.COLLECTIVE
                        and int(tid) in node.ins
                    )
                    if not (valid_in_place or equivalent_rank_rewrite):
                        issue = Diagnostic(
                            DiagnosticCode.DUPLICATE_PRODUCER,
                            f"tid {tid} has multiple non-in-place producers",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(tid),
                        )
                        return ProofPlan(ir.n, relation, (), (), (issue,))
                prior.append((node_index, output_index))

    for rank, tid in relation.pm_pieces:
        choices = writers["pm"].get(int(tid), [])
        if choices:
            producer_index = choices[-1][0]
            producer = side_nodes["pm"][producer_index]
            if producer.rank != rank:
                issue = Diagnostic(
                    DiagnosticCode.INVALID_LINEAGE,
                    f"lineage rank {rank} does not match final producer rank {producer.rank}",
                    side="pm",
                    node_index=producer_index,
                    op=producer.op,
                    output_tid=int(tid),
                )
                return ProofPlan(ir.n, relation, (), (), (issue,))

    # Detect dependency cycles against the complete writer graph before the
    # execution-order check below.  Otherwise a back edge first appears as a
    # generic "no earlier producer" and hides the actual closed cycle.
    for side in ("sm", "pm"):
        cycle_visiting: set[int] = set()
        cycle_done: set[int] = set()

        def cycle_visit(node_index: int) -> Optional[Diagnostic]:
            if node_index in cycle_done:
                return None
            node = side_nodes[side][node_index]
            if node_index in cycle_visiting:
                return Diagnostic(
                    DiagnosticCode.CYCLE,
                    f"dependency cycle reaches node {node_index}",
                    side=side,
                    node_index=node_index,
                    op=node.op,
                    output_tid=int(node.outs[0]) if node.outs else None,
                )
            cycle_visiting.add(node_index)
            for input_tid in node.ins:
                choices = writers[side].get(int(input_tid), [])
                if not choices:
                    continue
                # Graph semantics is an ordered fold: every read binds to the
                # latest writer strictly before this node.  Only when no prior
                # writer exists do we follow the first future writer, solely to
                # distinguish a closed cycle from a non-topological reference.
                earlier = [item for item in choices if item[0] < node_index]
                if earlier:
                    producer_index = earlier[-1][0]
                elif int(input_tid) in side_inputs[side]:
                    continue
                else:
                    producer_index = choices[0][0]
                issue = cycle_visit(producer_index)
                if issue is not None:
                    return issue
            cycle_visiting.remove(node_index)
            cycle_done.add(node_index)
            return None

        for node_index in range(len(side_nodes[side])):
            issue = cycle_visit(node_index)
            if issue is not None:
                return ProofPlan(ir.n, relation, (), (), (issue,))

    emitted: dict[tuple[str, int, int], CertificateStep] = {}
    visiting: set[tuple[str, int, int]] = set()
    ordered: list[CertificateStep] = []

    def producer_before(side: str, tid: int, before: Optional[int]) -> Optional[tuple[int, int]]:
        choices = writers[side].get(int(tid), [])
        if before is None:
            return choices[-1] if choices else None
        eligible = [item for item in choices if item[0] < before]
        return eligible[-1] if eligible else None

    def visit(side: str, node_index: int, output_index: int) -> Optional[Diagnostic]:
        key = (side, node_index, output_index)
        if key in emitted:
            return None
        node = side_nodes[side][node_index]
        output_tid = int(node.outs[output_index])
        if key in visiting:
            return Diagnostic(
                DiagnosticCode.CYCLE,
                f"dependency cycle reaches tid {output_tid}",
                side=side,
                node_index=node_index,
                op=node.op,
                output_tid=output_tid,
            )
        visiting.add(key)

        rule = registry.get(node.op)
        if rule is None:
            visiting.remove(key)
            return Diagnostic(
                DiagnosticCode.UNSUPPORTED_OPERATOR,
                f"operator {node.op} has no registered proof rule",
                side=side,
                node_index=node_index,
                op=node.op,
                output_tid=output_tid,
            )
        num_ranks = ir.sm_num_ranks if side == "sm" else ir.pm_num_ranks
        signature_error = rule.signature_error(node, num_ranks)
        if signature_error is not None:
            visiting.remove(key)
            return Diagnostic(
                DiagnosticCode.INVALID_SIGNATURE,
                f"operator {node.op}: {signature_error}",
                side=side,
                node_index=node_index,
                op=node.op,
                output_tid=output_tid,
            )

        dependencies: list[str] = []
        external_inputs: list[int] = []
        for input_tid in node.ins:
            producer = producer_before(side, int(input_tid), node_index)
            if producer is None:
                if int(input_tid) in side_inputs[side]:
                    external_inputs.append(int(input_tid))
                    continue
                visiting.remove(key)
                return Diagnostic(
                    DiagnosticCode.MISSING_PRODUCER,
                    f"input tid {input_tid} has no earlier producer or InitShapes entry",
                    side=side,
                    node_index=node_index,
                    op=node.op,
                    output_tid=output_tid,
                )
            issue = visit(side, producer[0], producer[1])
            if issue is not None:
                visiting.remove(key)
                return issue
            dependencies.append(emitted[(side, producer[0], producer[1])].step_id)

        step = CertificateStep(
            step_id=f"{side}:{node_index}:{output_index}",
            side=side,
            node_index=node_index,
            output_index=output_index,
            output_tid=output_tid,
            op=node.op,
            rule_kind=rule.kind,
            relation_effect=rule.relation_effect,
            rank=int(node.rank),
            input_tids=tuple(int(tid) for tid in node.ins),
            parameters=tuple(int(value) for value in (node.params or [])),
            denote_fn=rule.denote_fn,
            apply_lemmas=rule.apply_lemmas,
            output_projection=(
                rule.output_projections[output_index]
                if output_index < len(rule.output_projections)
                else None
            ),
            dependencies=tuple(dict.fromkeys(dependencies)),
            external_inputs=tuple(dict.fromkeys(external_inputs)),
        )
        visiting.remove(key)
        emitted[key] = step
        ordered.append(step)
        return None

    targets: list[tuple[str, int]] = [("sm", int(ir.lineage.ts))]
    targets.extend(("pm", int(tid)) for _rank, tid in ir.lineage.tps)
    target_steps: list[str] = []
    for side, tid in targets:
        producer = producer_before(side, tid, None)
        if producer is None:
            issue = Diagnostic(
                DiagnosticCode.MISSING_PRODUCER,
                f"target tid {tid} has no producer",
                side=side,
                output_tid=tid,
            )
            return ProofPlan(ir.n, relation, tuple(ordered), tuple(target_steps), (issue,))
        issue = visit(side, producer[0], producer[1])
        if issue is not None:
            return ProofPlan(ir.n, relation, tuple(ordered), tuple(target_steps), (issue,))
        target_steps.append(emitted[(side, producer[0], producer[1])].step_id)

    shape_issue = _collective_shape_issue(ir)
    if shape_issue is not None:
        return ProofPlan(ir.n, relation, tuple(ordered), tuple(target_steps), (shape_issue,))

    return ProofPlan(
        ir.n,
        relation,
        tuple(ordered),
        tuple(target_steps),
        (),
    )


def require_supported_plan(ir: GoalIR, registry: RuleRegistry) -> ProofPlan:
    plan = compile_proof_plan(ir, registry)
    if not plan.supported:
        raise ProofPlanningError(plan)
    return plan
