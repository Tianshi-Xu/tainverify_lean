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
    ORDINARY_TO_ZIGZAG = "ordinary_to_zigzag"
    ZIGZAG_PRESERVE = "zigzag_preserve"
    ZIGZAG_TO_ORDINARY = "zigzag_to_ordinary"
    STACK = "stack"
    PARAMETRIC = "parametric"
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
    allowed_output_counts: Optional[tuple[int, ...]] = None
    produced_output_indices: Optional[tuple[int, ...]] = None
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
    rule_id: Optional[str] = None

    def signature_error(self, node: Node, num_ranks: int) -> Optional[str]:
        if len(set(node.outs)) != len(node.outs):
            return "output tids must be unique within a node"
        if self.output_count is not None and len(node.outs) != self.output_count:
            return f"expected {self.output_count} outputs, got {len(node.outs)}"
        if self.allowed_output_counts is not None and len(node.outs) not in self.allowed_output_counts:
            return f"expected output count in {self.allowed_output_counts}, got {len(node.outs)}"
        if self.produced_output_indices is not None and any(
            index < 0 or index >= len(node.outs) for index in self.produced_output_indices
        ):
            return "semantic output index is outside declared outputs"
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
        if self.op == "FW_all2all_moe_gmm_full":
            if num_ranks != 2:
                return "only the proved two-rank full-MoE rule is supported"
            if len(node.ins) != 3 + 2 * num_ranks:
                return f"expected 3 + 2*numRanks inputs, got {len(node.ins)}"
        if self.op == "FW_multiref" and (node.params or [0])[0] < len(node.outs):
            return (
                "FW_multiref params[0] must cover every output: "
                f"got n={(node.params or [0])[0]} for {len(node.outs)} outputs"
            )
        return None


class RuleRegistry:
    def __init__(self, rules: Iterable[RuleSpec] = ()) -> None:
        self._rules: dict[str, RuleSpec] = {}
        self._variants: dict[str, list[RuleSpec]] = {}
        for rule in rules:
            self.register(rule)

    def register(self, rule: RuleSpec) -> None:
        if rule.op in self._rules:
            raise ValueError(f"duplicate proof rule for {rule.op}")
        self._rules[rule.op] = rule
        self._variants[rule.op] = [rule]

    def register_variant(self, rule: RuleSpec) -> None:
        if rule.op not in self._rules:
            raise ValueError(f"cannot register a variant without a base rule for {rule.op}")
        variants = self._variants[rule.op]
        identity = rule.rule_id or rule.op
        if any((candidate.rule_id or candidate.op) == identity for candidate in variants):
            raise ValueError(f"duplicate proof rule identity {identity!r} for {rule.op}")
        variants.append(rule)

    def get(self, op: str) -> Optional[RuleSpec]:
        return self._rules.get(op)

    def resolve(self, node: Node, num_ranks: int) -> tuple[Optional[RuleSpec], Optional[str]]:
        variants = self._variants.get(node.op, ())
        if not variants:
            return None, f"operator {node.op} has no registered proof rule"
        accepted = [rule for rule in variants if rule.signature_error(node, num_ranks) is None]
        if len(accepted) == 1:
            return accepted[0], None
        if len(accepted) > 1:
            identities = sorted(rule.rule_id or rule.op for rule in accepted)
            return None, f"operator {node.op} has ambiguous signature variants: {identities}"
        errors = sorted({rule.signature_error(node, num_ranks) for rule in variants})
        return None, f"operator {node.op} has no signature variant: {'; '.join(errors)}"

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
        "FW_float": 1,
        "FW_to": 1,
        "FW_rms_norm": 2,
        "FW_per_head_mix_precision_linear": 2,
        "FW_linear": 2,
        "FW_mix_precision_linear": 2,
        "FW_norm_linear": 2,
        "FW_matmul": 2,
        "FW_embedding": 2,
        "FW_sum": 1,
        "FW_sigmoid": 1,
        "FW_swiglu": 2,
        "FW_glu": 2,
        "FW_add": 2,
        "FW_mul": 2,
        "FW_view": 1,
        "FW_reshape": 1,
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
    nonempty_parameters = {"FW_view", "FW_reshape", "BW_view"}
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
                rule_id=op.lower().replace("_", "-"),
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
    rules.append(
        RuleSpec(
            op="FW_maybe_unshuffle",
            kind=RuleKind.SPECIAL,
            output_count=1,
            input_count=2,
            parameter_count=2,
            rank_sensitive=True,
            denote_fn="applyNodeFaithfulUnshuffleValue",
            apply_lemmas=("applyNodeDistributedFaithful_unshuffle_out",),
            relation_effect=RelationEffect.PARAMETRIC,
        )
    )
    rules.append(
        RuleSpec(
            op="FW_maybe_shuffle",
            kind=RuleKind.SPECIAL,
            output_count=1,
            input_count=2,
            parameter_count=2,
            rank_sensitive=True,
            denote_fn="applyNodeFaithfulShuffleValue",
            apply_lemmas=("applyNodeDistributedFaithful_shuffle_out",),
            relation_effect=RelationEffect.PARAMETRIC,
        )
    )
    for op, denote_fn, lemma in (
        (
            "BW_maybe_shuffle",
            "applyNodeBWMaybeShuffleValue",
            "applyNodeDistributed_bw_maybe_shuffle_out",
        ),
        (
            "BW_maybe_unshuffle",
            "applyNodeBWMaybeUnshuffleValue",
            "applyNodeDistributed_bw_maybe_unshuffle_out",
        ),
    ):
        rules.append(
            RuleSpec(
                op=op,
                kind=RuleKind.SPECIAL,
                output_count=1,
                input_count=2,
                parameter_count=2,
                rank_sensitive=True,
                denote_fn=denote_fn,
                apply_lemmas=(lemma,),
                relation_effect=RelationEffect.PARAMETRIC,
            )
        )
    for op, denote_fn, lemma_prefix in (
        (
            "BW_attn_sliding_window",
            "applyNodeRingAttn_bw_sliding_window",
            "applyNodeDistributed_bw_attn_sliding_window",
        ),
        (
            "BW_attn_zigzag",
            "applyNodeRingAttn_bw_zigzag",
            "applyNodeDistributed_bw_attn_zigzag",
        ),
    ):
        rules.append(
            RuleSpec(
                op=op,
                kind=RuleKind.MULTI_OUTPUT,
                output_count=3,
                input_count=6,
                parameter_count=6,
                rank_sensitive=True,
                denote_fn=denote_fn,
                apply_lemmas=tuple(f"{lemma_prefix}_out_{index}" for index in range(3)),
                output_projections=(".1", ".2.1", ".2.2"),
                relation_effect=RelationEffect.PROJECT,
            )
        )
    rules.append(
        RuleSpec(
            op="FW_all2all_moe_gmm_full",
            kind=RuleKind.SPECIAL,
            output_count=1,
            input_count=None,
            min_inputs=5,
            parameter_count=3,
            rank_sensitive=True,
            denote_fn="fw_all2all_moe_gmm_full",
            apply_lemmas=("applyNode_fw_all2all_moe_gmm_full_out_1p_r2",),
            relation_effect=RelationEffect.SPECIAL,
        )
    )
    rules.append(
        RuleSpec(
            op="FW_all2all_moe_gmm",
            kind=RuleKind.SPECIAL,
            output_count=1,
            input_count=5,
            allowed_parameter_counts=(4, 5),
            denote_fn="fw_all2all_moe_gmm",
            apply_lemmas=("applyNode_fw_all2all_moe_gmm_out_1p",),
            rank_sensitive=True,
            relation_effect=RelationEffect.SPECIAL,
        )
    )
    rules.append(
        RuleSpec(
            op="FW_topk_routing",
            kind=RuleKind.MULTI_OUTPUT,
            output_count=3,
            input_count=1,
            allowed_parameter_counts=(1, 2),
            denote_fn="fw_topk_routing",
            apply_lemmas=(
                "applyNode_fw_topk_routing_fst_out",
                "applyNode_fw_topk_routing_snd_out",
                "applyNode_fw_topk_routing_thd_out",
            ),
            output_projections=(".1", ".2.1", ".2.2"),
            relation_effect=RelationEffect.PROJECT,
        )
    )
    rules.append(
        RuleSpec(
            op="FW_rotary_embedding",
            kind=RuleKind.MULTI_OUTPUT,
            output_count=2,
            input_count=4,
            parameter_count=2,
            denote_fn="fw_rotary_embedding",
            apply_lemmas=(
                "applyNode_fw_rotary_embedding_fst_out",
                "applyNode_fw_rotary_embedding_snd_out",
            ),
            output_projections=(".1", ".2"),
            relation_effect=RelationEffect.PROJECT,
        )
    )
    rules.append(
        RuleSpec(
            op="FW_attn_zigzag",
            kind=RuleKind.SPECIAL,
            output_count=None,
            allowed_output_counts=(1, 2),
            produced_output_indices=(0,),
            input_count=5,
            parameter_count=6,
            denote_fn="applyNodeFaithfulZigzagAttnValue",
            apply_lemmas=("applyNodeDistributedFaithful_zigzag_attn_out",),
            rank_sensitive=True,
            relation_effect=RelationEffect.ZIGZAG_PRESERVE,
        )
    )
    rules.append(
        RuleSpec(
            op="FW_attn_sliding_window",
            kind=RuleKind.SPECIAL,
            output_count=None,
            allowed_output_counts=(1, 2),
            produced_output_indices=(0,),
            input_count=5,
            parameter_count=6,
            denote_fn="applyNodeRingAttn_sliding_window",
            apply_lemmas=("applyNodeRingAttn_sliding_window_out",),
            rank_sensitive=True,
            relation_effect=RelationEffect.SPECIAL,
        )
    )
    rules.append(
        RuleSpec(
            op="FW_stack",
            kind=RuleKind.SPECIAL,
            output_count=1,
            input_count=None,
            min_inputs=1,
            parameter_count=0,
            denote_fn="fw_stack",
            apply_lemmas=("applyNode_fw_stack_out",),
            relation_effect=RelationEffect.STACK,
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
    registry = RuleRegistry(rules)
    registry.register_variant(RuleSpec(
        op="FW_embedding",
        kind=RuleKind.POINTWISE,
        output_count=1,
        input_count=2,
        min_inputs=2,
        parameter_count=1,
        denote_fn="fw_embedding_offset",
        apply_lemmas=("applyNode_fw_embedding_offset_out",),
        rule_id="fw-embedding-offset",
    ))
    registry.register_variant(RuleSpec(
        op="BW_embedding",
        kind=RuleKind.POINTWISE,
        output_count=1,
        input_count=3,
        min_inputs=3,
        parameter_count=1,
        denote_fn="bw_embedding_offset",
        apply_lemmas=("applyNode_bw_embedding_offset_out",),
        rule_id="bw-embedding-offset",
    ))
    return registry


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
    rule_id: str
    rule_kind: RuleKind
    relation_effect: RelationEffect
    rank: int
    input_tids: tuple[int, ...]
    input_shapes: tuple[tuple[int, ...], ...]
    output_shape: tuple[int, ...]
    input_bindings: tuple[str, ...]
    declared_input_tids: tuple[int, ...]
    semantic_input_tids: tuple[int, ...]
    semantic_input_shapes: tuple[tuple[int, ...], ...]
    semantic_input_bindings: tuple[str, ...]
    declared_parameters: tuple[int, ...]
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
    schema_version: int = 5

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


def _collective_shape_issue(
    ir: GoalIR,
    inferred_out: Optional[dict[str, dict[int, list[int]]]] = None,
) -> Optional[Diagnostic]:
    """Validate dimension-bearing collectives against ordered inferred shapes."""
    shape_preserving = {
        "FW_layernorm", "FW_gelu", "FW_float", "FW_to", "FW_sigmoid", "FW_softmax",
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
        declared_shapes = {int(tid): list(shape) for tid, shape in initial_shapes}
        shapes = dict(declared_shapes)
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
            per_output_shapes: Optional[list[list[int]]] = None
            known_shapes = [shape for shape in input_shapes if shape is not None]
            if node.op == "FW_stack" and input_shapes:
                if all(shape is not None for shape in input_shapes):
                    stack_shapes = [shape for shape in input_shapes if shape is not None]
                    if any(shape != stack_shapes[0] for shape in stack_shapes[1:]):
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: stack input shapes differ",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    output_shape = [len(input_shapes)] + list(stack_shapes[0])
            elif node.op == "FW_inner_chunk_ce" and len(input_shapes) == 3:
                x_shape, w_shape, y_shape = input_shapes
                if x_shape is not None and w_shape is not None and y_shape is not None:
                    if len(x_shape) != 2 or len(w_shape) != 2 or x_shape[1] != w_shape[1]:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: x/weight shapes are incompatible",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    if y_shape != [x_shape[0]]:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: label shape does not match token dimension",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    per_output_shapes = [[x_shape[0]], [x_shape[0]]]
            elif node.op == "FW_multiref" and len(input_shapes) == 1:
                input_shape = input_shapes[0]
                if input_shape is not None:
                    per_output_shapes = [list(input_shape) for _ in node.outs]
            elif node.op in {"BW_attn_sliding_window", "BW_attn_zigzag"} and len(input_shapes) == 6:
                _g_shape, q_shape, k_shape, v_shape, _cuq_shape, _cuk_shape = input_shapes
                if q_shape is not None and k_shape is not None and v_shape is not None:
                    per_output_shapes = [list(q_shape), list(k_shape), list(v_shape)]
            elif node.op in {
                "FW_maybe_shuffle", "FW_maybe_unshuffle",
                "BW_maybe_shuffle", "BW_maybe_unshuffle",
            } and len(input_shapes) == 2:
                cp_size, cp_rank = (int(value) for value in (node.params or []))
                if cp_size not in {1, 2} or cp_rank < 0 or cp_rank >= cp_size:
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: unsupported cpSize or invalid cpRank",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                data_shape = input_shapes[0]
                if data_shape is not None:
                    output_shape = list(data_shape)
            elif node.op == "FW_all2all_moe_gmm_full" and len(input_shapes) >= 5:
                input_shape, rp_shape, rm_shape = input_shapes[:3]
                weight_shapes = input_shapes[3:]
                num_exp, top_k, _limit = (int(value) for value in (node.params or []))
                num_parts = len(weight_shapes) // 2
                w13_shapes = weight_shapes[:num_parts]
                w2_shapes = weight_shapes[num_parts:]
                if num_exp <= 0 or top_k <= 0 or top_k > num_exp:
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: invalid numExperts or topK",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                if all(shape is not None for shape in input_shapes):
                    assert input_shape is not None and rp_shape is not None and rm_shape is not None
                    typed_w13 = [shape for shape in w13_shapes if shape is not None]
                    typed_w2 = [shape for shape in w2_shapes if shape is not None]
                    local_exp = num_exp // num_parts if num_parts else 0
                    routing_ok = len(input_shape) == 2 and rp_shape == [input_shape[0], num_exp] and rm_shape == rp_shape
                    weights_ok = (
                        num_parts > 0 and num_exp % num_parts == 0
                        and all(len(shape) == 3 and shape[0] == local_exp and shape[2] == input_shape[1] for shape in typed_w13)
                        and all(len(shape) == 3 and shape[0] == local_exp and shape[1] == input_shape[1] for shape in typed_w2)
                        and all(w13[1] == 2 * w2[2] for w13, w2 in zip(typed_w13, typed_w2))
                    )
                    if not routing_ok or not weights_ok:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: routing or full expert weight shapes disagree",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    output_shape = list(input_shape)
            elif node.op == "FW_all2all_moe_gmm" and len(input_shapes) == 5:
                input_shape, rp_shape, rm_shape, w13_shape, w2_shape = input_shapes
                num_exp, start, end, top_k = (int(value) for value in (node.params or [])[:4])
                valid_params = 0 < num_exp and 0 <= start <= end <= num_exp and 0 < top_k <= num_exp
                if not valid_params:
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: invalid expert range or top_k",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                if all(shape is not None for shape in input_shapes):
                    assert input_shape is not None and rp_shape is not None and rm_shape is not None
                    assert w13_shape is not None and w2_shape is not None
                    local_count = end - start
                    routing_ok = len(input_shape) == 2 and rp_shape == [input_shape[0], num_exp] and rm_shape == rp_shape
                    weights_ok = (
                        len(w13_shape) == 3 and len(w2_shape) == 3
                        and w13_shape[0] == local_count and w2_shape[0] == local_count
                        and w13_shape[2] == input_shape[1] and w2_shape[1] == input_shape[1]
                        and w13_shape[1] == 2 * w2_shape[2]
                    )
                    if not routing_ok:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: routing shapes disagree with input/numExperts",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    if not weights_ok:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: local expert weight shapes disagree",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    output_shape = list(input_shape)
            elif node.op == "FW_topk_routing" and len(input_shapes) == 1:
                logits_shape = input_shapes[0]
                top_k = int((node.params or [0])[0])
                if logits_shape is not None:
                    if not logits_shape or top_k <= 0 or top_k > logits_shape[-1]:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: top_k is outside logits expert dimension",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    per_output_shapes = [list(logits_shape) for _ in range(3)]
            elif node.op in {"FW_attn_sliding_window", "FW_attn_zigzag"} and len(input_shapes) == 5:
                q_shape, k_shape, v_shape = input_shapes[:3]
                qh, kvh, d, vd, _causal, _window = (int(value) for value in (node.params or []))
                if any(value <= 0 for value in (qh, kvh, d, vd)):
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: attention dimensions must be positive",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                if q_shape is not None and k_shape is not None and v_shape is not None:
                    valid = (
                        len(q_shape) >= 2 and len(k_shape) >= 2 and len(v_shape) >= 2
                        and q_shape[-2:] == [qh, d]
                        and k_shape[-2:] == [kvh, d]
                        and v_shape[-2:] == [kvh, vd]
                    )
                    if not valid:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: attention tensor shapes disagree with parameters",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    per_output_shapes = [list(q_shape[:-1]) + [vd]]
            elif node.op == "FW_rotary_embedding" and len(input_shapes) == 4:
                q_shape, k_shape = input_shapes[2], input_shapes[3]
                if any(int(value) <= 0 for value in (node.params or [])):
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: rotary embedding requires positive head counts",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                if q_shape is not None and k_shape is not None:
                    per_output_shapes = [list(q_shape), list(k_shape)]
            elif node.op == "BW_layernorm" and len(input_shapes) == 4:
                grad_shape, input_shape, weight_shape, bias_shape = input_shapes
                if all(shape is not None for shape in input_shapes):
                    if grad_shape != input_shape or weight_shape != bias_shape:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: gradient/input or weight/bias shapes disagree",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    per_output_shapes = [
                        list(input_shape), list(weight_shape), list(bias_shape)
                    ]
            elif node.op == "BW_add" and len(input_shapes) == 3:
                grad_shape, left_shape, right_shape = input_shapes
                if all(shape is not None for shape in input_shapes):
                    combined = broadcast_shape(left_shape, right_shape)
                    if combined is None or grad_shape != combined:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: gradient does not match broadcast output",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    per_output_shapes = [list(left_shape), list(right_shape)]
            elif node.op == "BW_matmul" and len(input_shapes) == 3:
                grad_shape, left_shape, right_shape = input_shapes
                if all(shape is not None for shape in input_shapes):
                    valid = (
                        len(left_shape) >= 2 and len(right_shape) >= 2
                        and left_shape[:-2] == right_shape[:-2]
                        and left_shape[-1] == right_shape[-2]
                    )
                    expected = (
                        list(left_shape[:-1]) + [right_shape[-1]] if valid else None
                    )
                    if expected is None or grad_shape != expected:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: gradient does not match batched matmul output",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    per_output_shapes = [list(left_shape), list(right_shape)]
            elif node.op == "BW_multiref" and input_shapes:
                if all(shape is not None for shape in input_shapes):
                    if any(shape != input_shapes[0] for shape in input_shapes[1:]):
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: incoming gradient shapes differ",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    output_shape = list(input_shapes[0])
            elif node.op in {
                "BW_gelu", "BW_view", "BW_transpose", "BW_contiguous",
                "BW_softmax", "BW_div",
            } and len(input_shapes) == 2:
                if input_shapes[1] is not None:
                    output_shape = list(input_shapes[1])
            elif node.op == "BW_embedding" and len(input_shapes) == 3:
                if input_shapes[2] is not None:
                    output_shape = list(input_shapes[2])
            elif node.op == "BW_linear" and len(input_shapes) == 3:
                grad_shape, input_shape, weight_shape = input_shapes
                if all(shape is not None for shape in input_shapes):
                    if (
                        not grad_shape or not input_shape or len(weight_shape) != 2
                        or grad_shape[:-1] != input_shape[:-1]
                        or grad_shape[-1] != weight_shape[0]
                        or input_shape[-1] != weight_shape[1]
                    ):
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: gradient, input, and weight dimensions disagree",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    per_output_shapes = [list(input_shape), list(weight_shape)]
            elif node.op == "BW_sum" and len(input_shapes) == 2:
                if input_shapes[1] is not None:
                    output_shape = list(input_shapes[1])
            elif node.op == "FW_embedding" and len(input_shapes) == 2:
                ids_shape, weight_shape = input_shapes
                if ids_shape is not None and weight_shape is not None and len(weight_shape) == 2:
                    output_shape = list(ids_shape) + [weight_shape[1]]
            elif node.op in shape_preserving and input_shapes and input_shapes[0] is not None:
                output_shape = list(input_shapes[0])
            elif node.op in {"FW_swiglu", "FW_glu"} and len(input_shapes) == 2:
                first_shape, second_shape = input_shapes
                if first_shape is not None and second_shape is not None:
                    if first_shape != second_shape:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            (f"operator {node.op}: gate/up shapes differ"
                             if node.op == "FW_swiglu"
                             else f"operator {node.op}: binary input shapes differ"),
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    output_shape = list(
                        second_shape if node.op == "FW_swiglu" else first_shape
                    )
            elif node.op == "FW_rms_norm" and len(input_shapes) == 2:
                value_shape, weight_shape = input_shapes
                if value_shape is not None and weight_shape is not None:
                    if value_shape and weight_shape != [value_shape[-1]]:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: RMSNorm weight shape does not match last input dimension",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    output_shape = list(value_shape)
            elif node.op == "FW_sum":
                output_shape = [1]
            elif node.op in {"FW_add", "FW_mul"} and len(input_shapes) == 2:
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
            elif node.op in {"FW_view", "FW_reshape"} and node.params:
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
            elif node.op == "FW_matmul" and len(input_shapes) == 2:
                left_shape, right_shape = input_shapes
                if left_shape is not None and right_shape is not None:
                    if len(left_shape) < 2 or len(right_shape) < 2:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: matrix inputs must have rank at least 2",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    if left_shape[:-2] != right_shape[:-2]:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: batch dimensions differ",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    if left_shape[-1] != right_shape[-2]:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: contraction dimensions differ",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    output_shape = list(left_shape[:-1]) + [right_shape[-1]]
            elif node.op == "FW_per_head_mix_precision_linear" and len(input_shapes) == 2:
                value_shape, weight_shape = input_shapes
                if value_shape is not None and weight_shape is not None:
                    if not value_shape or len(weight_shape) != 3:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: unsupported input/weight rank",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    if value_shape[-1] != weight_shape[2]:
                        return Diagnostic(
                            DiagnosticCode.INVALID_SIGNATURE,
                            f"operator {node.op}: per-head linear inner dimensions differ",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=int(node.outs[0]) if node.outs else None,
                        )
                    output_shape = list(value_shape[:-1]) + list(weight_shape[:2])
            elif node.op in {"FW_linear", "FW_mix_precision_linear", "FW_norm_linear"} and len(input_shapes) == 2:
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
            elif node.op == "CROSS_DP_WRED" and known_shapes:
                if len(known_shapes) != len(input_shapes) or any(
                    shape != known_shapes[0] for shape in known_shapes[1:]
                ):
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: input shapes differ",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                output_shape = list(known_shapes[0])
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
            elif node.op == "ReduceScatterPrim" and known_shapes:
                if any(shape != known_shapes[0] for shape in known_shapes[1:]):
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: input shapes differ",
                        side=side, node_index=node_index, op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                if len(node.params or []) != 1:
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: expected one shard dimension",
                        side=side, node_index=node_index, op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                dimension = int(node.params[0])
                if (dimension >= len(known_shapes[0]) or num_ranks <= 0
                        or known_shapes[0][dimension] % num_ranks != 0):
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: shard dimension is not divisible by rank count",
                        side=side, node_index=node_index, op=node.op,
                        output_tid=int(node.outs[0]) if node.outs else None,
                    )
                output_shape = list(known_shapes[0])
                output_shape[dimension] //= num_ranks
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
            if per_output_shapes is not None:
                inferred_outputs = [
                    (int(tid), list(shape))
                    for tid, shape in zip(node.outs, per_output_shapes)
                ]
            elif output_shape is not None:
                inferred_outputs = [
                    (int(tid), list(output_shape)) for tid in node.outs
                ]
            else:
                inferred_outputs = []
            for tid, shape in inferred_outputs:
                declared_shape = declared_shapes.get(tid)
                if declared_shape is not None and list(declared_shape) != shape:
                    return Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op}: inferred output shape {shape} conflicts "
                        f"with declared shape {list(declared_shape)}",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=tid,
                    )
                shapes[tid] = shape
            if not inferred_outputs and node.outs:
                return Diagnostic(
                    DiagnosticCode.INVALID_SIGNATURE,
                    f"operator {node.op}: no registered shape inference for all inputs",
                    side=side,
                    node_index=node_index,
                    op=node.op,
                    output_tid=int(node.outs[0]),
                )
        inferred_shapes[side] = shapes

    if inferred_out is not None:
        inferred_out.update(
            {side: {tid: list(shape) for tid, shape in shapes.items()}
             for side, shapes in inferred_shapes.items()}
        )

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


MULTIRANK_VALUE_LOSSY_OPERATORS = frozenset()


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
    side_replica_groups = {
        "sm": tuple(ir.sm_replica_groups),
        "pm": tuple(ir.pm_replica_groups),
    }

    def replica_buddies(side: str, node_index: int) -> tuple[tuple[int, Node], ...]:
        nodes = side_nodes[side]
        node = nodes[node_index]
        if not node.outs:
            return ((node_index, node),)
        ref = (int(node.rank), int(node.outs[0]))
        matching = [
            group for group in side_replica_groups[side]
            if ref in {(member.rank, member.primary_out_tid) for member in group.members}
        ]
        if len(matching) != 1:
            return ((node_index, node),)
        group = matching[0]
        ranks = [member.rank for member in group.members]
        if len(ranks) != len(set(ranks)):
            return ((node_index, node),)
        resolved = []
        for member in group.members:
            candidates = [
                (index, candidate) for index, candidate in enumerate(nodes)
                if int(candidate.rank) == member.rank
                and candidate.outs
                and int(candidate.outs[0]) == member.primary_out_tid
            ]
            if len(candidates) != 1:
                return ((node_index, node),)
            resolved.append(candidates[0])
        if node_index not in {index for index, _candidate in resolved}:
            return ((node_index, node),)
        return tuple(resolved)

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
            output_tid = int(node.outs[0]) if node.outs else None
            num_ranks = ir.sm_num_ranks if side == "sm" else ir.pm_num_ranks
            if (
                side == "pm"
                and num_ranks > 1
                and node.op in {"BW_maybe_shuffle", "BW_maybe_unshuffle"}
            ):
                params = tuple(int(value) for value in (node.params or ()))
                cp_size = params[0] if len(params) == 2 else 0
                buddies = replica_buddies(side, node_index)
                try:
                    from .ordered_buddy_authority_policy import (
                        OrderedBuddyFailure,
                        OrderedBuddyRow,
                        check_ordered_cp_buddy_authority,
                    )
                except ImportError:
                    from ordered_buddy_authority_policy import (
                        OrderedBuddyFailure,
                        OrderedBuddyRow,
                        check_ordered_cp_buddy_authority,
                    )
                decision = check_ordered_cp_buddy_authority(
                    tuple(
                        OrderedBuddyRow(
                            buddy_index,
                            candidate.op,
                            tuple(int(value) for value in (candidate.params or ())),
                            tuple(int(tid) for tid in candidate.ins),
                        )
                        for buddy_index, candidate in buddies
                    ),
                    cp_size=cp_size,
                    expected_op=node.op,
                    current_node_key=node_index,
                )
                if decision.failure not in {
                    None,
                    OrderedBuddyFailure.UNIFORM_SIGNATURE_MISMATCH,
                }:
                    issue = Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op} requires complete ordered replica buddies",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=output_tid,
                    )
                    return ProofPlan(ir.n, relation, (), (), (issue,))
            if (
                side == "pm"
                and num_ranks > 1
                and node.op in {"BW_attn_sliding_window", "BW_attn_zigzag"}
            ):
                buddies = replica_buddies(side, node_index)
                buddy_nodes = tuple(candidate for _index, candidate in buddies)
                buddy_ranks = tuple(int(candidate.rank) for candidate in buddy_nodes)
                params = tuple(int(value) for value in (node.params or ()))
                metadata_tids = tuple(
                    tuple(int(value) for value in candidate.ins[4:6])
                    if len(candidate.ins) == 6 else (-1, -1)
                    for candidate in buddy_nodes
                )
                current = tuple(
                    offset for offset, (index, _candidate) in enumerate(buddies)
                    if index == node_index
                )
                if (
                    len(buddy_nodes) <= 1
                    or len(buddy_ranks) != len(set(buddy_ranks))
                    or current != ((buddy_ranks.index(int(node.rank)))
                                   if int(node.rank) in buddy_ranks else -1,)
                    or any(candidate.op != node.op for candidate in buddy_nodes)
                    or any(len(candidate.ins) != 6 or len(candidate.outs) != 3
                           for candidate in buddy_nodes)
                    or any(tuple(int(value) for value in (candidate.params or ())) != params
                           for candidate in buddy_nodes)
                    or len(set(metadata_tids)) != 1
                ):
                    issue = Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op} requires complete ordered replica buddies",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=output_tid,
                    )
                    return ProofPlan(ir.n, relation, (), (), (issue,))
                g_tids = tuple(int(candidate.ins[0]) for candidate in buddy_nodes)
                q_tids = tuple(int(candidate.ins[1]) for candidate in buddy_nodes)
                k_tids = tuple(int(candidate.ins[2]) for candidate in buddy_nodes)
                v_tids = tuple(int(candidate.ins[3]) for candidate in buddy_nodes)
                k_replicated = len(set(k_tids)) == 1
                v_replicated = len(set(v_tids)) == 1
                kv_coherent = (
                    k_replicated == v_replicated
                    and (
                        k_replicated
                        or (len(set(k_tids)) == len(buddy_nodes)
                            and len(set(v_tids)) == len(buddy_nodes))
                    )
                )
                if (
                    len(set(g_tids)) != len(buddy_nodes)
                    or len(set(q_tids)) != len(buddy_nodes)
                    or not kv_coherent
                    or (node.op == "BW_attn_sliding_window" and k_replicated)
                    or (node.op == "BW_attn_zigzag" and not k_replicated)
                ):
                    issue = Diagnostic(
                        DiagnosticCode.INVALID_SIGNATURE,
                        f"operator {node.op} requires coherent Q/K/V ownership with explicit K/V layout authority",
                        side=side,
                        node_index=node_index,
                        op=node.op,
                        output_tid=output_tid,
                    )
                    return ProofPlan(ir.n, relation, (), (), (issue,))
            if (
                side == "pm"
                and num_ranks > 1
                and node.op in MULTIRANK_VALUE_LOSSY_OPERATORS
            ):
                issue = Diagnostic(
                    DiagnosticCode.UNSUPPORTED_OPERATOR,
                    f"operator {node.op} lacks value-faithful distributed semantics",
                    side=side,
                    node_index=node_index,
                    op=node.op,
                    output_tid=output_tid,
                )
                return ProofPlan(ir.n, relation, (), (), (issue,))
            rule, resolution_error = registry.resolve(node, num_ranks)
            if rule is None:
                issue = Diagnostic(
                    DiagnosticCode.UNSUPPORTED_OPERATOR
                    if registry.get(node.op) is None
                    else DiagnosticCode.INVALID_SIGNATURE,
                    resolution_error or f"operator {node.op} has no registered proof rule",
                    side=side,
                    node_index=node_index,
                    op=node.op,
                    output_tid=output_tid,
                )
                return ProofPlan(ir.n, relation, (), (), (issue,))
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

    output_fingerprints: dict[tuple[str, int, int], tuple[object, ...]] = {}
    for side in ("sm", "pm"):
        current_fingerprints: dict[int, tuple[object, ...]] = {
            tid: ("external", tid) for tid in side_inputs[side]
        }
        for node_index, node in enumerate(side_nodes[side]):
            num_ranks = ir.sm_num_ranks if side == "sm" else ir.pm_num_ranks
            rule, _resolution_error = registry.resolve(node, num_ranks)
            output_indices = (
                rule.produced_output_indices
                if rule is not None and rule.produced_output_indices is not None
                else tuple(range(len(node.outs)))
            )
            input_fingerprints = tuple(
                current_fingerprints.get(int(tid), ("unresolved", int(tid)))
                for tid in node.ins
            )
            rank_component: object = int(node.rank) if rule is not None and rule.rank_sensitive else None
            for output_index in output_indices:
                tid = int(node.outs[output_index])
                fingerprint: tuple[object, ...] = (
                    "node",
                    node.op,
                    tuple(int(value) for value in (node.params or [])),
                    int(output_index),
                    rank_component,
                    input_fingerprints,
                )
                prior = writers[side].setdefault(tid, [])
                if prior:
                    previous_key = (side, prior[-1][0], prior[-1][1])
                    equivalent_rank_rewrite = (
                        rule is not None
                        and not rule.rank_sensitive
                        and output_fingerprints.get(previous_key) == fingerprint
                        and set(node.outs).isdisjoint(node.ins)
                    )
                    valid_in_place = (
                        rule is not None
                        and rule.kind is RuleKind.COLLECTIVE
                        and tid in node.ins
                    )
                    if not (valid_in_place or equivalent_rank_rewrite):
                        issue = Diagnostic(
                            DiagnosticCode.DUPLICATE_PRODUCER,
                            f"tid {tid} has multiple non-in-place producers",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=tid,
                        )
                        return ProofPlan(ir.n, relation, (), (), (issue,))
                prior.append((node_index, output_index))
                output_fingerprints[(side, node_index, output_index)] = fingerprint
                current_fingerprints[tid] = fingerprint

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

    inferred_shapes: dict[str, dict[int, list[int]]] = {}
    shape_issue = _collective_shape_issue(ir, inferred_shapes)

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

        num_ranks = ir.sm_num_ranks if side == "sm" else ir.pm_num_ranks
        rule, resolution_error = registry.resolve(node, num_ranks)
        if rule is None:
            visiting.remove(key)
            return Diagnostic(
                DiagnosticCode.UNSUPPORTED_OPERATOR
                if registry.get(node.op) is None
                else DiagnosticCode.INVALID_SIGNATURE,
                resolution_error or f"operator {node.op} has no registered proof rule",
                side=side,
                node_index=node_index,
                op=node.op,
                output_tid=output_tid,
            )
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
        input_bindings: list[str] = []
        for input_tid in node.ins:
            producer = producer_before(side, int(input_tid), node_index)
            if producer is None:
                if int(input_tid) in side_inputs[side]:
                    external_inputs.append(int(input_tid))
                    input_bindings.append(f"init:{int(input_tid)}")
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
            producer_step_id = emitted[(side, producer[0], producer[1])].step_id
            dependencies.append(producer_step_id)
            input_bindings.append(producer_step_id)

        declared_input_tids = tuple(int(tid) for tid in node.ins)
        declared_parameters = tuple(int(value) for value in (node.params or []))
        semantic_input_tids = declared_input_tids
        semantic_input_bindings = tuple(input_bindings)
        semantic_input_shapes = tuple(
            tuple(inferred_shapes.get(side, {}).get(int(tid), ()))
            for tid in semantic_input_tids
        )
        semantic_parameters = declared_parameters
        semantic_denote_fn = rule.denote_fn
        semantic_apply_lemmas = rule.apply_lemmas
        if node.op == "FW_all2all_moe_gmm":
            buddies = replica_buddies(side, node_index)
            weight_tids = tuple(int(buddy.ins[3]) for _index, buddy in buddies)
            weight_tids += tuple(int(buddy.ins[4]) for _index, buddy in buddies)
            semantic_input_tids = declared_input_tids[:3] + weight_tids
            semantic_bindings_list = list(input_bindings[:3])
            for semantic_tid in weight_tids:
                producer = producer_before(side, semantic_tid, node_index)
                if producer is None:
                    if semantic_tid not in side_inputs[side]:
                        visiting.remove(key)
                        return Diagnostic(
                            DiagnosticCode.MISSING_PRODUCER,
                            f"faithful MoE buddy weight tid {semantic_tid} has no prior producer or InitShapes entry",
                            side=side,
                            node_index=node_index,
                            op=node.op,
                            output_tid=output_tid,
                        )
                    external_inputs.append(semantic_tid)
                    semantic_bindings_list.append(f"init:{semantic_tid}")
                else:
                    issue = visit(side, producer[0], producer[1])
                    if issue is not None:
                        visiting.remove(key)
                        return issue
                    producer_step_id = emitted[(side, producer[0], producer[1])].step_id
                    dependencies.append(producer_step_id)
                    semantic_bindings_list.append(producer_step_id)
            semantic_input_bindings = tuple(semantic_bindings_list)
            semantic_input_shapes = tuple(
                tuple(inferred_shapes.get(side, {}).get(tid, ()))
                for tid in semantic_input_tids
            )
            semantic_parameters = (
                declared_parameters[0],
                declared_parameters[3],
                declared_parameters[4] if len(declared_parameters) > 4 else 10,
            )
            semantic_denote_fn = "fw_all2all_moe_gmm_full"
            semantic_apply_lemmas = ("applyNodeDistributed_moe_out",)

        relation_effect = rule.relation_effect
        if relation_effect is RelationEffect.PARAMETRIC:
            if node.op in {
                "FW_maybe_shuffle", "FW_maybe_unshuffle",
                "BW_maybe_shuffle", "BW_maybe_unshuffle",
            }:
                cp_size = int((node.params or [0])[0])
                if cp_size == 1:
                    relation_effect = RelationEffect.PRESERVE
                elif node.op in {"FW_maybe_shuffle", "BW_maybe_unshuffle"}:
                    relation_effect = RelationEffect.ORDINARY_TO_ZIGZAG
                else:
                    relation_effect = RelationEffect.ZIGZAG_TO_ORDINARY
            else:
                visiting.remove(key)
                return Diagnostic(
                    DiagnosticCode.INVALID_SIGNATURE,
                    f"operator {node.op}: unresolved parametric relation effect",
                    side=side,
                    node_index=node_index,
                    op=node.op,
                    output_tid=output_tid,
                )

        step = CertificateStep(
            step_id=f"{side}:{node_index}:{output_index}",
            side=side,
            node_index=node_index,
            output_index=output_index,
            output_tid=output_tid,
            op=node.op,
            rule_id=rule.rule_id or rule.op,
            rule_kind=rule.kind,
            relation_effect=relation_effect,
            rank=int(node.rank),
            input_tids=declared_input_tids,
            input_shapes=tuple(
                tuple(inferred_shapes.get(side, {}).get(int(tid), ()))
                for tid in node.ins
            ),
            output_shape=tuple(
                inferred_shapes.get(side, {}).get(output_tid, ())
            ),
            input_bindings=tuple(input_bindings),
            declared_input_tids=declared_input_tids,
            semantic_input_tids=semantic_input_tids,
            semantic_input_shapes=semantic_input_shapes,
            semantic_input_bindings=semantic_input_bindings,
            declared_parameters=declared_parameters,
            parameters=semantic_parameters,
            denote_fn=semantic_denote_fn,
            apply_lemmas=semantic_apply_lemmas,
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
