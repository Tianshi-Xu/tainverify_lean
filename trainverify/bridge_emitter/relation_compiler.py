"""Generic relation-composition certificates derived from typed proof plans."""
from __future__ import annotations

from dataclasses import dataclass, replace

try:
    from .parser import GoalIR, Node
    from .proof_compiler import CertificateStep, ProofPlan
except ImportError:
    from parser import GoalIR, Node
    from proof_compiler import CertificateStep, ProofPlan


class RelationCompositionError(ValueError):
    """The certificate DAG does not match a closed relation-composition rule."""


@dataclass(frozen=True)
class IndexedStackGatherCertificate:
    rule_id: str
    lean_theorem: str
    length: int
    shard_rows: int
    width: int
    sm_stack_step: str
    pm_stack_steps: tuple[str, str]
    pm_gather_step: str
    layer_step_triples: tuple[tuple[str, str, str], ...]


def _step_map(plan: ProofPlan) -> dict[str, CertificateStep]:
    by_id = {step.step_id: step for step in plan.steps}
    if len(by_id) != len(plan.steps):
        raise RelationCompositionError("certificate plan contains duplicate step ids")
    return by_id


@dataclass(frozen=True)
class InnerChunkCEGatherCertificate:
    rule_id: str
    lean_theorem: str
    label_independence_theorem: str | None
    output_projection: str
    full_rows: int
    shard_rows: int
    sm_ce_step: str
    pm_ce_steps: tuple[str, str]
    pm_gather_step: str


def match_inner_chunk_ce_projection_gather_two_rank(
    ir: GoalIR, plan: ProofPlan
) -> InnerChunkCEGatherCertificate:
    """Match one CE projection on full input against gathered rank-local CE outputs."""
    if plan.diagnostics:
        raise RelationCompositionError("cannot compose a plan with diagnostics")
    if ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2 or len(plan.target_steps) != 2:
        raise RelationCompositionError("CE projection/gather requires SM=1, PM=2 and two targets")
    by_id = _step_map(plan)
    try:
        sm_ce = by_id[plan.target_steps[0]]
        pm_gather = by_id[plan.target_steps[1]]
    except KeyError as exc:
        raise RelationCompositionError("target step is absent from certificate DAG") from exc
    if sm_ce.side != "sm" or sm_ce.op != "FW_inner_chunk_ce":
        raise RelationCompositionError("SM target is not an inner-chunk CE projection")
    if (
        pm_gather.side != "pm"
        or pm_gather.op != "AllGatherPrim"
        or pm_gather.parameters != (0,)
        or len(pm_gather.dependencies) != 2
        or len(pm_gather.input_tids) != 2
    ):
        raise RelationCompositionError("PM target is not a dimension-0 two-rank AllGather")
    try:
        pm_ce = tuple(by_id[step_id] for step_id in pm_gather.dependencies)
    except KeyError as exc:
        raise RelationCompositionError("AllGather dependency is absent") from exc
    if tuple(step.output_tid for step in pm_ce) != pm_gather.input_tids:
        raise RelationCompositionError("AllGather inputs and CE producers disagree")
    if tuple(step.rank for step in pm_ce) != (0, 1):
        raise RelationCompositionError("CE pieces are not rank-ordered (0, 1)")
    if any(step.side != "pm" or step.op != "FW_inner_chunk_ce" for step in pm_ce):
        raise RelationCompositionError("AllGather inputs are not CE projections")
    projection = sm_ce.output_projection
    if projection not in {".fst", ".snd"} or any(
        step.output_projection != projection for step in pm_ce
    ):
        raise RelationCompositionError("SM and PM CE output projection mismatch")
    if any(step.parameters != sm_ce.parameters for step in pm_ce):
        raise RelationCompositionError("SM and PM CE vocabulary parameters differ")
    if len(sm_ce.input_tids) != 3 or any(len(step.input_tids) != 3 for step in pm_ce):
        raise RelationCompositionError("CE signature is not ternary")
    if any(step.input_tids[1] != sm_ce.input_tids[1] for step in pm_ce):
        raise RelationCompositionError("CE weight is not shared across SM and PM")
    if len(ir.lineage.tsShape) != 1:
        raise RelationCompositionError("CE output lineage is not rank-1")
    full_rows = int(ir.lineage.tsShape[0])
    if full_rows <= 0 or full_rows % 2:
        raise RelationCompositionError("CE output rows do not split equally across two ranks")
    if projection == ".fst":
        theorem = "TrainVerify.Denote.fw_inner_chunk_ce_fst_allGather0_commute_2_of"
        label_theorem = None
    else:
        theorem = "TrainVerify.Denote.fw_inner_chunk_ce_snd_allGatherDim0_shards"
        label_theorem = (
            "TrainVerify.Denote.RelationCompiler."
            "inner_chunk_ce_snd_labels_independent"
        )
    return InnerChunkCEGatherCertificate(
        rule_id="inner-chunk-ce-projection-gather-two-rank",
        lean_theorem=theorem,
        label_independence_theorem=label_theorem,
        output_projection=projection,
        full_rows=full_rows,
        shard_rows=full_rows // 2,
        sm_ce_step=sm_ce.step_id,
        pm_ce_steps=(pm_ce[0].step_id, pm_ce[1].step_id),
        pm_gather_step=pm_gather.step_id,
    )


@dataclass(frozen=True)
class SynchronizedRelationStep:
    rule_id: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    output_projection: str
    lean_theorems: tuple[str, ...]
    metadata_tid: int | None = None


def _topk_theorem(projection: str, *, zigzag: bool) -> str:
    if zigzag:
        names = {
            ".1": "topk_routing_probs",
            ".2.1": "topk_routing_map",
            ".2.2": "topk_routing_gate_scores",
        }
        prefix = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel."
    else:
        names = {
            ".1": "topk_routing_probs_allGather0_commute_two",
            ".2.1": "topk_routing_map_allGather0_commute_two",
            ".2.2": "topk_routing_gate_scores_allGather0_commute_two",
        }
        prefix = "TrainVerify.Denote.RelationCompiler."
    try:
        return prefix + names[projection]
    except KeyError as exc:
        raise RelationCompositionError(f"unsupported top-k output projection {projection}") from exc


@dataclass(frozen=True)
class ChunkReconstructionCertificate:
    rule_id: str
    input_relation_kind: str
    output_step_triple: tuple[str, str, str]
    sm_full_step: str
    pm_full_source_step: str
    shard_rows: int
    width: int
    lean_theorem: str


@dataclass(frozen=True)
class RouterInputCheckpointCertificate:
    rule_id: str
    input_relation_kind: str
    equality_steps: tuple[str, str]
    wrapper_ops: tuple[str, ...]
    previous_relation_step_triple: tuple[str, str, str]


@dataclass(frozen=True)
class RMSNormRelationCertificate:
    rule_id: str
    input_relation_kind: str
    exposed_output_step_triple: tuple[str, str, str]
    operator_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    shared_weight_tid: int
    lean_theorem: str


def _strip_multiref_alias(step: CertificateStep, by_id: dict[str, CertificateStep]) -> CertificateStep:
    if step.op != "FW_multiref" or len(step.dependencies) != 1:
        raise RelationCompositionError("expected a unary multiref alias")
    return by_id[step.dependencies[0]]


@dataclass(frozen=True)
class ZigzagQRelationCertificate:
    rule_id: str
    input_relation_kind: str
    output_step_triple: tuple[str, str, str]
    full_linear_step: str
    gathered_linear_step: str
    gather_step: str
    input_step_triple: tuple[str, str, str]
    replicated_weight_tid: int
    lean_theorems: tuple[str, str]


def build_zigzag_attention_q_relations(
    plan: ProofPlan,
    attention_relations: tuple[AttentionRelationCertificate, ...],
) -> tuple[ZigzagQRelationCertificate, ...]:
    """Recognize full-Q versus gather/linear/chunk faithful zigzag transport."""
    by_id = _step_map(plan)
    result = []
    for attention in attention_relations:
        if attention.input_relation_kind != "zigzag":
            continue
        triple = attention.input_relation_step_triples[0]
        sm = by_id[triple[0]]
        chunks = (by_id[triple[1]], by_id[triple[2]])
        if sm.op != "FW_per_head_mix_precision_linear":
            raise RelationCompositionError("zigzag full Q is not per-head linear")
        if any(step.op != "ChunkPrim" or step.parameters != (0,) for step in chunks):
            raise RelationCompositionError("zigzag PM Q outputs are not dim-0 chunks")
        if tuple(step.rank for step in chunks) != (0, 1):
            raise RelationCompositionError("zigzag PM Q chunks are not rank ordered")
        source_bindings = tuple(step.input_bindings[0] for step in chunks)
        if len(set(source_bindings)) != 1 or source_bindings[0].startswith("init:"):
            raise RelationCompositionError("zigzag PM Q chunks do not share one produced source")
        pm_linear = by_id[source_bindings[0]]
        if pm_linear.op != "FW_per_head_mix_precision_linear":
            raise RelationCompositionError("zigzag PM Q chunk source is not per-head linear")
        if len(sm.input_bindings) != 2 or len(pm_linear.input_bindings) != 2:
            raise RelationCompositionError("zigzag Q linear signature is not binary")
        weights = (sm.input_bindings[1], pm_linear.input_bindings[1])
        if weights[0] != weights[1] or not weights[0].startswith("init:"):
            raise RelationCompositionError("zigzag Q linear weights are not replicated")
        gather_binding = pm_linear.input_bindings[0]
        if gather_binding.startswith("init:"):
            raise RelationCompositionError("zigzag PM Q linear input is not gathered")
        gather = by_id[gather_binding]
        if gather.op != "AllGatherPrim" or gather.parameters != (0,) or len(gather.input_bindings) != 2:
            raise RelationCompositionError("zigzag PM Q source is not a two-piece dim-0 gather")
        if sm.input_bindings[0].startswith("init:") or any(
            binding.startswith("init:") for binding in gather.input_bindings
        ):
            raise RelationCompositionError("zigzag Q input relation lacks produced tensors")
        result.append(ZigzagQRelationCertificate(
            rule_id="zigzag-q-gather-linear-chunk-two-rank",
            input_relation_kind="zigzag",
            output_step_triple=triple,
            full_linear_step=sm.step_id,
            gathered_linear_step=pm_linear.step_id,
            gather_step=gather.step_id,
            input_step_triple=(sm.input_bindings[0], *gather.input_bindings),
            replicated_weight_tid=int(weights[0].split(":", 1)[1]),
            lean_theorems=(
                "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.per_head_linear",
                "TrainVerify.Denote.fw_per_head_mix_precision_linear_allGather0_commute_2",
            ),
        ))
    return tuple(result)


@dataclass(frozen=True)
class KVRelationStepCertificate:
    rule_id: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    lean_theorem: str


@dataclass(frozen=True)
class ZigzagAttentionKVRelationCertificate:
    rule_id: str
    role: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    steps: tuple[KVRelationStepCertificate, ...]


def build_zigzag_attention_kv_relations(
    plan: ProofPlan,
    attention_relations: tuple[AttentionRelationCertificate, ...],
) -> tuple[ZigzagAttentionKVRelationCertificate, ...]:
    """Keep K/V ordinary while Q and attention outputs use zigzag layout."""
    by_id = _step_map(plan)
    result = []
    for attention in attention_relations:
        if attention.input_relation_kind != "zigzag":
            continue
        for role, start in zip(("k", "v"), attention.input_relation_step_triples[1:]):
            current = start
            certificates = []
            specs = (
                ("FW_to", "to-identity", "TrainVerify.Denote.fw_to_allGather0_commute_2"),
                ("FW_multiref", "multiref-alias", "TrainVerify.Denote.fw_multiref_allGather0_commute_2"),
                ("FW_per_head_mix_precision_linear", "per-head-mix-precision-linear-ordinary", "TrainVerify.Denote.fw_per_head_mix_precision_linear_allGather0_commute_2"),
            )
            for op, rule_id, theorem in specs:
                steps = tuple(by_id[step_id] for step_id in current)
                if any(step.op != op for step in steps):
                    raise RelationCompositionError(f"zigzag attention {role} chain expected {op}")
                if op == "FW_per_head_mix_precision_linear":
                    if any(len(step.input_bindings) != 2 for step in steps):
                        raise RelationCompositionError("per-head K/V linear signature is not binary")
                    weights = tuple(step.input_bindings[1] for step in steps)
                    if len(set(weights)) != 1 or not weights[0].startswith("init:"):
                        raise RelationCompositionError("per-head K/V weights are not replicated")
                    next_triple = _produced_binding_triple(steps, 0)
                else:
                    if any(len(step.input_bindings) != 1 for step in steps):
                        raise RelationCompositionError(f"{op} is not unary")
                    if op == "FW_to" and any(step.input_shapes[0] != step.output_shape for step in steps):
                        raise RelationCompositionError("FW_to changed a K/V shape")
                    next_triple = _produced_binding_triple(steps, 0)
                certificates.append(KVRelationStepCertificate(
                    rule_id=rule_id,
                    output_step_triple=current,
                    input_step_triple=next_triple,
                    lean_theorem=theorem,
                ))
                current = next_triple
            result.append(ZigzagAttentionKVRelationCertificate(
                rule_id=f"zigzag-attention-{role}-ordinary-input-chain",
                role=role,
                relation_kind="ordinary",
                output_step_triple=start,
                input_step_triple=current,
                steps=tuple(certificates),
            ))
    return tuple(result)


@dataclass(frozen=True)
class RotaryRelationCertificate:
    rule_id: str
    relation_kind: str
    output_step_triples: tuple[tuple[str, str, str], tuple[str, str, str]]
    output_projections: tuple[str, str]
    input_roles: tuple[str, str, str]
    input_relation_step_triples: tuple[
        tuple[str, str, str], tuple[str, str, str], tuple[str, str, str]
    ]
    replicated_cos_sin_tid: int
    lean_theorem: str


@dataclass(frozen=True)
class PerHeadLinearRelationCertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_role: str
    input_relation_step_triple: tuple[str, str, str]
    replicated_weight_tid: int
    lean_theorem: str


def _produced_binding_triple(
    steps: tuple[CertificateStep, CertificateStep, CertificateStep], index: int
) -> tuple[str, str, str]:
    bindings = tuple(step.input_bindings[index] for step in steps)
    if any(binding.startswith("init:") for binding in bindings):
        raise RelationCompositionError("expected a produced relation input")
    return bindings


def build_ordinary_rotary_relations(
    plan: ProofPlan,
    attention_relations: tuple[AttentionRelationCertificate, ...],
) -> tuple[RotaryRelationCertificate, ...]:
    by_id = _step_map(plan)
    result = []
    for attention in attention_relations:
        if attention.input_relation_kind != "ordinary":
            continue
        q_triple, k_triple, _v_triple = attention.input_relation_step_triples
        q_steps = tuple(by_id[step_id] for step_id in q_triple)
        k_steps = tuple(by_id[step_id] for step_id in k_triple)
        if any(step.op != "FW_rotary_embedding" or step.output_index != 0 for step in q_steps):
            raise RelationCompositionError("ordinary Q frontier is not rotary projection zero")
        if any(step.op != "FW_rotary_embedding" or step.output_index != 1 for step in k_steps):
            raise RelationCompositionError("ordinary K frontier is not rotary projection one")
        if any(q.node_index != k.node_index or q.input_bindings != k.input_bindings for q, k in zip(q_steps, k_steps)):
            raise RelationCompositionError("rotary Q/K projections do not share one operator application")
        projections = (q_steps[0].output_projection, k_steps[0].output_projection)
        if projections != (".1", ".2"):
            raise RelationCompositionError("rotary output projections are not the registered pair")
        cos_bindings = tuple(step.input_bindings[0] for step in q_steps)
        if len(set(cos_bindings)) != 1 or not cos_bindings[0].startswith("init:"):
            raise RelationCompositionError("rotary cos/sin input is not replicated")
        result.append(RotaryRelationCertificate(
            rule_id="rotary-embedding-ordinary-two-rank",
            relation_kind="ordinary",
            output_step_triples=(q_triple, k_triple),
            output_projections=projections,
            input_roles=("position", "q", "k"),
            input_relation_step_triples=(
                tuple(step.input_bindings[1] for step in q_steps),
                _produced_binding_triple(q_steps, 2),
                _produced_binding_triple(q_steps, 3),
            ),
            replicated_cos_sin_tid=int(cos_bindings[0].split(":", 1)[1]),
            lean_theorem="TrainVerify.Denote.fw_rotary_embedding_allGather0_commute_2",
        ))
    return tuple(result)


def build_ordinary_attention_v_relations(
    plan: ProofPlan,
    attention_relations: tuple[AttentionRelationCertificate, ...],
) -> tuple[PerHeadLinearRelationCertificate, ...]:
    by_id = _step_map(plan)
    result = []
    for attention in attention_relations:
        if attention.input_relation_kind != "ordinary":
            continue
        triple = attention.input_relation_step_triples[2]
        steps = tuple(by_id[step_id] for step_id in triple)
        if any(step.op != "FW_per_head_mix_precision_linear" or len(step.input_bindings) != 2 for step in steps):
            raise RelationCompositionError("ordinary V frontier is not per-head linear")
        weight_bindings = tuple(step.input_bindings[1] for step in steps)
        if len(set(weight_bindings)) != 1 or not weight_bindings[0].startswith("init:"):
            raise RelationCompositionError("per-head V weights are not replicated")
        result.append(PerHeadLinearRelationCertificate(
            rule_id="per-head-mix-precision-linear-ordinary-two-rank",
            relation_kind="ordinary",
            output_step_triple=triple,
            input_role="v-hidden",
            input_relation_step_triple=_produced_binding_triple(steps, 0),
            replicated_weight_tid=int(weight_bindings[0].split(":", 1)[1]),
            lean_theorem="TrainVerify.Denote.fw_per_head_mix_precision_linear_allGather0_commute_2",
        ))
    return tuple(result)


@dataclass(frozen=True)
class AttentionRelationCertificate:
    rule_id: str
    input_relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_roles: tuple[str, str, str]
    input_layouts: tuple[str, str, str]
    input_relation_step_triples: tuple[
        tuple[str, str, str], tuple[str, str, str], tuple[str, str, str]
    ]
    metadata_tids: tuple[int, int]
    parameters: tuple[int, ...]
    full_output_shape: tuple[int, ...]
    piece_output_shape: tuple[int, ...]
    lean_theorem: str


def build_attention_relations(
    plan: ProofPlan,
    unary_chains: tuple[UnaryRelationChainCertificate, ...],
) -> tuple[AttentionRelationCertificate, ...]:
    """Synchronize ordinary sliding attention and faithful zigzag attention."""
    by_id = _step_map(plan)
    result = []
    for chain in unary_chains:
        steps = tuple(by_id[step_id] for step_id in chain.input_step_triple)
        kind = chain.input_relation_kind
        expected_op = "FW_attn_sliding_window" if kind == "ordinary" else "FW_attn_zigzag"
        if any(step.op != expected_op or len(step.input_tids) != 5 for step in steps):
            raise RelationCompositionError(f"expected synchronized {expected_op} nodes")
        if any(len(step.dependencies) != 3 for step in steps):
            raise RelationCompositionError("attention must expose produced q/k/v dependencies")
        if tuple(step.rank for step in steps) != (0, 0, 1):
            raise RelationCompositionError("attention PM buddies are not rank ordered")
        parameter_sets = {step.parameters for step in steps}
        if len(parameter_sets) != 1:
            raise RelationCompositionError("attention parameters disagree across SM/PM")
        metadata = tuple(steps[0].input_tids[3:5])
        if len(metadata) != 2 or any(tuple(step.input_tids[3:5]) != metadata for step in steps[1:]):
            raise RelationCompositionError("attention metadata inputs are not shared")
        full_shape = steps[0].output_shape
        piece_shapes = (steps[1].output_shape, steps[2].output_shape)
        if piece_shapes[0] != piece_shapes[1] or len(full_shape) != 3 or len(piece_shapes[0]) != 3:
            raise RelationCompositionError("attention output shapes are not compatible rank-3 tensors")
        if full_shape[0] != 2 * piece_shapes[0][0] or full_shape[1:] != piece_shapes[0][1:]:
            raise RelationCompositionError("attention output shapes do not preserve the two-rank row split")
        inputs = tuple(
            tuple(step.dependencies[input_index] for step in steps)
            for input_index in range(3)
        )
        if kind == "ordinary":
            rule_id = "sliding-window-attention-ordinary-two-rank"
            layouts = ("ordinary", "ordinary", "ordinary")
            theorem = (
                "TrainVerify.Denote.GeneratedPatterns."
                "applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair"
            )
        else:
            rule_id = "zigzag-attention-sharded-kv-two-rank"
            layouts = ("zigzag", "ordinary", "ordinary")
            theorem = (
                "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel."
                "attn_zigzag_sharded_kv"
            )
        result.append(AttentionRelationCertificate(
            rule_id=rule_id,
            input_relation_kind=kind,
            output_step_triple=chain.input_step_triple,
            input_roles=("q", "k", "v"),
            input_layouts=layouts,
            input_relation_step_triples=inputs,
            metadata_tids=metadata,
            parameters=steps[0].parameters,
            full_output_shape=full_shape,
            piece_output_shape=piece_shapes[0],
            lean_theorem=theorem,
        ))
    return tuple(result)


@dataclass(frozen=True)
class UnaryRelationCertificate:
    rule_id: str
    input_relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    full_input_shape: tuple[int, ...]
    piece_input_shape: tuple[int, ...]
    full_output_shape: tuple[int, ...]
    piece_output_shape: tuple[int, ...]
    lean_theorem: str


@dataclass(frozen=True)
class UnaryRelationChainCertificate:
    rule_id: str
    input_relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    steps: tuple[UnaryRelationCertificate, ...]


def _shape_maps(ir: GoalIR) -> tuple[dict[int, tuple[int, ...]], dict[int, tuple[int, ...]]]:
    sm = {tid: tuple(shape) for tid, shape in ir.sm_shapes}
    pm = {tid: tuple(shape) for tid, shape in ir.pm_shapes}
    if len(sm) != len(ir.sm_shapes) or len(pm) != len(ir.pm_shapes):
        raise RelationCompositionError("duplicate shape tids are forbidden")
    return sm, pm


def build_attention_output_unary_relations(
    ir: GoalIR,
    plan: ProofPlan,
    add_relations: tuple[AddRelationCertificate, ...],
) -> tuple[UnaryRelationChainCertificate, ...]:
    """Compile the shape-sensitive unary chain from attention to residual add."""
    by_id = _step_map(plan)
    _shape_maps(ir)  # retain the duplicate-shape-TID fail-closed boundary
    expected_ops = (
        "FW_float", "FW_view", "FW_mix_precision_linear", "FW_reshape", "FW_reshape"
    )
    rule_ids = (
        "float-identity", "view-2d-identity", "mix-precision-linear-2d",
        "reshape-2d-identity", "reshape-3d-to-2d",
    )
    result = []
    for add in add_relations:
        current = add.input_relation_step_triples[1]
        chain = []
        for position, (expected_op, rule_id) in enumerate(zip(expected_ops, rule_ids)):
            steps = tuple(by_id[step_id] for step_id in current)
            if any(step.op != expected_op or len(step.dependencies) != 1 for step in steps):
                raise RelationCompositionError(
                    f"attention output unary chain expected {expected_op} at position {position}"
                )
            input_shapes = tuple(step.input_shapes[0] for step in steps)
            output_shapes = tuple(step.output_shape for step in steps)
            full_in, p0_in, p1_in = input_shapes
            full_out, p0_out, p1_out = output_shapes
            if p0_in != p1_in or p0_out != p1_out:
                raise RelationCompositionError("rank-local unary shapes disagree")
            if len(full_in) < 2 or len(p0_in) < 2 or full_in[0] != 2 * p0_in[0]:
                raise RelationCompositionError("unary relation does not preserve the two-rank row split")
            if rule_id in {"float-identity", "view-2d-identity", "reshape-2d-identity"}:
                if full_in != full_out or p0_in != p0_out or len(full_in) != 2:
                    raise RelationCompositionError(f"{rule_id} is not shape identity")
                if expected_op != "FW_float":
                    if tuple(steps[0].parameters) != full_out or tuple(steps[1].parameters) != p0_out or tuple(steps[2].parameters) != p1_out:
                        raise RelationCompositionError(f"{rule_id} target shapes do not match outputs")
            elif rule_id == "mix-precision-linear-2d":
                if any(len(step.input_tids) != 2 for step in steps):
                    raise RelationCompositionError("mix-precision linear is not binary")
                weight_tids = tuple(step.input_tids[1] for step in steps)
                if len(set(weight_tids)) != 1:
                    raise RelationCompositionError("mix-precision linear weights are not shared")
                weight_shapes = tuple(step.input_shapes[1] for step in steps)
                if len(set(weight_shapes)) != 1 or len(weight_shapes[0]) != 2:
                    raise RelationCompositionError("mix-precision linear weight shapes disagree")
                weight_shape = weight_shapes[0]
                out_dim, in_dim = weight_shape
                if full_in[1] != in_dim or p0_in[1] != in_dim or full_out != (full_in[0], out_dim) or p0_out != (p0_in[0], out_dim):
                    raise RelationCompositionError("mix-precision linear dimensions are incompatible")
            else:
                if len(full_in) != 3 or len(p0_in) != 3:
                    raise RelationCompositionError("reshape-3d-to-2d requires rank-3 inputs")
                if full_out != (full_in[0], full_in[1] * full_in[2]) or p0_out != (p0_in[0], p0_in[1] * p0_in[2]):
                    raise RelationCompositionError("reshape-3d-to-2d dimensions are incompatible")
                if tuple(steps[0].parameters) != full_out or tuple(steps[1].parameters) != p0_out or tuple(steps[2].parameters) != p1_out:
                    raise RelationCompositionError("reshape-3d-to-2d target shapes do not match outputs")
            kind = add.input_relation_kind
            if kind == "ordinary":
                theorem = {
                    "float-identity": "TrainVerify.Denote.fw_float_allGather0_commute_2",
                    "view-2d-identity": "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.view_id",
                    "mix-precision-linear-2d": "TrainVerify.Denote.fw_mix_precision_linear_allGather0_commute_2",
                    "reshape-2d-identity": "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.view_id",
                    "reshape-3d-to-2d": "TrainVerify.Denote.GeneratedPatterns.fw_view_allGather0_commute_cp2",
                }[rule_id]
            else:
                theorem = {
                    "float-identity": "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.fw_float",
                    "view-2d-identity": "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_id",
                    "mix-precision-linear-2d": "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.mix_precision_linear",
                    "reshape-2d-identity": "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_id",
                    "reshape-3d-to-2d": "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_3d_to_2d",
                }[rule_id]
            next_triple = tuple(step.dependencies[0] for step in steps)
            chain.append(UnaryRelationCertificate(
                rule_id=rule_id,
                input_relation_kind=kind,
                output_step_triple=current,
                input_step_triple=next_triple,
                full_input_shape=full_in,
                piece_input_shape=p0_in,
                full_output_shape=full_out,
                piece_output_shape=p0_out,
                lean_theorem=theorem,
            ))
            current = next_triple
        result.append(UnaryRelationChainCertificate(
            rule_id=f"attention-output-unary-chain-{add.input_relation_kind}",
            input_relation_kind=add.input_relation_kind,
            output_step_triple=add.input_relation_step_triples[1],
            input_step_triple=current,
            steps=tuple(chain),
        ))
    return tuple(result)


@dataclass(frozen=True)
class AddRelationCertificate:
    rule_id: str
    input_relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_relation_step_triples: tuple[
        tuple[str, str, str], tuple[str, str, str]
    ]
    lean_theorem: str


def build_add_relations(
    plan: ProofPlan,
    rms_relations: tuple[RMSNormRelationCertificate, ...],
) -> tuple[AddRelationCertificate, ...]:
    """Split synchronized residual adds into two relation prerequisites."""
    by_id = _step_map(plan)
    result = []
    for rms in rms_relations:
        steps = tuple(by_id[step_id] for step_id in rms.input_step_triple)
        if any(step.op != "FW_add" or len(step.dependencies) != 2 for step in steps):
            raise RelationCompositionError("RMSNorm input frontier is not a synchronized binary add")
        left = tuple(step.dependencies[0] for step in steps)
        right = tuple(step.dependencies[1] for step in steps)
        kind = rms.input_relation_kind
        theorem = (
            "TrainVerify.Denote.GeneratedPatterns.elemwiseAdd_allGather0_commute_cp2"
            if kind == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.add"
        )
        result.append(AddRelationCertificate(
            rule_id=f"elementwise-add-{kind}-two-rank",
            input_relation_kind=kind,
            output_step_triple=rms.input_step_triple,
            input_relation_step_triples=(left, right),
            lean_theorem=theorem,
        ))
    return tuple(result)


def build_rms_norm_relations(
    plan: ProofPlan,
    checkpoints: tuple[RouterInputCheckpointCertificate, ...],
) -> tuple[RMSNormRelationCertificate, ...]:
    """Synchronize RMSNorm across full/rank0/rank1 after stripping aliases."""
    by_id = _step_map(plan)
    result = []
    for checkpoint in checkpoints:
        exposed = checkpoint.previous_relation_step_triple
        sm = by_id[exposed[0]]
        pm0 = _strip_multiref_alias(by_id[exposed[1]], by_id)
        pm1 = _strip_multiref_alias(by_id[exposed[2]], by_id)
        if sm.op != "FW_rms_norm" or pm0.op != "FW_rms_norm" or pm1.op != "FW_rms_norm":
            raise RelationCompositionError("router checkpoint is not produced by synchronized RMSNorm")
        if any(len(step.input_tids) != 2 or len(step.dependencies) != 1 for step in (sm, pm0, pm1)):
            raise RelationCompositionError("RMSNorm certificate signature is not binary with one produced input")
        weights = (sm.input_tids[1], pm0.input_tids[1], pm1.input_tids[1])
        if len(set(weights)) != 1:
            raise RelationCompositionError("RMSNorm weights are not shared")
        sm_input = _strip_multiref_alias(by_id[sm.dependencies[0]], by_id)
        pm0_input = _strip_multiref_alias(by_id[pm0.dependencies[0]], by_id)
        pm1_input = _strip_multiref_alias(by_id[pm1.dependencies[0]], by_id)
        kind = checkpoint.input_relation_kind
        theorem = (
            "TrainVerify.Denote.ZigzagCollective.fw_rms_norm_allGather0_commute_2_core"
            if kind == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.rms_norm"
        )
        result.append(RMSNormRelationCertificate(
            rule_id=f"rms-norm-{kind}-two-rank",
            input_relation_kind=kind,
            exposed_output_step_triple=exposed,
            operator_step_triple=(sm.step_id, pm0.step_id, pm1.step_id),
            input_step_triple=(sm_input.step_id, pm0_input.step_id, pm1_input.step_id),
            shared_weight_tid=weights[0],
            lean_theorem=theorem,
        ))
    return tuple(result)


def build_router_input_checkpoints(
    plan: ProofPlan,
    chunks: tuple[ChunkReconstructionCertificate, ...],
) -> tuple[RouterInputCheckpointCertificate, ...]:
    """Peel congruent router wrappers to the previous layer gather relation."""
    by_id = _step_map(plan)
    result = []
    for chunk in chunks:
        left_id = chunk.sm_full_step
        right_id = chunk.pm_full_source_step
        wrappers = []
        for expected in ("FW_norm_linear", "FW_float"):
            left = by_id[left_id]
            right = by_id[right_id]
            if left.op != expected or right.op != expected:
                raise RelationCompositionError(f"router equality lacks congruent {expected} wrapper")
            if (
                left.parameters != right.parameters
                or left.output_projection != right.output_projection
                or left.external_inputs != right.external_inputs
                or len(left.dependencies) != 1
                or len(right.dependencies) != 1
            ):
                raise RelationCompositionError(f"router {expected} wrappers are not congruent")
            wrappers.append(expected)
            left_id = left.dependencies[0]
            right_id = right.dependencies[0]
        left = by_id[left_id]
        right = by_id[right_id]
        if left.op != "FW_multiref" or len(left.dependencies) != 1:
            raise RelationCompositionError("SM router input boundary is not a multiref alias")
        if (
            right.op != "AllGatherPrim"
            or right.parameters != (0,)
            or len(right.dependencies) != 2
            or len(right.input_tids) != 2
        ):
            raise RelationCompositionError("PM router input boundary is not a two-rank dim-0 gather")
        pieces = tuple(by_id[step_id] for step_id in right.dependencies)
        if tuple(step.rank for step in pieces) != (0, 1):
            raise RelationCompositionError("PM previous-layer pieces are not rank-ordered")
        result.append(RouterInputCheckpointCertificate(
            rule_id=f"router-input-from-{chunk.input_relation_kind}-gather",
            input_relation_kind=chunk.input_relation_kind,
            equality_steps=(chunk.sm_full_step, chunk.pm_full_source_step),
            wrapper_ops=tuple(wrappers),
            previous_relation_step_triple=(left.dependencies[0], right.dependencies[0], right.dependencies[1]),
        ))
    return tuple(result)


def build_chunk_reconstruction_relations(
    plan: ProofPlan,
    terminal: IndexedStackGatherCertificate,
    layers: tuple[SynchronizedRelationStep, ...],
) -> tuple[ChunkReconstructionCertificate, ...]:
    """Turn SM/full + two PM ChunkPrim outputs into equality prerequisites."""
    by_id = _step_map(plan)
    result = []
    for layer in layers:
        try:
            sm, chunk0, chunk1 = (by_id[step_id] for step_id in layer.input_step_triple)
        except KeyError as exc:
            raise RelationCompositionError("layer relation frontier step is absent") from exc
        if chunk0.op != "ChunkPrim" or chunk1.op != "ChunkPrim":
            raise RelationCompositionError("PM relation frontier is not a ChunkPrim pair")
        if (chunk0.rank, chunk1.rank) != (0, 1) or chunk0.parameters != (0,) or chunk1.parameters != (0,):
            raise RelationCompositionError("ChunkPrim pair is not rank-ordered along dimension 0")
        if (
            len(chunk0.input_tids) != 1
            or len(chunk1.input_tids) != 1
            or chunk0.input_tids != chunk1.input_tids
            or len(chunk0.dependencies) != 1
            or chunk0.dependencies != chunk1.dependencies
        ):
            raise RelationCompositionError("ChunkPrim pieces do not share the same PM full source")
        relation_kind = (
            "zigzag" if layer.rule_id == "zigzag-topk-unshuffle-two-rank" else "ordinary"
        )
        result.append(ChunkReconstructionCertificate(
            rule_id="chunk-reconstruct-dim0-two-rank",
            input_relation_kind=relation_kind,
            output_step_triple=layer.input_step_triple,
            sm_full_step=sm.step_id,
            pm_full_source_step=chunk0.dependencies[0],
            shard_rows=terminal.shard_rows,
            width=terminal.width,
            lean_theorem=(
                "TrainVerify.Denote.RelationCompiler."
                "allGather0_reconstruct_chunks_2d"
            ),
        ))
    return tuple(result)


def build_indexed_stack_layer_relations(
    plan: ProofPlan, terminal: IndexedStackGatherCertificate
) -> tuple[SynchronizedRelationStep, ...]:
    """Join each full/rank0/rank1 payload into a synchronized relation step."""
    by_id = _step_map(plan)
    result = []
    for triple in terminal.layer_step_triples:
        try:
            sm, pm0, pm1 = (by_id[step_id] for step_id in triple)
        except KeyError as exc:
            raise RelationCompositionError("stack payload step is absent") from exc
        if (sm.side, pm0.side, pm1.side) != ("sm", "pm", "pm"):
            raise RelationCompositionError("stack payload sides are not SM/PM/PM")
        if (pm0.rank, pm1.rank) != (0, 1):
            raise RelationCompositionError("stack payload pieces are not rank-ordered")

        if sm.op == pm0.op == pm1.op == "FW_topk_routing":
            projection = sm.output_projection or ""
            if any(step.output_projection != projection for step in (pm0, pm1)):
                raise RelationCompositionError("ordinary top-k projection mismatch")
            if any(len(step.dependencies) != 1 for step in (sm, pm0, pm1)):
                raise RelationCompositionError("top-k projection has non-unary ancestry")
            result.append(SynchronizedRelationStep(
                rule_id="ordinary-topk-projection-two-rank",
                output_step_triple=triple,
                input_step_triple=(sm.dependencies[0], pm0.dependencies[0], pm1.dependencies[0]),
                output_projection=projection,
                lean_theorems=(_topk_theorem(projection, zigzag=False),),
            ))
            continue

        if sm.op == pm0.op == pm1.op == "FW_maybe_unshuffle":
            if sm.parameters != (1, 0) or pm0.parameters != (2, 0) or pm1.parameters != (2, 1):
                raise RelationCompositionError("unshuffle CP/rank parameters are not (1,0)/(2,0)/(2,1)")
            if len({sm.input_tids[1], pm0.input_tids[1], pm1.input_tids[1]}) != 1:
                raise RelationCompositionError("unshuffle metadata tensor ids differ")
            if any(len(step.dependencies) != 1 for step in (sm, pm0, pm1)):
                raise RelationCompositionError("unshuffle payload ancestry is not unary")
            try:
                topk = tuple(by_id[step.dependencies[0]] for step in (sm, pm0, pm1))
            except KeyError as exc:
                raise RelationCompositionError("unshuffle input projection step is absent") from exc
            if any(step.op != "FW_topk_routing" for step in topk):
                raise RelationCompositionError("unshuffle payloads are not top-k projections")
            projection = topk[0].output_projection or ""
            if any(step.output_projection != projection for step in topk[1:]):
                raise RelationCompositionError("zigzag top-k projection mismatch")
            if any(len(step.dependencies) != 1 for step in topk):
                raise RelationCompositionError("zigzag top-k input ancestry is not unary")
            result.append(SynchronizedRelationStep(
                rule_id="zigzag-topk-unshuffle-two-rank",
                output_step_triple=triple,
                input_step_triple=tuple(step.dependencies[0] for step in topk),
                output_projection=projection,
                lean_theorems=(
                    _topk_theorem(projection, zigzag=True),
                    "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.unshuffle_gather_single",
                ),
                metadata_tid=sm.input_tids[1],
            ))
            continue

        raise RelationCompositionError(
            f"unsupported synchronized stack payload operators {sm.op}/{pm0.op}/{pm1.op}"
        )
    return tuple(result)


def match_indexed_stack_gather_two_rank(
    ir: GoalIR, plan: ProofPlan
) -> IndexedStackGatherCertificate:
    """Match stack(full layers) = AllGather(dim1, stack(rank-local layers)).

    The matcher derives every tensor id, list length, and dimension from the
    public lineage and certificate DAG.  It emits only proof obligations for
    the generic Lean theorem; it does not assume the per-layer relations.
    """
    if plan.diagnostics:
        raise RelationCompositionError("cannot compose a plan with diagnostics")
    if ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2:
        raise RelationCompositionError("indexed stack/gather requires SM=1 and PM=2")
    if len(plan.target_steps) != 2:
        raise RelationCompositionError("indexed stack/gather requires one SM and one PM target")

    by_id = _step_map(plan)
    try:
        sm_stack = by_id[plan.target_steps[0]]
        pm_gather = by_id[plan.target_steps[1]]
    except KeyError as exc:
        raise RelationCompositionError("target step is absent from certificate DAG") from exc

    if sm_stack.side != "sm" or sm_stack.op != "FW_stack":
        raise RelationCompositionError("SM target is not an indexed FW_stack")
    if (
        pm_gather.side != "pm"
        or pm_gather.op != "AllGatherPrim"
        or pm_gather.parameters != (1,)
        or len(pm_gather.input_tids) != 2
    ):
        raise RelationCompositionError("PM target is not a dimension-1 two-rank AllGather")

    producers = {
        step.output_tid: step
        for step in plan.steps
        if step.side == "pm" and step.op == "FW_stack"
    }
    try:
        pm_stacks = tuple(producers[tid] for tid in pm_gather.input_tids)
    except KeyError as exc:
        raise RelationCompositionError("AllGather input is not produced by FW_stack") from exc
    if tuple(step.rank for step in pm_stacks) != (0, 1):
        raise RelationCompositionError("AllGather inputs are not rank-ordered (0, 1)")
    if tuple(step.step_id for step in pm_stacks) != pm_gather.dependencies:
        raise RelationCompositionError("AllGather dependencies do not match rank-ordered stack inputs")

    length = len(sm_stack.dependencies)
    if length == 0 or any(len(step.dependencies) != length for step in pm_stacks):
        raise RelationCompositionError("SM and PM indexed stacks have unequal or empty lengths")
    if len(ir.lineage.tsShape) != 3:
        raise RelationCompositionError("indexed stack/gather requires a rank-3 full output shape")
    out_length, full_rows, width = (int(value) for value in ir.lineage.tsShape)
    if out_length != length or full_rows <= 0 or full_rows % 2 or width <= 0:
        raise RelationCompositionError("lineage shape does not determine positive equal row shards")
    shard_rows = full_rows // 2

    triples = tuple(
        zip(sm_stack.dependencies, pm_stacks[0].dependencies, pm_stacks[1].dependencies)
    )
    return IndexedStackGatherCertificate(
        rule_id="indexed-stack-gather-two-rank",
        lean_theorem=(
            "TrainVerify.Denote.RelationCompiler."
            "fw_stack_allGather0_dim1_commute_2d_element"
        ),
        length=length,
        shard_rows=shard_rows,
        width=width,
        sm_stack_step=sm_stack.step_id,
        pm_stack_steps=(pm_stacks[0].step_id, pm_stacks[1].step_id),
        pm_gather_step=pm_gather.step_id,
        layer_step_triples=triples,
    )


@dataclass(frozen=True)
class FrontierAttentionCertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triples: tuple[tuple[str, str, str], tuple[str, str, str], tuple[str, str, str]]
    input_relation_kinds: tuple[str, str, str]
    metadata_bindings: tuple[str, str]
    lean_theorem: str


def expand_attention_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[FrontierAttentionCertificate, ...],
    tuple[tuple[str, str, str], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        operators = {step.op for step in steps}
        if len(operators) != 1 or next(iter(operators)) not in {"FW_attn_sliding_window", "FW_attn_zigzag"}:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        operator = steps[0].op
        expected_layout = "ordinary" if operator == "FW_attn_sliding_window" else "zigzag"
        if layout != expected_layout:
            raise RelationCompositionError("attention operator/layout mismatch")
        if any(len(step.input_bindings) != 5 for step in steps):
            raise RelationCompositionError("attention signature does not expose Q/K/V plus metadata")
        metadata = tuple(steps[0].input_bindings[3:5])
        if any(tuple(step.input_bindings[3:5]) != metadata for step in steps[1:]):
            raise RelationCompositionError("attention metadata is not shared")
        inputs = tuple(_produced_binding_triple(steps, index) for index in (0, 1, 2))
        input_layouts = (
            ("ordinary", "ordinary", "ordinary")
            if layout == "ordinary"
            else ("zigzag", "ordinary", "ordinary")
        )
        theorem = (
            "TrainVerify.Denote.GeneratedPatterns.applyNode_FW_attn_sliding_window_reconstruction_2_of_buddy_pair"
            if layout == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.attn_zigzag_sharded_kv"
        )
        certificates.append(FrontierAttentionCertificate(
            rule_id=f"attention-{layout}-qkv-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triples=inputs,
            input_relation_kinds=input_layouts,
            metadata_bindings=metadata,
            lean_theorem=theorem,
        ))
        rewritten.extend(inputs)
        rewritten_layouts.extend(input_layouts)
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class FrontierFlatten3DCertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    input_shape: tuple[int, int, int]
    output_shape: tuple[int, int]
    lean_theorem: str


def advance_flatten_3d_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[FrontierFlatten3DCertificate, ...],
    tuple[tuple[str, str, str], ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_reshape" for step in steps):
            rewritten.append(frontier)
            continue
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError("3D flatten received an unsupported relation layout")
        valid = True
        for step in steps:
            if len(step.input_shapes) != 1:
                valid = False
                break
            source = step.input_shapes[0]
            target = step.output_shape
            if len(source) != 3 or len(target) != 2 or target != (source[0], source[1] * source[2]):
                valid = False
                break
        if not valid:
            rewritten.append(frontier)
            continue
        source = steps[0].input_shapes[0]
        target = steps[0].output_shape
        if steps[1].input_shapes[0] != steps[2].input_shapes[0]:
            raise RelationCompositionError("3D flatten shard input shapes disagree")
        if source[0] != steps[1].input_shapes[0][0] + steps[2].input_shapes[0][0]:
            raise RelationCompositionError("3D flatten shards do not reconstruct full rows")
        input_triple = _produced_binding_triple(steps, 0)
        theorem = (
            "TrainVerify.Denote.GeneratedPatterns.fw_view_allGather0_commute_cp2"
            if layout == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_3d_to_2d"
        )
        certificates.append(FrontierFlatten3DCertificate(
            rule_id=f"flatten-3d-{layout}-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triple=input_triple,
            input_shape=source,
            output_shape=target,
            lean_theorem=theorem,
        ))
        rewritten.append(input_triple)
    return tuple(certificates), tuple(rewritten)


@dataclass(frozen=True)
class FrontierLinearCertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    replicated_weight_tid: int
    input_features: int
    weight_input_features: int
    output_features: int
    lean_theorem: str


def advance_linear_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[FrontierLinearCertificate, ...], tuple[tuple[str, str, str], ...]]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_mix_precision_linear" for step in steps):
            rewritten.append(frontier)
            continue
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError("linear received an unsupported relation layout")
        if any(len(step.input_bindings) != 2 or len(step.input_shapes) != 2 for step in steps):
            raise RelationCompositionError("linear signature is not data plus weight")
        weights = tuple(step.input_bindings[1] for step in steps)
        if len(set(weights)) != 1 or not weights[0].startswith("init:"):
            raise RelationCompositionError("linear weights are not replicated")
        for step in steps:
            data_shape, weight_shape = step.input_shapes
            output_shape = step.output_shape
            if len(data_shape) != 2 or len(weight_shape) != 2 or len(output_shape) != 2:
                raise RelationCompositionError("linear relation requires 2D tensors")
            if data_shape[1] != weight_shape[1] or output_shape != (data_shape[0], weight_shape[0]):
                raise RelationCompositionError("linear matrix dimensions disagree")
        input_triple = _produced_binding_triple(steps, 0)
        theorem = (
            "TrainVerify.Denote.fw_mix_precision_linear_allGather0_commute_2"
            if layout == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.mix_precision_linear"
        )
        certificates.append(FrontierLinearCertificate(
            rule_id=f"mix-precision-linear-{layout}-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triple=input_triple,
            replicated_weight_tid=int(weights[0].split(":", 1)[1]),
            input_features=steps[0].input_shapes[0][1],
            weight_input_features=steps[0].input_shapes[1][1],
            output_features=steps[0].output_shape[1],
            lean_theorem=theorem,
        ))
        rewritten.append(input_triple)
    return tuple(certificates), tuple(rewritten)


@dataclass(frozen=True)
class FrontierIdentityViewCertificate:
    rule_id: str
    operator: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    input_shape: tuple[int, ...]
    output_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    lean_theorem: str


def advance_identity_view_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[FrontierIdentityViewCertificate, ...],
    tuple[tuple[str, str, str], ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        operators = {step.op for step in steps}
        if len(operators) != 1 or next(iter(operators)) not in {"FW_view", "FW_reshape"}:
            rewritten.append(frontier)
            continue
        operator = steps[0].op
        if not all(step.input_shapes == (step.output_shape,) for step in steps):
            rewritten.append(frontier)
            continue
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError("identity view received an unsupported relation layout")
        full_shape = steps[0].output_shape
        shard_shapes = (steps[1].output_shape, steps[2].output_shape)
        if len(full_shape) != 2 or shard_shapes[0] != shard_shapes[1]:
            raise RelationCompositionError("identity view relation shapes are not two-rank 2D")
        if full_shape[0] != shard_shapes[0][0] + shard_shapes[1][0] or full_shape[1:] != shard_shapes[0][1:]:
            raise RelationCompositionError("identity view shard shapes do not reconstruct full shape")
        input_triple = _produced_binding_triple(steps, 0)
        theorem = (
            "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.view_id"
            if layout == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_id"
        )
        certificates.append(FrontierIdentityViewCertificate(
            rule_id=f"identity-{operator.removeprefix('FW_').replace('_', '-')}-{layout}-two-rank",
            operator=operator,
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triple=input_triple,
            input_shape=full_shape,
            output_shape=full_shape,
            shard_shape=shard_shapes[0],
            lean_theorem=theorem,
        ))
        rewritten.append(input_triple)
    return tuple(certificates), tuple(rewritten)


@dataclass(frozen=True)
class FrontierFloatCertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    shape: tuple[int, ...]
    lean_theorem: str


def advance_float_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[FrontierFloatCertificate, ...], tuple[tuple[str, str, str], ...]]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_float" for step in steps):
            rewritten.append(frontier)
            continue
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError("float received an unsupported relation layout")
        if any(len(step.input_bindings) != 1 for step in steps):
            raise RelationCompositionError("float signature is not unary")
        if any(step.input_shapes != (step.output_shape,) for step in steps):
            raise RelationCompositionError("float changed tensor shape")
        input_triple = _produced_binding_triple(steps, 0)
        theorem = (
            "TrainVerify.Denote.fw_float_allGather0_commute_2"
            if layout == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.fw_float"
        )
        certificates.append(FrontierFloatCertificate(
            rule_id=f"float-{layout}-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triple=input_triple,
            shape=steps[0].output_shape,
            lean_theorem=theorem,
        ))
        rewritten.append(input_triple)
    return tuple(certificates), tuple(rewritten)


@dataclass(frozen=True)
class FrontierAddCertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triples: tuple[tuple[str, str, str], tuple[str, str, str]]
    lean_theorem: str


def expand_add_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[FrontierAddCertificate, ...],
    tuple[tuple[str, str, str], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_add" for step in steps):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError("add received an unsupported relation layout")
        if any(len(step.input_bindings) != 2 for step in steps):
            raise RelationCompositionError("add signature is not binary")
        inputs = tuple(
            _produced_binding_triple(steps, index) for index in (0, 1)
        )
        theorem = (
            "TrainVerify.Denote.GeneratedPatterns.elemwiseAdd_allGather0_commute_cp2"
            if layout == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.add"
        )
        certificates.append(FrontierAddCertificate(
            rule_id=f"elementwise-add-{layout}-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triples=inputs,
            lean_theorem=theorem,
        ))
        rewritten.extend(inputs)
        rewritten_layouts.extend((layout, layout))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class FrontierRMSNormCertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    replicated_weight_tid: int
    lean_theorem: str


def advance_rms_norm_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[FrontierRMSNormCertificate, ...], tuple[tuple[str, str, str], ...]]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_rms_norm" for step in steps):
            rewritten.append(frontier)
            continue
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError("RMSNorm received an unsupported relation layout")
        if any(len(step.input_bindings) != 2 for step in steps):
            raise RelationCompositionError("RMSNorm signature is not binary")
        weights = tuple(step.input_bindings[1] for step in steps)
        if len(set(weights)) != 1 or not weights[0].startswith("init:"):
            raise RelationCompositionError("RMSNorm weights are not replicated")
        input_triple = _produced_binding_triple(steps, 0)
        theorem = (
            "TrainVerify.Denote.ZigzagCollective.fw_rms_norm_allGather0_commute_2_core"
            if layout == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.rms_norm"
        )
        certificates.append(FrontierRMSNormCertificate(
            rule_id=f"rms-norm-{layout}-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triple=input_triple,
            replicated_weight_tid=int(weights[0].split(":", 1)[1]),
            lean_theorem=theorem,
        ))
        rewritten.append(input_triple)
    return tuple(certificates), tuple(rewritten)


@dataclass(frozen=True)
class MultirefAliasCertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    output_index: int
    arity: int
    lean_theorem: str


def peel_multiref_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[MultirefAliasCertificate, ...], tuple[tuple[str, str, str], ...]]:
    """Peel synchronized multiref projections as semantic aliases."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_multiref" for step in steps):
            rewritten.append(frontier)
            continue
        if any(len(step.input_bindings) != 1 or len(step.parameters) != 1 for step in steps):
            raise RelationCompositionError("multiref alias signature is not unary with one arity")
        if len({step.parameters for step in steps}) != 1:
            raise RelationCompositionError("multiref alias arities disagree")
        output_indices = tuple(step.output_index for step in steps)
        if len(set(output_indices)) != 1 or output_indices[0] >= steps[0].parameters[0]:
            raise RelationCompositionError("multiref output indices disagree or exceed arity")
        input_triple = tuple(step.input_bindings[0] for step in steps)
        certificates.append(MultirefAliasCertificate(
            rule_id="multiref-projection-alias",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triple=input_triple,
            output_index=output_indices[0],
            arity=steps[0].parameters[0],
            lean_theorem="TrainVerify.Denote.fw_multiref_allGather0_commute_2",
        ))
        rewritten.append(input_triple)
    return tuple(certificates), tuple(rewritten)


@dataclass(frozen=True)
class RelationSideCondition:
    rule_id: str
    kind: str
    relation_kind: str
    source_step: str | None = None
    metadata_binding: str | None = None
    lower: int | None = None
    upper: int | None = None
    rows: int | None = None
    expert_split: int | None = None
    total_experts: int | None = None
    lean_proposition_key: str = ""


@dataclass(frozen=True)
class HiddenShardedEmbeddingAllToAllCertificate:
    rule_id: str
    sm_embedding_step: str
    pm_embedding_steps: tuple[str, str]
    alltoall_steps: tuple[str, str]
    ids_binding: str
    full_weight_tid: int
    shard_weight_rank_tids: tuple[tuple[int, int], ...]
    weight_gather_dim: int
    tokens: int
    vocab: int
    hidden_shard: int
    full_output_shape: tuple[int, ...]
    shard_output_shape: tuple[int, ...]
    lean_theorem: str


def close_hidden_sharded_embedding_alltoall_boundaries(
    ir: GoalIR,
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[HiddenShardedEmbeddingAllToAllCertificate, ...], tuple[tuple[str, str, str], ...], tuple[str, ...]]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    remaining = []
    remaining_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            remaining.append(frontier); remaining_layouts.append(layout); continue
        sm_embedding, a2a0, a2a1 = (by_id[binding] for binding in frontier)
        if sm_embedding.op != "FW_embedding" or a2a0.op != "AllToAllPrim" or a2a1.op != "AllToAllPrim":
            remaining.append(frontier); remaining_layouts.append(layout); continue
        if layout != "ordinary":
            raise RelationCompositionError("hidden-sharded embedding AllToAll boundary must be ordinary")
        if tuple((step.side, step.rank) for step in (sm_embedding, a2a0, a2a1)) != (("sm", 0), ("pm", 0), ("pm", 1)):
            raise RelationCompositionError("embedding AllToAll frontier is not SM/rank0/rank1 ordered")
        if sm_embedding.parameters or a2a0.parameters != (1, 0) or a2a1.parameters != (1, 0):
            raise RelationCompositionError("embedding or AllToAll parameters are unsupported")
        if len(sm_embedding.input_bindings) != 2 or len(a2a0.input_bindings) != 2 or a2a1.input_bindings != a2a0.input_bindings:
            raise RelationCompositionError("embedding AllToAll does not share two PM embedding sources")
        pm_embedding_bindings = a2a0.input_bindings
        if any(binding.startswith("init:") or binding not in by_id for binding in pm_embedding_bindings):
            raise RelationCompositionError("AllToAll source is not a typed PM embedding")
        pm0, pm1 = (by_id[binding] for binding in pm_embedding_bindings)
        if tuple((step.side, step.rank, step.op) for step in (pm0, pm1)) != (("pm", 0, "FW_embedding"), ("pm", 1, "FW_embedding")):
            raise RelationCompositionError("AllToAll embedding sources are not rank ordered")
        if pm0.parameters or pm1.parameters or len(pm0.input_bindings) != 2 or len(pm1.input_bindings) != 2:
            raise RelationCompositionError("PM embedding signature or parameters are unsupported")
        ids_binding = sm_embedding.input_bindings[0]
        if not ids_binding.startswith("init:") or pm0.input_bindings[0] != ids_binding or pm1.input_bindings[0] != ids_binding:
            raise RelationCompositionError("embedding ids are not one replicated external input")
        full_weight_binding = sm_embedding.input_bindings[1]
        if not full_weight_binding.startswith("init:") or not pm0.input_bindings[1].startswith("init:") or not pm1.input_bindings[1].startswith("init:"):
            raise RelationCompositionError("embedding weights are not external lineage inputs")
        full_weight_tid = int(full_weight_binding.split(":", 1)[1])
        shard_weight_tids = (int(pm0.input_bindings[1].split(":", 1)[1]), int(pm1.input_bindings[1].split(":", 1)[1]))
        lineage = ir.init_lineages.get(full_weight_tid)
        expected_lineage = ((0, shard_weight_tids[0]), (1, shard_weight_tids[1]))
        if lineage is None or lineage.ts != full_weight_tid or tuple((int(rank), int(tid)) for rank, tid in lineage.tps) != expected_lineage or lineage.gatherDim != 1 or lineage.replicated:
            raise RelationCompositionError("full embedding weight lacks exact dim-1 two-shard InitGoal lineage")
        ids_shape = sm_embedding.input_shapes[0]
        full_weight_shape = sm_embedding.input_shapes[1]
        shard_weight_shape = pm0.input_shapes[1]
        if len(ids_shape) != 1 or len(full_weight_shape) != 2 or len(shard_weight_shape) != 2 or pm1.input_shapes[1] != shard_weight_shape:
            raise RelationCompositionError("embedding ids or weight rank is unsupported")
        if tuple(lineage.tsShape) != full_weight_shape or tuple(tuple(shape) for shape in lineage.tpShapes) != (shard_weight_shape, shard_weight_shape):
            raise RelationCompositionError("embedding weight lineage shapes disagree with operator inputs")
        vocab, hidden_shard = shard_weight_shape
        if full_weight_shape != (vocab, 2 * hidden_shard) or ids_shape[0] % 2 != 0:
            raise RelationCompositionError("embedding hidden shards do not reconstruct full dimensions")
        tokens = ids_shape[0] // 2
        if min(tokens, vocab, hidden_shard) <= 0:
            raise RelationCompositionError("embedding boundary has a non-positive dimension")
        if pm0.input_shapes[0] != ids_shape or pm1.input_shapes[0] != ids_shape or pm0.output_shape != (2 * tokens, hidden_shard) or pm1.output_shape != (2 * tokens, hidden_shard):
            raise RelationCompositionError("PM embedding output shapes disagree")
        full_output_shape = sm_embedding.output_shape
        shard_output_shape = a2a0.output_shape
        if full_output_shape != (2 * tokens, 2 * hidden_shard) or a2a1.output_shape != shard_output_shape or shard_output_shape != (tokens, 2 * hidden_shard):
            raise RelationCompositionError("embedding AllToAll output shapes disagree")
        if a2a0.input_shapes != (pm0.output_shape, pm1.output_shape) or a2a1.input_shapes != a2a0.input_shapes:
            raise RelationCompositionError("AllToAll input shapes disagree with PM embeddings")
        certificates.append(HiddenShardedEmbeddingAllToAllCertificate(
            rule_id="hidden-sharded-embedding-alltoall-ordinary-two-rank",
            sm_embedding_step=frontier[0], pm_embedding_steps=pm_embedding_bindings,
            alltoall_steps=(frontier[1], frontier[2]), ids_binding=ids_binding,
            full_weight_tid=full_weight_tid, shard_weight_rank_tids=expected_lineage,
            weight_gather_dim=1, tokens=tokens, vocab=vocab, hidden_shard=hidden_shard,
            full_output_shape=full_output_shape, shard_output_shape=shard_output_shape,
            lean_theorem="TrainVerify.Denote.fw_embedding_hidden_shards_allToAll_two",
        ))
    return tuple(certificates), tuple(remaining), tuple(remaining_layouts)


@dataclass(frozen=True)
class InitChunkBoundaryCertificate:
    rule_id: str
    sm_tid: int
    lineage_pm_rank_tids: tuple[tuple[int, int], ...]
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    chunk_step_pair: tuple[str, str]
    relation_kind: str
    lean_theorem: str


def close_init_chunk_boundaries(ir: GoalIR, plan: ProofPlan, frontiers: tuple[tuple[str, str, str], ...], layouts: tuple[str, ...]) -> tuple[tuple[InitChunkBoundaryCertificate, ...], tuple[tuple[str, str, str], ...], tuple[str, ...]]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    remaining = []
    remaining_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if not frontier[0].startswith("init:") or any(binding.startswith("init:") for binding in frontier[1:]):
            remaining.append(frontier); remaining_layouts.append(layout); continue
        rank0, rank1 = by_id[frontier[1]], by_id[frontier[2]]
        if rank0.op != "ChunkPrim" or rank1.op != "ChunkPrim":
            remaining.append(frontier); remaining_layouts.append(layout); continue
        if layout != "ordinary":
            raise RelationCompositionError("init full-tensor chunk boundary must be ordinary")
        sm_tid = int(frontier[0].split(":", 1)[1])
        lineage = ir.init_lineages.get(sm_tid)
        if lineage is None:
            remaining.append(frontier)
            remaining_layouts.append(layout)
            continue
        lineage_pairs = tuple((int(rank), int(tid)) for rank, tid in lineage.tps)
        if lineage.ts != sm_tid or lineage_pairs != ((0, sm_tid),) or lineage.gatherDim is not None or lineage.replicated:
            raise RelationCompositionError(f"init lineage {sm_tid} is not one rank-0 full tensor")
        if (rank0.rank, rank1.rank) != (0, 1) or rank0.parameters != (0,) or rank1.parameters != (0,):
            raise RelationCompositionError("init chunk pair has malformed rank or dimension")
        if rank0.input_tids != (sm_tid,) or rank1.input_tids != (sm_tid,) or rank0.input_bindings != (f"init:{sm_tid}",) or rank1.input_bindings != (f"init:{sm_tid}",):
            raise RelationCompositionError("init chunk pair does not read the lineage PM tid")
        full_shape = tuple(lineage.tsShape)
        if tuple(tuple(shape) for shape in lineage.tpShapes) != (full_shape,) or rank0.input_shapes != (full_shape,) or rank1.input_shapes != (full_shape,):
            raise RelationCompositionError("init lineage and chunk input shapes disagree")
        shard_shape = rank0.output_shape
        if rank1.output_shape != shard_shape or len(full_shape) < 1 or full_shape != (shard_shape[0] * 2, *shard_shape[1:]):
            raise RelationCompositionError("init chunk outputs do not reconstruct the full shape")
        certificates.append(InitChunkBoundaryCertificate(
            rule_id="init-lineage-full-to-two-chunks", sm_tid=sm_tid,
            lineage_pm_rank_tids=lineage_pairs, full_shape=full_shape, shard_shape=shard_shape,
            chunk_step_pair=(frontier[1], frontier[2]), relation_kind="ordinary",
            lean_theorem="TrainVerify.Denote.allGatherPrimDimN_chunkPrimDimN_id_dim0_2",
        ))
    return tuple(certificates), tuple(remaining), tuple(remaining_layouts)


@dataclass(frozen=True)
class FullProducerChunkCertificate:
    rule_id: str
    operator: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    pre_layout: str
    post_layout: str
    sm_operator_step: str
    pm_full_operator_step: str
    pm_chunk_steps: tuple[str, str]
    sm_identity_chain: tuple[str, ...]
    pm_identity_chain: tuple[str, ...]
    pm_allgather_step: str
    input_step_triple: tuple[str, str, str]
    replicated_weight_binding: str
    weight_init_lineage_rank_tids: tuple[tuple[int, int], ...]
    weight_equality_theorem: str
    full_input_shape: tuple[int, ...]
    full_output_shape: tuple[int, ...]
    shard_output_shape: tuple[int, ...]
    operator_relation_theorem: str
    reconstruction_theorem: str
    result_relation_theorem: str


def advance_full_producer_chunk_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
    goal_ir: GoalIR | None = None,
) -> tuple[tuple[FullProducerChunkCertificate, ...], tuple[tuple[str, str, str], ...], tuple[str, ...]]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    supported = {
        "FW_norm_linear": (
            "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.norm_linear",
            "TrainVerify.Denote.RelationCompiler.allGather0_reconstruct_chunks_2d",
        ),
        "FW_per_head_mix_precision_linear": (
            "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.per_head_linear",
            "TrainVerify.Denote.allGather0_reconstruct_chunks_3d",
        ),
    }
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        sm_step, chunk0, chunk1 = (by_id[binding] for binding in frontier)
        if sm_step.op not in supported or chunk0.op != "ChunkPrim" or chunk1.op != "ChunkPrim":
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError("full-producer chunk relation has unknown layout")
        if layout == "zigzag" and sm_step.op not in {"FW_norm_linear", "FW_per_head_mix_precision_linear"}:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if goal_ir is None:
            raise RelationCompositionError("full-producer chunk relation lacks GoalIR lineage authority")
        if (chunk0.rank, chunk1.rank) != (0, 1) or chunk0.parameters != (0,) or chunk1.parameters != (0,):
            raise RelationCompositionError("full-producer chunk pair has malformed rank or dimension")
        if len(chunk0.input_bindings) != 1 or chunk1.input_bindings != chunk0.input_bindings:
            raise RelationCompositionError("full-producer chunks do not share one prior producer")
        pm_full_binding = chunk0.input_bindings[0]
        if pm_full_binding.startswith("init:") or pm_full_binding not in by_id:
            raise RelationCompositionError("full-producer chunk source is not a typed prior step")
        pm_full = by_id[pm_full_binding]
        if pm_full.op != sm_step.op or pm_full.denote_fn != sm_step.denote_fn or pm_full.parameters != sm_step.parameters:
            raise RelationCompositionError("SM and PM full producers have different semantic identities")
        if len(sm_step.input_bindings) != 2 or len(pm_full.input_bindings) != 2:
            raise RelationCompositionError("full producer operator is not activation plus weight")
        weight_binding = sm_step.input_bindings[1]
        if pm_full.input_bindings[1] != weight_binding or not weight_binding.startswith("init:"):
            raise RelationCompositionError("full producer weight is not one replicated external binding")
        weight_tid = int(weight_binding.split(":", 1)[1])
        weight_lineage = goal_ir.init_lineages.get(weight_tid)
        weight_pairs = () if weight_lineage is None else tuple(
            (int(rank), int(tid)) for rank, tid in weight_lineage.tps
        )
        if weight_lineage is None or weight_lineage.ts != weight_tid or weight_pairs != ((0, weight_tid),) or weight_tid not in goal_ir.full_init_goal_ids:
            raise RelationCompositionError("replicated full-producer weight lacks public singleton InitGoal lineage")
        if tuple(weight_lineage.tsShape) != sm_step.input_shapes[1] or tuple(tuple(shape) for shape in weight_lineage.tpShapes) != (sm_step.input_shapes[1],):
            raise RelationCompositionError("replicated full-producer weight lineage shapes disagree")
        if sm_step.input_shapes != pm_full.input_shapes or sm_step.output_shape != pm_full.output_shape:
            raise RelationCompositionError("SM and PM full producer shapes disagree")
        if chunk0.input_shapes != (pm_full.output_shape,) or chunk1.input_shapes != (pm_full.output_shape,):
            raise RelationCompositionError("chunk input shape does not equal PM full output shape")
        shard_shape = chunk0.output_shape
        full_output_shape = pm_full.output_shape
        if chunk1.output_shape != shard_shape or not full_output_shape or full_output_shape != (2 * shard_shape[0], *shard_shape[1:]):
            raise RelationCompositionError("rank chunks do not reconstruct the PM full output shape")
        if any(dim <= 0 for dim in (*sm_step.input_shapes[0], *sm_step.input_shapes[1], *full_output_shape, *shard_shape)):
            raise RelationCompositionError("full producer relation has a non-positive shape dimension")
        if sm_step.op == "FW_norm_linear":
            data_shape, weight_shape = sm_step.input_shapes
            if len(data_shape) != 2 or len(weight_shape) != 2 or len(full_output_shape) != 2 or full_output_shape != (data_shape[0], weight_shape[0]) or data_shape[1] != weight_shape[1]:
                raise RelationCompositionError("norm-linear full producer dimensions disagree")
        else:
            data_shape, weight_shape = sm_step.input_shapes
            if len(data_shape) != 2 or len(weight_shape) != 3 or len(full_output_shape) != 3 or full_output_shape != (data_shape[0], weight_shape[0], weight_shape[1]) or data_shape[1] != weight_shape[2]:
                raise RelationCompositionError("per-head full producer dimensions disagree")
        current = pm_full.input_bindings[0]
        identity_chain = []
        while current in by_id:
            candidate = by_id[current]
            if candidate.op == "AllGatherPrim":
                break
            if candidate.denote_fn != "id" or len(candidate.input_bindings) != 1 or len(candidate.input_shapes) != 1 or candidate.input_shapes[0] != candidate.output_shape:
                raise RelationCompositionError("PM full activation is not derived from dim-0 AllGather through semantic identities")
            identity_chain.append(current)
            current = candidate.input_bindings[0]
        if current not in by_id:
            raise RelationCompositionError("PM full activation has no typed dim-0 AllGather producer")
        gather = by_id[current]
        if gather.op != "AllGatherPrim" or gather.parameters != (0,) or len(gather.input_bindings) != 2 or len(gather.input_shapes) != 2:
            raise RelationCompositionError("PM full activation collective is not binary dim-0 AllGather")
        if gather.input_shapes[0] != gather.input_shapes[1] or gather.output_shape != sm_step.input_shapes[0] or gather.output_shape != (2 * gather.input_shapes[0][0], *gather.input_shapes[0][1:]):
            raise RelationCompositionError("PM activation AllGather shapes do not reconstruct the SM full input")
        source0, source1 = (by_id[binding] for binding in gather.input_bindings)
        if (source0.rank, source1.rank) != (0, 1):
            raise RelationCompositionError("PM activation AllGather sources are not rank ordered")
        sm_current = sm_step.input_bindings[0]
        sm_identity_chain = []
        for pm_identity_binding in identity_chain:
            if sm_current not in by_id:
                raise RelationCompositionError("SM activation identity chain ends before PM chain")
            sm_identity = by_id[sm_current]
            pm_identity = by_id[pm_identity_binding]
            if sm_identity.op != pm_identity.op or sm_identity.denote_fn != "id" or len(sm_identity.input_bindings) != 1 or len(sm_identity.input_shapes) != 1 or sm_identity.input_shapes[0] != sm_identity.output_shape:
                raise RelationCompositionError("SM and PM full activation identity chains disagree")
            sm_identity_chain.append(sm_current)
            sm_current = sm_identity.input_bindings[0]
        input_triple = (sm_current, gather.input_bindings[0], gather.input_bindings[1])
        operator_theorem, reconstruction_theorem = supported[sm_step.op]
        result_theorem = (
            "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.per_head_linear_fullProducer_chunks"
            if sm_step.op == "FW_per_head_mix_precision_linear"
            else "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.norm_linear_fullProducer_chunks"
        )
        if layout == "zigzag" and sm_step.op == "FW_per_head_mix_precision_linear":
            operator_theorem = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.per_head_linear"
            reconstruction_theorem = "TrainVerify.Denote.GeneratedPatterns.chunk_allGather_cp2_dim0_3d"
            result_theorem = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.per_head_linear_fullProducer_chunks"
        elif layout == "zigzag":
            operator_theorem = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.norm_linear"
            reconstruction_theorem = "TrainVerify.Denote.GeneratedPatterns.chunk_allGather_cp2_dim0_2d"
            result_theorem = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.norm_linear_fullProducer_chunks"
        certificates.append(FullProducerChunkCertificate(
            rule_id=f"{sm_step.op}-full-producer-chunks-{layout}-two-rank",
            operator=sm_step.op, relation_kind=layout, output_step_triple=frontier,
            pre_layout=layout, post_layout=layout,
            sm_operator_step=frontier[0], pm_full_operator_step=pm_full_binding,
            pm_chunk_steps=(frontier[1], frontier[2]), sm_identity_chain=tuple(sm_identity_chain),
            pm_identity_chain=tuple(identity_chain), pm_allgather_step=current, input_step_triple=input_triple,
            replicated_weight_binding=weight_binding,
            weight_init_lineage_rank_tids=weight_pairs,
            weight_equality_theorem="TrainVerify.Denote.InitGoalHolds.singleton_value_eq",
            full_input_shape=sm_step.input_shapes[0],
            full_output_shape=full_output_shape, shard_output_shape=shard_shape,
            operator_relation_theorem=operator_theorem,
            reconstruction_theorem=reconstruction_theorem,
            result_relation_theorem=result_theorem,
        ))
        rewritten.append(input_triple); rewritten_layouts.append(layout)
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class FrontierTopKRoutingCertificate:
    rule_id: str
    output_step_triples: tuple[tuple[str, str, str], tuple[str, str, str]]
    output_projections: tuple[str, str]
    input_step_triple: tuple[str, str, str]
    full_input_shape: tuple[int, ...]
    shard_input_shape: tuple[int, ...]
    top_k: int
    normalize_topk_prob: int
    num_experts: int
    relation_kind: str
    lean_theorem: str


def expand_topk_routing_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[FrontierTopKRoutingCertificate, ...],
    tuple[tuple[str, str, str], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    groups: dict[tuple[str, tuple[tuple[str, int], ...]], dict[int, tuple[int, tuple[str, str, str], tuple[CertificateStep, ...]]]] = {}
    for position, (frontier, layout) in enumerate(zip(frontiers, layouts)):
        if any(binding.startswith("init:") for binding in frontier):
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_topk_routing" for step in steps):
            continue
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError("top-k routing has unknown relation layout")
        indices = {step.output_index for step in steps}
        if len(indices) != 1 or next(iter(indices)) not in (0, 1):
            raise RelationCompositionError("top-k routing projection triple is inconsistent")
        projection = next(iter(indices))
        key = (layout, tuple((step.side, step.node_index) for step in steps))
        if projection in groups.setdefault(key, {}):
            raise RelationCompositionError("duplicate top-k routing projection frontier")
        groups[key][projection] = (position, frontier, steps)
    for projections in groups.values():
        if set(projections) != {0, 1}:
            raise RelationCompositionError("top-k routing requires both semantic output projections")
    first_positions = {min(item[0] for item in projections.values()): key for key, projections in groups.items()}
    consumed = {item[0] for projections in groups.values() for item in projections.values()}
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for position, (frontier, layout) in enumerate(zip(frontiers, layouts)):
        if position not in consumed:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        key = first_positions.get(position)
        if key is None:
            continue
        score_entry = groups[key][0]
        map_entry = groups[key][1]
        score_steps = score_entry[2]
        map_steps = map_entry[2]
        if any(len(step.input_bindings) != 1 or len(step.input_shapes) != 1 for step in (*score_steps, *map_steps)):
            raise RelationCompositionError("top-k routing signature mismatch")
        if any(score.input_bindings != mapping.input_bindings for score, mapping in zip(score_steps, map_steps)):
            raise RelationCompositionError("top-k routing projections do not share inputs")
        if any(score.parameters != mapping.parameters for score, mapping in zip(score_steps, map_steps)):
            raise RelationCompositionError("top-k routing projections do not share parameters")
        if not (score_steps[0].parameters == score_steps[1].parameters == score_steps[2].parameters) or len(score_steps[0].parameters) != 2:
            raise RelationCompositionError("top-k routing parameters disagree across ranks")
        top_k, normalize_topk_prob = score_steps[0].parameters
        full_shape = score_steps[0].input_shapes[0]
        shard_shape = score_steps[1].input_shapes[0]
        if len(full_shape) != 2 or score_steps[2].input_shapes[0] != shard_shape or full_shape != (shard_shape[0] * 2, shard_shape[1]):
            raise RelationCompositionError("top-k routing input shapes do not form a two-rank split")
        num_experts = full_shape[1]
        if not 0 < top_k <= num_experts:
            raise RelationCompositionError("top-k routing topK exceeds expert dimension")
        expected_outputs = (full_shape, shard_shape, shard_shape)
        if tuple(step.output_shape for step in score_steps) != expected_outputs or tuple(step.output_shape for step in map_steps) != expected_outputs:
            raise RelationCompositionError("top-k routing output projection shapes mismatch")
        inputs = tuple(step.input_bindings[0] for step in score_steps)
        if any(binding.startswith("init:") for binding in inputs):
            raise RelationCompositionError("top-k routing logits are not produced")
        if layout == "zigzag" and shard_shape[0] % 2 != 0:
            raise RelationCompositionError("zigzag top-k routing local token rows are not even")
        theorem = (
            "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.topk_routing_all"
            if layout == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.topk_routing_all"
        )
        certificates.append(FrontierTopKRoutingCertificate(
            rule_id=f"topk-routing-two-output-{layout}-two-rank",
            output_step_triples=(score_entry[1], map_entry[1]),
            output_projections=(".1", ".2.1"),
            input_step_triple=inputs,
            full_input_shape=full_shape,
            shard_input_shape=shard_shape,
            top_k=top_k,
            normalize_topk_prob=normalize_topk_prob,
            num_experts=num_experts,
            relation_kind=layout,
            lean_theorem=theorem,
        ))
        rewritten.append(inputs)
        rewritten_layouts.append(layout)
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class ContractDischargeCertificate:
    rule_id: str
    side: str
    tid: int
    total_tokens: int
    num_ranks: int
    source_condition: RelationSideCondition
    lean_theorem: str


def discharge_public_contract_conditions(
    ir: GoalIR,
    conditions: tuple[RelationSideCondition, ...] | list[RelationSideCondition],
) -> tuple[tuple[ContractDischargeCertificate, ...], tuple[RelationSideCondition, ...]]:
    certificates = []
    unresolved = []
    contracts = {(item.side, item.tid, item.total_tokens, item.num_ranks) for item in ir.packed_cu_contracts}
    for condition in conditions:
        matched = None
        if condition.rule_id == "packed-cu-decodes-single" and condition.kind == "packed-cu-seqlens-wf" and condition.metadata_binding is not None and condition.metadata_binding.startswith("init:") and condition.lower == 0 and condition.upper is not None:
            try:
                tid = int(condition.metadata_binding.split(":", 1)[1])
            except ValueError:
                tid = -1
            key = ("pm", tid, condition.upper, 2)
            if key in contracts:
                matched = key
        if matched is None:
            unresolved.append(condition)
            continue
        side, tid, total_tokens, num_ranks = matched
        certificates.append(ContractDischargeCertificate(
            rule_id="packed-cu-contract-decode-single",
            side=side,
            tid=tid,
            total_tokens=total_tokens,
            num_ranks=num_ranks,
            source_condition=condition,
            lean_theorem="TrainVerify.Denote.PackedCuSeqlensWF.decoded_single",
        ))
    return tuple(certificates), tuple(unresolved)


@dataclass(frozen=True)
class ZigzagMetadataRegionCertificate:
    rule_id: str
    region_id: int
    metadata_source: str
    contract_metadata_tid: int
    total_tokens: int
    num_ranks: int
    alias_tids: tuple[int, ...]
    frontier_triples: tuple[tuple[str, str, str], ...]
    metadata_alias_theorem: str
    contract_theorem: str


def resolve_zigzag_metadata_regions(
    ir: GoalIR,
    certificates: tuple[object, ...],
    unresolved_frontiers: tuple[tuple[str, str, str], ...],
    unresolved_layouts: tuple[str, ...],
) -> tuple[tuple[ZigzagMetadataRegionCertificate, ...], dict[tuple[str, str, str], ZigzagMetadataRegionCertificate]]:
    if len(unresolved_frontiers) != len(unresolved_layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    parent = {}
    seeds = {}

    def add(node):
        parent.setdefault(node, node)

    def find(node):
        add(node)
        while parent[node] != node:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    def union(left, right):
        rl, rr = find(left), find(right)
        if rl != rr:
            parent[rr] = rl

    def source_for_tid(tid: int) -> str:
        matches = [item.source for item in ir.pm_input_value_classes if tid in item.tids]
        if len(matches) != 1:
            raise RelationCompositionError(f"zigzag metadata tid {tid} has non-unique PM InputValueClass")
        return matches[0]

    def add_seed(node, binding: str):
        if not binding.startswith("init:"):
            raise RelationCompositionError("zigzag metadata binding is not external")
        tid = int(binding.split(":", 1)[1])
        add(node)
        seeds.setdefault(node, []).append((source_for_tid(tid), tid))

    for cert in certificates:
        output = getattr(cert, "output_step_triple", None)
        if isinstance(cert, FaithfulShuffleCertificate):
            add(output)
            seeds.setdefault(output, []).append((cert.metadata_source, cert.node_metadata_tid))
            continue
        if isinstance(cert, FrontierUnshuffleCertificate):
            add_seed(cert.input_step_triple, cert.metadata_binding)
            continue
        if getattr(cert, "relation_kind", None) != "zigzag":
            continue
        outputs = getattr(cert, "output_step_triples", None)
        if outputs is None:
            if output is None:
                raise RelationCompositionError(f"zigzag certificate {type(cert).__name__} lacks an output frontier")
            outputs = (output,)
        for output_frontier in outputs:
            add(output_frontier)
        inputs = getattr(cert, "input_step_triples", None)
        if inputs is None:
            one = getattr(cert, "input_step_triple", None)
            inputs = () if one is None else (one,)
        kinds = getattr(cert, "input_relation_kinds", None)
        if kinds is None:
            zigzag_inputs = tuple(inputs)
        else:
            if len(kinds) != len(inputs):
                raise RelationCompositionError("zigzag certificate input relation kinds have wrong arity")
            zigzag_inputs = tuple(frontier for frontier, kind in zip(inputs, kinds) if kind == "zigzag")
        for output_frontier in outputs:
            for input_frontier in zigzag_inputs:
                union(output_frontier, input_frontier)
        metadata_bindings = getattr(cert, "metadata_bindings", ())
        if metadata_bindings:
            # Attention stores q/k metadata in that order; the faithful zigzag
            # relation is keyed by q metadata, while ordinary K/V prerequisites
            # do not join this component.
            add_seed(outputs[0], metadata_bindings[0])

    zigzag_unresolved = []
    for frontier, layout in zip(unresolved_frontiers, unresolved_layouts):
        if layout == "zigzag":
            add(frontier)
            zigzag_unresolved.append(frontier)

    component_nodes = {}
    component_seeds = {}
    for node in tuple(parent):
        root = find(node)
        component_nodes.setdefault(root, []).append(node)
    for node, values in seeds.items():
        component_seeds.setdefault(find(node), []).extend(values)

    regions = []
    region_for_root = {}
    ordered_roots = sorted(component_nodes, key=lambda root: min(component_nodes[root]))
    for region_id, root in enumerate(ordered_roots):
        values = component_seeds.get(root, [])
        if not values:
            raise RelationCompositionError(
                f"zigzag certificate component has no metadata authority seed: {min(component_nodes[root])}"
            )
        sources = {source for source, _tid in values}
        if len(sources) != 1:
            raise RelationCompositionError("zigzag certificate component mixes metadata value classes")
        source = next(iter(sources))
        alias_tids = tuple(sorted({tid for _source, tid in values}))
        contract_candidates = []
        for fact in ir.packed_cu_contracts:
            if fact.side != "pm":
                continue
            classes = [item for item in ir.pm_input_value_classes if fact.tid in item.tids]
            if len(classes) == 1 and classes[0].source == source:
                contract_candidates.append(fact)
        if not contract_candidates:
            raise RelationCompositionError("zigzag metadata region has no public PackedCuSeqlensWF contract")
        contract = contract_candidates[0]
        if any(fact.total_tokens != contract.total_tokens or fact.num_ranks != contract.num_ranks for fact in contract_candidates):
            raise RelationCompositionError("zigzag metadata aliases have conflicting public contracts")
        region = ZigzagMetadataRegionCertificate(
            rule_id="zigzag-metadata-region-from-public-value-class",
            region_id=region_id, metadata_source=source,
            contract_metadata_tid=contract.tid, total_tokens=contract.total_tokens,
            num_ranks=contract.num_ranks, alias_tids=alias_tids,
            frontier_triples=tuple(sorted(component_nodes[root])),
            metadata_alias_theorem="TrainVerify.Denote.InputValueClassesHold.eq_of_mem",
            contract_theorem="TrainVerify.Denote.PackedCuSeqlensWF.toZigzagCuWF",
        )
        regions.append(region)
        region_for_root[root] = region
    authority_by_frontier = {}
    for frontier in zigzag_unresolved:
        authority_by_frontier[frontier] = region_for_root[find(frontier)]
    return tuple(regions), authority_by_frontier


@dataclass(frozen=True)
class FaithfulShuffleCertificate:
    rule_id: str
    pre_layout: str
    post_layout: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    node_metadata_tid: int
    contract_metadata_tid: int
    metadata_source: str
    metadata_init_lineage_rank_tids: tuple[tuple[int, int], ...]
    total_tokens: int
    num_ranks: int
    sm_replica_members: tuple[tuple[int, int], ...]
    pm_replica_members: tuple[tuple[int, int], ...]
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    metadata_alias_theorem: str
    metadata_cross_store_theorem: str
    contract_theorem: str
    lean_theorem: str


def advance_faithful_shuffle_relation_frontiers(
    ir: GoalIR,
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[FaithfulShuffleCertificate, ...], tuple[tuple[str, str, str], ...], tuple[str, ...]]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    rewritten_layouts = []

    def value_class(classes, tid: int, side: str):
        matches = [item for item in classes if tid in item.tids]
        if len(matches) != 1:
            raise RelationCompositionError(f"{side} shuffle metadata tid has non-unique InputValueClass")
        return matches[0]

    def matching_group(groups, expected):
        matches = []
        for group in groups:
            members = tuple((member.rank, member.primary_out_tid) for member in group.members)
            if any(member in expected for member in members):
                matches.append((group, members))
        if len(matches) != 1 or matches[0][1] != expected:
            raise RelationCompositionError("shuffle replica group is missing, ambiguous, or out of order")
        return matches[0]

    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_maybe_shuffle" for step in steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if layout != "zigzag":
            raise RelationCompositionError("faithful shuffle output must be a zigzag frontier")
        if tuple((step.side, step.rank) for step in steps) != (("sm", 0), ("pm", 0), ("pm", 1)):
            raise RelationCompositionError("faithful shuffle frontier is not SM/rank0/rank1 ordered")
        if tuple(step.parameters for step in steps) != ((1, 0), (2, 0), (2, 1)):
            raise RelationCompositionError("faithful shuffle collective parameters are malformed")
        if any(len(step.input_bindings) != 2 or len(step.input_tids) != 2 or len(step.input_shapes) != 2 for step in steps):
            raise RelationCompositionError("faithful shuffle signature is not data plus metadata")
        metadata_tids = tuple(step.input_tids[1] for step in steps)
        if len(set(metadata_tids)) != 1:
            raise RelationCompositionError("faithful shuffle nodes do not use one metadata tid")
        metadata_tid = metadata_tids[0]
        if any(step.input_bindings[1] != f"init:{metadata_tid}" for step in steps):
            raise RelationCompositionError("faithful shuffle metadata is not an external input binding")
        if any(step.input_shapes[1] != (2,) for step in steps):
            raise RelationCompositionError("faithful shuffle metadata shape is not packed two-rank cu_seqlens")
        metadata_lineage = ir.init_lineages.get(metadata_tid)
        metadata_lineage_pairs = () if metadata_lineage is None else tuple(
            (int(rank), int(tid)) for rank, tid in metadata_lineage.tps
        )
        if metadata_lineage is None or metadata_lineage.ts != metadata_tid or metadata_lineage_pairs != ((0, metadata_tid),) or tuple(metadata_lineage.tsShape) != (2,) or tuple(tuple(shape) for shape in metadata_lineage.tpShapes) != ((2,),) or metadata_lineage.gatherDim is not None or metadata_lineage.replicated:
            raise RelationCompositionError("faithful shuffle metadata lacks singleton cross-store InitGoal lineage")
        full_shape = steps[0].input_shapes[0]
        shard_shape = steps[1].input_shapes[0]
        if steps[2].input_shapes[0] != shard_shape or steps[0].output_shape != full_shape or steps[1].output_shape != shard_shape or steps[2].output_shape != shard_shape:
            raise RelationCompositionError("faithful shuffle input/output shapes disagree")
        if not full_shape or full_shape != (2 * shard_shape[0], *shard_shape[1:]) or any(dim <= 0 for dim in (*full_shape, *shard_shape)):
            raise RelationCompositionError("faithful shuffle shapes do not form a positive two-rank split")
        sm_class = value_class(ir.sm_input_value_classes, metadata_tid, "SM")
        pm_class = value_class(ir.pm_input_value_classes, metadata_tid, "PM")
        if sm_class.source != pm_class.source:
            raise RelationCompositionError("SM and PM shuffle metadata value classes disagree")
        contract_candidates = []
        for fact in ir.packed_cu_contracts:
            if fact.side != "pm" or fact.total_tokens != full_shape[0] or fact.num_ranks != 2:
                continue
            classes = [item for item in ir.pm_input_value_classes if fact.tid in item.tids]
            if len(classes) == 1 and classes[0].source == pm_class.source:
                contract_candidates.append(fact)
        if not contract_candidates:
            raise RelationCompositionError("shuffle metadata has no public PackedCuSeqlensWF alias contract")
        contract = contract_candidates[0]
        sm_expected = ((0, steps[0].output_tid),)
        pm_expected = ((0, steps[1].output_tid), (1, steps[2].output_tid))
        _sm_group, sm_members = matching_group(ir.sm_replica_groups, sm_expected)
        _pm_group, pm_members = matching_group(ir.pm_replica_groups, pm_expected)
        input_triple = _produced_binding_triple(steps, 0)
        certificates.append(FaithfulShuffleCertificate(
            rule_id="faithful-maybe-shuffle-ordinary-to-zigzag-two-rank",
            pre_layout="ordinary", post_layout="zigzag", output_step_triple=frontier,
            input_step_triple=input_triple, node_metadata_tid=metadata_tid,
            contract_metadata_tid=contract.tid, metadata_source=pm_class.source,
            metadata_init_lineage_rank_tids=metadata_lineage_pairs,
            total_tokens=contract.total_tokens, num_ranks=contract.num_ranks,
            sm_replica_members=sm_members, pm_replica_members=pm_members,
            full_shape=full_shape, shard_shape=shard_shape,
            metadata_alias_theorem="TrainVerify.Denote.InputValueClassesHold.eq_of_mem",
            metadata_cross_store_theorem="TrainVerify.Denote.InitGoalHolds.singleton_value_eq",
            contract_theorem="TrainVerify.Denote.PackedCuSeqlensWF.toZigzagCuWF",
            lean_theorem="TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.of_sources",
        ))
        rewritten.append(input_triple); rewritten_layouts.append("ordinary")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class FrontierUnshuffleCertificate:
    rule_id: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    metadata_binding: str
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    pre_layout: str
    post_layout: str
    lean_theorem: str


def advance_unshuffle_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[FrontierUnshuffleCertificate, ...],
    tuple[RelationSideCondition, ...],
    tuple[tuple[str, str, str], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    conditions = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_maybe_unshuffle" for step in steps):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if layout != "ordinary":
            raise RelationCompositionError("FW_maybe_unshuffle output must be ordinary")
        full, rank0, rank1 = steps
        if (full.parameters, rank0.parameters, rank1.parameters) != ((1, 0), (2, 0), (2, 1)):
            raise RelationCompositionError("two-rank unshuffle parameters are malformed")
        if any(len(step.input_bindings) != 2 or len(step.input_shapes) != 2 for step in steps):
            raise RelationCompositionError("two-rank unshuffle signature mismatch")
        metadata = tuple(step.input_bindings[1] for step in steps)
        if len(set(metadata)) != 1 or not metadata[0].startswith("init:"):
            raise RelationCompositionError("unshuffle metadata is not one shared external input")
        full_shape = full.input_shapes[0]
        shard_shape = rank0.input_shapes[0]
        if len(full_shape) != 2 or len(shard_shape) != 2:
            raise RelationCompositionError("unshuffle supports rank-2 payloads only")
        if rank1.input_shapes[0] != shard_shape or full_shape != (shard_shape[0] * 2, shard_shape[1]):
            raise RelationCompositionError("unshuffle payload shapes do not form a two-rank split")
        if full.output_shape != full_shape or rank0.output_shape != shard_shape or rank1.output_shape != shard_shape:
            raise RelationCompositionError("unshuffle output shapes differ from payload shapes")
        inputs = tuple(step.input_bindings[0] for step in steps)
        if any(binding.startswith("init:") for binding in inputs):
            raise RelationCompositionError("unshuffle payload is not produced")
        certificates.append(FrontierUnshuffleCertificate(
            rule_id="zigzag-to-ordinary-unshuffle-two-rank",
            output_step_triple=frontier,
            input_step_triple=inputs,
            metadata_binding=metadata[0],
            full_shape=full_shape,
            shard_shape=shard_shape,
            pre_layout="zigzag",
            post_layout="ordinary",
            lean_theorem="TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.to_gather2_unshuffle",
        ))
        conditions.append(RelationSideCondition(
            rule_id="packed-cu-decodes-single",
            kind="packed-cu-seqlens-wf",
            relation_kind="zigzag",
            metadata_binding=metadata[0],
            lower=0,
            upper=full_shape[0],
        ))
        rewritten.append(inputs)
        rewritten_layouts.append("zigzag")
    return tuple(certificates), tuple(conditions), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class FrontierOrdinaryMoECertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triples: tuple[tuple[str, str, str], tuple[str, str, str], tuple[str, str, str]]
    full_weight_bindings: tuple[str, str]
    shard_weight_bindings: tuple[tuple[str, str], tuple[str, str]]
    num_experts: int
    expert_split: int
    top_k: int
    lean_theorem: str



@dataclass(frozen=True)
class FrontierZigzagFullMoECertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triples: tuple[tuple[str, str, str], tuple[str, str, str], tuple[str, str, str]]
    full_weight_bindings: tuple[str, str]
    shard_weight_bindings: tuple[tuple[str, str], tuple[str, str]]
    weight_lineage_rank_tids: tuple[tuple[tuple[int, int], ...], tuple[tuple[int, int], ...]]
    weight_lineage_theorem: str
    num_experts: int
    expert_split: int
    top_k: int
    token_rows: int
    hidden_dim: int
    t_dim: int
    d_dim: int
    lean_theorem: str

def expand_ordinary_moe_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
    goal_ir: GoalIR | None = None,
) -> tuple[
    tuple[object, ...],
    tuple[RelationSideCondition, ...],
    tuple[tuple[str, str, str], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_all2all_moe_gmm" for step in steps):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError("full MoE has unknown relation layout")
        if goal_ir is None:
            raise RelationCompositionError("full MoE relation lacks GoalIR weight-lineage authority")
        full, rank0, rank1 = steps
        if any(step.denote_fn != "fw_all2all_moe_gmm_full" for step in steps):
            raise RelationCompositionError("ordinary MoE is not compiled with faithful full-expert semantics")
        if len(full.semantic_input_shapes) != 5 or len(full.semantic_input_bindings) != 5:
            raise RelationCompositionError("single-rank full MoE semantic signature mismatch")
        if any(len(step.semantic_input_shapes) != 7 or len(step.semantic_input_bindings) != 7 for step in (rank0, rank1)):
            raise RelationCompositionError("two-rank full MoE semantic signature mismatch")
        if not (full.parameters == rank0.parameters == rank1.parameters) or len(full.parameters) != 3:
            raise RelationCompositionError("full MoE semantic parameters disagree")
        num_exp, top_k, _limit = full.parameters
        full_x, full_rp, full_rm, full_w13, full_w2 = full.semantic_input_shapes
        rank_x, rank_rp, rank_rm, w13_a, w13_b, w2_a, w2_b = rank0.semantic_input_shapes
        if rank1.semantic_input_shapes != rank0.semantic_input_shapes:
            raise RelationCompositionError("full MoE buddy-expanded PM shapes disagree")
        if len(rank_x) != 2 or len(rank_rp) != 2 or len(w13_a) != 3 or len(w2_a) != 3:
            raise RelationCompositionError("full MoE tensor ranks are malformed")
        rows, h_model = rank_x
        if full_x != (rows * 2, h_model) or full.output_shape != full_x:
            raise RelationCompositionError("full MoE activation shape mismatch")
        if rank_rp != (rows, num_exp) or rank_rm != rank_rp or full_rp != (rows * 2, num_exp) or full_rm != full_rp:
            raise RelationCompositionError("full MoE routing shapes mismatch")
        expert_split = w13_a[0]
        if w13_b != w13_a or w2_b != w2_a or w2_a[0] != expert_split:
            raise RelationCompositionError("full MoE expert shard shapes disagree")
        if num_exp != expert_split * 2:
            raise RelationCompositionError("full MoE expert shards do not cover all experts")
        if full_w13 != (num_exp, *w13_a[1:]) or full_w2 != (num_exp, *w2_a[1:]):
            raise RelationCompositionError("single-rank MoE weights do not match gathered PM weights")
        if rank0.output_shape != rank_x or rank1.output_shape != rank_x:
            raise RelationCompositionError("full MoE output shape mismatch")
        inputs = []
        for index in range(3):
            bindings = tuple(step.semantic_input_bindings[index] for step in steps)
            if any(binding.startswith("init:") for binding in bindings):
                raise RelationCompositionError("full MoE activation/routing input is not produced")
            inputs.append(bindings)
        rank0_weights = rank0.semantic_input_bindings[3:]
        rank1_weights = rank1.semantic_input_bindings[3:]
        if rank0_weights != rank1_weights:
            raise RelationCompositionError("PM full MoE nodes do not resolve identical ordered weight buddies")
        full_weight_bindings = (full.semantic_input_bindings[3], full.semantic_input_bindings[4])
        if any(not binding.startswith("init:") for binding in (*full_weight_bindings, *rank0_weights)):
            raise RelationCompositionError("full MoE weights are not external authority bindings")
        expected_weight_pairs = (
            ((0, int(rank0_weights[0].split(":", 1)[1])), (1, int(rank0_weights[1].split(":", 1)[1]))),
            ((0, int(rank0_weights[2].split(":", 1)[1])), (1, int(rank0_weights[3].split(":", 1)[1]))),
        )
        expected_full_shapes = (full_w13, full_w2)
        expected_shard_shapes = (w13_a, w2_a)
        weight_lineages = []
        for binding, expected_pairs, full_shape, shard_shape in zip(
            full_weight_bindings, expected_weight_pairs, expected_full_shapes, expected_shard_shapes
        ):
            full_tid = int(binding.split(":", 1)[1])
            lineage = goal_ir.init_lineages.get(full_tid)
            pairs = () if lineage is None else tuple((int(rank), int(tid)) for rank, tid in lineage.tps)
            gather_dim = None if lineage is None else lineage.gatherDim
            if lineage is None or lineage.ts != full_tid or pairs != expected_pairs or full_tid not in goal_ir.full_init_goal_ids:
                raise RelationCompositionError("full MoE weight lacks exact public two-shard InitGoal lineage")
            if gather_dim not in (None, 0) or lineage.replicated:
                raise RelationCompositionError("full MoE weight lineage is not non-replicated dim-0 gather")
            if tuple(lineage.tsShape) != full_shape or tuple(tuple(shape) for shape in lineage.tpShapes) != (shard_shape, shard_shape):
                raise RelationCompositionError("full MoE weight lineage shapes disagree")
            if shard_shape == (1,):
                raise RelationCompositionError("full MoE weight lineage would select all-reduce reconstruction")
            weight_lineages.append(pairs)
        t_dim, d_dim = w13_a[1], w2_a[2]
        if w13_a[2] != h_model or w2_a[1] != h_model or t_dim != 2 * d_dim:
            raise RelationCompositionError("full MoE swiglu weight dimensions disagree")
        if any(value <= 0 for value in (rows, h_model, num_exp, expert_split, t_dim, d_dim)):
            raise RelationCompositionError("full MoE has non-positive dimensions")
        if layout == "zigzag" and rows % 2 != 0:
            raise RelationCompositionError("zigzag full MoE local token rows are not even")
        certificate_common = dict(
            relation_kind=layout, output_step_triple=frontier,
            input_step_triples=tuple(inputs), full_weight_bindings=full_weight_bindings,
            shard_weight_bindings=((rank0_weights[0], rank0_weights[1]), (rank0_weights[2], rank0_weights[3])),
            num_experts=num_exp, expert_split=expert_split, top_k=top_k,
        )
        if layout == "zigzag":
            certificates.append(FrontierZigzagFullMoECertificate(
                rule_id="zigzag-full-moe-expert-split-two-rank",
                weight_lineage_rank_tids=tuple(weight_lineages),
                weight_lineage_theorem="TrainVerify.Denote.InitGoalHolds.gather2_dim0",
                token_rows=rows, hidden_dim=h_model, t_dim=t_dim, d_dim=d_dim,
                lean_theorem="TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.all2all_moe_gmm_full_1x2",
                **certificate_common,
            ))
        else:
            certificates.append(FrontierOrdinaryMoECertificate(
                rule_id="ordinary-full-moe-expert-split-two-rank",
                lean_theorem="TrainVerify.Denote.GeneratedPatterns.fw_all2all_moe_gmm_full_split_commute_2",
                **certificate_common,
            ))
        rewritten.extend(inputs)
        rewritten_layouts.extend((layout, layout, layout))
    return tuple(certificates), (), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class FrontierPointwiseCertificate:
    rule_id: str
    operator: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triples: tuple[tuple[str, str, str], ...]
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    lean_theorem: str


def expand_pointwise_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[FrontierPointwiseCertificate, ...],
    tuple[tuple[str, str, str], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    arities = {"FW_sigmoid": 1, "FW_swiglu": 2}
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        operators = {step.op for step in steps}
        if len(operators) != 1 or next(iter(operators)) not in arities:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        operator = steps[0].op
        arity = arities[operator]
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError(f"{operator} has an unsupported relation layout")
        if any(len(step.input_shapes) != arity or len(step.input_bindings) != arity for step in steps):
            raise RelationCompositionError(f"{operator} signature mismatch")
        for step in steps:
            if any(shape != step.output_shape for shape in step.input_shapes):
                raise RelationCompositionError(f"{operator} is not shape-preserving pointwise")
        if steps[1].output_shape != steps[2].output_shape:
            raise RelationCompositionError(f"{operator} shard shapes disagree")
        if len(steps[0].output_shape) != 2 or steps[0].output_shape[0] != steps[1].output_shape[0] * 2:
            raise RelationCompositionError(f"{operator} shards do not reconstruct full rows")
        if steps[0].output_shape[1:] != steps[1].output_shape[1:]:
            raise RelationCompositionError(f"{operator} non-row dimensions disagree")
        inputs = tuple(_produced_binding_triple(steps, index) for index in range(arity))
        if layout == "ordinary":
            ordinary_name = "sigmoid" if operator == "FW_sigmoid" else "swiglu"
            theorem = f"TrainVerify.Denote.RelationCompiler.Ordinary2Rel.{ordinary_name}"
        else:
            theorem = f"TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.{operator.removeprefix('FW_')}"
        certificates.append(FrontierPointwiseCertificate(
            rule_id=f"{operator.removeprefix('FW_')}-{layout}-two-rank",
            operator=operator,
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triples=inputs,
            full_shape=steps[0].output_shape,
            shard_shape=steps[1].output_shape,
            lean_theorem=theorem,
        ))
        rewritten.extend(inputs)
        rewritten_layouts.extend((layout,) * arity)
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class FrontierMulCertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triples: tuple[tuple[str, str, str], tuple[str, str, str]]
    full_input_shapes: tuple[tuple[int, ...], tuple[int, ...]]
    shard_input_shapes: tuple[tuple[int, ...], tuple[int, ...]]
    lean_theorem: str


def expand_mul_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[FrontierMulCertificate, ...],
    tuple[tuple[str, str, str], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_mul" for step in steps):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if layout not in {"ordinary", "zigzag"}:
            raise RelationCompositionError("FW_mul has an unsupported relation layout")
        if any(len(step.input_shapes) != 2 or len(step.input_bindings) != 2 for step in steps):
            raise RelationCompositionError("FW_mul signature mismatch")
        full_a, full_b = steps[0].input_shapes
        if len(full_a) != 2 or len(full_b) != 2:
            raise RelationCompositionError("broadcast FW_mul requires rank-2 tensors")
        if full_a != (full_b[0], 1) or steps[0].output_shape != full_b:
            raise RelationCompositionError("full FW_mul is not [rows,1] by [rows,width] broadcast")

        # PM may present commutative FW_mul operands in the opposite order.  The
        # relation roles are defined by the SM gate/payload order, so align each
        # PM step to those roles before building binding triples.
        expected_shards = ((full_a[0] // 2, full_a[1]), (full_b[0] // 2, full_b[1]))
        role_indices = [(0, 1)]
        for step in steps[1:]:
            try:
                indices = tuple(step.input_shapes.index(shape) for shape in expected_shards)
            except ValueError as exc:
                raise RelationCompositionError("FW_mul PM inputs do not match SM roles") from exc
            if len(set(indices)) != 2:
                raise RelationCompositionError("FW_mul PM input roles are ambiguous")
            role_indices.append(indices)
        shard_a, shard_b = (steps[1].input_shapes[index] for index in role_indices[1])
        if shard_a != (shard_b[0], 1) or steps[1].output_shape != shard_b:
            raise RelationCompositionError("shard FW_mul is not [rows,1] by [rows,width] broadcast")
        if tuple(steps[2].input_shapes[index] for index in role_indices[2]) != (shard_a, shard_b) or steps[2].output_shape != steps[1].output_shape:
            raise RelationCompositionError("FW_mul shard shapes disagree")
        if full_b[0] != shard_b[0] * 2 or full_b[1] != shard_b[1]:
            raise RelationCompositionError("FW_mul shards do not reconstruct full rows")
        inputs = tuple(
            tuple(step.input_bindings[role_indices[rank][role]] for rank, step in enumerate(steps))
            for role in range(2)
        )
        theorem = (
            "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.mul_broadcast_col1"
            if layout == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.mul_broadcast_col1"
        )
        certificates.append(FrontierMulCertificate(
            rule_id=f"broadcast-mul-{layout}-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triples=inputs,
            full_input_shapes=(full_a, full_b),
            shard_input_shapes=(shard_a, shard_b),
            lean_theorem=theorem,
        ))
        rewritten.extend(inputs)
        rewritten_layouts.extend((layout, layout))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class FrontierToCertificate:
    rule_id: str
    relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_step_triple: tuple[str, str, str]
    input_shape: tuple[int, ...]
    output_shape: tuple[int, ...]
    lean_theorem: str


def advance_to_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[FrontierToCertificate, ...], tuple[tuple[str, str, str], ...]]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_to" for step in steps):
            rewritten.append(frontier)
            continue
        if layout != "ordinary":
            raise RelationCompositionError("FW_to lacks a registered zigzag transfer theorem")
        if any(len(step.input_shapes) != 1 or step.input_shapes[0] != step.output_shape for step in steps):
            raise RelationCompositionError("FW_to is not shape-preserving")
        if steps[0].output_shape[0] != steps[1].output_shape[0] + steps[2].output_shape[0]:
            raise RelationCompositionError("FW_to shards do not reconstruct full rows")
        if steps[1].output_shape != steps[2].output_shape:
            raise RelationCompositionError("FW_to shard shapes disagree")
        input_triple = _produced_binding_triple(steps, 0)
        certificates.append(FrontierToCertificate(
            rule_id="to-ordinary-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triple=input_triple,
            input_shape=steps[0].input_shapes[0],
            output_shape=steps[0].output_shape,
            lean_theorem="TrainVerify.Denote.fw_to_allGather0_commute_2",
        ))
        rewritten.append(input_triple)
    return tuple(certificates), tuple(rewritten)


def advance_per_head_linear_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[PerHeadLinearRelationCertificate, ...], tuple[tuple[str, str, str], ...]]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    for frontier, layout in zip(frontiers, layouts):
        if any(binding.startswith("init:") for binding in frontier):
            rewritten.append(frontier)
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_per_head_mix_precision_linear" for step in steps):
            rewritten.append(frontier)
            continue
        if layout != "ordinary":
            raise RelationCompositionError("per-head linear lacks a registered zigzag transfer theorem")
        if any(len(step.input_shapes) != 2 or len(step.input_bindings) != 2 for step in steps):
            raise RelationCompositionError("per-head linear signature mismatch")
        data_shape, weight_shape = steps[0].input_shapes
        if len(data_shape) != 2 or len(weight_shape) != 3:
            raise RelationCompositionError("per-head linear requires rank-2 data and rank-3 weight")
        expected = (data_shape[0], weight_shape[0], weight_shape[1])
        if weight_shape[2] != data_shape[1] or steps[0].output_shape != expected:
            raise RelationCompositionError("per-head linear dimensions do not compose")
        weight_bindings = tuple(step.input_bindings[1] for step in steps)
        if len(set(weight_bindings)) != 1 or not weight_bindings[0].startswith("init:"):
            raise RelationCompositionError("per-head linear weight is not replicated")
        if steps[1].output_shape != steps[2].output_shape:
            raise RelationCompositionError("per-head linear shard output shapes disagree")
        if steps[0].output_shape[0] != steps[1].output_shape[0] + steps[2].output_shape[0]:
            raise RelationCompositionError("per-head linear shards do not reconstruct full rows")
        input_triple = _produced_binding_triple(steps, 0)
        certificates.append(PerHeadLinearRelationCertificate(
            rule_id="per-head-linear-ordinary-two-rank",
            relation_kind="ordinary",
            output_step_triple=frontier,
            input_role="activation",
            input_relation_step_triple=input_triple,
            replicated_weight_tid=int(weight_bindings[0].split(":", 1)[1]),
            lean_theorem="TrainVerify.Denote.fw_per_head_mix_precision_linear_allGather0_commute_2",
        ))
        rewritten.append(input_triple)
    return tuple(certificates), tuple(rewritten)


def expand_rotary_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[RotaryRelationCertificate, ...],
    tuple[tuple[str, str, str], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    by_id = _step_map(plan)
    groups: dict[tuple[object, ...], dict[int, tuple[int, tuple[str, str, str], tuple[CertificateStep, ...]]]] = {}
    frontier_keys: dict[int, tuple[object, ...]] = {}
    for position, (frontier, layout) in enumerate(zip(frontiers, layouts)):
        if any(binding.startswith("init:") for binding in frontier):
            continue
        steps = tuple(by_id[binding] for binding in frontier)
        if not all(step.op == "FW_rotary_embedding" for step in steps):
            continue
        if layout != "ordinary":
            raise RelationCompositionError("rotary embedding requires ordinary relation layout")
        output_indices = {step.output_index for step in steps}
        if len(output_indices) != 1:
            raise RelationCompositionError("rotary projection indices disagree across ranks")
        output_index = next(iter(output_indices))
        key = (layout, *(step.node_index for step in steps))
        groups.setdefault(key, {})[output_index] = (position, frontier, steps)
        frontier_keys[position] = key
    for key, outputs in groups.items():
        if set(outputs) != {0, 1}:
            raise RelationCompositionError(f"rotary relation group lacks both outputs: {key}")
    certificates = []
    rewritten = []
    rewritten_layouts = []
    emitted = set()
    for position, (frontier, layout) in enumerate(zip(frontiers, layouts)):
        key = frontier_keys.get(position)
        if key is None:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if key in emitted:
            continue
        emitted.add(key)
        q_position, q_frontier, q_steps = groups[key][0]
        k_position, k_frontier, k_steps = groups[key][1]
        del q_position, k_position
        for q_step, k_step in zip(q_steps, k_steps):
            if q_step.input_bindings != k_step.input_bindings:
                raise RelationCompositionError("rotary outputs do not share one operator input binding")
            if len(q_step.input_bindings) != 4:
                raise RelationCompositionError("rotary signature is not cos/position/Q/K")
        cos_bindings = tuple(step.input_bindings[0] for step in q_steps)
        if len(set(cos_bindings)) != 1 or not cos_bindings[0].startswith("init:"):
            raise RelationCompositionError("rotary cos/sin input is not replicated")
        position_triple = tuple(step.input_bindings[1] for step in q_steps)
        q_input = _produced_binding_triple(q_steps, 2)
        k_input = _produced_binding_triple(q_steps, 3)
        inputs = (position_triple, q_input, k_input)
        certificates.append(RotaryRelationCertificate(
            rule_id="rotary-embedding-two-output-ordinary-two-rank",
            relation_kind="ordinary",
            output_step_triples=(q_frontier, k_frontier),
            output_projections=(".1", ".2"),
            input_roles=("position", "query", "key"),
            input_relation_step_triples=inputs,
            replicated_cos_sin_tid=int(cos_bindings[0].split(":", 1)[1]),
            lean_theorem="TrainVerify.Denote.fw_rotary_embedding_allGather0_commute_2",
        ))
        rewritten.extend(inputs)
        rewritten_layouts.extend(("ordinary", "ordinary", "ordinary"))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


def deduplicate_relation_frontiers(
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[tuple[str, str, str], ...], tuple[str, ...]]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("relation frontier/layout lengths disagree")
    seen = set()
    unique_frontiers = []
    unique_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        key = (layout, frontier)
        if key in seen:
            continue
        seen.add(key)
        unique_frontiers.append(frontier)
        unique_layouts.append(layout)
    return tuple(unique_frontiers), tuple(unique_layouts)


def _extend_unique_certificates(sink: list[object] | None, items: tuple[object, ...]) -> None:
    if sink is None:
        return
    seen = set(sink)
    for item in items:
        if item not in seen:
            seen.add(item)
            sink.append(item)


def normalize_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, str, str], ...],
    layouts: tuple[str, ...],
    *,
    rules: tuple[str, ...] = ("alias", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "attention", "rotary", "to", "per_head_linear", "mul", "pointwise", "ordinary_moe", "shuffle", "unshuffle", "topk", "full_producer_chunk", "add"),
    goal_ir: GoalIR | None = None,
    deduplicate_each_round: bool = False,
    certificate_sink: list[object] | None = None,
    side_condition_sink: list[RelationSideCondition] | None = None,
) -> tuple[tuple[tuple[str, str, str], ...], tuple[str, ...]]:
    """Apply registered relation rules to a deterministic fixed point."""
    known = {"alias", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "attention", "rotary", "to", "per_head_linear", "mul", "pointwise", "ordinary_moe", "shuffle", "unshuffle", "topk", "full_producer_chunk", "add"}
    unknown = set(rules) - known
    if unknown:
        raise RelationCompositionError(f"unknown relation normalization rules: {sorted(unknown)}")
    current_frontiers = frontiers
    current_layouts = layouts
    for _iteration in range(len(plan.steps) + 1):
        if deduplicate_each_round:
            current_frontiers, current_layouts = deduplicate_relation_frontiers(
                current_frontiers, current_layouts
            )
        prior_state = (current_frontiers, current_layouts)
        if "alias" in rules:
            _certs, current_frontiers = peel_multiref_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "rms_norm" in rules:
            _certs, current_frontiers = advance_rms_norm_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "float" in rules:
            _certs, current_frontiers = advance_float_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "identity_view" in rules:
            _certs, current_frontiers = advance_identity_view_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "linear" in rules:
            _certs, current_frontiers = advance_linear_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "flatten_3d" in rules:
            _certs, current_frontiers = advance_flatten_3d_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "attention" in rules:
            _certs, current_frontiers, current_layouts = expand_attention_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "rotary" in rules:
            _certs, current_frontiers, current_layouts = expand_rotary_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "to" in rules:
            _certs, current_frontiers = advance_to_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "per_head_linear" in rules:
            _certs, current_frontiers = advance_per_head_linear_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "mul" in rules:
            _certs, current_frontiers, current_layouts = expand_mul_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "pointwise" in rules:
            _certs, current_frontiers, current_layouts = expand_pointwise_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "ordinary_moe" in rules:
            _certs, _conditions, current_frontiers, current_layouts = expand_ordinary_moe_relation_frontiers(
                plan, current_frontiers, current_layouts, goal_ir
            )
            _extend_unique_certificates(certificate_sink, _certs)
            _extend_unique_certificates(side_condition_sink, _conditions)
        if "shuffle" in rules and goal_ir is not None:
            _certs, current_frontiers, current_layouts = advance_faithful_shuffle_relation_frontiers(
                goal_ir, plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "unshuffle" in rules:
            _certs, _conditions, current_frontiers, current_layouts = advance_unshuffle_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
            _extend_unique_certificates(side_condition_sink, _conditions)
        if "topk" in rules:
            _certs, current_frontiers, current_layouts = expand_topk_routing_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "full_producer_chunk" in rules:
            _certs, current_frontiers, current_layouts = advance_full_producer_chunk_relation_frontiers(
                plan, current_frontiers, current_layouts, goal_ir
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "add" in rules:
            _certs, current_frontiers, current_layouts = expand_add_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if deduplicate_each_round:
            current_frontiers, current_layouts = deduplicate_relation_frontiers(
                current_frontiers, current_layouts
            )
        if (current_frontiers, current_layouts) == prior_state:
            return current_frontiers, current_layouts
    raise RelationCompositionError("relation frontier normalization did not converge")


@dataclass(frozen=True)
class RelationPlan:
    family: str
    terminal_rule_id: str
    synchronized_steps: tuple[SynchronizedRelationStep, ...]
    certificates: tuple[object, ...]
    unresolved_frontiers: tuple[tuple[str, ...], ...]
    unresolved_layouts: tuple[str, ...]
    unresolved_side_conditions: tuple[RelationSideCondition, ...]
    zigzag_regions: tuple[ZigzagMetadataRegionCertificate, ...] = ()
    transition_specs: tuple[CertificateTransitionSpec, ...] = ()
    coverage_plan: ExactNodeCoveragePlan | None = None
    dependency_plan: TransitionDependencyPlan | None = None
    atomic_schedule: AtomicSchedulePlan | None = None
    dependent_chain_plan: ClosedDependentChainPlan | None = None
    schema_version: int = 6
    graph_coverage_complete: bool = False
    composer_registered: bool = False

    @property
    def complete(self) -> bool:
        return (
            not self.unresolved_frontiers
            and not self.unresolved_side_conditions
            and self.graph_coverage_complete
            and self.composer_registered
        )


@dataclass(frozen=True, order=True)
class RelationFactSpec:
    """Closed relation fact for the dependent-chain emitter.

    `layout` selects a registered Lean predicate family.  `step_triple` is an
    ordered SM/PM value reference tuple; arbitrary Python/Lean propositions are
    deliberately not representable here.
    """

    layout: str
    step_triple: tuple[str, ...]


@dataclass(frozen=True)
class ClosedRelationFactRecord:
    fact_id: str
    source: RelationFactSpec
    kind: str
    sm_tid: int
    pm_rank0_tid: int
    pm_rank1_tid: int
    metadata_tid: int | None
    metadata_region_id: int | None
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]


def materialize_closed_relation_facts(
    ir: GoalIR,
    proof: ProofPlan,
    relation: RelationPlan,
) -> tuple[ClosedRelationFactRecord, ...]:
    """Resolve every relation fact to closed Lean constructor arguments."""

    specs = {
        fact
        for transition in relation.transition_specs
        for fact in (*transition.pre_facts, *transition.post_facts)
    }
    by_step = {step.step_id: step for step in proof.steps}
    region_by_frontier = {}
    for region in relation.zigzag_regions:
        for frontier in region.frontier_triples:
            previous = region_by_frontier.get(frontier)
            if previous is not None and previous.region_id != region.region_id:
                raise RelationCompositionError(
                    f"zigzag relation fact belongs to multiple metadata regions: {frontier}"
                )
            region_by_frontier[frontier] = region

    metadata_seed = {}
    for certificate in relation.certificates:
        if isinstance(certificate, FaithfulShuffleCertificate):
            source = RelationFactSpec("zigzag", certificate.output_step_triple)
            previous = metadata_seed.get(source)
            if previous is not None and previous != certificate.node_metadata_tid:
                raise RelationCompositionError(
                    f"conflicting shuffle metadata seeds for {source.step_triple}"
                )
            metadata_seed[source] = certificate.node_metadata_tid
    actual_metadata = {}
    transitions_by_id = {
        transition.transition_id: transition for transition in relation.transition_specs
    }
    if relation.dependency_plan is None:
        raise RelationCompositionError("closed facts require a transition dependency plan")
    for transition_id in relation.dependency_plan.order:
        transition = transitions_by_id[transition_id]
        inherited = {
            actual_metadata[fact]
            for fact in transition.pre_facts
            if fact.layout == "zigzag" and fact in actual_metadata
        }
        missing_inputs = [
            fact for fact in transition.pre_facts
            if fact.layout == "zigzag" and fact not in actual_metadata
        ]
        if missing_inputs:
            raise RelationCompositionError(
                f"zigzag metadata input is not live at {transition_id}: {missing_inputs}"
            )
        for fact in transition.post_facts:
            if fact.layout != "zigzag":
                continue
            seeded = metadata_seed.get(fact)
            if seeded is not None:
                if inherited and inherited != {seeded}:
                    raise RelationCompositionError(
                        f"shuffle metadata seed conflicts with inherited authority: {transition_id}"
                    )
                actual_metadata[fact] = seeded
                continue
            if len(inherited) != 1:
                raise RelationCompositionError(
                    f"zigzag transition has non-unique metadata authority: {transition_id}"
                )
            actual_metadata[fact] = next(iter(inherited))

    def resolve(ref: str, expected_side: str) -> tuple[int, tuple[int, ...]]:
        if ref.startswith("init:"):
            if expected_side != "sm":
                raise RelationCompositionError(
                    f"unexpected init reference on {expected_side} relation side: {ref}"
                )
            try:
                tid = int(ref.split(":", 1)[1])
            except ValueError as exc:
                raise RelationCompositionError(f"invalid init relation reference: {ref}") from exc
            lineage = ir.init_lineages.get(tid)
            if lineage is None:
                raise RelationCompositionError(f"missing init lineage for relation fact: {tid}")
            return tid, tuple(lineage.tsShape)
        step = by_step.get(ref)
        if step is None:
            raise RelationCompositionError(f"unknown relation fact step reference: {ref}")
        if step.side != expected_side:
            raise RelationCompositionError(
                f"relation fact side mismatch for {ref}: expected {expected_side}, got {step.side}"
            )
        if step.output_shape is None:
            raise RelationCompositionError(f"relation fact has unknown output shape: {ref}")
        return step.output_tid, tuple(step.output_shape)

    ordered = sorted(specs, key=lambda fact: (fact.layout, fact.step_triple))
    result = []
    for ordinal, fact in enumerate(ordered):
        sm_tid, full_shape = resolve(fact.step_triple[0], "sm")
        pm0_tid, shard0_shape = resolve(fact.step_triple[1], "pm")
        pm1_tid, shard1_shape = resolve(fact.step_triple[2], "pm")
        if shard0_shape != shard1_shape:
            raise RelationCompositionError(
                f"relation fact PM shard shapes disagree: {fact.step_triple}"
            )
        metadata_tid = None
        metadata_region_id = None
        if fact.layout == "zigzag":
            region = region_by_frontier.get(fact.step_triple)
            if region is None:
                raise RelationCompositionError(
                    f"zigzag relation fact has no unique metadata region: {fact.step_triple}"
                )
            metadata_tid = actual_metadata.get(fact)
            if metadata_tid is None:
                raise RelationCompositionError(
                    f"zigzag relation fact lacks directional metadata authority: {fact.step_triple}"
                )
            if metadata_tid not in region.alias_tids:
                raise RelationCompositionError(
                    f"zigzag metadata tid is outside its public alias region: {metadata_tid}"
                )
            metadata_region_id = region.region_id
        elif fact.layout != "ordinary":
            raise RelationCompositionError(f"unsupported closed relation layout: {fact.layout}")
        result.append(ClosedRelationFactRecord(
            fact_id=f"fact_{ordinal:06d}",
            source=fact,
            kind=fact.layout,
            sm_tid=sm_tid,
            pm_rank0_tid=pm0_tid,
            pm_rank1_tid=pm1_tid,
            metadata_tid=metadata_tid,
            metadata_region_id=metadata_region_id,
            full_shape=full_shape,
            shard_shape=shard0_shape,
        ))
    return tuple(result)


@dataclass(frozen=True)
class ClosedTensorShapeFactRecord:
    fact_id: str
    side: str
    tid: int
    shape: tuple[int, ...]
    init_goal_id: int
    kind: str = "tensor_shape"


@dataclass(frozen=True)
class ClosedTensorEqFactRecord:
    fact_id: str
    left_side: str
    left_tid: int
    right_side: str
    right_tid: int
    kind: str = "tensor_eq"


@dataclass(frozen=True)
class ClosedGatherFactRecord:
    fact_id: str
    sm_tid: int
    pm_rank0_tid: int
    pm_rank1_tid: int
    dim: int
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    kind: str = "gather"


@dataclass(frozen=True)
class ClosedPackedCuFactRecord:
    fact_id: str
    side: str
    tid: int
    total_tokens: int
    num_ranks: int
    kind: str = "packed_cu"


@dataclass(frozen=True)
class ClosedRelationStateRecord:
    state_id: str
    fact_ids: tuple[str, ...]


@dataclass(frozen=True)
class ClosedDependentSegmentRecord:
    segment_id: str
    component_id: str
    pre_state_id: str
    post_state_id: str
    transition_ids: tuple[str, ...]
    sm_range: tuple[int, int]
    pm_range: tuple[int, int]


@dataclass(frozen=True)
class ClosedDependentChainPlan:
    relation_facts: tuple[ClosedRelationFactRecord, ...]
    authority_facts: tuple[
        ClosedTensorEqFactRecord | ClosedTensorShapeFactRecord |
        ClosedGatherFactRecord | ClosedPackedCuFactRecord, ...
    ]
    anchor_fact: ClosedTensorShapeFactRecord
    states: tuple[ClosedRelationStateRecord, ...]
    segments: tuple[ClosedDependentSegmentRecord, ...]
    initial_state_id: str
    terminal_state_id: str
    terminal_target_fact_id: str
    expected_sm_node_count: int
    expected_pm_node_count: int

    @property
    def complete(self) -> bool:
        if not self.states or len(self.states) != len(self.segments) + 1:
            return False
        if self.initial_state_id != self.states[0].state_id:
            return False
        if self.terminal_state_id != self.states[-1].state_id:
            return False
        if self.terminal_target_fact_id not in self.states[-1].fact_ids:
            return False
        if any(not state.fact_ids for state in self.states):
            return False
        for index, segment in enumerate(self.segments):
            if segment.pre_state_id != self.states[index].state_id:
                return False
            if segment.post_state_id != self.states[index + 1].state_id:
                return False
        for side, expected in (("sm", self.expected_sm_node_count), ("pm", self.expected_pm_node_count)):
            cursor = 0
            for segment in self.segments:
                begin, end = segment.sm_range if side == "sm" else segment.pm_range
                if begin == end:
                    continue
                if begin != cursor or end < begin:
                    return False
                cursor = end
            if cursor != expected:
                return False
        return True


def build_closed_dependent_chain_plan(
    ir: GoalIR,
    proof: ProofPlan,
    relation: RelationPlan,
) -> ClosedDependentChainPlan:
    """Turn the frozen atomic schedule into nonempty closed liveness states."""

    schedule = relation.atomic_schedule
    dependency = relation.dependency_plan
    if schedule is None or not schedule.complete or dependency is None:
        raise RelationCompositionError("closed chain requires a complete frozen atomic schedule")
    facts = materialize_closed_relation_facts(ir, proof, relation)
    record_by_source = {item.source: item for item in facts}

    sm_written = {tid for node in ir.sm_nodes for tid in node.outs}
    anchor_tid = next((
        tid for tid in sorted(ir.full_init_goal_ids)
        if tid in ir.init_lineages and tid not in sm_written
    ), None)
    if anchor_tid is None:
        raise RelationCompositionError("no immutable SM init tensor-shape anchor is available")
    anchor_lineage = ir.init_lineages[anchor_tid]
    anchor = ClosedTensorShapeFactRecord(
        fact_id=f"anchor_sm_shape_{anchor_tid}",
        side="sm",
        tid=anchor_tid,
        shape=tuple(anchor_lineage.tsShape),
        init_goal_id=anchor_tid,
    )

    sm_written_tids = {tid for node in ir.sm_nodes for tid in node.outs}
    pm_written_tids = {tid for node in ir.pm_nodes for tid in node.outs}
    authority_facts = []
    authority_keys = set()

    def add_authority(item, key, side_tids):
        if key in authority_keys:
            return
        for side, tid in side_tids:
            written = sm_written_tids if side == "sm" else pm_written_tids
            if tid in written:
                raise RelationCompositionError(
                    f"closed authority fact references graph-written tid: {side}:{tid}"
                )
        authority_keys.add(key)
        authority_facts.append(item)

    facts_by_region = {}
    for fact in facts:
        if fact.metadata_region_id is not None:
            facts_by_region.setdefault(fact.metadata_region_id, set()).add(fact.metadata_tid)
    for region in sorted(relation.zigzag_regions, key=lambda item: item.region_id):
        add_authority(
            ClosedPackedCuFactRecord(
                fact_id=f"authority_packed_cu_{region.region_id:06d}",
                side="pm", tid=region.contract_metadata_tid,
                total_tokens=region.total_tokens, num_ranks=region.num_ranks,
            ),
            ("packed_cu", region.contract_metadata_tid, region.total_tokens, region.num_ranks),
            (("pm", region.contract_metadata_tid),),
        )
        actual_tids = facts_by_region.get(region.region_id, set())
        if not actual_tids:
            raise RelationCompositionError(
                f"metadata region has no materialized zigzag facts: {region.region_id}"
            )
        for actual_tid in sorted(actual_tids):
            add_authority(
                ClosedTensorEqFactRecord(
                    fact_id=f"authority_pm_metadata_eq_{region.region_id:06d}_{actual_tid}",
                    left_side="pm", left_tid=actual_tid,
                    right_side="pm", right_tid=region.contract_metadata_tid,
                ),
                ("tensor_eq", "pm", actual_tid, "pm", region.contract_metadata_tid),
                (("pm", actual_tid), ("pm", region.contract_metadata_tid)),
            )
    for certificate in relation.certificates:
        if not isinstance(certificate, InitChunkBoundaryCertificate):
            continue
        add_authority(
            ClosedTensorShapeFactRecord(
                fact_id=f"authority_init_shape_sm_{certificate.sm_tid}",
                side="sm", tid=certificate.sm_tid, shape=certificate.full_shape,
                init_goal_id=certificate.sm_tid,
            ),
            ("tensor_shape", "sm", certificate.sm_tid, certificate.full_shape),
            (("sm", certificate.sm_tid),),
        )
        for _rank, pm_tid in certificate.lineage_pm_rank_tids:
            add_authority(
                ClosedTensorShapeFactRecord(
                    fact_id=f"authority_init_shape_pm_{pm_tid}",
                    side="pm", tid=pm_tid, shape=certificate.full_shape,
                    init_goal_id=pm_tid,
                ),
                ("tensor_shape", "pm", pm_tid, certificate.full_shape),
                (("pm", pm_tid),),
            )
    for certificate in relation.certificates:
        if type(certificate) is InitChunkBoundaryCertificate:
            pm_tids = tuple(tid for _rank, tid in certificate.lineage_pm_rank_tids)
            if len(pm_tids) != 1:
                raise RelationCompositionError("InitChunk lineage is not singleton full-value authority")
            add_authority(
                ClosedTensorEqFactRecord(
                    fact_id=f"authority_init_eq_{certificate.sm_tid}_{pm_tids[0]}",
                    left_side="sm", left_tid=certificate.sm_tid,
                    right_side="pm", right_tid=pm_tids[0],
                ),
                ("tensor_eq", "sm", certificate.sm_tid, "pm", pm_tids[0]),
                (("sm", certificate.sm_tid), ("pm", pm_tids[0])),
            )
        elif type(certificate) is HiddenShardedEmbeddingAllToAllCertificate:
            if not certificate.ids_binding.startswith("init:"):
                raise RelationCompositionError("hidden embedding ids are not external")
            ids_tid = int(certificate.ids_binding.split(":", 1)[1])
            add_authority(
                ClosedTensorEqFactRecord(
                    fact_id=f"authority_embedding_ids_eq_{ids_tid}",
                    left_side="sm", left_tid=ids_tid,
                    right_side="pm", right_tid=ids_tid,
                ),
                ("tensor_eq", "sm", ids_tid, "pm", ids_tid),
                (("sm", ids_tid), ("pm", ids_tid)),
            )
            ids_lineage = ir.init_lineages.get(ids_tid)
            if ids_lineage is None:
                raise RelationCompositionError("hidden embedding ids lack InitGoal shape")
            add_authority(
                ClosedTensorShapeFactRecord(
                    fact_id=f"authority_embedding_ids_shape_sm_{ids_tid}",
                    side="sm", tid=ids_tid, shape=tuple(ids_lineage.tsShape),
                    init_goal_id=ids_tid,
                ),
                ("tensor_shape", "sm", ids_tid, tuple(ids_lineage.tsShape)),
                (("sm", ids_tid),),
            )
            shard_tids = tuple(tid for _rank, tid in certificate.shard_weight_rank_tids)
            if len(shard_tids) != 2:
                raise RelationCompositionError("hidden embedding does not have two weight shards")
            full_shape = (certificate.vocab, certificate.hidden_shard * 2)
            shard_shape = (certificate.vocab, certificate.hidden_shard)
            add_authority(
                ClosedGatherFactRecord(
                    fact_id=f"authority_embedding_weight_gather_{certificate.full_weight_tid}",
                    sm_tid=certificate.full_weight_tid,
                    pm_rank0_tid=shard_tids[0], pm_rank1_tid=shard_tids[1],
                    dim=certificate.weight_gather_dim,
                    full_shape=full_shape, shard_shape=shard_shape,
                ),
                ("gather", certificate.full_weight_tid, *shard_tids,
                 certificate.weight_gather_dim, full_shape, shard_shape),
                (("sm", certificate.full_weight_tid),
                 ("pm", shard_tids[0]), ("pm", shard_tids[1])),
            )
    for certificate in relation.certificates:
        if type(certificate) not in (
            FrontierOrdinaryMoECertificate, FrontierZigzagFullMoECertificate,
        ):
            continue
        if len(certificate.full_weight_bindings) != 2 or len(certificate.shard_weight_bindings) != 2:
            raise RelationCompositionError("full MoE does not have exactly two expert weights")
        for weight_index, (full_binding, shard_bindings) in enumerate(zip(
            certificate.full_weight_bindings, certificate.shard_weight_bindings
        )):
            if not full_binding.startswith("init:") or len(shard_bindings) != 2 or any(
                not binding.startswith("init:") for binding in shard_bindings
            ):
                raise RelationCompositionError("full MoE weight bindings are not external InitGoal values")
            full_tid = int(full_binding.split(":", 1)[1])
            shard_tids = tuple(int(binding.split(":", 1)[1]) for binding in shard_bindings)
            lineage = ir.init_lineages.get(full_tid)
            if lineage is None:
                raise RelationCompositionError(f"full MoE weight lacks InitGoal lineage: {full_tid}")
            if tuple(lineage.tps) != ((0, shard_tids[0]), (1, shard_tids[1])):
                raise RelationCompositionError("full MoE weight lineage is not the exact ordered shard pair")
            if lineage.gatherDim not in (None, 0) or lineage.replicated or len(lineage.tpShapes) != 2:
                raise RelationCompositionError("full MoE weight is not a dim-0 two-rank gather")
            full_shape = tuple(lineage.tsShape)
            shard_shapes = tuple(tuple(shape) for shape in lineage.tpShapes)
            if not full_shape or shard_shapes[0] != shard_shapes[1] or (
                full_shape[0] != shard_shapes[0][0] * 2 or full_shape[1:] != shard_shapes[0][1:]
            ):
                raise RelationCompositionError("full MoE weight lineage shapes are not dim-0 shards")
            if type(certificate) is FrontierZigzagFullMoECertificate and (
                certificate.weight_lineage_rank_tids[weight_index]
                != ((0, shard_tids[0]), (1, shard_tids[1]))
            ):
                raise RelationCompositionError("zigzag MoE certificate disagrees with InitGoal weight lineage")
            add_authority(
                ClosedGatherFactRecord(
                    fact_id=f"authority_moe_weight_gather_{full_tid}",
                    sm_tid=full_tid, pm_rank0_tid=shard_tids[0],
                    pm_rank1_tid=shard_tids[1], dim=0,
                    full_shape=full_shape, shard_shape=shard_shapes[0],
                ),
                ("gather", full_tid, *shard_tids, 0, full_shape, shard_shapes[0]),
                (("sm", full_tid), ("pm", shard_tids[0]), ("pm", shard_tids[1])),
            )

    replicated_tids = set()
    for certificate in relation.certificates:
        if type(certificate) in (
            FrontierLinearCertificate, FrontierRMSNormCertificate,
            PerHeadLinearRelationCertificate,
        ):
            replicated_tids.add(certificate.replicated_weight_tid)
        elif type(certificate) is FullProducerChunkCertificate:
            if not certificate.replicated_weight_binding.startswith("init:"):
                raise RelationCompositionError("full-producer weight is not an external binding")
            weight_tid = int(certificate.replicated_weight_binding.split(":", 1)[1])
            if certificate.weight_init_lineage_rank_tids != ((0, weight_tid),):
                raise RelationCompositionError("full-producer weight lacks singleton InitGoal lineage")
            replicated_tids.add(weight_tid)
        elif type(certificate) is RotaryRelationCertificate:
            replicated_tids.add(certificate.replicated_cos_sin_tid)
    for tid in sorted(replicated_tids):
        lineage = ir.init_lineages.get(tid)
        if lineage is None or tuple(lineage.tsShape) == ():
            raise RelationCompositionError(
                f"replicated parameter lacks an InitGoal shape: {tid}"
            )
        shape = tuple(lineage.tsShape)
        add_authority(
            ClosedTensorEqFactRecord(
                fact_id=f"authority_replicated_eq_{tid}",
                left_side="sm", left_tid=tid, right_side="pm", right_tid=tid,
            ),
            ("tensor_eq", "sm", tid, "pm", tid), (("sm", tid), ("pm", tid)),
        )
        for side in ("sm", "pm"):
            add_authority(
                ClosedTensorShapeFactRecord(
                    fact_id=f"authority_replicated_shape_{side}_{tid}",
                    side=side, tid=tid, shape=shape, init_goal_id=tid,
                ),
                ("tensor_shape", side, tid, shape), ((side, tid),),
            )
    by_step = {step.step_id: step for step in proof.steps}
    for certificate in relation.certificates:
        if not isinstance(certificate, FaithfulShuffleCertificate):
            continue
        sm_step = by_step[certificate.output_step_triple[0]]
        if len(sm_step.input_tids) < 2:
            raise RelationCompositionError("shuffle SM step lacks metadata input")
        sm_metadata_tid = sm_step.input_tids[1]
        add_authority(
            ClosedTensorEqFactRecord(
                fact_id=f"authority_cross_metadata_eq_{sm_metadata_tid}_{certificate.node_metadata_tid}",
                left_side="sm", left_tid=sm_metadata_tid,
                right_side="pm", right_tid=certificate.node_metadata_tid,
            ),
            ("tensor_eq", "sm", sm_metadata_tid, "pm", certificate.node_metadata_tid),
            (("sm", sm_metadata_tid), ("pm", certificate.node_metadata_tid)),
        )
    authority_facts = tuple(sorted(authority_facts, key=lambda item: item.fact_id))

    consumers = {item.source: set() for item in facts}
    producer = {}
    transition_by_id = {item.transition_id: item for item in relation.transition_specs}
    for transition in relation.transition_specs:
        component = schedule.transition_components[transition.transition_id]
        for fact in transition.post_facts:
            if fact in producer:
                raise RelationCompositionError(f"closed chain fact has duplicate producer: {fact}")
            producer[fact] = component
        for fact in transition.pre_facts:
            consumers.setdefault(fact, set()).add(component)

    consumed = {fact for transition in relation.transition_specs for fact in transition.pre_facts}
    sinks = [
        fact for transition in relation.transition_specs for fact in transition.post_facts
        if fact not in consumed and proof.target_steps[0] in fact.step_triple
    ]
    sinks = sorted(set(sinks), key=lambda item: (item.layout, item.step_triple))
    if len(sinks) != 1:
        raise RelationCompositionError(
            f"terminal relation fact is not unique: found {len(sinks)} candidates"
        )
    target_source = sinks[0]
    target_fact_id = record_by_source[target_source].fact_id

    components = {item.component_id: item for item in schedule.components}
    transition_order = {item: index for index, item in enumerate(dependency.order)}
    ordered_components = [components[item] for item in schedule.order]
    shuffle_indices = [
        index for index, component in enumerate(ordered_components)
        if any(
            any(fact.layout == "ordinary" for fact in transition_by_id[tid].pre_facts)
            and any(fact.layout == "zigzag" for fact in transition_by_id[tid].post_facts)
            for tid in component.transition_ids
        )
    ]
    authority_last_use = {}
    for fact in authority_facts:
        if fact.kind == "tensor_eq":
            side_tids = ((fact.left_side, fact.left_tid), (fact.right_side, fact.right_tid))
        elif fact.kind == "tensor_shape":
            side_tids = ((fact.side, fact.tid),)
        elif fact.kind == "gather":
            side_tids = (("sm", fact.sm_tid), ("pm", fact.pm_rank0_tid),
                         ("pm", fact.pm_rank1_tid))
        else:
            side_tids = ()
        uses = []
        for index, component in enumerate(ordered_components):
            sm_inputs = {tid for node in ir.sm_nodes[slice(*component.sm_range)] for tid in node.ins}
            pm_inputs = {tid for node in ir.pm_nodes[slice(*component.pm_range)] for tid in node.ins}
            if any(tid in (sm_inputs if side == "sm" else pm_inputs) for side, tid in side_tids):
                uses.append(index)
        if fact.kind == "packed_cu":
            uses.extend(shuffle_indices)
        authority_last_use[fact.fact_id] = max(uses, default=0)
    live = {anchor.fact_id, *(item.fact_id for item in authority_facts)}
    available_sources = set()
    completed_components = set()
    states = [ClosedRelationStateRecord(state_id="state_000000", fact_ids=tuple(sorted(live)))]
    segments = []
    for ordinal, component_id in enumerate(schedule.order):
        component = components[component_id]
        ordered_transitions = tuple(sorted(
            component.transition_ids, key=lambda item: transition_order[item]
        ))
        local = set(available_sources)
        for transition_id in ordered_transitions:
            transition = transition_by_id[transition_id]
            missing = set(transition.pre_facts) - local
            if missing:
                raise RelationCompositionError(
                    f"component consumes unavailable relation facts: {component_id}: {sorted(map(repr, missing))}"
                )
            local.update(transition.post_facts)
        completed_components.add(component_id)
        available_sources.update(
            fact for transition_id in ordered_transitions
            for fact in transition_by_id[transition_id].post_facts
        )
        available_sources = {
            fact for fact in available_sources
            if fact == target_source or any(
                consumer not in completed_components for consumer in consumers.get(fact, ())
            )
        }
        live = {
            anchor.fact_id,
            *(fact_id for fact_id, last_use in authority_last_use.items() if last_use > ordinal),
            *(record_by_source[fact].fact_id for fact in available_sources),
        }
        post_state = ClosedRelationStateRecord(
            state_id=f"state_{ordinal + 1:06d}",
            fact_ids=tuple(sorted(live)),
        )
        states.append(post_state)
        segments.append(ClosedDependentSegmentRecord(
            segment_id=f"segment_{ordinal:06d}",
            component_id=component_id,
            pre_state_id=states[-2].state_id,
            post_state_id=post_state.state_id,
            transition_ids=ordered_transitions,
            sm_range=component.sm_range,
            pm_range=component.pm_range,
        ))

    plan = ClosedDependentChainPlan(
        relation_facts=facts,
        authority_facts=authority_facts,
        anchor_fact=anchor,
        states=tuple(states),
        segments=tuple(segments),
        initial_state_id=states[0].state_id,
        terminal_state_id=states[-1].state_id,
        terminal_target_fact_id=target_fact_id,
        expected_sm_node_count=len(ir.sm_nodes),
        expected_pm_node_count=len(ir.pm_nodes),
    )
    if not plan.complete:
        raise RelationCompositionError("closed dependent chain failed exact coverage validation")
    return plan


@dataclass(frozen=True)
class CertificateTransitionSpec:
    transition_id: str
    rule_id: str
    pre_facts: tuple[RelationFactSpec, ...]
    post_facts: tuple[RelationFactSpec, ...]
    sm_node_indices: tuple[int, ...]
    pm_node_indices: tuple[int, ...]
    lean_theorem: str


def _fact(layout: str, refs: tuple[str, ...]) -> RelationFactSpec:
    if layout not in {"ordinary", "zigzag"}:
        raise RelationCompositionError(f"closed relation fact has unknown layout {layout!r}")
    if len(refs) != 3:
        raise RelationCompositionError("closed relation fact must contain one SM and two ordered PM refs")
    return RelationFactSpec(layout, tuple(refs))


def _step_node_footprint(refs: tuple[str, ...]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    sm: set[int] = set()
    pm: set[int] = set()
    for ref in refs:
        if ref.startswith("init:"):
            continue
        fields = ref.split(":")
        if len(fields) != 3 or fields[0] not in {"sm", "pm"}:
            raise RelationCompositionError(f"malformed certificate step reference {ref!r}")
        try:
            node_index = int(fields[1])
            int(fields[2])
        except ValueError as exc:
            raise RelationCompositionError(f"malformed certificate step reference {ref!r}") from exc
        (sm if fields[0] == "sm" else pm).add(node_index)
    return tuple(sorted(sm)), tuple(sorted(pm))


def _merge_footprints(*ref_groups: tuple[str, ...]) -> tuple[tuple[int, ...], tuple[int, ...]]:
    sm: set[int] = set()
    pm: set[int] = set()
    for refs in ref_groups:
        left, right = _step_node_footprint(tuple(refs))
        sm.update(left)
        pm.update(right)
    return tuple(sorted(sm)), tuple(sorted(pm))


def build_certificate_transition_specs(
    plan: ProofPlan,
    certificates: tuple[object, ...],
) -> tuple[CertificateTransitionSpec, ...]:
    """Normalize every executable certificate through an explicit adapter.

    Contract and metadata-region certificates are closed assumptions rather
    than graph transitions.  Every other accepted dataclass is named below;
    unknown certificate types fail closed instead of being reflected by field
    name.
    """

    del plan  # Step IDs already bind the immutable ordered node indices.
    transitions: list[CertificateTransitionSpec] = []
    for ordinal, cert in enumerate(certificates):
        if type(cert) is RotaryRelationCertificate and cert.rule_id == "rotary-embedding-ordinary-two-rank":
            # Superseded by the two-output primitive certificate emitted by
            # fixed-point normalization.
            continue
        if type(cert) is PerHeadLinearRelationCertificate and cert.rule_id == "per-head-mix-precision-linear-ordinary-two-rank":
            # Superseded by the primitive per-head-linear certificate.
            continue
        if type(cert) in (
            ContractDischargeCertificate,
            ZigzagMetadataRegionCertificate,
            ChunkReconstructionCertificate,
            RouterInputCheckpointCertificate,
            RMSNormRelationCertificate,
            AddRelationCertificate,
            UnaryRelationChainCertificate,
            AttentionRelationCertificate,
            ZigzagQRelationCertificate,
            ZigzagAttentionKVRelationCertificate,
        ):
            # Closed assumptions and legacy derived macro certificates do not
            # own graph nodes.  Their primitive frontier certificates remain
            # in the same RelationPlan and are adapted below.
            continue
        pre: tuple[RelationFactSpec, ...]
        post: tuple[RelationFactSpec, ...]
        footprint_groups: tuple[tuple[str, ...], ...]
        if type(cert) in (MultirefAliasCertificate, FrontierIdentityViewCertificate,
                FrontierLinearCertificate, FrontierRMSNormCertificate,
                FrontierFloatCertificate, FrontierFlatten3DCertificate,
                FrontierToCertificate):
            pre = (_fact(cert.relation_kind, cert.input_step_triple),)
            post = (_fact(cert.relation_kind, cert.output_step_triple),)
            footprint_groups = (cert.output_step_triple,)
        elif type(cert) in (FrontierAddCertificate, FrontierMulCertificate,
                FrontierPointwiseCertificate, FrontierAttentionCertificate,
                FrontierOrdinaryMoECertificate, FrontierZigzagFullMoECertificate):
            input_layouts = (
                cert.input_relation_kinds
                if type(cert) is FrontierAttentionCertificate
                else (cert.relation_kind,) * len(cert.input_step_triples)
            )
            if len(input_layouts) != len(cert.input_step_triples):
                raise RelationCompositionError(f"{type(cert).__name__} input relation arity mismatch")
            pre = tuple(_fact(kind, refs) for kind, refs in zip(input_layouts, cert.input_step_triples))
            post = (_fact(cert.relation_kind, cert.output_step_triple),)
            footprint_groups = (cert.output_step_triple,)
        elif type(cert) is FrontierTopKRoutingCertificate:
            pre = (_fact(cert.relation_kind, cert.input_step_triple),)
            post = tuple(_fact(cert.relation_kind, refs) for refs in cert.output_step_triples)
            footprint_groups = tuple(cert.output_step_triples)
        elif type(cert) is FullProducerChunkCertificate:
            pre = (_fact(cert.pre_layout, cert.input_step_triple),)
            post = (_fact(cert.post_layout, cert.output_step_triple),)
            footprint_groups = (
                (cert.sm_operator_step,),
                (cert.pm_full_operator_step,),
                tuple(cert.pm_chunk_steps),
                tuple(cert.sm_identity_chain),
                tuple(cert.pm_identity_chain),
                (cert.pm_allgather_step,),
            )
        elif type(cert) is PerHeadLinearRelationCertificate:
            pre = (_fact(cert.relation_kind, cert.input_relation_step_triple),)
            post = (_fact(cert.relation_kind, cert.output_step_triple),)
            footprint_groups = (cert.output_step_triple,)
        elif type(cert) is RotaryRelationCertificate:
            pre = tuple(_fact(cert.relation_kind, refs) for refs in cert.input_relation_step_triples)
            post = tuple(_fact(cert.relation_kind, refs) for refs in cert.output_step_triples)
            footprint_groups = tuple(cert.output_step_triples)
        elif type(cert) is FrontierUnshuffleCertificate:
            pre = (_fact(cert.pre_layout, cert.input_step_triple),)
            post = (_fact(cert.post_layout, cert.output_step_triple),)
            footprint_groups = (cert.output_step_triple,)
        elif type(cert) is FaithfulShuffleCertificate:
            pre = (_fact(cert.pre_layout, cert.input_step_triple),)
            post = (_fact(cert.post_layout, cert.output_step_triple),)
            footprint_groups = (cert.output_step_triple,)
        elif type(cert) is InitChunkBoundaryCertificate:
            post_refs = (f"init:{cert.sm_tid}", *tuple(cert.chunk_step_pair))
            pre = ()
            post = (_fact(cert.relation_kind, post_refs),)
            footprint_groups = (tuple(cert.chunk_step_pair),)
        elif type(cert) is HiddenShardedEmbeddingAllToAllCertificate:
            post_refs = (cert.sm_embedding_step, *tuple(cert.alltoall_steps))
            pre = ()
            post = (_fact("ordinary", post_refs),)
            footprint_groups = (
                (cert.sm_embedding_step,), tuple(cert.pm_embedding_steps), tuple(cert.alltoall_steps)
            )
        elif type(cert) is InnerChunkCEGatherCertificate:
            post_refs = (cert.sm_ce_step, *tuple(cert.pm_ce_steps))
            pre = ()
            post = (_fact("ordinary", post_refs),)
            footprint_groups = ((cert.sm_ce_step,), tuple(cert.pm_ce_steps), (cert.pm_gather_step,))
        elif type(cert) is IndexedStackGatherCertificate:
            pre = tuple(_fact("ordinary", refs) for refs in cert.layer_step_triples)
            post_refs = (cert.sm_stack_step, *tuple(cert.pm_stack_steps))
            post = (_fact("ordinary", post_refs),)
            footprint_groups = (
                (cert.sm_stack_step,), tuple(cert.pm_stack_steps), (cert.pm_gather_step,)
            )
        else:
            raise RelationCompositionError(
                f"no explicit transition adapter for certificate type {type(cert).__name__}"
            )

        sm_nodes, pm_nodes = _merge_footprints(*footprint_groups)
        if not post:
            raise RelationCompositionError(f"{type(cert).__name__} transition has no post fact")
        lean_theorem = (
            cert.result_relation_theorem
            if type(cert) is FullProducerChunkCertificate
            else cert.lean_theorem
        )
        if not lean_theorem:
            raise RelationCompositionError(
                f"{type(cert).__name__} transition lacks a registered Lean theorem"
            )
        transitions.append(CertificateTransitionSpec(
            transition_id=f"{ordinal:06d}:{type(cert).__name__}:{cert.rule_id}",
            rule_id=cert.rule_id,
            pre_facts=tuple(sorted(set(pre))),
            post_facts=tuple(sorted(set(post))),
            sm_node_indices=sm_nodes,
            pm_node_indices=pm_nodes,
            lean_theorem=lean_theorem,
        ))
    return tuple(transitions)


def build_synchronized_transition_specs(
    synchronized_steps: tuple[SynchronizedRelationStep, ...],
    *,
    ordinal_base: int = 1_000_000,
) -> tuple[CertificateTransitionSpec, ...]:
    """Adapt synchronized terminal steps not represented by primitive certificates."""

    result = []
    for offset, step in enumerate(synchronized_steps):
        if step.rule_id == "ordinary-topk-projection-two-rank":
            if step.output_projection != ".2.2":
                # The generic two-output top-k primitive owns projections .1/.2.1.
                continue
            pre_layout = post_layout = "ordinary"
        elif step.rule_id == "zigzag-topk-unshuffle-two-rank":
            pre_layout, post_layout = "zigzag", "ordinary"
        else:
            raise RelationCompositionError(
                f"no explicit synchronized transition adapter for {step.rule_id}"
            )
        sm_nodes, pm_nodes = _merge_footprints(step.output_step_triple)
        result.append(CertificateTransitionSpec(
            transition_id=(
                f"{ordinal_base + offset:06d}:SynchronizedRelationStep:{step.rule_id}"
            ),
            rule_id=step.rule_id,
            pre_facts=(_fact(pre_layout, step.input_step_triple),),
            post_facts=(_fact(post_layout, step.output_step_triple),),
            sm_node_indices=sm_nodes,
            pm_node_indices=pm_nodes,
            lean_theorem=step.lean_theorems[-1],
        ))
    return tuple(result)


@dataclass(frozen=True)
class TransitionDependencyPlan:
    order: tuple[str, ...]
    dependencies: tuple[tuple[str, tuple[str, ...]], ...]


def build_transition_dependency_plan(
    transitions: tuple[CertificateTransitionSpec, ...],
) -> TransitionDependencyPlan:
    """Reverse the backward frontier certificates into a deterministic DAG."""

    import heapq

    by_id = {item.transition_id: item for item in transitions}
    if len(by_id) != len(transitions):
        raise RelationCompositionError("dependent transitions contain duplicate identities")
    producers: dict[RelationFactSpec, str] = {}
    for item in transitions:
        for fact in item.post_facts:
            prior = producers.get(fact)
            if prior is not None and prior != item.transition_id:
                raise RelationCompositionError(
                    f"relation fact has multiple producers: {prior}, {item.transition_id}"
                )
            producers[fact] = item.transition_id
    dependencies: dict[str, set[str]] = {}
    consumers: dict[str, set[str]] = {item.transition_id: set() for item in transitions}
    for item in transitions:
        required = set()
        for fact in item.pre_facts:
            producer = producers.get(fact)
            if producer is None:
                raise RelationCompositionError(
                    f"relation pre-fact has no producer: {item.transition_id} {fact}"
                )
            if producer == item.transition_id:
                raise RelationCompositionError(
                    f"relation transition depends on its own post-fact: {item.transition_id}"
                )
            required.add(producer)
            consumers[producer].add(item.transition_id)
        dependencies[item.transition_id] = required

    def key(transition_id: str):
        item = by_id[transition_id]
        return (
            min(item.sm_node_indices, default=2**63 - 1),
            min(item.pm_node_indices, default=2**63 - 1),
            max(item.sm_node_indices, default=-1),
            max(item.pm_node_indices, default=-1),
            transition_id,
        )

    remaining = {name: set(values) for name, values in dependencies.items()}
    ready = [(key(name), name) for name, values in remaining.items() if not values]
    heapq.heapify(ready)
    order = []
    while ready:
        _priority, current = heapq.heappop(ready)
        order.append(current)
        for consumer in sorted(consumers[current]):
            remaining[consumer].discard(current)
            if not remaining[consumer]:
                heapq.heappush(ready, (key(consumer), consumer))
    if len(order) != len(transitions):
        blocked = tuple(sorted(name for name, values in remaining.items() if values))
        raise RelationCompositionError(
            f"relation transition dependency graph contains a cycle: {blocked[:3]}"
        )
    return TransitionDependencyPlan(
        order=tuple(order),
        dependencies=tuple(
            (name, tuple(sorted(values))) for name, values in sorted(dependencies.items())
        ),
    )


@dataclass(frozen=True)
class AtomicScheduleComponent:
    component_id: str
    item_ids: tuple[str, ...]
    transition_ids: tuple[str, ...]
    sm_range: tuple[int, int]
    pm_range: tuple[int, int]
    predecessors: tuple[str, ...]


@dataclass(frozen=True)
class AtomicSchedulePlan:
    components: tuple[AtomicScheduleComponent, ...]
    order: tuple[str, ...]
    sm_node_components: tuple[str, ...]
    pm_node_components: tuple[str, ...]
    transition_components: dict[str, str]
    authority_digest: str
    transition_digest: str
    digest: str
    frozen: bool = True

    @property
    def complete(self) -> bool:
        component_ids = {item.component_id for item in self.components}
        return (
            self.frozen
            and set(self.order) == component_ids
            and len(self.order) == len(component_ids)
            and all(item in component_ids for item in self.sm_node_components)
            and all(item in component_ids for item in self.pm_node_components)
            and all(item in component_ids for item in self.transition_components.values())
        )


def build_atomic_schedule(
    ir: GoalIR,
    transitions: tuple[CertificateTransitionSpec, ...],
) -> AtomicSchedulePlan:
    """Freeze shared semantic owners and form a deterministic two-axis SCC schedule."""

    import hashlib
    import heapq
    import json

    transitions = tuple(sorted(transitions, key=lambda item: item.transition_id))
    by_id = {item.transition_id: item for item in transitions}
    if len(by_id) != len(transitions):
        raise RelationCompositionError("atomic schedule has duplicate transition ids")
    if not transitions:
        raise RelationCompositionError("atomic schedule has no semantic transitions")

    parent = {item.transition_id: item.transition_id for item in transitions}

    def find(item):
        while parent[item] != item:
            parent[item] = parent[parent[item]]
            item = parent[item]
        return item

    def union(left, right):
        left, right = find(left), find(right)
        if left == right:
            return
        if left > right:
            left, right = right, left
        parent[right] = left

    users = {
        "sm": [set() for _ in ir.sm_nodes],
        "pm": [set() for _ in ir.pm_nodes],
    }
    for item in transitions:
        if not item.sm_node_indices and not item.pm_node_indices:
            raise RelationCompositionError(
                f"semantic transition has empty footprint: {item.transition_id}"
            )
        for side, indices, bound in (
            ("sm", item.sm_node_indices, len(ir.sm_nodes)),
            ("pm", item.pm_node_indices, len(ir.pm_nodes)),
        ):
            if tuple(sorted(set(indices))) != indices:
                raise RelationCompositionError(
                    f"{side} footprint is not sorted and unique: {item.transition_id}"
                )
            for index in indices:
                if index < 0 or index >= bound:
                    raise RelationCompositionError(
                        f"{side} footprint index out of bounds: {item.transition_id}:{index}"
                    )
                users[side][index].add(item.transition_id)
    for side in ("sm", "pm"):
        for node_users in users[side]:
            ordered = sorted(node_users)
            for other in ordered[1:]:
                union(ordered[0], other)

    groups = {}
    for transition_id in sorted(by_id):
        groups.setdefault(find(transition_id), []).append(transition_id)
    canonical_group = {}
    for members in groups.values():
        group_id = f"semantic:{members[0]}"
        for member in members:
            canonical_group[member] = group_id

    node_items = {"sm": [None] * len(ir.sm_nodes), "pm": [None] * len(ir.pm_nodes)}
    all_items = set(canonical_group.values())
    for side in ("sm", "pm"):
        index = 0
        while index < len(node_items[side]):
            node_users = users[side][index]
            if node_users:
                owners = {canonical_group[item] for item in node_users}
                if len(owners) != 1:
                    raise RelationCompositionError("shared-node union is incomplete")
                node_items[side][index] = next(iter(owners))
                index += 1
                continue
            begin = index
            while index < len(node_items[side]) and not users[side][index]:
                index += 1
            frame_id = f"frame:{side}:{begin:06d}:{index:06d}"
            all_items.add(frame_id)
            for position in range(begin, index):
                node_items[side][position] = frame_id
    if any(item is None for side in ("sm", "pm") for item in node_items[side]):
        raise RelationCompositionError("atomic schedule does not partition an authority axis")

    edges = set()
    semantic_items = set(canonical_group.values())
    for side in ("sm", "pm"):
        stream = []
        for item in node_items[side]:
            if not stream or stream[-1] != item:
                stream.append(item)
        edges.update((left, right) for left, right in zip(stream, stream[1:]) if left != right)
        for index, item in enumerate(stream):
            if not item.startswith("frame:"):
                continue
            right = next((candidate for candidate in stream[index + 1:] if candidate in semantic_items), None)
            left = next((candidate for candidate in reversed(stream[:index]) if candidate in semantic_items), None)
            owner = right or left or min(semantic_items)
            edges.add((item, owner))
            edges.add((owner, item))

    dependency = build_transition_dependency_plan(transitions)
    for consumer, producers in dependency.dependencies:
        for producer in producers:
            left, right = canonical_group[producer], canonical_group[consumer]
            if left != right:
                edges.add((left, right))

    graph = {item: set() for item in all_items}
    reverse = {item: set() for item in all_items}
    for left, right in edges:
        graph[left].add(right)
        reverse[right].add(left)

    visited = set()
    finish = []
    for root in sorted(all_items):
        if root in visited:
            continue
        stack = [(root, False)]
        while stack:
            node, expanded = stack.pop()
            if expanded:
                finish.append(node)
                continue
            if node in visited:
                continue
            visited.add(node)
            stack.append((node, True))
            for child in sorted(graph[node], reverse=True):
                if child not in visited:
                    stack.append((child, False))

    raw_components = []
    assigned = set()
    for root in reversed(finish):
        if root in assigned:
            continue
        members = []
        stack = [root]
        assigned.add(root)
        while stack:
            node = stack.pop()
            members.append(node)
            for child in sorted(reverse[node], reverse=True):
                if child not in assigned:
                    assigned.add(child)
                    stack.append(child)
        raw_components.append(tuple(sorted(members)))

    def positions_for(members, side):
        member_set = set(members)
        return [index for index, item in enumerate(node_items[side]) if item in member_set]

    raw_components.sort(key=lambda members: (
        min(positions_for(members, "sm"), default=2**63 - 1),
        min(positions_for(members, "pm"), default=2**63 - 1),
        members,
    ))
    item_component = {}
    component_ranges = {}
    for ordinal, members in enumerate(raw_components):
        component_id = f"component:{ordinal:06d}"
        for item in members:
            item_component[item] = component_id
        ranges = []
        for side, bound in (("sm", len(ir.sm_nodes)), ("pm", len(ir.pm_nodes))):
            positions = positions_for(members, side)
            if not positions:
                ranges.append((bound, bound))
                continue
            begin, end = positions[0], positions[-1] + 1
            if positions != list(range(begin, end)):
                raise RelationCompositionError(
                    f"atomic SCC is non-convex on {side}: {component_id}"
                )
            ranges.append((begin, end))
        component_ranges[component_id] = tuple(ranges)

    dag_edges = {
        (item_component[left], item_component[right])
        for left, right in edges
        if item_component[left] != item_component[right]
    }
    predecessors = {item: set() for item in component_ranges}
    children = {item: set() for item in component_ranges}
    for left, right in dag_edges:
        predecessors[right].add(left)
        children[left].add(right)
    remaining = {item: set(values) for item, values in predecessors.items()}
    ready = []
    for component_id, values in remaining.items():
        if not values:
            sm_range, pm_range = component_ranges[component_id]
            heapq.heappush(ready, ((sm_range[0], pm_range[0], component_id), component_id))
    order = []
    while ready:
        _key, current = heapq.heappop(ready)
        order.append(current)
        for child in sorted(children[current]):
            remaining[child].discard(current)
            if not remaining[child]:
                sm_range, pm_range = component_ranges[child]
                heapq.heappush(ready, ((sm_range[0], pm_range[0], child), child))
    if len(order) != len(component_ranges):
        raise RelationCompositionError("atomic SCC condensation graph is cyclic")

    transition_components = {
        transition_id: item_component[canonical_group[transition_id]]
        for transition_id in sorted(by_id)
    }
    sm_node_components = tuple(item_component[item] for item in node_items["sm"])
    pm_node_components = tuple(item_component[item] for item in node_items["pm"])
    components = []
    for component_id in sorted(component_ranges):
        item_ids = tuple(sorted(item for item, owner in item_component.items() if owner == component_id))
        transition_ids = tuple(sorted(
            item for item, owner in transition_components.items() if owner == component_id
        ))
        sm_range, pm_range = component_ranges[component_id]
        components.append(AtomicScheduleComponent(
            component_id=component_id,
            item_ids=item_ids,
            transition_ids=transition_ids,
            sm_range=sm_range,
            pm_range=pm_range,
            predecessors=tuple(sorted(predecessors[component_id])),
        ))

    def node_payload(node):
        return [node.rank, node.op, list(node.ins), list(node.outs), list(node.params or ())]

    authority_payload = {
        "sm": [node_payload(node) for node in ir.sm_nodes],
        "pm": [node_payload(node) for node in ir.pm_nodes],
    }
    transition_payload = [
        [item.transition_id, item.rule_id,
         list(item.sm_node_indices), list(item.pm_node_indices),
         [repr(fact) for fact in item.pre_facts], [repr(fact) for fact in item.post_facts],
         item.lean_theorem]
        for item in transitions
    ]
    authority_digest = hashlib.sha256(json.dumps(
        authority_payload, separators=(",", ":"), sort_keys=True
    ).encode()).hexdigest()
    transition_digest = hashlib.sha256(json.dumps(
        transition_payload, separators=(",", ":"), sort_keys=True
    ).encode()).hexdigest()
    plan_payload = {
        "authority": authority_digest,
        "transitions": transition_digest,
        "components": [
            [item.component_id, list(item.item_ids), list(item.transition_ids),
             list(item.sm_range), list(item.pm_range), list(item.predecessors)]
            for item in components
        ],
        "order": order,
        "sm": sm_node_components,
        "pm": pm_node_components,
    }
    digest = hashlib.sha256(json.dumps(
        plan_payload, separators=(",", ":"), sort_keys=True
    ).encode()).hexdigest()
    plan = AtomicSchedulePlan(
        components=tuple(components),
        order=tuple(order),
        sm_node_components=sm_node_components,
        pm_node_components=pm_node_components,
        transition_components=transition_components,
        authority_digest=authority_digest,
        transition_digest=transition_digest,
        digest=digest,
    )
    if not plan.complete:
        raise RelationCompositionError("atomic schedule failed completeness validation")
    return plan


@dataclass(frozen=True)
class NodeCoverageSlot:
    side: str
    node_index: int
    node_fingerprint: tuple[int, str, tuple[int, ...], tuple[int, ...], tuple[int, ...]]
    kind: str
    transition_ids: tuple[str, ...]


@dataclass(frozen=True)
class ExactNodeCoveragePlan:
    sm_nodes: tuple[NodeCoverageSlot, ...]
    pm_nodes: tuple[NodeCoverageSlot, ...]

    @property
    def complete(self) -> bool:
        return all(item.node_index == index for index, item in enumerate(self.sm_nodes)) and all(
            item.node_index == index for index, item in enumerate(self.pm_nodes)
        )


def build_exact_node_coverage_plan(
    ir: GoalIR,
    transitions: tuple[CertificateTransitionSpec, ...],
) -> ExactNodeCoveragePlan:
    """Bind semantic certificate footprints and explicit frames to authority order."""

    transition_ids = [item.transition_id for item in transitions]
    if len(set(transition_ids)) != len(transition_ids):
        raise RelationCompositionError("dependent transitions contain duplicate identities")
    sm_owners: list[list[str]] = [[] for _ in ir.sm_nodes]
    pm_owners: list[list[str]] = [[] for _ in ir.pm_nodes]
    for item in transitions:
        for index in item.sm_node_indices:
            if not 0 <= index < len(ir.sm_nodes):
                raise RelationCompositionError(
                    f"SM transition node {index} is outside authority graph"
                )
            sm_owners[index].append(item.transition_id)
        for index in item.pm_node_indices:
            if not 0 <= index < len(ir.pm_nodes):
                raise RelationCompositionError(
                    f"PM transition node {index} is outside authority graph"
                )
            pm_owners[index].append(item.transition_id)

    def slots(side: str, nodes: list[Node], owners: list[list[str]]) -> tuple[NodeCoverageSlot, ...]:
        result = []
        for index, (node, node_owners) in enumerate(zip(nodes, owners)):
            fingerprint = (
                int(node.rank),
                str(node.op),
                tuple(int(value) for value in node.ins),
                tuple(int(value) for value in node.outs),
                tuple(int(value) for value in (node.params or ())),
            )
            canonical_owners = tuple(sorted(set(node_owners)))
            result.append(NodeCoverageSlot(
                side=side,
                node_index=index,
                node_fingerprint=fingerprint,
                kind="semantic" if canonical_owners else "frame",
                transition_ids=canonical_owners,
            ))
        return tuple(result)

    plan = ExactNodeCoveragePlan(
        sm_nodes=slots("sm", ir.sm_nodes, sm_owners),
        pm_nodes=slots("pm", ir.pm_nodes, pm_owners),
    )
    if not plan.complete:
        raise RelationCompositionError("exact node coverage does not preserve authority order")
    return plan


def _dependency_for_input(
    step: CertificateStep, input_tid: int, by_id: dict[str, CertificateStep]
) -> str:
    matches = [
        dependency
        for dependency in step.dependencies
        if by_id[dependency].output_tid == input_tid
    ]
    if len(matches) != 1:
        raise RelationCompositionError(
            f"step {step.step_id} does not have one producer for input tid {input_tid}"
        )
    return matches[0]


def compile_relation_plan(
    ir: GoalIR,
    proof: ProofPlan,
    *,
    peel_aliases: bool = True,
    deduplicate_frontiers: bool = True,
) -> RelationPlan:
    """Compile registered terminal relation families without hiding backbone gaps."""
    stack_error = None
    try:
        terminal = match_indexed_stack_gather_two_rank(ir, proof)
    except RelationCompositionError as exc:
        stack_error = exc
    else:
        layers = build_indexed_stack_layer_relations(proof, terminal)
        chunks = build_chunk_reconstruction_relations(proof, terminal, layers)
        terminal_mixed_certificates, _terminal_inputs, _terminal_layouts = (
            advance_full_producer_chunk_relation_frontiers(
                proof,
                tuple(item.output_step_triple for item in chunks),
                tuple(item.input_relation_kind for item in chunks),
                ir,
            )
        )
        if len(terminal_mixed_certificates) != len(chunks):
            raise RelationCompositionError(
                "indexed terminal chunk relations lack layout-typed full-producer certificates"
            )
        checkpoints = build_router_input_checkpoints(proof, chunks)
        rms_relations = build_rms_norm_relations(proof, checkpoints)
        add_relations = build_add_relations(proof, rms_relations)
        attention_output_chains = build_attention_output_unary_relations(
            ir, proof, add_relations
        )
        attention_relations = build_attention_relations(
            proof, attention_output_chains
        )
        ordinary_rotary_relations = build_ordinary_rotary_relations(
            proof, attention_relations
        )
        ordinary_value_relations = build_ordinary_attention_v_relations(
            proof, attention_relations
        )
        zigzag_q_relations = build_zigzag_attention_q_relations(
            proof, attention_relations
        )
        zigzag_kv_relations = build_zigzag_attention_kv_relations(
            proof, attention_relations
        )
        ordinary_rotary = iter(ordinary_rotary_relations)
        ordinary_values = iter(ordinary_value_relations)
        zigzag_q = iter(zigzag_q_relations)
        zigzag_kv = iter(zigzag_kv_relations)
        compiled_certificates: list[object] = []
        unresolved_side_conditions: list[RelationSideCondition] = []
        _extend_unique_certificates(compiled_certificates, (
            terminal,
            *chunks,
            *terminal_mixed_certificates,
            *checkpoints,
            *rms_relations,
            *add_relations,
            *attention_output_chains,
            *attention_relations,
            *ordinary_rotary_relations,
            *ordinary_value_relations,
            *zigzag_q_relations,
            *zigzag_kv_relations,
        ))
        terminal_backbone_frontiers, terminal_backbone_layouts = normalize_relation_frontiers(
            proof,
            _terminal_inputs,
            _terminal_layouts,
            goal_ir=ir,
            deduplicate_each_round=True,
            certificate_sink=compiled_certificates,
            side_condition_sink=unresolved_side_conditions,
        )
        terminal_embedding, terminal_backbone_frontiers, terminal_backbone_layouts = (
            close_hidden_sharded_embedding_alltoall_boundaries(
                ir, proof, terminal_backbone_frontiers, terminal_backbone_layouts
            )
        )
        _extend_unique_certificates(compiled_certificates, terminal_embedding)
        terminal_init, terminal_backbone_frontiers, terminal_backbone_layouts = (
            close_init_chunk_boundaries(
                ir, proof, terminal_backbone_frontiers, terminal_backbone_layouts
            )
        )
        _extend_unique_certificates(compiled_certificates, terminal_init)
        if terminal_backbone_frontiers:
            raise RelationCompositionError(
                "indexed terminal mixed relations do not close to registered input boundaries"
            )

        unresolved = []
        unresolved_layouts = []
        for add, attention in zip(add_relations, attention_relations):
            unresolved.append(add.input_relation_step_triples[0])
            unresolved_layouts.append(attention.input_relation_kind)
            if attention.input_relation_kind == "ordinary":
                rotary = next(ordinary_rotary)
                value = next(ordinary_values)
                unresolved.extend(rotary.input_relation_step_triples)
                unresolved_layouts.extend(("ordinary", "ordinary", "ordinary"))
                unresolved.append(value.input_relation_step_triple)
                unresolved_layouts.append("ordinary")
            else:
                q_relation = next(zigzag_q)
                k_relation = next(zigzag_kv)
                v_relation = next(zigzag_kv)
                if (k_relation.role, v_relation.role) != ("k", "v"):
                    raise RelationCompositionError("zigzag K/V relation order is not stable")
                unresolved.extend((
                    q_relation.input_step_triple,
                    k_relation.input_step_triple,
                    v_relation.input_step_triple,
                ))
                unresolved_layouts.extend(("zigzag", "ordinary", "ordinary"))
        unresolved_frontiers = tuple(unresolved)
        if peel_aliases:
            unresolved_frontiers, normalized_layouts = normalize_relation_frontiers(
                proof,
                unresolved_frontiers,
                tuple(unresolved_layouts),
                goal_ir=ir,
                deduplicate_each_round=True,
                certificate_sink=compiled_certificates,
                side_condition_sink=unresolved_side_conditions,
            )
            unresolved_layouts = list(normalized_layouts)
        embedding_certificates, unresolved_frontiers, embedding_layouts = close_hidden_sharded_embedding_alltoall_boundaries(
            ir, proof, unresolved_frontiers, tuple(unresolved_layouts)
        )
        unresolved_layouts = list(embedding_layouts)
        _extend_unique_certificates(compiled_certificates, embedding_certificates)
        init_chunk_certificates, unresolved_frontiers, closed_layouts = close_init_chunk_boundaries(
            ir, proof, unresolved_frontiers, tuple(unresolved_layouts)
        )
        unresolved_layouts = list(closed_layouts)
        _extend_unique_certificates(compiled_certificates, init_chunk_certificates)
        contract_certificates, remaining_conditions = discharge_public_contract_conditions(
            ir, unresolved_side_conditions
        )
        _extend_unique_certificates(compiled_certificates, contract_certificates)
        unresolved_side_conditions = list(remaining_conditions)
        if deduplicate_frontiers:
            unresolved_frontiers, deduplicated_layouts = deduplicate_relation_frontiers(
                unresolved_frontiers, tuple(unresolved_layouts)
            )
            unresolved_layouts = list(deduplicated_layouts)
        if peel_aliases and deduplicate_frontiers:
            zigzag_regions, _authority_by_frontier = resolve_zigzag_metadata_regions(
                ir, tuple(compiled_certificates), unresolved_frontiers, tuple(unresolved_layouts)
            )
            _extend_unique_certificates(compiled_certificates, zigzag_regions)
        else:
            # Partial-pass diagnostics intentionally expose a disconnected DAG.
            # They must not publish metadata-region certificates.
            zigzag_regions = ()
        certificate_tuple = tuple(compiled_certificates)
        transition_specs = (
            build_certificate_transition_specs(proof, certificate_tuple)
            + build_synchronized_transition_specs(layers)
        )
        coverage_plan = build_exact_node_coverage_plan(ir, transition_specs)
        dependency_plan = build_transition_dependency_plan(transition_specs)
        atomic_schedule = build_atomic_schedule(ir, transition_specs)
        base_plan = RelationPlan(
            family="indexed-stack-gather",
            terminal_rule_id=terminal.rule_id,
            synchronized_steps=layers,
            certificates=certificate_tuple,
            unresolved_frontiers=unresolved_frontiers,
            unresolved_layouts=tuple(unresolved_layouts),
            unresolved_side_conditions=tuple(unresolved_side_conditions),
            zigzag_regions=zigzag_regions,
            transition_specs=transition_specs,
            coverage_plan=coverage_plan,
            dependency_plan=dependency_plan,
            atomic_schedule=atomic_schedule,
        )
        if unresolved_frontiers or unresolved_layouts or unresolved_side_conditions:
            return base_plan
        return replace(
            base_plan,
            dependent_chain_plan=build_closed_dependent_chain_plan(ir, proof, base_plan),
        )

    try:
        terminal_ce = match_inner_chunk_ce_projection_gather_two_rank(ir, proof)
    except RelationCompositionError as ce_error:
        raise RelationCompositionError(
            f"no registered relation family: stack={stack_error}; ce={ce_error}"
        ) from ce_error
    by_id = _step_map(proof)
    sm = by_id[terminal_ce.sm_ce_step]
    pm0, pm1 = (by_id[step_id] for step_id in terminal_ce.pm_ce_steps)
    frontiers = ((
        _dependency_for_input(sm, sm.input_tids[0], by_id),
        _dependency_for_input(pm0, pm0.input_tids[0], by_id),
        _dependency_for_input(pm1, pm1.input_tids[0], by_id),
    ),)
    layouts = ("ordinary",)
    compiled_certificates: list[object] = [terminal_ce]
    unresolved_side_conditions: list[RelationSideCondition] = []
    if peel_aliases:
        frontiers, layouts = normalize_relation_frontiers(
            proof,
            frontiers,
            layouts,
            goal_ir=ir,
            certificate_sink=compiled_certificates,
            side_condition_sink=unresolved_side_conditions,
            deduplicate_each_round=True,
        )
    embedding_certificates, frontiers, layouts = close_hidden_sharded_embedding_alltoall_boundaries(
        ir, proof, frontiers, layouts
    )
    _extend_unique_certificates(compiled_certificates, embedding_certificates)
    init_chunk_certificates, frontiers, layouts = close_init_chunk_boundaries(
        ir, proof, frontiers, layouts
    )
    _extend_unique_certificates(compiled_certificates, init_chunk_certificates)
    contract_certificates, remaining_conditions = discharge_public_contract_conditions(
        ir, unresolved_side_conditions
    )
    _extend_unique_certificates(compiled_certificates, contract_certificates)
    unresolved_side_conditions = list(remaining_conditions)
    if deduplicate_frontiers:
        frontiers, layouts = deduplicate_relation_frontiers(frontiers, layouts)
    if peel_aliases and deduplicate_frontiers:
        zigzag_regions, _authority_by_frontier = resolve_zigzag_metadata_regions(
            ir, tuple(compiled_certificates), frontiers, layouts
        )
        _extend_unique_certificates(compiled_certificates, zigzag_regions)
    else:
        zigzag_regions = ()
    certificate_tuple = tuple(compiled_certificates)
    transition_specs = build_certificate_transition_specs(proof, certificate_tuple)
    coverage_plan = build_exact_node_coverage_plan(ir, transition_specs)
    dependency_plan = build_transition_dependency_plan(transition_specs)
    atomic_schedule = build_atomic_schedule(ir, transition_specs)
    base_plan = RelationPlan(
        family="ce-projection-gather",
        terminal_rule_id=terminal_ce.rule_id,
        synchronized_steps=(),
        certificates=certificate_tuple,
        unresolved_frontiers=frontiers,
        unresolved_layouts=layouts,
        unresolved_side_conditions=tuple(unresolved_side_conditions),
        zigzag_regions=zigzag_regions,
        transition_specs=transition_specs,
        coverage_plan=coverage_plan,
        dependency_plan=dependency_plan,
        atomic_schedule=atomic_schedule,
    )
    if frontiers or layouts or unresolved_side_conditions:
        return base_plan
    return replace(
        base_plan,
        dependent_chain_plan=build_closed_dependent_chain_plan(ir, proof, base_plan),
    )
